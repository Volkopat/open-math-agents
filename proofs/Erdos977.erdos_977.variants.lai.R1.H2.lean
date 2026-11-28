import OMAReductions.R_Erdos977_erdos_977_variants_lai_R1
import Mathlib

-- Step Erdos977.erdos_977.variants.lai.R1.H2: hypothesis H2 of reduction Erdos977.erdos_977.variants.lai.R1
-- Credit: @koolkao

/-!
# Lai's local valuation bound for n! + 1 on a proportional interval

Original formalization (Lane C, claude-code for koolkao) of the argument of L. Lai,
On the largest prime divisor of n!+1, arXiv:2103.14894 (Lemmas 2.2, 2.4, 2.7 and Section 3),
specialised to f = 1, with all bounds on (log p) * ord_p(n!+1), so uniform in p > N.

* Luca-Shparlinski count: at most H^2 + (b-a)/H + 1 integers n in [a,b], b < p, have p | n!+1
  (a gap of length h between two of them is a root mod p of (X+1)...(X+h) - 1).
* Two blocks (u, u+h], (v, v+h'] with h <= h' whose four endpoints satisfy p^m | n!+1 and with
  distinct products give p^m | (B - A)/h!, so m log p <= h log(e x/h) + (h'-h) log x.
* Lai uses Heath-Brown's prime-gap moments only to make B - A nonzero. Here instead: equal products
  of blocks of lengths h < h' force h' - h <= 2 log2 x + 1 (2-adic valuations), so any
  2 log2 x + 2 gaps in one length bucket contain two with distinct products.
* Lemma 2.7: ranks t' in the top half of the top-t set; pairing and Jensen for y log(e x/y).
* Summing over blocks t -> (1/2 + 1/q) t by strong induction gives (|J|/(9 log(2q/(q+2)))) log^2 x.
-/


/-! Lane C, Erdős 977 (Lai) H2 — arithmetic of blocks of consecutive integers. -/

namespace LaneCLai
open Finset Real
open scoped Nat

/-- `A u h = (u+1)(u+2)…(u+h)`. -/
def A (u h : ℕ) : ℕ := ∏ i ∈ range h, (u + 1 + i)

lemma fact_mul_A (u h : ℕ) : u ! * A u h = (u + h)! := by
  induction h with
  | zero => simp [A]
  | succ h ih =>
    rw [A, prod_range_succ, ← A, ← mul_assoc, ih, show u + (h + 1) = (u + h) + 1 by ring,
      Nat.factorial_succ]
    ring

lemma A_eq (u h : ℕ) : A u h = h ! * (u + h).choose h := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (show h ≤ u + h by omega)
  rw [show u + h - h = u by omega] at h1
  have h2 := fact_mul_A u h
  have hu : 0 < u ! := Nat.factorial_pos u
  have : u ! * A u h = u ! * (h ! * (u + h).choose h) := by rw [h2, ← h1]; ring
  exact Nat.eq_of_mul_eq_mul_left hu this

lemma A_pos (u h : ℕ) : 0 < A u h := by
  unfold A; exact prod_pos (fun i _ => by omega)

lemma A_le {u h x : ℕ} (hx : u + h ≤ x) : A u h ≤ x ^ h := by
  unfold A
  calc ∏ i ∈ range h, (u + 1 + i) ≤ ∏ _i ∈ range h, x :=
        prod_le_prod' (fun i hi => by have := mem_range.mp hi; omega)
    _ = x ^ h := by simp

lemma two_le_A {u h : ℕ} (hu : 1 ≤ u) (hh : 1 ≤ h) : 2 ≤ A u h := by
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  unfold A
  rw [prod_range_succ']
  have : 1 ≤ ∏ i ∈ range k, (u + 1 + (i + 1)) := Nat.one_le_iff_ne_zero.mpr
    (prod_ne_zero_iff.mpr (fun i _ => by omega))
  nlinarith

lemma A_lt_A {u u' h : ℕ} (hh : 1 ≤ h) (hu : u < u') : A u h < A u' h := by
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  unfold A
  rw [prod_range_succ, prod_range_succ]
  have h1 : ∏ i ∈ range k, (u + 1 + i) ≤ ∏ i ∈ range k, (u' + 1 + i) :=
    prod_le_prod' (fun i _ => by omega)
  have h2 : 0 < ∏ i ∈ range k, (u + 1 + i) := prod_pos (fun i _ => by omega)
  calc (∏ i ∈ range k, (u + 1 + i)) * (u + 1 + k) < (∏ i ∈ range k, (u + 1 + i)) * (u' + 1 + k) :=
        Nat.mul_lt_mul_of_pos_left (by omega) h2
    _ ≤ _ := Nat.mul_le_mul_right _ h1

lemma A_inj {u u' h : ℕ} (hh : 1 ≤ h) (he : A u h = A u' h) : u = u' := by
  rcases lt_trichotomy u u' with h1 | h1 | h1
  · exact absurd he (A_lt_A hh h1).ne
  · exact h1
  · exact absurd he (A_lt_A hh h1).ne'

lemma coprime_of_dvd_fact_add_one {p m u : ℕ} (hp : p.Prime) (hm : 0 < m) (hu : p ^ m ∣ u ! + 1) :
    Nat.Coprime (p ^ m) (u !) := by
  apply Nat.Coprime.pow_left
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro h
  have h1 : p ∣ u ! + 1 := (dvd_pow_self p hm.ne').trans hu
  have : p ∣ 1 := (Nat.dvd_add_right h).mp h1
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

/-- Two factorials `≡ -1 (mod p^m)` give `(u+1)…v ≡ 1 (mod p^m)`. -/
lemma dvd_A_sub_one {p m u v : ℕ} (hp : p.Prime) (huv : u ≤ v) (hu : p ^ m ∣ u ! + 1)
    (hv : p ^ m ∣ v ! + 1) : p ^ m ∣ A u (v - u) - 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hcop := coprime_of_dvd_fact_add_one hp hm hu
  have hA := fact_mul_A u (v - u)
  rw [show u + (v - u) = v by omega] at hA
  have hApos := A_pos u (v - u)
  have hd := Nat.dvd_sub hv hu
  have : v ! + 1 - (u ! + 1) = u ! * (A u (v - u) - 1) := by
    rw [← hA, Nat.mul_sub, mul_one]; omega
  rw [this] at hd
  exact hcop.dvd_of_dvd_mul_left hd

/-- The two-block bound (Lai, Lemma 2.4, specialised to `f = 1`). -/
lemma two_block {p m u h u' h' x : ℕ} (hp : p.Prime) (hhp : h < p) (hh : h ≤ h')
    (h1 : p ^ m ∣ A u h - 1) (h2 : p ^ m ∣ A u' h' - 1) (hne : A u h ≠ A u' h')
    (hx1 : u + h ≤ x) (hx2 : u' + h' ≤ x) (hx : 1 ≤ x) : p ^ m * h ! ≤ x ^ h' := by
  have hc1 := A_eq u h
  have hc2 := A_eq u' h'
  obtain ⟨r, hr⟩ := Nat.factorial_dvd_factorial hh
  set c := (u + h).choose h
  set c' := r * (u' + h').choose h'
  have hA2 : A u' h' = h ! * c' := by rw [hc2, hr]; ring
  have hcop : Nat.Coprime (p ^ m) (h !) := by
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    exact fun hd => absurd ((Nat.Prime.dvd_factorial hp).mp hd) (by omega)
  have hpos1 := A_pos u h
  have hpos2 := A_pos u' h'
  have hcc : c ≠ c' := by
    intro hcc; apply hne; rw [hc1, hA2, hcc]
  rcases lt_or_gt_of_ne hcc with hlt | hlt
  · have hd := Nat.dvd_sub h2 h1
    have : A u' h' - 1 - (A u h - 1) = h ! * (c' - c) := by
      rw [hA2, hc1, Nat.mul_sub]; have := Nat.mul_le_mul_left (h !) hlt.le; omega
    rw [this] at hd
    have hd' := hcop.dvd_of_dvd_mul_left hd
    have hle : p ^ m ≤ c' - c := Nat.le_of_dvd (by omega) hd'
    calc p ^ m * h ! ≤ c' * h ! := Nat.mul_le_mul_right _ (by omega)
      _ = A u' h' := by rw [hA2]; ring
      _ ≤ x ^ h' := A_le hx2
  · have hd := Nat.dvd_sub h1 h2
    have : A u h - 1 - (A u' h' - 1) = h ! * (c - c') := by
      rw [hA2, hc1, Nat.mul_sub]; have := Nat.mul_le_mul_left (h !) hlt.le; omega
    rw [this] at hd
    have hd' := hcop.dvd_of_dvd_mul_left hd
    have hle : p ^ m ≤ c - c' := Nat.le_of_dvd (by omega) hd'
    calc p ^ m * h ! ≤ c * h ! := Nat.mul_le_mul_right _ (by omega)
      _ = A u h := by rw [hc1]; ring
      _ ≤ x ^ h := A_le hx1
      _ ≤ x ^ h' := Nat.pow_le_pow_right hx hh

/-- `phiL x y = y (1 + log x - log y)`. -/
noncomputable def phiL (x y : ℝ) : ℝ := y * (1 + Real.log x - Real.log y)

lemma log_factorial_ge (h : ℕ) : (h : ℝ) * Real.log h - h ≤ Real.log (h ! : ℝ) := by
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · simp
  have h1 := Real.pow_div_factorial_le_exp (h : ℝ) (show (0 : ℝ) ≤ h by positivity) h
  have hf : (0 : ℝ) < (h ! : ℝ) := by exact_mod_cast Nat.factorial_pos h
  have hp : (0 : ℝ) < (h : ℝ) ^ h := pow_pos (by exact_mod_cast hh) _
  have := Real.log_le_log (div_pos hp hf) h1
  rw [Real.log_div hp.ne' hf.ne', Real.log_exp, Real.log_pow] at this
  linarith

lemma two_block_log {p m u h u' h' x : ℕ} (hp : p.Prime) (hhp : h < p) (hh : h ≤ h')
    (h1 : p ^ m ∣ A u h - 1) (h2 : p ^ m ∣ A u' h' - 1) (hne : A u h ≠ A u' h')
    (hx1 : u + h ≤ x) (hx2 : u' + h' ≤ x) (hx : 1 ≤ x) :
    (m : ℝ) * Real.log p ≤ phiL x h + ((h' : ℝ) - h) * Real.log x := by
  have key := two_block hp hhp hh h1 h2 hne hx1 hx2 hx
  have hpp : (0 : ℝ) < (p : ℝ) ^ m := pow_pos (by exact_mod_cast hp.pos) _
  have hf : (0 : ℝ) < (h ! : ℝ) := by exact_mod_cast Nat.factorial_pos h
  have hx' : (0 : ℝ) < x := by exact_mod_cast hx
  have key' : ((p : ℝ) ^ m) * (h ! : ℝ) ≤ (x : ℝ) ^ h' := by exact_mod_cast key
  have hl := Real.log_le_log (mul_pos hpp hf) key'
  rw [Real.log_mul hpp.ne' hf.ne', Real.log_pow, Real.log_pow] at hl
  have := log_factorial_ge h
  unfold phiL
  nlinarith

lemma one_block_log {p m u h x : ℕ} (hu : 1 ≤ u) (hh : 1 ≤ h) (h1 : p ^ m ∣ A u h - 1)
    (hx1 : u + h ≤ x) (hp : 1 < p) :
    (m : ℝ) * Real.log p ≤ h * Real.log x := by
  have h2 := two_le_A hu hh
  have hle : p ^ m ≤ A u h - 1 := Nat.le_of_dvd (by omega) h1
  have hle2 : p ^ m ≤ x ^ h := le_trans hle (le_trans (Nat.sub_le _ _) (A_le hx1))
  have hx : 1 ≤ x := by omega
  have hpp : (0 : ℝ) < (p : ℝ) ^ m := pow_pos (by exact_mod_cast (show 0 < p by omega)) _
  have key' : ((p : ℝ) ^ m) ≤ (x : ℝ) ^ h := by exact_mod_cast hle2
  have hl := Real.log_le_log hpp key'
  rw [Real.log_pow, Real.log_pow] at hl
  linarith

lemma digits_sum_le (n : ℕ) : (Nat.digits 2 n).sum ≤ Nat.log 2 n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hlen := Nat.length_digits 2 n (by norm_num) hn.ne'
  have : ∀ d ∈ Nat.digits 2 n, d ≤ 1 := fun d hd => by
    have := Nat.digits_lt_base (by norm_num) hd; omega
  calc (Nat.digits 2 n).sum ≤ (Nat.digits 2 n).length * 1 := List.sum_le_card_nsmul _ _ this
    _ = _ := by rw [hlen]; ring

lemma padic_two_fact_ge (n : ℕ) : n ≤ padicValNat 2 (n !) + Nat.log 2 n + 1 := by
  have := @sub_one_mul_padicValNat_factorial 2 ⟨Nat.prime_two⟩ n
  have h2 := digits_sum_le n
  norm_num at this
  omega

lemma padic_two_fact_le (n : ℕ) : padicValNat 2 (n !) ≤ n := by
  have := @sub_one_mul_padicValNat_factorial 2 ⟨Nat.prime_two⟩ n
  norm_num at this
  omega

/-- Equal products of blocks of different lengths force the lengths to be close. -/
lemma eq_prod_close {u h u' h' x : ℕ} (he : A u h = A u' h') (hh : h < h')
    (hx1 : u + h ≤ x) (hx2 : u' + h' ≤ x) : h' - h ≤ 2 * Nat.log 2 x + 1 := by
  have hdvd : h' ! ∣ h ! * (u + h).choose h := by
    rw [← A_eq, he, A_eq]; exact dvd_mul_right _ _
  have hne1 : h ! ≠ 0 := Nat.factorial_ne_zero h
  have hne2 : (u + h).choose h ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hv := (Nat.factorization_le_iff_dvd (Nat.factorial_ne_zero h')
    (mul_ne_zero hne1 hne2)).mpr hdvd 2
  rw [Nat.factorization_mul hne1 hne2] at hv
  simp only [Finsupp.add_apply] at hv
  rw [Nat.factorization_def _ Nat.prime_two, Nat.factorization_def _ Nat.prime_two] at hv
  have hc := @Nat.factorization_choose_le_log 2 (u + h) h
  have h3 := padic_two_fact_ge h'
  have h4 := padic_two_fact_le h
  have h5 : Nat.log 2 (u + h) ≤ Nat.log 2 x := Nat.log_mono_right hx1
  have h6 : Nat.log 2 h' ≤ Nat.log 2 x := Nat.log_mono_right (by omega)
  omega

end LaneCLai


/-! Lane C, Erdős 977 (Lai) H2 — sorted positions and gaps of a finite set of naturals. -/

namespace LaneCLai
open Finset

/-- The `i`-th smallest element of `P` (junk `0` past the end). -/
noncomputable def pos (P : Finset ℕ) (i : ℕ) : ℕ :=
  if h : i < P.card then P.orderEmbOfFin rfl ⟨i, h⟩ else 0

lemma pos_mem {P : Finset ℕ} {i : ℕ} (hi : i < P.card) : pos P i ∈ P := by
  unfold pos; rw [dif_pos hi]; exact orderEmbOfFin_mem P rfl _

lemma pos_lt {P : Finset ℕ} {i j : ℕ} (hij : i < j) (hj : j < P.card) : pos P i < pos P j := by
  unfold pos; rw [dif_pos (hij.trans hj), dif_pos hj]
  exact (P.orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.mpr hij)

lemma pos_le {P : Finset ℕ} {i j : ℕ} (hij : i ≤ j) (hj : j < P.card) : pos P i ≤ pos P j := by
  rcases hij.lt_or_eq with h | rfl
  · exact (pos_lt h hj).le
  · exact le_rfl

lemma pos_inj {P : Finset ℕ} {i j : ℕ} (hi : i < P.card) (hj : j < P.card)
    (h : pos P i = pos P j) : i = j := by
  rcases lt_trichotomy i j with h1 | h1 | h1
  · exact absurd h (pos_lt h1 hj).ne
  · exact h1
  · exact absurd h (pos_lt h1 hi).ne'

lemma exists_pos {P : Finset ℕ} {n : ℕ} (hn : n ∈ P) : ∃ i < P.card, pos P i = n := by
  have : n ∈ Set.range (P.orderEmbOfFin rfl) := by rw [range_orderEmbOfFin]; exact hn
  obtain ⟨⟨i, hi⟩, hi'⟩ := this
  exact ⟨i, hi, by unfold pos; rw [dif_pos hi]; exact hi'⟩

lemma pos_mem_Icc {P : Finset ℕ} {a b i : ℕ} (hP : P ⊆ Icc a b) (hi : i < P.card) :
    a ≤ pos P i ∧ pos P i ≤ b := mem_Icc.mp (hP (pos_mem hi))

/-- Length of the `i`-th gap. -/
noncomputable def len (P : Finset ℕ) (i : ℕ) : ℕ := pos P (i + 1) - pos P i

lemma len_pos {P : Finset ℕ} {i : ℕ} (hi : i + 1 < P.card) : 1 ≤ len P i := by
  unfold len; have := pos_lt (P := P) (show i < i + 1 by omega) hi; omega

lemma pos_add_len {P : Finset ℕ} {i : ℕ} (hi : i + 1 < P.card) :
    pos P i + len P i = pos P (i + 1) := by
  unfold len; have := pos_lt (P := P) (show i < i + 1 by omega) hi; omega

lemma sum_len {P : Finset ℕ} (n : ℕ) (hn : n < P.card) :
    ∑ i ∈ range n, len P i = pos P n - pos P 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih (by omega)]
    have h1 := pos_le (Nat.zero_le n) (show n < P.card by omega)
    have h2 := pos_add_len (P := P) (i := n) hn
    omega

lemma sum_len_le {P : Finset ℕ} {a b : ℕ} (hP : P ⊆ Icc a b) (hc : 1 ≤ P.card) :
    ∑ i ∈ range (P.card - 1), len P i ≤ b - a := by
  rw [sum_len _ (by omega)]
  have h1 := pos_mem_Icc hP (show P.card - 1 < P.card by omega)
  have h2 := pos_mem_Icc hP (show 0 < P.card by omega)
  omega

/-- Gaps with an endpoint outside `P'` number at most `2 |P \ P'|`. -/
lemma card_dead_le {P P' : Finset ℕ} :
    ((range (P.card - 1)).filter (fun i => pos P i ∉ P' ∨ pos P (i + 1) ∉ P')).card
      ≤ 2 * (P \ P').card := by
  have hsub : (range (P.card - 1)).filter (fun i => pos P i ∉ P' ∨ pos P (i + 1) ∉ P') ⊆
      ((range (P.card - 1)).filter (fun i => pos P i ∉ P')) ∪
      ((range (P.card - 1)).filter (fun i => pos P (i + 1) ∉ P')) := by
    intro i hi; simp only [mem_filter, mem_union] at hi ⊢; tauto
  have c1 : ((range (P.card - 1)).filter (fun i => pos P i ∉ P')).card ≤ (P \ P').card := by
    apply card_le_card_of_injOn (pos P)
    · intro i hi
      simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hi
      simp only [coe_sdiff, Set.mem_diff, mem_coe]
      exact ⟨pos_mem (by omega), hi.2⟩
    · intro i hi j hj h
      simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hi hj
      exact pos_inj (by omega) (by omega) h
  have c2 : ((range (P.card - 1)).filter (fun i => pos P (i + 1) ∉ P')).card ≤ (P \ P').card := by
    apply card_le_card_of_injOn (fun i => pos P (i + 1))
    · intro i hi
      simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hi
      simp only [coe_sdiff, Set.mem_diff, mem_coe]
      exact ⟨pos_mem (by omega), hi.2⟩
    · intro i hi j hj h
      simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hi hj
      have := pos_inj (by omega) (by omega) h
      omega
  calc _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_union_le _ _
    _ ≤ _ := by omega

end LaneCLai


/-! Lane C, Erdős 977 (Lai) H2 — few `n` in an interval below `p` with `p ∣ n! + 1`
(Luca–Shparlinski, Lemma 2.2 of Lai, `f = 1`), via root counting modulo `p`. -/

namespace LaneCLai
open Finset Polynomial
open scoped Nat

/-- `(X+1)(X+2)…(X+h) - 1` over `ZMod p`. -/
noncomputable def Ppoly (p h : ℕ) : (ZMod p)[X] :=
  (∏ j ∈ range h, (X + C ((j : ZMod p) + 1))) - 1

lemma Ppoly_natDegree (p h : ℕ) [Fact p.Prime] (hh : 1 ≤ h) : (Ppoly p h).natDegree = h := by
  unfold Ppoly
  rw [show (1 : (ZMod p)[X]) = C 1 by simp, natDegree_sub_C, natDegree_prod_of_monic]
  · rw [Finset.sum_congr rfl (fun j _ => natDegree_X_add_C _)]
    simp
  · intro j _; exact monic_X_add_C _

lemma Ppoly_ne_zero (p h : ℕ) [Fact p.Prime] (hh : 1 ≤ h) : Ppoly p h ≠ 0 := by
  intro h0
  have := Ppoly_natDegree p h hh
  rw [h0, natDegree_zero] at this
  omega

lemma Ppoly_eval (p u h : ℕ) : (Ppoly p h).eval (u : ZMod p) = ((A u h : ℕ) : ZMod p) - 1 := by
  unfold Ppoly A
  simp only [eval_sub, eval_prod, eval_add, eval_X, eval_C, eval_one, Nat.cast_prod]
  congr 1
  apply prod_congr rfl
  intro j _
  push_cast; ring

/-- At most `h` gaps of length exactly `h`. -/
lemma card_len_eq_le {p : ℕ} (hp : p.Prime) {Q : Finset ℕ} {b : ℕ} (hQ : ∀ n ∈ Q, n ≤ b)
    (hb : b < p) (hdiv : ∀ n ∈ Q, p ∣ n ! + 1) (h : ℕ) (hh : 1 ≤ h) :
    ((range (Q.card - 1)).filter (fun i => len Q i = h)).card ≤ h := by
  haveI : Fact p.Prime := ⟨hp⟩
  set S := (range (Q.card - 1)).filter (fun i => len Q i = h)
  have hinj : Set.InjOn (fun i => ((pos Q i : ℕ) : ZMod p)) (S : Set ℕ) := by
    intro i hi j hj hij
    simp only [S, coe_filter, mem_range, Set.mem_setOf_eq] at hi hj
    have hi' := hQ _ (pos_mem (show i < Q.card by omega))
    have hj' := hQ _ (pos_mem (show j < Q.card by omega))
    have : pos Q i = pos Q j := by
      have := (ZMod.natCast_eq_natCast_iff' _ _ p).mp hij
      rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact pos_inj (by omega) (by omega) this
  have hcard : S.card = (S.image (fun i => ((pos Q i : ℕ) : ZMod p))).card :=
    (card_image_of_injOn hinj).symm
  rw [hcard, ← Ppoly_natDegree p h hh]
  apply card_le_degree_of_subset_roots
  intro z hz
  rw [Finset.mem_val, mem_image] at hz
  obtain ⟨i, hi, rfl⟩ := hz
  simp only [S, mem_filter, mem_range] at hi
  rw [mem_roots (Ppoly_ne_zero p h hh), IsRoot.def, Ppoly_eval]
  have hu := pos_mem (show i < Q.card by omega)
  have hv := pos_mem (show i + 1 < Q.card by omega)
  have hlen : len Q i = h := hi.2
  have hd := dvd_A_sub_one (m := 1) hp
    (pos_lt (P := Q) (show i < i + 1 by omega) (show i + 1 < Q.card by omega)).le
    (by simpa using hdiv _ hu) (by simpa using hdiv _ hv)
  rw [pow_one] at hd
  change p ∣ A (pos Q i) (len Q i) - 1 at hd
  rw [hlen] at hd
  have hA := A_pos (pos Q i) h
  have h1 : ((A (pos Q i) h - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
  rw [Nat.cast_sub hA, Nat.cast_one, sub_eq_zero] at h1
  rw [h1, sub_self]

/-- Lai's Lemma 2.2 for `f = 1`: `|Q| ≤ H² + (b-a)/H + 1`. -/
lemma card_LS {p : ℕ} (hp : p.Prime) {Q : Finset ℕ} {a b : ℕ} (hQ : Q ⊆ Icc a b)
    (hb : b < p) (hdiv : ∀ n ∈ Q, p ∣ n ! + 1) (H : ℕ) (hH : 1 ≤ H) :
    Q.card * H ≤ H * H * H + (b - a) + H := by
  rcases Nat.eq_zero_or_pos Q.card with h0 | hc
  · rw [h0]; simp
  have hQb : ∀ n ∈ Q, n ≤ b := fun n hn => (mem_Icc.mp (hQ hn)).2
  set G := range (Q.card - 1)
  have hsplit : G.card = (G.filter (fun i => len Q i ≤ H)).card +
      (G.filter (fun i => ¬ len Q i ≤ H)).card := (card_filter_add_card_filter_not _).symm
  have hsmall : (G.filter (fun i => len Q i ≤ H)).card ≤ H * H := by
    have hsub : G.filter (fun i => len Q i ≤ H) ⊆
        (Icc 1 H).biUnion (fun h => G.filter (fun i => len Q i = h)) := by
      intro i hi
      simp only [G, mem_filter, mem_range] at hi
      simp only [mem_biUnion, mem_Icc, mem_filter, G, mem_range]
      exact ⟨len Q i, ⟨len_pos (by omega), hi.2⟩, hi.1, rfl⟩
    calc _ ≤ _ := card_le_card hsub
      _ ≤ ∑ h ∈ Icc 1 H, (G.filter (fun i => len Q i = h)).card := card_biUnion_le
      _ ≤ ∑ h ∈ Icc 1 H, H := sum_le_sum (fun h hh => by
          have := mem_Icc.mp hh
          exact (card_len_eq_le hp hQb hb hdiv h this.1).trans this.2)
      _ = H * H := by simp
  have hbig : (G.filter (fun i => ¬ len Q i ≤ H)).card * H ≤ b - a := by
    calc (G.filter (fun i => ¬ len Q i ≤ H)).card * H
        = ∑ i ∈ G.filter (fun i => ¬ len Q i ≤ H), H := by rw [sum_const, smul_eq_mul]
      _ ≤ ∑ i ∈ G.filter (fun i => ¬ len Q i ≤ H), len Q i :=
          sum_le_sum (fun i hi => by simp only [mem_filter] at hi; omega)
      _ ≤ ∑ i ∈ G, len Q i := sum_le_sum_of_subset (filter_subset _ _)
      _ ≤ b - a := sum_len_le hQ hc
  have hG : G.card = Q.card - 1 := card_range _
  have : Q.card ≤ H * H + (G.filter (fun i => ¬ len Q i ≤ H)).card + 1 := by omega
  calc Q.card * H ≤ (H * H + (G.filter (fun i => ¬ len Q i ≤ H)).card + 1) * H :=
        Nat.mul_le_mul_right _ this
    _ = H * H * H + (G.filter (fun i => ¬ len Q i ≤ H)).card * H + H := by ring
    _ ≤ _ := by omega

end LaneCLai


/-! Lane C, Erdős 977 (Lai) H2 — the function `phiL x y = y (1 + log x - log y)`:
monotonicity on `[0, x]`, Jensen's inequality, and a pairing (layer cake) inequality. -/

namespace LaneCLai
open Finset Real

lemma phiL_nonneg {x y : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) : 0 ≤ phiL x y := by
  unfold phiL
  rcases hy.eq_or_lt with rfl | hy'
  · simp
  have := Real.log_le_log hy' hyx
  nlinarith

lemma phiL_mono {x y₁ y₂ : ℝ} (h1 : 0 ≤ y₁) (h12 : y₁ ≤ y₂) (h2x : y₂ ≤ x) : phiL x y₁ ≤ phiL x y₂ := by
  rcases h1.eq_or_lt with rfl | h1'
  · rw [show phiL x 0 = 0 by simp [phiL]]; exact phiL_nonneg (by linarith) h2x
  have hy2 : 0 < y₂ := lt_of_lt_of_le h1' h12
  -- tangent line for y log y at y₂
  have ht : y₂ * Real.log y₂ - y₁ * Real.log y₁ ≤ (Real.log y₂ + 1) * (y₂ - y₁) := by
    have := Real.log_le_sub_one_of_pos (show 0 < y₂ / y₁ from div_pos hy2 h1')
    rw [Real.log_div hy2.ne' h1'.ne'] at this
    have h3 : y₁ * (Real.log y₂ - Real.log y₁) ≤ y₁ * (y₂ / y₁ - 1) :=
      mul_le_mul_of_nonneg_left this h1
    have h4 : y₁ * (y₂ / y₁ - 1) = y₂ - y₁ := by first | (field_simp; ring) | field_simp
    rw [h4] at h3
    linarith
  have hl := Real.log_le_log hy2 h2x
  unfold phiL
  nlinarith

lemma phiL_concave {x : ℝ} (hx : 1 ≤ x) : ConcaveOn ℝ (Set.Ici 0) (phiL x) := by
  have hc : 0 ≤ 1 + Real.log x := by have := Real.log_nonneg hx; linarith
  have h1 : ConcaveOn ℝ (Set.Ici (0:ℝ)) (fun y => (1 + Real.log x) * y) := by
    refine ⟨convex_Ici 0, fun a _ b _ s t _ _ _ => ?_⟩
    simp only [smul_eq_mul]; exact le_of_eq (by ring)
  have h2 := h1.add Real.concaveOn_negMulLog
  have heq : phiL x = (fun y => (1 + Real.log x) * y) + Real.negMulLog := by
    funext y
    simp only [phiL, Pi.add_apply, Real.negMulLog]
    ring
  rw [heq]
  exact h2

/-- Jensen: `∑ phiL(ℓ g) ≤ Λ log n + x` when `∑ ℓ ≤ Λ ≤ x`. -/
lemma jensen_phiL {ι : Type*} (G : Finset ι) (ℓ : ι → ℝ) {x Λ : ℝ} (hx : 1 ≤ x)
    (hℓ : ∀ g ∈ G, 0 ≤ ℓ g) (hS : ∑ g ∈ G, ℓ g ≤ Λ) (hΛ : Λ ≤ x) (hG : 1 ≤ G.card) :
    ∑ g ∈ G, phiL x (ℓ g) ≤ Λ * Real.log G.card + x := by
  set n : ℝ := (G.card : ℝ) with hndef
  have hn : (1 : ℝ) ≤ n := by rw [hndef]; exact_mod_cast hG
  have hn0 : (0 : ℝ) < n := by linarith
  have hn0' : n ≠ 0 := hn0.ne'
  set S := ∑ g ∈ G, ℓ g with hSdef
  have hS0 : 0 ≤ S := sum_nonneg hℓ
  have hΛ0 : 0 ≤ Λ := hS0.trans hS
  have hw1 : ∑ _g ∈ G, (1 / n) = 1 := by
    rw [sum_const, nsmul_eq_mul, ← hndef]; field_simp
  have hJ := (phiL_concave hx).le_map_sum (t := G) (w := fun _ => 1 / n) (p := ℓ)
    (fun _ _ => div_nonneg zero_le_one hn0.le) hw1 (fun g hg => Set.mem_Ici.mpr (hℓ g hg))
  simp only [smul_eq_mul] at hJ
  rw [← mul_sum, ← mul_sum] at hJ
  have hJ' : ∑ g ∈ G, phiL x (ℓ g) ≤ n * phiL x (S / n) := by
    have h1 := mul_le_mul_of_nonneg_left hJ hn0.le
    calc ∑ g ∈ G, phiL x (ℓ g) = n * (1 / n * ∑ g ∈ G, phiL x (ℓ g)) := by field_simp
      _ ≤ n * phiL x (1 / n * S) := h1
      _ = n * phiL x (S / n) := by rw [one_div_mul_eq_div]
  refine hJ'.trans ?_
  have hln := Real.log_nonneg hn
  rcases hS0.eq_or_lt with h0 | hpos
  · rw [← h0]
    simp only [zero_div, phiL, zero_mul, mul_zero]
    nlinarith [mul_nonneg hΛ0 hln]
  have hrw : n * phiL x (S / n) = S * Real.log n + S * (1 + Real.log x - Real.log S) := by
    unfold phiL
    rw [Real.log_div hpos.ne' hn0']
    first | (first | (field_simp; ring) | field_simp) | field_simp
  rw [hrw]
  have hSx : S ≤ x := hS.trans hΛ
  have hxS : S * (1 + Real.log x - Real.log S) ≤ x := by
    have hx0 : 0 < x := by linarith
    have := Real.log_le_sub_one_of_pos (show 0 < x / S from div_pos hx0 hpos)
    rw [Real.log_div hx0.ne' hpos.ne'] at this
    have h3 := mul_le_mul_of_nonneg_left this hpos.le
    have h4 : S * (x / S - 1) = x - S := by first | (field_simp; ring) | field_simp
    rw [h4] at h3
    linarith
  have := mul_le_mul_of_nonneg_right hS hln
  linarith

/-- Pairing inequality: if for each `j < n` at least `2 (n - j)` of the `ℓ g` are `≥ y j`,
then `2 ∑_{j<n} phiL (y j) ≤ ∑_g phiL (ℓ g)`. -/
lemma layer_phiL {ι : Type*} [DecidableEq ι] {x : ℝ} (ℓ : ι → ℝ) (y : ℕ → ℝ)
    (hy : ∀ j, 0 ≤ y j) : ∀ (n : ℕ) (G : Finset ι), (∀ g ∈ G, 0 ≤ ℓ g ∧ ℓ g ≤ x) →
    (∀ j < n, 2 * (n - j) ≤ (G.filter (fun g => y j ≤ ℓ g)).card) →
    2 * ∑ j ∈ range n, phiL x (y j) ≤ ∑ g ∈ G, phiL x (ℓ g) := by
  intro n
  induction n with
  | zero =>
    intro G hG _
    simp only [range_zero, sum_empty, mul_zero]
    exact sum_nonneg (fun g hg => phiL_nonneg (hG g hg).1 (hG g hg).2)
  | succ n ih =>
    intro G hG hcnt
    have h2 := hcnt n (Nat.lt_succ_self n)
    rw [show n + 1 - n = 1 by omega] at h2
    obtain ⟨g₁, hg₁, g₂, hg₂, hne⟩ :=
      (Finset.one_lt_card (s := G.filter (fun g => y n ≤ ℓ g))).mp (by omega)
    simp only [mem_filter] at hg₁ hg₂
    obtain ⟨G', hG'def⟩ : ∃ G' : Finset ι, G' = (G.erase g₁).erase g₂ := ⟨_, rfl⟩
    have hG'm : ∀ g, g ∈ G' ↔ g ≠ g₂ ∧ g ≠ g₁ ∧ g ∈ G := by
      intro g; rw [hG'def, mem_erase, mem_erase]
    have hG' : ∀ g ∈ G', 0 ≤ ℓ g ∧ ℓ g ≤ x := fun g hg => hG g ((hG'm g).mp hg).2.2
    have hcnt' : ∀ j < n, 2 * (n - j) ≤ (G'.filter (fun g => y j ≤ ℓ g)).card := by
      intro j hj
      have := hcnt j (by omega)
      have hsub : G.filter (fun g => y j ≤ ℓ g) ⊆
          insert g₁ (insert g₂ (G'.filter (fun g => y j ≤ ℓ g))) := by
        intro g hg
        simp only [mem_filter] at hg
        simp only [mem_insert, mem_filter, hG'm]
        by_cases h1 : g = g₁
        · left; exact h1
        by_cases h2' : g = g₂
        · right; left; exact h2'
        right; right; exact ⟨⟨h2', h1, hg.1⟩, hg.2⟩
      have := (card_le_card hsub).trans (card_insert_le _ _)
      have := this.trans (Nat.succ_le_succ (card_insert_le _ _))
      omega
    have hrec := ih G' hG' hcnt'
    have hsplit : ∑ g ∈ G, phiL x (ℓ g) =
        phiL x (ℓ g₁) + phiL x (ℓ g₂) + ∑ g ∈ G', phiL x (ℓ g) := by
      rw [hG'def, ← add_sum_erase _ _ hg₁.1,
        ← add_sum_erase _ _ (mem_erase.mpr ⟨hne.symm, hg₂.1⟩)]
      ring
    have m1 := phiL_mono (hy n) hg₁.2 (hG g₁ hg₁.1).2
    have m2 := phiL_mono (hy n) hg₂.2 (hG g₂ hg₂.1).2
    rw [sum_range_succ, hsplit]
    linarith

end LaneCLai


/-! Lane C, Erdős 977 (Lai) H2 — the one-level estimate behind Lai's Lemma 2.7.

`P` is a set of points, `P' ⊆ P` the points where `p^m ∣ n! + 1`.  If at least `2|P \ P'| + R + 1`
gaps of `P` have length `≤ y`, then at least `R + 1` of them have both endpoints in `P'`; a bucket of
width `y / B + 1` contains `2 log₂ x + 2` of them, two of which have distinct products (lengths of
blocks with equal products differ by at most `2 log₂ x + 1`), and the two-block bound applies. -/

namespace LaneCLai
open Finset Real
open scoped Nat

lemma gap_dvd {p m : ℕ} (hp : p.Prime) {P P' : Finset ℕ} (hm : ∀ n ∈ P', p ^ m ∣ n ! + 1)
    {i : ℕ} (hi : i + 1 < P.card) (h1 : pos P i ∈ P') (h2 : pos P (i + 1) ∈ P') :
    p ^ m ∣ A (pos P i) (len P i) - 1 :=
  dvd_A_sub_one hp (pos_lt (P := P) (show i < i + 1 by omega) hi).le (hm _ h1) (hm _ h2)

lemma sub_lt_of_div_eq {u v w : ℕ} (hw : 0 < w) (huv : u ≤ v) (he : u / w = v / w) : v - u < w := by
  have h1 := Nat.lt_div_mul_add (a := v) hw
  have h2 := Nat.div_mul_le_self u w
  rw [he] at h2
  omega

lemma per_k {p m a b x : ℕ} (hp : p.Prime) (hx : 1 ≤ x) (hbx : b ≤ x) (hbp : b < p)
    {P P' : Finset ℕ} (hP : P ⊆ Icc a b) (hm : ∀ n ∈ P', p ^ m ∣ n ! + 1)
    {y R B : ℕ} (hyx : y ≤ x) (hB : 1 ≤ B) (hBR : B * (2 * Nat.log 2 x + 2) ≤ R)
    (hwin : 2 * (P \ P').card + R + 1 ≤
      ((range (P.card - 1)).filter (fun i => len P i ≤ y)).card) :
    (m : ℝ) * Real.log p ≤ phiL x y + ((y / B : ℕ) : ℝ) * Real.log x := by
  classical
  set E := 2 * Nat.log 2 x + 1 with hE
  set G := range (P.card - 1)
  set W := G.filter (fun i => len P i ≤ y ∧ pos P i ∈ P' ∧ pos P (i + 1) ∈ P')
  have hW : R + 1 ≤ W.card := by
    have hsub : G.filter (fun i => len P i ≤ y) ⊆
        W ∪ G.filter (fun i => pos P i ∉ P' ∨ pos P (i + 1) ∉ P') := by
      intro i hi
      simp only [mem_filter] at hi
      simp only [W, mem_union, mem_filter]
      by_cases h : pos P i ∈ P' ∧ pos P (i + 1) ∈ P'
      · left; exact ⟨hi.1, hi.2, h⟩
      · right; exact ⟨hi.1, by tauto⟩
    have := (card_le_card hsub).trans (card_union_le _ _)
    have hd : (G.filter (fun i => pos P i ∉ P' ∨ pos P (i + 1) ∉ P')).card ≤
        2 * (P \ P').card := card_dead_le (P := P) (P' := P')
    omega
  set w := y / B + 1 with hw
  have hw0 : 0 < w := Nat.succ_pos _
  set f : ℕ → ℕ := fun i => (len P i - 1) / w
  have hmaps : ∀ i ∈ W, f i ∈ range B := by
    intro i hi
    simp only [W, mem_filter] at hi
    rw [mem_range]
    show (len P i - 1) / w < B
    apply Nat.div_lt_of_lt_mul
    have h1 := Nat.lt_div_mul_add (a := y) (show 0 < B by omega)
    have h2 : len P i - 1 ≤ y := by omega
    calc len P i - 1 ≤ y := h2
      _ < y / B * B + B := h1
      _ = w * B := by rw [hw]; ring
  have hcard : (range B).card * (E + 1) < W.card := by
    rw [card_range]
    calc B * (E + 1) = B * (2 * Nat.log 2 x + 2) := by rw [hE]; try ring
      _ ≤ R := hBR
      _ < W.card := by omega
  obtain ⟨c, -, hc⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hcard
  set F := W.filter (fun i => f i = c)
  have hFW : F ⊆ W := filter_subset _ _
  have hlen1 : ∀ i ∈ W, 1 ≤ len P i := by
    intro i hi; simp only [W, G, mem_filter, mem_range] at hi; exact len_pos (by omega)
  have hiW : ∀ i ∈ W, i + 1 < P.card := by
    intro i hi; simp only [W, G, mem_filter, mem_range] at hi; omega
  have hposx : ∀ i ∈ W, pos P i + len P i ≤ x := by
    intro i hi
    rw [pos_add_len (hiW i hi)]
    exact (pos_mem_Icc hP (show i + 1 < P.card from hiW i hi)).2.trans hbx
  -- two gaps in the same bucket with distinct products
  have hex : ∃ i ∈ F, ∃ j ∈ F, len P i ≤ len P j ∧
      A (pos P i) (len P i) ≠ A (pos P j) (len P j) := by
    by_contra hall
    push_neg at hall
    have hFne : F.Nonempty := card_pos.mp (by omega)
    obtain ⟨i₀, hi₀, hmin⟩ := exists_min_image F (len P) hFne
    have hrange : ∀ j ∈ F, len P j ∈ Icc (len P i₀) (len P i₀ + E) := by
      intro j hj
      have h1 := hmin j hj
      rw [mem_Icc]
      refine ⟨h1, ?_⟩
      rcases h1.lt_or_eq with h2 | h2
      · have := eq_prod_close (hall i₀ hi₀ j hj h1) h2 (hposx i₀ (hFW hi₀)) (hposx j (hFW hj))
        omega
      · omega
    have hinj : Set.InjOn (len P) (F : Set ℕ) := by
      intro i hi j hj hij
      have hi' : i ∈ F := hi
      have hj' : j ∈ F := hj
      have hA := hall i hi' j hj' hij.le
      rw [hij] at hA
      have := A_inj (hlen1 j (hFW hj')) hA
      exact pos_inj (by have := hiW i (hFW hi'); omega) (by have := hiW j (hFW hj'); omega) this
    have := card_le_card_of_injOn (len P) (fun j hj => mem_coe.mpr (hrange j (mem_coe.mp hj))) hinj
    rw [Nat.card_Icc] at this
    omega
  obtain ⟨i, hiF, j, hjF, hij, hne⟩ := hex
  have hiW' := hFW hiF
  have hjW' := hFW hjF
  have hi2 := hiW'
  have hj2 := hjW'
  simp only [W, mem_filter] at hi2 hj2
  have hfij : f i = f j := by
    simp only [F, mem_filter] at hiF hjF; rw [hiF.2, hjF.2]
  have hdiff0 : len P j - len P i ≤ w - 1 := by
    have := sub_lt_of_div_eq hw0 (Nat.sub_le_sub_right hij 1) hfij
    have h1 := hlen1 i hiW'
    omega
  have hw1 : w - 1 = y / B := by rw [hw, Nat.add_sub_cancel]
  have hdiff : len P j - len P i ≤ y / B := hw1 ▸ hdiff0
  have hlp : len P i < p := by
    have := pos_mem_Icc hP (show i + 1 < P.card from hiW i hiW')
    have := pos_mem_Icc hP (show i < P.card by have := hiW i hiW'; omega)
    unfold len; omega
  have key := two_block_log hp hlp hij (gap_dvd hp hm (hiW i hiW') hi2.2.2.1 hi2.2.2.2)
    (gap_dvd hp hm (hiW j hjW') hj2.2.2.1 hj2.2.2.2) hne (hposx i hiW') (hposx j hjW') hx
  have hmono := phiL_mono (x := (x : ℝ)) (Nat.cast_nonneg (len P i))
    (show (len P i : ℝ) ≤ y by exact_mod_cast hi2.2.1) (by exact_mod_cast hyx)
  have hlx : 0 ≤ Real.log x := Real.log_nonneg (by exact_mod_cast hx)
  have hd' : ((len P j : ℝ) - len P i) ≤ ((y / B : ℕ) : ℝ) := by
    rw [← Nat.cast_sub hij]; exact_mod_cast hdiff
  nlinarith

end LaneCLai


/-! Lane C, Erdős 977 (Lai) H2 — ranks (a greedy chain of top sets) and Lai's Lemma 2.7. -/

namespace LaneCLai
open Finset Real
open scoped Nat

noncomputable def nextPt (Q S : Finset ℕ) (o : ℕ → ℕ) : ℕ :=
  if h : (Q \ S).Nonempty then Classical.choose (exists_max_image (Q \ S) o h) else 0

lemma nextPt_spec {Q S : Finset ℕ} {o : ℕ → ℕ} (h : (Q \ S).Nonempty) :
    nextPt Q S o ∈ Q \ S ∧ ∀ n ∈ Q \ S, o n ≤ o (nextPt Q S o) := by
  unfold nextPt; rw [dif_pos h]; exact Classical.choose_spec (exists_max_image (Q \ S) o h)

/-- `chain Q o r` = the `r` points of `Q` with the largest values of `o` (greedy). -/
noncomputable def chain (Q : Finset ℕ) (o : ℕ → ℕ) : ℕ → Finset ℕ
  | 0 => ∅
  | r + 1 => if (Q \ chain Q o r).Nonempty then insert (nextPt Q (chain Q o r) o) (chain Q o r)
      else chain Q o r

/-- `val Q o r` = the `(r+1)`-th largest value. -/
noncomputable def val (Q : Finset ℕ) (o : ℕ → ℕ) (r : ℕ) : ℕ := o (nextPt Q (chain Q o r) o)

variable {Q : Finset ℕ} {o : ℕ → ℕ}

lemma chain_basic : ∀ r ≤ Q.card, chain Q o r ⊆ Q ∧ (chain Q o r).card = r := by
  intro r
  induction r with
  | zero => intro _; simp [chain]
  | succ r ih =>
    intro hr
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hne : (Q \ chain Q o r).Nonempty := by
      rw [← card_pos, card_sdiff_of_subset h1]; omega
    have hs := nextPt_spec (o := o) hne
    rw [mem_sdiff] at hs
    simp only [chain, if_pos hne]
    exact ⟨insert_subset hs.1.1 h1, by rw [card_insert_of_notMem hs.1.2, h2]⟩

lemma chain_succ {r : ℕ} (hr : r < Q.card) :
    chain Q o (r + 1) = insert (nextPt Q (chain Q o r) o) (chain Q o r) ∧
      (Q \ chain Q o r).Nonempty := by
  obtain ⟨h1, h2⟩ := chain_basic (o := o) r hr.le
  have hne : (Q \ chain Q o r).Nonempty := by
    rw [← card_pos, card_sdiff_of_subset h1]; omega
  exact ⟨by simp only [chain, if_pos hne], hne⟩

lemma chain_mono {r s : ℕ} (hrs : r ≤ s) (hs : s ≤ Q.card) : chain Q o r ⊆ chain Q o s := by
  induction s, hrs using Nat.le_induction with
  | base => exact subset_rfl
  | succ s _ ih =>
    rw [(chain_succ (o := o) (show s < Q.card by omega)).1]
    exact ih (by omega) |>.trans (subset_insert _ _)

lemma val_le_val {r s : ℕ} (hrs : r ≤ s) (hs : s < Q.card) : val Q o s ≤ val Q o r := by
  obtain ⟨_, hne⟩ := chain_succ (o := o) hs
  have h1 := (nextPt_spec (o := o) hne).1
  have hsub := chain_mono (o := o) hrs hs.le
  obtain ⟨_, hne'⟩ := chain_succ (o := o) (show r < Q.card by omega)
  have h2 := (nextPt_spec (o := o) hne').2
  unfold val
  apply h2
  rw [mem_sdiff] at h1 ⊢
  exact ⟨h1.1, fun h => h1.2 (hsub h)⟩

/-- Every point among the top `r+1` has value at least the `(r+1)`-th largest. -/
lemma val_le_of_mem {r : ℕ} (hr : r < Q.card) {n : ℕ} (hn : n ∈ chain Q o (r + 1)) :
    val Q o r ≤ o n := by
  induction r with
  | zero =>
    rw [(chain_succ (o := o) hr).1] at hn
    simp only [chain, insert_empty, mem_singleton] at hn
    rw [hn]; rfl
  | succ r ih =>
    rw [(chain_succ (o := o) hr).1, mem_insert] at hn
    rcases hn with rfl | hn
    · rfl
    · exact (val_le_val (Nat.le_succ r) hr).trans (ih (by omega) hn)

lemma sum_chain : ∀ r ≤ Q.card, ∑ n ∈ chain Q o r, o n = ∑ j ∈ range r, val Q o j := by
  intro r
  induction r with
  | zero => intro _; simp [chain]
  | succ r ih =>
    intro hr
    obtain ⟨h1, hne⟩ := chain_succ (o := o) (show r < Q.card by omega)
    have hs := (nextPt_spec (o := o) hne).1
    rw [mem_sdiff] at hs
    rw [h1, sum_insert hs.2, sum_range_succ, ih (by omega), add_comm]
    rfl

lemma chain_full : chain Q o Q.card = Q := by
  obtain ⟨h1, h2⟩ := chain_basic (o := o) Q.card le_rfl
  exact eq_of_subset_of_card_le h1 (le_of_eq h2.symm)

/-! ### Lai's Lemma 2.7 (block estimate) -/

section block
variable {p a b x : ℕ}

set_option maxHeartbeats 4000000 in
/-- Parameters: `s = t / (2q)`, `K = t/2 - 2s`, `R = s`, `B = s/(E+1)`, `Y = (b-a)/s`. -/
lemma block (hp : p.Prime) (hx : 1 ≤ x) (hbx : b ≤ x) (hbp : b < p) (hab : a ≤ b)
    (hQ : Q ⊆ Icc a b) (hdiv : ∀ n ∈ Q, p ^ (o n) ∣ n ! + 1) {q t W : ℕ} (hq : 3 ≤ q)
    (hW : 1 ≤ W) (ht : t ≤ Q.card)
    (ht0 : 2 * q * (2 * Nat.log 2 x + 2) * ((2 * q + 1) * W + 1) ≤ t) :
    Real.log p * ∑ k ∈ range (t / 2 - 2 * (t / (2 * q)) + 1), (val Q o (t - k - 1) : ℝ) ≤
      ((b - a : ℕ) * Real.log t + x) / 2 + ((b - a : ℕ) : ℝ) / W * Real.log x := by
  classical
  set E1 := 2 * Nat.log 2 x + 2 with hE1
  set s := t / (2 * q) with hs
  set K := t / 2 - 2 * s with hK
  set B := s / E1 with hB
  set Y := (b - a) / s with hY
  set P := chain Q o t with hPdef
  have hPQ : P ⊆ Q := (chain_basic (Q := Q) (o := o) t ht).1
  have hPc : P.card = t := (chain_basic (Q := Q) (o := o) t ht).2
  have hP : P ⊆ Icc a b := hPQ.trans hQ
  have hE1pos : 2 ≤ E1 := by omega
  -- arithmetic of the parameters
  have hsq : 2 * q * s ≤ t := by
    have := Nat.div_mul_le_self t (2 * q)
    rw [← hs] at this
    linarith [mul_comm s (2 * q)]
  have hs1 : E1 * ((2 * q + 1) * W + 1) ≤ s := by
    rw [hs, Nat.le_div_iff_mul_le (by omega)]
    calc E1 * ((2 * q + 1) * W + 1) * (2 * q) = 2 * q * E1 * ((2 * q + 1) * W + 1) := by ring
      _ ≤ t := ht0
  have hs1' : 1 ≤ s := by
    have : 1 ≤ E1 * ((2 * q + 1) * W + 1) :=
      Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (Nat.succ_ne_zero _))
    omega
  have hBE : B * E1 ≤ s := Nat.div_mul_le_self s E1
  have hB1 : (2 * q + 1) * W + 1 ≤ B := by
    rw [hB, Nat.le_div_iff_mul_le (by omega)]
    calc ((2 * q + 1) * W + 1) * E1 = E1 * ((2 * q + 1) * W + 1) := by ring
      _ ≤ s := hs1
  have hBpos : 1 ≤ B := le_trans (Nat.le_add_left 1 _) hB1
  have h6s : 6 * s ≤ t := by nlinarith
  have hs2 : 2 ≤ s := by nlinarith
  have hKt : 2 * K + s + 3 ≤ t := by omega
  have hGc : (range (P.card - 1)).card = t - 1 := by rw [card_range, hPc]
  -- the threshold `y_k`
  have hlenle : ∀ i ∈ range (P.card - 1), len P i ≤ b - a := by
    intro i hi
    rw [mem_range] at hi
    have h1 := pos_mem_Icc hP (show i + 1 < P.card by omega)
    have h2 := pos_mem_Icc hP (show i < P.card by omega)
    unfold len; omega
  have hbig : ((range (P.card - 1)).filter (fun i => ¬ len P i ≤ Y)).card < s := by
    have hsum : ((range (P.card - 1)).filter (fun i => ¬ len P i ≤ Y)).card * (Y + 1) ≤ b - a := by
      calc _ = ∑ i ∈ (range (P.card - 1)).filter (fun i => ¬ len P i ≤ Y), (Y + 1) := by
            rw [sum_const, smul_eq_mul]
        _ ≤ ∑ i ∈ (range (P.card - 1)).filter (fun i => ¬ len P i ≤ Y), len P i :=
            sum_le_sum (fun i hi => by simp only [mem_filter] at hi; omega)
        _ ≤ ∑ i ∈ range (P.card - 1), len P i := sum_le_sum_of_subset (filter_subset _ _)
        _ ≤ b - a := sum_len_le hP (by omega)
    have h2 : b - a < (Y + 1) * s := by
      have := Nat.lt_div_mul_add (a := b - a) (show 0 < s by omega)
      rw [hY]; linarith
    by_contra hc
    have hc' := not_lt.mp hc
    have := Nat.mul_le_mul_left (Y + 1) hc'
    nlinarith
  have hexY : ∀ k ≤ K, 2 * k + s + 1 ≤
      ((range (P.card - 1)).filter (fun i => len P i ≤ Y)).card := by
    intro k hk
    have := card_filter_add_card_filter_not (s := range (P.card - 1))
      (fun i => len P i ≤ Y)
    rw [hGc] at this
    omega
  have hex : ∀ k ≤ K, ∃ y, 2 * k + s + 1 ≤
      ((range (P.card - 1)).filter (fun i => len P i ≤ y)).card := fun k hk => ⟨Y, hexY k hk⟩
  set yk : ℕ → ℕ := fun k =>
    if hk : k ≤ K then Nat.find (hex k hk) else 0 with hyk
  have hyk_spec : ∀ k ≤ K, 2 * k + s + 1 ≤
      ((range (P.card - 1)).filter (fun i => len P i ≤ yk k)).card := by
    intro k hk; simp only [hyk, dif_pos hk]; exact Nat.find_spec (hex k hk)
  have hyk_Y : ∀ k ≤ K, yk k ≤ Y := by
    intro k hk; simp only [hyk, dif_pos hk]; exact Nat.find_min' _ (hexY k hk)
  have hyk_ba : ∀ k ≤ K, yk k ≤ b - a := by
    intro k hk; simp only [hyk, dif_pos hk]
    apply Nat.find_min'
    have : (range (P.card - 1)).filter (fun i => len P i ≤ b - a) = range (P.card - 1) :=
      filter_true_of_mem hlenle
    rw [this, hGc]; omega
  have hyk_min : ∀ k ≤ K, 0 < yk k → ((range (P.card - 1)).filter
      (fun i => len P i ≤ yk k - 1)).card < 2 * k + s + 1 := by
    intro k hk hpos
    have := Nat.find_min (hex k hk) (show Nat.find (hex k hk) - 1 < Nat.find (hex k hk) by
      simp only [hyk, dif_pos hk] at hpos; omega)
    simp only [hyk, dif_pos hk]
    omega
  -- per-k estimate
  have hper : ∀ k ∈ range (K + 1), (val Q o (t - k - 1) : ℝ) * Real.log p ≤
      phiL x (yk k) + ((Y / B : ℕ) : ℝ) * Real.log x := by
    intro k hk
    rw [mem_range] at hk
    have hkt : k < t := by omega
    set P' := chain Q o (t - k)
    have hP'P : P' ⊆ P := chain_mono (o := o) (by omega) ht
    have hcard : (P \ P').card = k := by
      rw [card_sdiff_of_subset hP'P, hPc, (chain_basic (Q := Q) (o := o) (t - k) (by omega)).2]
      omega
    have hm : ∀ n ∈ P', p ^ (val Q o (t - k - 1)) ∣ n ! + 1 := by
      intro n hn
      have hn' : n ∈ chain Q o (t - k - 1 + 1) := by rwa [show t - k - 1 + 1 = t - k by omega]
      have h1 := val_le_of_mem (o := o) (show t - k - 1 < Q.card by omega) hn'
      exact (pow_dvd_pow p h1).trans (hdiv n (hPQ (hP'P hn)))
    have h := per_k hp hx hbx hbp hP hm (y := yk k) (R := s) (B := B)
      ((hyk_ba k (by omega)).trans (by omega)) hBpos hBE
      (by rw [hcard]; exact hyk_spec k (by omega))
    have hmono : ((yk k / B : ℕ) : ℝ) ≤ ((Y / B : ℕ) : ℝ) := by
      exact_mod_cast Nat.div_le_div_right (hyk_Y k (by omega))
    have hlx : 0 ≤ Real.log x := Real.log_nonneg (by exact_mod_cast hx)
    nlinarith
  -- pairing and Jensen
  have hlayer : 2 * ∑ k ∈ range (K + 1), phiL x (yk k) ≤
      ∑ i ∈ range (P.card - 1), phiL x (len P i) := by
    apply layer_phiL (fun i => (len P i : ℝ)) (fun k => (yk k : ℝ)) (fun _ => Nat.cast_nonneg _)
    · intro i hi
      exact ⟨Nat.cast_nonneg _, by exact_mod_cast (hlenle i hi).trans (by omega)⟩
    · intro j hj
      show 2 * (K + 1 - j) ≤ ((range (P.card - 1)).filter (fun i => (yk j : ℝ) ≤ (len P i : ℝ))).card
      have hjK : j ≤ K := by omega
      have := card_filter_add_card_filter_not (s := range (P.card - 1))
        (fun i => len P i ≤ yk j - 1)
      rw [hGc] at this
      have hfeq : (range (P.card - 1)).filter (fun i => ¬ len P i ≤ yk j - 1) ⊆
          (range (P.card - 1)).filter (fun i => (yk j : ℝ) ≤ (len P i : ℝ)) := by
        intro i hi
        simp only [mem_filter] at hi ⊢
        refine ⟨hi.1, ?_⟩
        exact_mod_cast (show yk j ≤ len P i by omega)
      rcases Nat.eq_zero_or_pos (yk j) with h0 | hpos
      · have : (range (P.card - 1)).filter (fun i => (yk j : ℝ) ≤ (len P i : ℝ)) =
            range (P.card - 1) := filter_true_of_mem (fun i _ => by rw [h0]; simp)
        rw [this, hGc]; omega
      · have := hyk_min j hjK hpos
        have := card_le_card hfeq
        omega
  have hjensen : ∑ i ∈ range (P.card - 1), phiL x (len P i) ≤
      ((b - a : ℕ) : ℝ) * Real.log t + x := by
    have hG1 : 1 ≤ (range (P.card - 1)).card := by rw [hGc]; omega
    have hj := jensen_phiL (range (P.card - 1)) (fun i => (len P i : ℝ)) (x := x)
      (Λ := ((b - a : ℕ) : ℝ)) (by exact_mod_cast hx) (fun _ _ => Nat.cast_nonneg _)
      (by exact_mod_cast sum_len_le hP (by omega)) (by exact_mod_cast (show b - a ≤ x by omega)) hG1
    refine hj.trans ?_
    rw [hGc]
    have : Real.log ((t - 1 : ℕ) : ℝ) ≤ Real.log t := by
      rcases Nat.eq_zero_or_pos (t - 1) with h0 | hpos
      · rw [h0]; simp; exact Real.log_natCast_nonneg t
      · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast Nat.sub_le t 1)
    have hΛ0 : (0 : ℝ) ≤ ((b - a : ℕ) : ℝ) := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left this hΛ0
    linarith
  -- the cost term
  have hcost : ((K + 1 : ℕ) : ℝ) * ((Y / B : ℕ) : ℝ) ≤ ((b - a : ℕ) : ℝ) / W := by
    have hKW : (K + 1) * W ≤ s * B := by
      have h1 : t < 2 * q * (s + 1) := by
        have := Nat.lt_div_mul_add (a := t) (show 0 < 2 * q by omega)
        rw [← hs] at this
        nlinarith
      have h2 : K + 1 ≤ q * (s + 1) + 1 := by
        have h3 : K ≤ t / 2 := Nat.sub_le _ _
        have h4 : t / 2 * 2 ≤ t := Nat.div_mul_le_self t 2
        nlinarith
      have h3 : (q * (s + 1) + 1) * W ≤ s * B := by
        have : (q * (s + 1) + 1) ≤ (2 * q + 1) * s := by nlinarith
        calc (q * (s + 1) + 1) * W ≤ (2 * q + 1) * s * W := Nat.mul_le_mul_right _ this
          _ = s * ((2 * q + 1) * W) := by ring
          _ ≤ s * B := Nat.mul_le_mul_left _ (Nat.le_of_succ_le hB1)
      calc (K + 1) * W ≤ (q * (s + 1) + 1) * W := Nat.mul_le_mul_right _ h2
        _ ≤ s * B := h3
    have hYB : Y / B ≤ (b - a) / (s * B) := by
      rw [hY, Nat.div_div_eq_div_mul]
    have hnat : (K + 1) * (Y / B) * W ≤ b - a := by
      calc (K + 1) * (Y / B) * W = (K + 1) * W * (Y / B) := by ring
        _ ≤ s * B * ((b - a) / (s * B)) := Nat.mul_le_mul hKW hYB
        _ ≤ b - a := by rw [mul_comm]; exact Nat.div_mul_le_self _ _
    have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
    rw [le_div_iff₀ hWpos]
    exact_mod_cast hnat
  -- assemble
  have hsum := sum_le_sum hper
  rw [← sum_mul, sum_add_distrib, sum_const, card_range, nsmul_eq_mul] at hsum
  have hlx : 0 ≤ Real.log x := Real.log_nonneg (by exact_mod_cast hx)
  have hc2 := mul_le_mul_of_nonneg_right hcost hlx
  have e : Real.log p * ∑ k ∈ range (K + 1), (val Q o (t - k - 1) : ℝ) =
      (∑ k ∈ range (K + 1), (val Q o (t - k - 1) : ℝ)) * Real.log p := mul_comm _ _
  rw [e]
  have e2 : ((K + 1 : ℕ) : ℝ) * (((Y / B : ℕ) : ℝ) * Real.log x) =
      ((K + 1 : ℕ) : ℝ) * ((Y / B : ℕ) : ℝ) * Real.log x := by ring
  rw [e2] at hsum
  linarith

end block

end LaneCLai


/-! Lane C, Erdős 977 (Lai) H2 — summing Lemma 2.7 over geometric blocks (Lai, Section 3),
as a strong induction on the number of ranks. -/

namespace LaneCLai
open Finset Real
open scoped Nat

/-- The bound `Φ(t) = Λ/(4L) (log t)² + β log t + Z`. -/
noncomputable def Φ (Λ x L W t₀ t : ℝ) : ℝ :=
  Λ / (4 * L) * Real.log t ^ 2 + ((x / 2 + Λ * Real.log x / W) / L + Λ / 4) * Real.log t +
    (Real.log 2 + x * Real.log x + Λ * Real.log x * (1 + Real.log t₀))

lemma Φ_mono {Λ x L W t₀ u v : ℝ} (hΛ : 0 ≤ Λ) (hx : 1 ≤ x) (hL : 0 < L) (hW : 0 < W)
    (hu : 1 ≤ u) (huv : u ≤ v) : Φ Λ x L W t₀ u ≤ Φ Λ x L W t₀ v := by
  unfold Φ
  have h1 := Real.log_le_log (by linarith) huv
  have h0 := Real.log_nonneg hu
  have hlx := Real.log_nonneg hx
  have hα : 0 ≤ Λ / (4 * L) := div_nonneg hΛ (by linarith)
  have hβ : 0 ≤ (x / 2 + Λ * Real.log x / W) / L + Λ / 4 :=
    add_nonneg (div_nonneg (add_nonneg (by linarith) (div_nonneg (mul_nonneg hΛ hlx) hW.le)) hL.le)
      (by linarith)
  have : Real.log u ^ 2 ≤ Real.log v ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left this hα, mul_le_mul_of_nonneg_left h1 hβ]

lemma Φ_step {Λ x L W t₀ t ρ : ℝ} (hL : 0 < L) (hW : 0 < W) (hρ : Real.log ρ = -L)
    (ht : 0 < t) (hρ0 : 0 < ρ) :
    Φ Λ x L W t₀ (ρ * t) + (Λ * Real.log t + x) / 2 + Λ / W * Real.log x = Φ Λ x L W t₀ t := by
  unfold Φ
  rw [Real.log_mul hρ0.ne' ht.ne', hρ]
  have hL' : L ≠ 0 := hL.ne'
  have hW' : W ≠ 0 := hW.ne'
  first | (first | (field_simp; ring) | field_simp) | field_simp

section main
variable {p a b x : ℕ} {Q : Finset ℕ} {o : ℕ → ℕ}

set_option maxHeartbeats 2000000 in
lemma base_bound (hp : p.Prime) (ha : 1 ≤ a) (hx : 2 ≤ x) (hbx : b ≤ x) (hbp : b < p)
    (hQ : Q ⊆ Icc a b) (hdiv : ∀ n ∈ Q, p ^ (o n) ∣ n ! + 1) {t : ℕ} (ht : t ≤ Q.card) :
    Real.log p * ∑ j ∈ range t, (val Q o j : ℝ) ≤
      Real.log 2 + x * Real.log x + ((b - a : ℕ) : ℝ) * Real.log x * (1 + Real.log t) := by
  classical
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hΛ : (0 : ℝ) ≤ ((b - a : ℕ) : ℝ) := Nat.cast_nonneg _
  rcases Nat.eq_zero_or_pos t with rfl | htpos
  · simp only [range_zero, sum_empty, mul_zero]
    have := Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num)
    have := mul_nonneg (show (0:ℝ) ≤ x by positivity) hlx
    have := mul_nonneg (mul_nonneg hΛ hlx) (show (0:ℝ) ≤ 1 + Real.log ((0 : ℕ) : ℝ) by simp)
    linarith
  -- the top value
  have hkey : ∀ n ∈ Q, (o n : ℝ) * Real.log p ≤ Real.log 2 + x * Real.log x := by
    intro n hnQ
    have hnb : n ≤ x := (mem_Icc.mp (hQ hnQ)).2.trans hbx
    have hd := Nat.le_of_dvd (by positivity) (hdiv n hnQ)
    have h2 : n ! + 1 ≤ 2 * x ^ x := by
      have := (Nat.factorial_le_pow n).trans (Nat.pow_le_pow_left hnb n)
      have := Nat.pow_le_pow_right (show 1 ≤ x by omega) (show n ≤ x from hnb)
      have : 1 ≤ x ^ x := Nat.one_le_pow _ _ (by omega)
      omega
    have h3 : ((p : ℝ) ^ (o n)) ≤ 2 * (x : ℝ) ^ x := by exact_mod_cast hd.trans h2
    have h4 := Real.log_le_log (pow_pos (by exact_mod_cast hp.pos) _) h3
    rw [Real.log_pow, Real.log_mul (by norm_num) (pow_pos (by linarith) _).ne', Real.log_pow] at h4
    linarith
  have h0 : (val Q o 0 : ℝ) * Real.log p ≤ Real.log 2 + x * Real.log x := by
    obtain ⟨_, hne⟩ := chain_succ (o := o) (show 0 < Q.card by omega)
    have hn := (nextPt_spec (o := o) hne).1
    rw [mem_sdiff] at hn
    exact hkey _ hn.1
  -- the other values: a gap of length at most `(b-a)/j`
  have hj : ∀ j ∈ range (t - 1), (val Q o (j + 1) : ℝ) * Real.log p ≤
      ((b - a : ℕ) : ℝ) * Real.log x * (1 / ((j : ℝ) + 1)) := by
    intro j hj
    rw [mem_range] at hj
    set P := chain Q o (j + 2)
    have hPQ : P ⊆ Q := (chain_basic (Q := Q) (o := o) (j + 2) (by omega)).1
    have hPc : P.card = j + 2 := (chain_basic (Q := Q) (o := o) (j + 2) (by omega)).2
    have hP : P ⊆ Icc a b := hPQ.trans hQ
    have hsum := sum_len_le hP (by omega)
    rw [hPc] at hsum
    obtain ⟨i, hi, hile⟩ : ∃ i ∈ range (j + 1), len P i * (j + 1) ≤ b - a := by
      by_contra hc
      push_neg at hc
      have : ∑ i ∈ range (j + 1), (b - a) < ∑ i ∈ range (j + 1), len P i * (j + 1) :=
        sum_lt_sum_of_nonempty (by simp) hc
      rw [sum_const, card_range, smul_eq_mul, ← sum_mul] at this
      have h2 := Nat.mul_le_mul_right (j + 1) hsum
      simp only [show j + 2 - 1 = j + 1 by omega] at h2
      nlinarith
    rw [mem_range] at hi
    have hm : ∀ n ∈ P, p ^ (val Q o (j + 1)) ∣ n ! + 1 := by
      intro n hn
      have h1 := val_le_of_mem (o := o) (show j + 1 < Q.card by omega) hn
      exact (pow_dvd_pow p h1).trans (hdiv n (hPQ hn))
    have hdv := gap_dvd hp hm (show i + 1 < P.card by omega) (pos_mem (by omega)) (pos_mem (by omega))
    have hu : 1 ≤ pos P i := (pos_mem_Icc hP (show i < P.card by omega)).1.trans' ha
    have hpx : pos P i + len P i ≤ x := by
      rw [pos_add_len (show i + 1 < P.card by omega)]
      exact (pos_mem_Icc hP (show i + 1 < P.card by omega)).2.trans hbx
    have key := one_block_log hu (len_pos (show i + 1 < P.card by omega)) hdv hpx hp.one_lt
    have hl : (len P i : ℝ) ≤ ((b - a : ℕ) : ℝ) * (1 / ((j : ℝ) + 1)) := by
      rw [mul_one_div, le_div_iff₀ (by positivity)]
      exact_mod_cast hile
    have := mul_le_mul_of_nonneg_right hl hlx
    linarith
  -- sum up
  have hsplit : ∑ j ∈ range t, (val Q o j : ℝ) =
      (val Q o 0 : ℝ) + ∑ j ∈ range (t - 1), (val Q o (j + 1) : ℝ) := by
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    rw [sum_range_succ', add_comm]; simp
  have hharm : ∑ j ∈ range (t - 1), (1 / ((j : ℝ) + 1)) ≤ 1 + Real.log t := by
    have h := harmonic_le_one_add_log (t - 1)
    have : ((harmonic (t - 1) : ℚ) : ℝ) = ∑ j ∈ range (t - 1), (1 / ((j : ℝ) + 1)) := by
      simp [harmonic]
    rw [this] at h
    refine h.trans ?_
    have : Real.log ((t - 1 : ℕ) : ℝ) ≤ Real.log t := by
      rcases Nat.eq_zero_or_pos (t - 1) with h0 | hpos
      · rw [h0]; simp; exact Real.log_natCast_nonneg t
      · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast Nat.sub_le t 1)
    linarith
  rw [hsplit, mul_add, mul_sum]
  have h2 := sum_le_sum hj
  rw [← mul_sum] at h2
  have h3 := mul_le_mul_of_nonneg_left hharm (mul_nonneg hΛ hlx)
  have h4 : ∑ j ∈ range (t - 1), Real.log p * (val Q o (j + 1) : ℝ) =
      ∑ j ∈ range (t - 1), (val Q o (j + 1) : ℝ) * Real.log p := by
    apply sum_congr rfl; intro j _; ring
  rw [h4]
  linarith

set_option maxHeartbeats 4000000 in
/-- The per-prime estimate: `log p · ∑_{n ∈ Q} o n ≤ Φ(|Q|)`. -/
theorem lai_local (hp : p.Prime) (ha : 1 ≤ a) (hx : 2 ≤ x) (hbx : b ≤ x) (hbp : b < p)
    (hab : a ≤ b) (hQ : Q ⊆ Icc a b) (hdiv : ∀ n ∈ Q, p ^ (o n) ∣ n ! + 1) {q W : ℕ}
    (hq : 3 ≤ q) (hW : 1 ≤ W) :
    Real.log p * ∑ n ∈ Q, (o n : ℝ) ≤
      Φ ((b - a : ℕ) : ℝ) x (Real.log (2 * q / (q + 2))) W
        (2 * q * (2 * Nat.log 2 x + 2) * ((2 * q + 1) * W + 1) : ℕ) Q.card := by
  classical
  set t₀ := 2 * q * (2 * Nat.log 2 x + 2) * ((2 * q + 1) * W + 1) with ht₀
  set L := Real.log (2 * q / (q + 2)) with hLdef
  set Λ : ℝ := ((b - a : ℕ) : ℝ)
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hL : 0 < L := Real.log_pos (by rw [lt_div_iff₀ (by linarith)]; linarith)
  set ρ : ℝ := (q + 2) / (2 * q) with hρdef
  have hρ0 : 0 < ρ := by rw [hρdef]; exact div_pos (by linarith) (by linarith)
  have hρL : Real.log ρ = -L := by
    rw [hρdef, hLdef, ← Real.log_inv, inv_div]
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
  have hWR : (0 : ℝ) < W := by exact_mod_cast hW
  have hΛ : 0 ≤ Λ := Nat.cast_nonneg _
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have ht0big : 4 ≤ t₀ := by
    rw [ht₀]
    have : 1 ≤ (2 * q + 1) * W + 1 := by omega
    have : 2 ≤ 2 * Nat.log 2 x + 2 := by omega
    have : 6 ≤ 2 * q := by omega
    calc 4 ≤ 6 * 2 * 1 := by norm_num
      _ ≤ 2 * q * (2 * Nat.log 2 x + 2) * ((2 * q + 1) * W + 1) := by gcongr
  -- strong induction on the number of ranks
  have main : ∀ t ≤ Q.card, Real.log p * ∑ j ∈ range t, (val Q o j : ℝ) ≤
      Φ Λ x L W t₀ t := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro ht
      by_cases hsmall : t ≤ t₀
      · refine (base_bound hp ha hx hbx hbp hQ hdiv ht).trans ?_
        have h1 : Real.log 2 + x * Real.log x + Λ * Real.log x * (1 + Real.log t) ≤
            Real.log 2 + x * Real.log x + Λ * Real.log x * (1 + Real.log t₀) := by
          rcases Nat.eq_zero_or_pos t with h0 | hpos
          · rw [h0]; simp
            have := Real.log_natCast_nonneg t₀
            nlinarith [mul_nonneg hΛ hlx]
          · have := Real.log_le_log (by exact_mod_cast hpos) (show (t : ℝ) ≤ t₀ by exact_mod_cast hsmall)
            nlinarith [mul_nonneg hΛ hlx]
        refine h1.trans ?_
        unfold Φ
        rcases Nat.eq_zero_or_pos t with h0 | hpos
        · rw [h0]; simp
        · have := Real.log_natCast_nonneg t
          have : 0 ≤ (x / 2 + Λ * Real.log x / W) / L + Λ / 4 :=
            add_nonneg (div_nonneg (add_nonneg (by linarith)
              (div_nonneg (mul_nonneg hΛ hlx) hWR.le)) hL.le) (by linarith)
          have : 0 ≤ Λ / (4 * L) * Real.log t ^ 2 :=
            mul_nonneg (div_nonneg hΛ (by linarith)) (sq_nonneg _)
          nlinarith
      push_neg at hsmall
      set s := t / (2 * q)
      set K := t / 2 - 2 * s
      have hsq : s * (2 * q) ≤ t := Nat.div_mul_le_self t (2 * q)
      have h4s : 4 * s ≤ t := by nlinarith
      have hK : K + 1 ≤ t := by omega
      set t' := t - (K + 1)
      have hsplit : ∑ j ∈ range t, (val Q o j : ℝ) = ∑ j ∈ range t', (val Q o j : ℝ) +
          ∑ k ∈ range (K + 1), (val Q o (t - k - 1) : ℝ) := by
        rw [← sum_range_add_sum_Ico _ (show t' ≤ t by omega), sum_Ico_eq_sum_range,
          show t - t' = K + 1 by omega]
        congr 1
        rw [← sum_range_reflect (fun k => (val Q o (t' + k) : ℝ)) (K + 1)]
        apply sum_congr rfl
        intro k hk
        rw [mem_range] at hk
        rw [show t' + (K + 1 - 1 - k) = t - k - 1 by omega]
      have hblock : Real.log p * ∑ k ∈ range (K + 1), (val Q o (t - k - 1) : ℝ) ≤
          ((b - a : ℕ) * Real.log t + x) / 2 + ((b - a : ℕ) : ℝ) / W * Real.log x :=
        block (o := o) hp (by omega) hbx hbp hab hQ hdiv (q := q) (t := t) (W := W)
          hq hW ht hsmall.le
      have hIH := ih t' (by omega) (by omega)
      have ht'1 : 1 ≤ t' := by omega
      have ht'ρ : (t' : ℝ) ≤ ρ * t := by
        have h1 : t' + t / 2 ≤ t / 2 + 2 * s + t / 2 := by omega
        have h2 : (t / 2 : ℕ) * 2 ≤ t := Nat.div_mul_le_self t 2
        have h3 : t' ≤ t / 2 + 2 * s := by omega
        have h4 : (t' : ℝ) ≤ (t / 2 : ℕ) + 2 * (s : ℝ) := by exact_mod_cast h3
        have h5 : ((t / 2 : ℕ) : ℝ) * 2 ≤ t := by exact_mod_cast h2
        have h6 : (s : ℝ) * (2 * q) ≤ t := by exact_mod_cast hsq
        have hq0 : (0 : ℝ) < q := by linarith
        have : ρ * t = t / 2 + t / q := by rw [hρdef]; first | (field_simp; ring) | field_simp
        rw [this]
        have : 2 * (s : ℝ) ≤ t / q := by rw [le_div_iff₀ hq0]; linarith
        linarith
      have hmono := Φ_mono (Λ := Λ) (x := x) (L := L) (W := W) (t₀ := t₀) hΛ hx1 hL hWR
        (show (1 : ℝ) ≤ t' by exact_mod_cast ht'1) ht'ρ
      have hstep := Φ_step (Λ := Λ) (x := x) (W := W) (t₀ := t₀) (t := t) hL hWR hρL
        (by exact_mod_cast (show 0 < t by omega)) hρ0
      rw [hsplit, mul_add]
      linarith
  have hs : (∑ n ∈ Q, (o n : ℝ)) = ∑ j ∈ range Q.card, (val Q o j : ℝ) := by
    have := sum_chain (o := o) Q.card le_rfl
    rw [chain_full] at this
    exact_mod_cast this
  rw [hs]
  exact main Q.card le_rfl

end main

end LaneCLai


/-! Lane C, Erdős 977 (Lai) H2 — final assembly: the per-prime estimate on `[N, (1+d)N]`. -/

namespace LaneCLai
open Finset Real Filter
open scoped Nat Topology

/-- `log (2q/(q+2)) → log 2`. -/
lemma tendsto_Lq : Tendsto (fun q : ℕ => Real.log (2 * q / (q + 2))) atTop (𝓝 (Real.log 2)) := by
  have h : Tendsto (fun q : ℕ => (2 : ℝ) * q / (q + 2)) atTop (𝓝 2) := by
    have h1 : Tendsto (fun q : ℕ => (2 : ℝ) - 4 / ((q : ℝ) + 2)) atTop (𝓝 (2 - 0)) := by
      refine tendsto_const_nhds.sub ?_
      exact tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    rw [sub_zero] at h1
    refine h1.congr' (Eventually.of_forall fun q => ?_)
    have : (q : ℝ) + 2 ≠ 0 := by positivity
    first | (field_simp; ring) | field_simp
  exact (Real.continuousAt_log (by norm_num)).tendsto.comp h

lemma exists_q (η : ℝ) (hη : 0 < η) :
    ∃ q : ℕ, 3 ≤ q ∧ 0 < Real.log (2 * q / (q + 2)) ∧
      1 / (9 * Real.log (2 * q / (q + 2))) ≤ 1 / (9 * Real.log 2) + η / 4 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h0 : Tendsto (fun q : ℕ => 9 * Real.log (2 * q / (q + 2))) atTop (𝓝 (9 * Real.log 2)) :=
    tendsto_const_nhds.mul tendsto_Lq
  have h1' := h0.inv₀ (by positivity)
  have h1 : Tendsto (fun q : ℕ => 1 / (9 * Real.log (2 * q / (q + 2)))) atTop
      (𝓝 (1 / (9 * Real.log 2))) := by
    simp only [one_div]; exact h1'
  have h2 := h1.eventually (ge_mem_nhds (show 1 / (9 * Real.log 2) < 1 / (9 * Real.log 2) + η / 4
    by linarith))
  have h3 := (tendsto_Lq.eventually (lt_mem_nhds hl2))
  obtain ⟨q, hq⟩ := (h2.and (h3.and (eventually_ge_atTop 3))).exists
  exact ⟨q, hq.2.2, hq.2.1, hq.1⟩

lemma card_Q_le {p : ℕ} (hp : p.Prime) {Q : Finset ℕ} {a b x : ℕ} (hQ : Q ⊆ Icc a b)
    (hb : b < p) (hdiv : ∀ n ∈ Q, p ∣ n ! + 1) (hbx : b ≤ x) (hab : a ≤ b) (hx : 1 ≤ x) :
    (Q.card : ℝ) ≤ 6 * (x : ℝ) ^ ((2 : ℝ) / 3) := by
  set H := ⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ + 1 with hH
  have hH1 : 1 ≤ H := by omega
  have h := card_LS hp hQ hb hdiv H hH1
  have hx0 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  set c := (x : ℝ) ^ ((1 : ℝ) / 3) with hcdef
  have hc1 : 1 ≤ c := by rw [hcdef]; exact Real.one_le_rpow hx0 (by norm_num)
  have hc3 : c ^ 3 = x := by
    rw [hcdef, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  have hc2 : (x : ℝ) ^ ((2 : ℝ) / 3) = c ^ 2 := by
    rw [hcdef, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  have hHc : c ≤ H := by
    have := Nat.lt_floor_add_one c; push_cast [hH]; linarith
  have hHc' : (H : ℝ) ≤ c + 1 := by
    have := Nat.floor_le (show 0 ≤ c by linarith); push_cast [hH]; linarith
  have hR : (Q.card : ℝ) * H ≤ (H : ℝ) * H * H + ((b - a : ℕ) : ℝ) + H := by exact_mod_cast h
  have hba : ((b - a : ℕ) : ℝ) ≤ x := by exact_mod_cast (show b - a ≤ x by omega)
  rw [hc2]
  have hHpos : (0 : ℝ) < H := by linarith
  have : (Q.card : ℝ) ≤ (H : ℝ) * H + x / H + 1 := by
    rw [← sub_nonneg]
    have : (H : ℝ) * H + x / H + 1 - Q.card = ((H : ℝ) * H * H + x + H - Q.card * H) / H := by
      first | (field_simp; ring) | field_simp
    rw [this]; apply div_nonneg _ hHpos.le; linarith
  have hxH : (x : ℝ) / H ≤ c ^ 2 := by
    rw [div_le_iff₀ hHpos, ← hc3]; nlinarith
  have hHH : (H : ℝ) * H ≤ (c + 1) * (c + 1) := mul_le_mul hHc' hHc' hHpos.le (by linarith)
  nlinarith [mul_nonneg (sub_nonneg.mpr hc1) (show (0:ℝ) ≤ c by linarith)]

lemma Φ_le {Λ M x L W t₀ t : ℝ} (hΛ : 0 ≤ Λ) (hΛM : Λ ≤ M) (hx : 1 ≤ x) (hL : 0 < L)
    (hW : 0 < W) (ht : 1 ≤ t) (ht₀ : 1 ≤ t₀) : Φ Λ x L W t₀ t ≤ Φ M x L W t₀ t := by
  unfold Φ
  have h1 := Real.log_nonneg ht
  have h2 := Real.log_nonneg hx
  have h3 := Real.log_nonneg ht₀
  have e1 : Λ / (4 * L) * Real.log t ^ 2 ≤ M / (4 * L) * Real.log t ^ 2 :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hΛM (by linarith)) (by positivity)
  have e2a : Λ * Real.log x / W ≤ M * Real.log x / W :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hΛM h2) hW.le
  have e2b : (x / 2 + Λ * Real.log x / W) / L ≤ (x / 2 + M * Real.log x / W) / L :=
    div_le_div_of_nonneg_right (by linarith) hL.le
  have e2 : ((x / 2 + Λ * Real.log x / W) / L + Λ / 4) * Real.log t ≤
      ((x / 2 + M * Real.log x / W) / L + M / 4) * Real.log t :=
    mul_le_mul_of_nonneg_right (by linarith) h1
  have e3 : Λ * Real.log x * (1 + Real.log t₀) ≤ M * Real.log x * (1 + Real.log t₀) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hΛM h2) (by linarith)
  linarith

set_option maxHeartbeats 4000000 in
theorem H2_main (d : ℝ) (hd : 0 < d) (hd1 : d < 1) (η : ℝ) (hη : 0 < η) : ∀ᶠ N : ℕ in atTop,
    ∀ p : ℕ, p.Prime → N < p →
      (∑ n ∈ Icc N ⌊(1 + d) * N⌋₊, ((n.factorial + 1).factorization p : ℝ) * Real.log p) ≤
        (1 / (9 * Real.log 2) + η) * (Icc N ⌊(1 + d) * N⌋₊).card * (Real.log N) ^ 2 := by
  classical
  obtain ⟨q, hq3, hL, hqL⟩ := exists_q η hη
  set L := Real.log (2 * q / (q + 2)) with hLdef
  set κ := 1 / (9 * Real.log 2) with hκdef
  set W : ℕ := ⌈16 / (L * η)⌉₊ + 1 with hWdef
  have hW1 : 1 ≤ W := by omega
  have hWR : (0 : ℝ) < W := by exact_mod_cast hW1
  have hWL : 1 / (W * L) ≤ η / 16 := by
    have h1 : 16 / (L * η) ≤ W := by
      have := Nat.le_ceil (16 / (L * η)); push_cast [hWdef]; linarith
    rw [div_le_iff₀ (by positivity)] at h1
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set C₁ : ℝ := 4 * q * ((2 * q + 1) * W + 1) with hC₁
  have hC₁pos : 1 ≤ C₁ := by
    have : (3 : ℝ) ≤ q := by exact_mod_cast hq3
    have : (1 : ℝ) ≤ W := by exact_mod_cast hW1
    rw [hC₁]
    nlinarith [mul_nonneg (show (0:ℝ) ≤ q by linarith)
      (mul_nonneg (show (0:ℝ) ≤ 2 * q + 1 by linarith) (show (0:ℝ) ≤ W by linarith))]
  -- eventualities in `ℓ = log N`
  have hℓ : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog : ∀ᶠ ℓ : ℝ in atTop, Real.log (2 * ℓ + 3) ≤ η / 64 * (2 * ℓ + 3) := by
    have := Real.isLittleO_log_id_atTop.def (show 0 < η / 64 by positivity)
    have ht : Tendsto (fun ℓ : ℝ => 2 * ℓ + 3) atTop atTop :=
      tendsto_atTop_add_const_right _ 3 (tendsto_id.const_mul_atTop (by norm_num))
    filter_upwards [ht.eventually this, ht.eventually (eventually_ge_atTop 1)] with ℓ h1 h2
    simp only [id, Real.norm_eq_abs] at h1
    rw [abs_of_nonneg (Real.log_nonneg h2), abs_of_nonneg (by linarith)] at h1
    exact h1
  -- the big polynomial inequality, divided by `M = |T|`
  have hpoly : ∀ᶠ ℓ : ℝ in atTop,
      (κ + η / 4) * (ℓ + 4) ^ 2 + η / 16 * (ℓ + 4) ^ 2 + (2 / (d * L) + 1) * (ℓ + 4) +
        (1 + 4 / d * (ℓ + 1)) + (ℓ + 1) * (1 + Real.log C₁ + Real.log (2 * ℓ + 3)) ≤
        (κ + η) * ℓ ^ 2 := by
    have hlC : 0 ≤ Real.log C₁ := Real.log_nonneg hC₁pos
    have hκ : 0 < κ := by
      rw [hκdef]; have := Real.log_pos (show (1:ℝ) < 2 by norm_num); positivity
    set D := 1 + 2 / (d * L) + 4 / d + Real.log C₁ with hDdef
    have hA : 0 ≤ 2 / (d * L) := by positivity
    have hB : 0 ≤ 4 / d := by positivity
    have hD1 : 1 ≤ D := by linarith
    filter_upwards [hlog, eventually_ge_atTop (1 : ℝ),
      eventually_ge_atTop ((10000 * (κ + η + 1) * D) / η)] with ℓ h1 h2 h3
    have h3' : 10000 * (κ + η + 1) * D ≤ η * ℓ := by
      rwa [div_le_iff₀ hη, mul_comm ℓ] at h3
    have hℓ0 : 0 ≤ ℓ := by linarith
    have hbig : 10000 * (κ + η + 1) * D * ℓ ≤ η * ℓ * ℓ := mul_le_mul_of_nonneg_right h3' hℓ0
    have hDℓ : (κ + η + 1) * ℓ ≤ (κ + η + 1) * D * ℓ := by
      have : (κ + η + 1) * 1 ≤ (κ + η + 1) * D := mul_le_mul_of_nonneg_left hD1 (by positivity)
      nlinarith
    have hκℓ : κ ≤ κ * ℓ := by nlinarith
    have hηℓ : η ≤ η * ℓ := by nlinarith
    have hDl : D ≤ D * ℓ := by nlinarith
    have l1 : (2 / (d * L) + 1) * (ℓ + 4) ≤ D * (ℓ + 4) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have l2 : 4 / d * (ℓ + 1) ≤ D * (ℓ + 1) := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have l3 : (ℓ + 1) * (1 + Real.log C₁) ≤ (ℓ + 1) * D :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have l4 : (ℓ + 1) * Real.log (2 * ℓ + 3) ≤ η / 64 * ((ℓ + 1) * (2 * ℓ + 3)) := by
      have := mul_le_mul_of_nonneg_left h1 (show 0 ≤ ℓ + 1 by linarith)
      linarith
    have hsplit : (ℓ + 1) * (1 + Real.log C₁ + Real.log (2 * ℓ + 3)) =
        (ℓ + 1) * (1 + Real.log C₁) + (ℓ + 1) * Real.log (2 * ℓ + 3) := by ring
    rw [hsplit]
    have hD0 : 0 ≤ D := by linarith
    have p1 := mul_nonneg hη.le hℓ0
    have p2 := mul_nonneg hκ.le hℓ0
    have p3 := mul_nonneg (mul_nonneg hκ.le hD0) hℓ0
    have p4 := mul_nonneg (mul_nonneg hη.le hD0) hℓ0
    have p5 := mul_nonneg hD0 hℓ0
    have p6 : 1 * ℓ ≤ D * ℓ := mul_le_mul_of_nonneg_right hD1 hℓ0
    linarith
  filter_upwards [hℓ.eventually hpoly, eventually_ge_atTop 3] with N hN hN3
  intro p hp hNp
  set x := ⌊(1 + d) * N⌋₊ with hxdef
  set T := Icc N x
  have hNR : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hx1 : ((1 + d) * N) - 1 < x := Nat.sub_one_lt_floor _
  have hx2 : (x : ℝ) ≤ (1 + d) * N := Nat.floor_le (by positivity)
  have hNx : N ≤ x := by
    apply Nat.le_floor; push_cast; nlinarith
  have hx2' : 2 ≤ x := by omega
  set b := min x (p - 1)
  have hbx : b ≤ x := min_le_left _ _
  have hbp : b < p := by have := hp.pos; omega
  have hab : N ≤ b := by have := hp.pos; omega
  set o : ℕ → ℕ := fun n => (n ! + 1).factorization p
  set Q := (Icc N b).filter (fun n => p ∣ n ! + 1)
  have hQ : Q ⊆ Icc N b := filter_subset _ _
  have hdivQ : ∀ n ∈ Q, p ^ (o n) ∣ n ! + 1 := fun n _ => Nat.ordProj_dvd _ _
  -- the sum over `T` is the sum over `Q`
  have hsumeq : ∑ n ∈ T, ((n ! + 1).factorization p : ℝ) * Real.log p =
      Real.log p * ∑ n ∈ Q, (o n : ℝ) := by
    rw [mul_sum]
    symm
    apply sum_subset_zero_on_sdiff
    · intro n hn
      have := mem_Icc.mp (hQ hn)
      exact mem_Icc.mpr ⟨this.1, this.2.trans hbx⟩
    · intro n hn
      rw [Finset.mem_sdiff] at hn
      have h0 : (n ! + 1).factorization p = 0 := by
        apply Nat.factorization_eq_zero_of_not_dvd
        intro hdv
        apply hn.2
        rw [mem_filter, mem_Icc]
        refine ⟨⟨(mem_Icc.mp hn.1).1, ?_⟩, hdv⟩
        by_contra hnb
        have hnx := (mem_Icc.mp hn.1).2
        have hpn : p ≤ n := by omega
        have := (Nat.dvd_add_right (Nat.dvd_factorial hp.pos hpn)).mp hdv
        exact hp.one_lt.ne' (Nat.dvd_one.mp this)
      simp [h0]
    · intro n _; exact mul_comm _ _
  rw [hsumeq]
  have hloc := lai_local (o := o) hp (by omega) hx2' hbx hbp hab hQ hdivQ hq3 hW1
  refine hloc.trans ?_
  -- bound the number of points
  have hQc := card_Q_le hp hQ hbp (fun n hn => (mem_filter.mp hn).2) hbx hab (by omega)
  set t₀ : ℕ := 2 * q * (2 * Nat.log 2 x + 2) * ((2 * q + 1) * W + 1)
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
  set Mt : ℝ := 6 * (x : ℝ) ^ ((2 : ℝ) / 3)
  have hMt1 : 1 ≤ Mt := by
    have := Real.one_le_rpow hxR (show (0:ℝ) ≤ 2 / 3 by norm_num); simp only [Mt]; linarith
  have ht₀1 : (1 : ℝ) ≤ t₀ := by
    have : 1 ≤ t₀ := Nat.one_le_iff_ne_zero.mpr (show 2 * q * (2 * Nat.log 2 x + 2) *
      ((2 * q + 1) * W + 1) ≠ 0 from Nat.mul_ne_zero (Nat.mul_ne_zero (by omega) (by omega))
        (Nat.succ_ne_zero _))
    exact_mod_cast this
  set Λ : ℝ := ((b - N : ℕ) : ℝ)
  set M : ℝ := (T.card : ℝ)
  have hTc : T.card = x + 1 - N := Nat.card_Icc N x
  have hΛM : Λ ≤ M := by
    simp only [Λ, M]; exact_mod_cast (show b - N ≤ T.card by omega)
  have hMd : d * N ≤ M := by
    simp only [M]; rw [hTc]; push_cast [Nat.cast_sub (show N ≤ x + 1 by omega)]; linarith
  have hMpos : 0 < M := by nlinarith
  have hstep1 : Φ Λ x L W t₀ Q.card ≤ Φ M x L W t₀ Mt := by
    refine (?_ : Φ Λ x L W t₀ Q.card ≤ Φ Λ x L W t₀ Mt).trans
      (Φ_le (Nat.cast_nonneg _) hΛM hxR hL hWR hMt1 ht₀1)
    rcases Nat.eq_zero_or_pos Q.card with h0 | hpos
    · rw [h0]
      unfold Φ
      have hΛ0 : 0 ≤ Λ := Nat.cast_nonneg _
      have hb : 0 ≤ (x / 2 + Λ * Real.log x / W) / L + Λ / 4 :=
        add_nonneg (div_nonneg (add_nonneg (by positivity)
          (div_nonneg (mul_nonneg hΛ0 (Real.log_nonneg hxR)) hWR.le)) hL.le) (by linarith)
      have ha : 0 ≤ Λ / (4 * L) * Real.log Mt ^ 2 :=
        mul_nonneg (div_nonneg hΛ0 (by linarith)) (sq_nonneg _)
      have hc := mul_nonneg hb (Real.log_nonneg hMt1)
      simp only [Nat.cast_zero, Real.log_zero]
      nlinarith
    · exact Φ_mono (Nat.cast_nonneg _) hxR hL hWR (by exact_mod_cast hpos) hQc
  refine hstep1.trans ?_
  -- now a real inequality
  set ℓ := Real.log N with hℓdef
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓdef, Real.le_log_iff_exp_le (by linarith)]
    have : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
    linarith
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hlx : Real.log x ≤ ℓ + 1 := by
    have h1 : (x : ℝ) ≤ 2 * N := by
      have := mul_le_mul_of_nonneg_right hd1.le (show (0:ℝ) ≤ N by positivity)
      linarith
    have h2 := Real.log_le_log (by linarith) h1
    rw [Real.log_mul (by norm_num) (by linarith), ← hℓdef] at h2
    have := Real.log_two_lt_d9; linarith
  have hlx0 : 0 ≤ Real.log x := Real.log_nonneg hxR
  have hlMt : Real.log Mt ≤ (2 / 3) * (ℓ + 1) + 2 := by
    simp only [Mt]
    rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos (by linarith) _).ne',
      Real.log_rpow (by linarith)]
    have : Real.log 6 < 2 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have := Real.exp_one_gt_d9
      nlinarith [Real.exp_pos 1, show Real.exp 2 = Real.exp 1 * Real.exp 1 by
        rw [← Real.exp_add]; norm_num]
    nlinarith
  have hlMt0 : 0 ≤ Real.log Mt := Real.log_nonneg hMt1
  have hlt₀ : Real.log t₀ ≤ Real.log C₁ + Real.log (2 * ℓ + 3) := by
    have hlog2 : (Nat.log 2 x : ℝ) ≤ Real.log x / Real.log 2 := by
      rw [le_div_iff₀ (Real.log_pos (by norm_num))]
      have := Nat.pow_log_le_self 2 (show x ≠ 0 by omega)
      have h3 : ((2 : ℝ) ^ (Nat.log 2 x)) ≤ x := by exact_mod_cast this
      have := Real.log_le_log (by positivity) h3
      rwa [Real.log_pow] at this
    have hl2 : (1 : ℝ) / 2 ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have hlog2' : (Nat.log 2 x : ℝ) ≤ 2 * (ℓ + 1) := by
      refine hlog2.trans ?_
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have : (t₀ : ℝ) ≤ C₁ * (2 * ℓ + 3) := by
      simp only [t₀, C₁]; push_cast
      have : (0 : ℝ) ≤ (2 * q + 1) * W + 1 := by positivity
      have : (0 : ℝ) ≤ q := by positivity
      nlinarith
    calc Real.log t₀ ≤ Real.log (C₁ * (2 * ℓ + 3)) := Real.log_le_log (by linarith) this
      _ = _ := Real.log_mul (by linarith) (by linarith)
  -- expand Φ and compare
  unfold Φ
  have hxN : (x : ℝ) ≤ 2 / d * M := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hd]
    have h1 := mul_le_mul_of_nonneg_right hx2 hd.le
    have h2 : (1 + d) * N * d ≤ 2 * (d * N) := by
      have := mul_nonneg (mul_nonneg hd.le (show (0:ℝ) ≤ N by positivity)) (sub_nonneg.mpr hd1.le)
      nlinarith
    linarith
  have e1 : M / (4 * L) * Real.log Mt ^ 2 ≤ M * ((κ + η / 4) * (ℓ + 4) ^ 2) := by
    have hsq : Real.log Mt ^ 2 ≤ ((2 / 3) * (ℓ + 4)) ^ 2 := by
      have : Real.log Mt ≤ (2 / 3) * (ℓ + 4) := by linarith
      exact pow_le_pow_left₀ hlMt0 this 2
    have : 1 / (4 * L) * ((2 / 3) * (ℓ + 4)) ^ 2 = (1 / (9 * L)) * (ℓ + 4) ^ 2 := by
      first | (field_simp; ring) | field_simp
    have h2 : (1 / (9 * L)) * (ℓ + 4) ^ 2 ≤ (κ + η / 4) * (ℓ + 4) ^ 2 :=
      mul_le_mul_of_nonneg_right hqL (by positivity)
    have hL4 : 0 ≤ 1 / (4 * L) := by positivity
    calc M / (4 * L) * Real.log Mt ^ 2 = M * (1 / (4 * L) * Real.log Mt ^ 2) := by ring
      _ ≤ M * (1 / (4 * L) * ((2 / 3) * (ℓ + 4)) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hL4) hMpos.le
      _ ≤ _ := by rw [this]; exact mul_le_mul_of_nonneg_left h2 hMpos.le
  have e2 : ((x / 2 + M * Real.log x / W) / L + M / 4) * Real.log Mt ≤
      M * (η / 16 * (ℓ + 4) ^ 2 + (2 / (d * L) + 1) * (ℓ + 4)) := by
    have hlt : Real.log Mt ≤ ℓ + 4 := by linarith
    have a1 : (x / 2 / L) * Real.log Mt ≤ M * (1 / (d * L) * (ℓ + 4)) := by
      have hx2M : (x : ℝ) / 2 ≤ M / d := by
        rw [le_div_iff₀ hd]
        have := mul_le_mul_of_nonneg_right hxN hd.le
        have e : 2 / d * M * d = 2 * M := by first | (field_simp; ring) | field_simp
        linarith
      have : x / 2 / L ≤ M * (1 / (d * L)) := by
        have h1 := div_le_div_of_nonneg_right hx2M hL.le
        have e : M / d / L = M * (1 / (d * L)) := by ring
        linarith
      calc (x / 2 / L) * Real.log Mt ≤ M * (1 / (d * L)) * (ℓ + 4) :=
            mul_le_mul this hlt hlMt0 (by positivity)
        _ = _ := by ring
    have a2 : (M * Real.log x / W / L) * Real.log Mt ≤ M * (η / 16 * (ℓ + 4) ^ 2) := by
      have : M * Real.log x / W / L * Real.log Mt = M * (1 / (W * L)) * (Real.log x * Real.log Mt) := by
        ring
      rw [this]
      have h3 : Real.log x * Real.log Mt ≤ (ℓ + 4) ^ 2 := by
        have : Real.log x ≤ ℓ + 4 := by linarith
        calc Real.log x * Real.log Mt ≤ (ℓ + 4) * (ℓ + 4) := mul_le_mul this hlt hlMt0 (by linarith)
          _ = (ℓ + 4) ^ 2 := by ring
      have hWL0 : 0 ≤ 1 / (W * L) := by positivity
      calc M * (1 / (W * L)) * (Real.log x * Real.log Mt) ≤ M * (η / 16) * (ℓ + 4) ^ 2 := by
            rw [mul_assoc, mul_assoc]
            apply mul_le_mul_of_nonneg_left _ hMpos.le
            exact mul_le_mul hWL h3 (mul_nonneg hlx0 hlMt0) (by positivity)
        _ = _ := by ring
    have a3 : M / 4 * Real.log Mt ≤ M * (ℓ + 4) := by
      have := mul_le_mul_of_nonneg_left hlt (show 0 ≤ M / 4 by linarith)
      have : 0 ≤ M * (ℓ + 4) := by positivity
      linarith
    have : ((x / 2 + M * Real.log x / W) / L + M / 4) * Real.log Mt =
        (x / 2 / L) * Real.log Mt + (M * Real.log x / W / L) * Real.log Mt + M / 4 * Real.log Mt := by
      ring
    rw [this]
    have : M * (η / 16 * (ℓ + 4) ^ 2 + (2 / (d * L) + 1) * (ℓ + 4)) =
        M * (1 / (d * L) * (ℓ + 4)) + M * (η / 16 * (ℓ + 4) ^ 2) + M * (ℓ + 4) +
          M * (1 / (d * L) * (ℓ + 4)) := by ring
    rw [this]
    have : 0 ≤ M * (1 / (d * L) * (ℓ + 4)) := by positivity
    linarith
  have e3 : Real.log 2 + x * Real.log x + M * Real.log x * (1 + Real.log t₀) ≤
      M * ((1 + 4 / d * (ℓ + 1)) + (ℓ + 1) * (1 + Real.log C₁ + Real.log (2 * ℓ + 3))) := by
    have a1 : Real.log 2 ≤ M := by
      have := Real.log_two_lt_d9
      have hM1 : (1 : ℝ) ≤ M := by
        simp only [M]; exact_mod_cast (show 1 ≤ T.card by omega)
      linarith
    have a2 : x * Real.log x ≤ M * (4 / d * (ℓ + 1)) := by
      calc x * Real.log x ≤ (2 / d * M) * (ℓ + 1) :=
            mul_le_mul hxN hlx hlx0 (by positivity)
        _ ≤ M * (4 / d * (ℓ + 1)) := by
            have : 0 ≤ M * (2 / d * (ℓ + 1)) := by positivity
            have e : M * (4 / d * (ℓ + 1)) = (2 / d * M) * (ℓ + 1) + M * (2 / d * (ℓ + 1)) := by ring
            linarith
    have a3 : M * Real.log x * (1 + Real.log t₀) ≤
        M * ((ℓ + 1) * (1 + Real.log C₁ + Real.log (2 * ℓ + 3))) := by
      have : 0 ≤ 1 + Real.log t₀ := by have := Real.log_nonneg ht₀1; linarith
      have : Real.log x * (1 + Real.log t₀) ≤ (ℓ + 1) * (1 + Real.log C₁ + Real.log (2 * ℓ + 3)) := by
        apply mul_le_mul hlx (by linarith) (by linarith) (by linarith)
      calc M * Real.log x * (1 + Real.log t₀) = M * (Real.log x * (1 + Real.log t₀)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left this hMpos.le
    have e : M * ((1 + 4 / d * (ℓ + 1)) + (ℓ + 1) * (1 + Real.log C₁ + Real.log (2 * ℓ + 3))) =
        M * 1 + M * (4 / d * (ℓ + 1)) + M * ((ℓ + 1) * (1 + Real.log C₁ + Real.log (2 * ℓ + 3))) := by
      ring
    linarith
  have hfin := mul_le_mul_of_nonneg_left hN hMpos.le
  linarith

end LaneCLai


theorem OMA.solution : OMA.R_Erdos977_erdos_977_variants_lai_R1.H2 := by
  intro d hd hd1 η hη
  filter_upwards [LaneCLai.H2_main d hd hd1 η hη] with N hN
  exact hN
