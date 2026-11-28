import OMAStatements.S_oeis_a367396

/-!
A367396: count the complementary subsets by their disjoint forbidden pairs.
The independence polynomial gives the fixed-size binomial formula, whose generating
series yields both the proposed rational identity and the order-five recurrence.

Proves the statement merged in PR #20346. Related prior formalizations of the
complementary count and recurrence: Jewoo Suh, oeis-lean (2026-10-14),
https://github.com/jewoo-suh/oeis-lean/tree/1b2f715df2642944650976bdbfbf7a9adf76e290
and https://www.trureturing.org/research/oeis-a367400-cardinality-sum-avoiding-subsets/.
This self-contained proof also derives the formal power-series identity.
-/

namespace A367396Support
open PowerSeries

theorem recurrence_of_gf (a : ℕ → ℤ)
    (h : mk a * ((2 * X - 1) * (X ^ 4 - 2 * X ^ 3 + X ^ 2 - 2 * X + 1)) =
      (X : PowerSeries ℤ) ^ 3 * (X - 1)) :
    ∀ n : ℕ, 4 < n →
      a n = 4 * a (n-1) - 5 * a (n-2) + 4 * a (n-3) -
        5 * a (n-4) + 2 * a (n-5) := by
  intro n hn
  have he : mk a * ((2 * X - 1) * (X ^ 4 - 2 * X ^ 3 + X ^ 2 - 2 * X + 1)) =
      C 2 * (mk a * X ^ 5) - C 5 * (mk a * X ^ 4) +
      C 4 * (mk a * X ^ 3) - C 5 * (mk a * X ^ 2) +
      C 4 * (mk a * X ^ 1) - mk a := by
    norm_num
    ring
  rw [he] at h
  have hc := congrArg (coeff n) h
  have h₁ : 1 ≤ n := by omega
  have h₂ : 2 ≤ n := by omega
  have h₃ : 3 ≤ n := by omega
  have h₄ : 4 ≤ n := by omega
  have h₅ : 5 ≤ n := by omega
  have hne3 : n ≠ 3 := by omega
  have hne4 : n ≠ 4 := by omega
  rw [mul_sub, mul_one, ← pow_succ] at hc
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow,
    coeff_mk, h₁, h₂, h₃, h₄, h₅, hne3, hne4, if_true, if_false] at hc
  linarith


theorem gf_from_complement (A B : PowerSeries ℤ)
    (hAll : (A+B) * (1-2*X) = 1)
    (hBad : B * ((1-X) * (X^4-2*X^3+X^2-2*X+1)) =
      (X^4-2*X^3+X^2-2*X+1) + X) :
    A * ((2*X-1) * (X^4-2*X^3+X^2-2*X+1)) = X^3*(X-1) := by
  have hne : (1-X : PowerSeries ℤ) ≠ 0 := by
    intro h
    have hc := congrArg constantCoeff h
    norm_num at hc
  apply mul_left_cancel₀ hne
  linear_combination -((1-X)*(X^4-2*X^3+X^2-2*X+1)) * hAll +
    (1-2*X) * hBad


theorem total_gf (A B : PowerSeries ℤ)
    (h : ∀ n, coeff n A + coeff n B = 2^n) :
    (A+B) * (1-2*X) = 1 := by
  have he : A+B = rescale (2 : ℤ) (mk 1) := by
    ext n
    simpa [coeff_rescale, coeff_mk] using h n
  rw [he]
  simpa using congrArg (rescale (2 : ℤ))
    (mk_one_mul_one_sub_eq_one (S := ℤ))

def GoodSubset (s : Finset ℕ) : Prop :=
  ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ x+y=s.card

noncomputable def goodCount (n : ℕ) : ℕ := by
  classical
  exact (((Finset.Icc 1 n).powerset).filter GoodSubset).card

noncomputable def badCount (n : ℕ) : ℕ := by
  classical
  exact (((Finset.Icc 1 n).powerset).filter fun s => ¬GoodSubset s).card

theorem count_partition (n : ℕ) : goodCount n + badCount n = 2^n := by
  classical
  unfold goodCount badCount
  rw [Finset.card_filter_add_card_filter_not, Finset.card_powerset]
  simp


noncomputable def badFixedCount (n k : ℕ) : ℕ := by
  classical
  exact (((Finset.Icc 1 n).powersetCard k).filter fun s => ¬GoodSubset s).card

theorem badCount_eq_sum_fixed (n : ℕ) :
    badCount n = ∑ k ∈ Finset.range (n+1), badFixedCount n k := by
  classical
  unfold badCount badFixedCount
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun s : Finset ℕ => s.card) (t := Finset.range (n+1))]
  · apply Finset.sum_congr rfl
    intro k hk
    congr 1
    ext s
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
    tauto
  · intro s hs
    have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1
    have hcard := Finset.card_le_card hsub
    simp only [Finset.mem_coe, Finset.mem_range]
    simpa using Nat.lt_succ_of_le hcard

theorem badFixedCount_zero (n : ℕ) : badFixedCount n 0 = 1 := by
  classical
  have he : ¬ GoodSubset ∅ := by simp [GoodSubset]
  simp [badFixedCount, Finset.filter_singleton, he]

theorem badFixedCount_one (n : ℕ) : badFixedCount n 1 = n := by
  classical
  have he : ((Finset.Icc 1 n).powersetCard 1).filter (fun s => ¬GoodSubset s) =
      (Finset.Icc 1 n).powersetCard 1 := by
    apply Finset.filter_eq_self.mpr
    intro s hs
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp (Finset.mem_powersetCard.mp hs).2
    simp [GoodSubset]
  simp [badFixedCount, he]

theorem not_good_iff_avoids_pairs (s : Finset ℕ) (k : ℕ)
    (hc : s.card = k) (hpos : ∀ x ∈ s, 1 ≤ x) :
    ¬GoodSubset s ↔ ∀ x ∈ Finset.Icc 1 ((k-1)/2), ¬(x ∈ s ∧ k-x ∈ s) := by
  constructor
  · intro h x hx hmem
    have hx' := Finset.mem_Icc.mp hx
    apply h
    refine ⟨x, hmem.1, k-x, hmem.2, ?_, ?_⟩ <;> omega
  · intro h ⟨x, hx, y, hy, hne, hsum⟩
    have hxp := hpos x hx
    have hyp := hpos y hy
    by_cases hxy : x < y
    · have hlow : x ∈ Finset.Icc 1 ((k-1)/2) := Finset.mem_Icc.mpr ⟨hxp, by omega⟩
      apply h x hlow
      exact ⟨hx, by simpa only [show k-x=y by omega] using hy⟩
    · have hlow : y ∈ Finset.Icc 1 ((k-1)/2) := Finset.mem_Icc.mpr ⟨hyp, by omega⟩
      apply h y hlow
      exact ⟨hy, by simpa only [show k-y=x by omega] using hx⟩

theorem conclusions_of_bad_gf
    (hBad : mk (fun n => (badCount n : ℤ)) *
      ((1-X) * (X^4-2*X^3+X^2-2*X+1)) =
      (X^4-2*X^3+X^2-2*X+1) + X) :
    (∀ n : ℕ, 4 < n →
      (goodCount n : ℤ) = 4 * (goodCount (n-1) : ℤ) -
        5 * (goodCount (n-2) : ℤ) + 4 * (goodCount (n-3) : ℤ) -
        5 * (goodCount (n-4) : ℤ) + 2 * (goodCount (n-5) : ℤ)) ∧
    (mk (fun n => (goodCount n : ℤ)) *
      ((2*X-1) * (X^4-2*X^3+X^2-2*X+1)) =
      (X : PowerSeries ℤ)^3 * (X-1)) := by
  have hAll := total_gf (mk (fun n => (goodCount n : ℤ)))
    (mk (fun n => (badCount n : ℤ))) (by
      intro n
      simp only [coeff_mk]
      exact_mod_cast count_partition n)
  have hg := gf_from_complement _ _ hAll hBad
  exact ⟨recurrence_of_gf _ hg, hg⟩

end A367396Support





namespace A367396GF
open PowerSeries

noncomputable def G : PowerSeries ℤ := mk 1

lemma G_mul : G * (1-X) = 1 := mk_one_mul_one_sub_eq_one ℤ

lemma coeff_shifted_choose (a k n : ℕ) :
    coeff n (G^(k+1) * (X : PowerSeries ℤ)^(a+k)) =
      if a ≤ n then ((n-a).choose k : ℤ) else 0 := by
  rw [G, mk_one_pow_eq_mk_choose_add, coeff_mul_X_pow', coeff_mk]
  by_cases h : a+k ≤ n
  · rw [if_pos h, if_pos (by omega)]
    congr 2
    omega
  · rw [if_neg h]
    split_ifs with ha
    · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
    · rfl

noncomputable def fixedSeries (r k : ℕ) : PowerSeries ℤ :=
  ∑ j ∈ Finset.range (r+1),
    C ((r.choose j : ℤ)*2^j) * (G^(k-j+1) * X^(2*r+(k-j)))

lemma coeff_fixedSeries (r k n : ℕ) (hrk : r < k) :
    coeff n (fixedSeries r k) =
      ∑ j ∈ Finset.range (r+1),
        (r.choose j : ℤ)*2^j * ((n-2*r).choose (k-j) : ℤ) := by
  simp only [fixedSeries, map_sum, coeff_C_mul, coeff_shifted_choose]
  apply Finset.sum_congr rfl
  intro j hj
  have hjr : j ≤ r := by simpa using Finset.mem_range.mp hj
  by_cases hn : 2*r ≤ n
  · rw [if_pos hn]
  · have hz : (n-2*r).choose (k-j) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [hn, hz]

lemma fixedSeries_mul (r k : ℕ) (hrk : r ≤ k) :
    fixedSeries r k * (1-X)^(k+1) =
      (X : PowerSeries ℤ)^(r+k) * (2-X)^r := by
  unfold fixedSeries
  rw [Finset.sum_mul]
  calc
    _ = ∑ j ∈ Finset.range (r+1),
        C ((r.choose j : ℤ)*2^j) * X^(2*r+(k-j)) * (1-X)^j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjr : j ≤ r := by simpa using Finset.mem_range.mp hj
      have hc : G^(k-j+1) * (1-X)^(k+1) = (1-X)^j := by
        rw [show k+1=(k-j+1)+j by omega, pow_add (1-X), ← mul_assoc,
          ← mul_pow, G_mul, one_pow, one_mul]
      calc
        _ = C ((r.choose j : ℤ)*2^j) * X^(2*r+(k-j)) *
            (G^(k-j+1) * (1-X)^(k+1)) := by ring
        _ = _ := by rw [hc]
    _ = X^(r+k) * ∑ j ∈ Finset.range (r+1),
        (2*(1-X))^j * X^(r-j) * (r.choose j : PowerSeries ℤ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hjr : j ≤ r := by simpa using Finset.mem_range.mp hj
      rw [show 2*r+(k-j)=(r+k)+(r-j) by omega, pow_add]
      simp only [map_mul, map_pow, map_natCast, map_ofNat, mul_pow]
      ring
    _ = X^(r+k) * (2*(1-X)+X)^r := by rw [add_pow]
    _ = _ := by congr 1; ring

lemma fixedSeries_closed (r k : ℕ) (hrk : r ≤ k) :
    fixedSeries r k = (X : PowerSeries ℤ)^(r+k) * (2-X)^r * G^(k+1) := by
  have h := congrArg (fun z : PowerSeries ℤ => z*G^(k+1)) (fixedSeries_mul r k hrk)
  have hc : (1-X)^(k+1)*G^(k+1) = 1 := by
    rw [← mul_pow, mul_comm (1-X) G, G_mul, one_pow]
  simpa only [mul_assoc, hc, mul_one] using h

noncomputable def Q : PowerSeries ℤ := X^3*(2-X)*G^2

lemma Q_constant : constantCoeff Q = 0 := by simp [Q]

lemma fixedSeries_pair (r : ℕ) :
    fixedSeries r (2*r+1) + fixedSeries r (2*r+2) = X*G^3*Q^r := by
  rw [fixedSeries_closed r _ (by omega), fixedSeries_closed r _ (by omega)]
  have hg : G = 1+X*G := by linear_combination G_mul
  simp only [Q, mul_pow, pow_mul, pow_add, pow_one]
  calc
    _ = (X^(r*3)*(2-X)^r*G^(r*2)) * (X*G^2) * (1+X*G) := by ring
    _ = _ := by rw [← hg]; ring

open scoped PowerSeries.WithPiTopology

noncomputable def expectedBad : PowerSeries ℤ := G + X*G^3*∑' r : ℕ, Q^r

lemma expectedBad_gf :
    expectedBad * ((1-X)*(X^4-2*X^3+X^2-2*X+1)) =
      (X^4-2*X^3+X^2-2*X+1) + X := by
  have hc : G^2*(1-X)^2 = 1 := by rw [← mul_pow, G_mul, one_pow]
  have hq : (1-Q)*(1-X)^2 = X^4-2*X^3+X^2-2*X+1 := by
    dsimp [Q]
    calc
      _ = (1-X)^2-X^3*(2-X)*(G^2*(1-X)^2) := by ring
      _ = _ := by rw [hc]; ring
  have ht : (∑' r : ℕ, Q^r)*(X^4-2*X^3+X^2-2*X+1) = (1-X)^2 := by
    rw [← hq, ← mul_assoc,
      PowerSeries.WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero Q_constant,
      one_mul]
  calc
    _ = G*(1-X)*(X^4-2*X^3+X^2-2*X+1) +
        X*G^3*(1-X)*((∑' r : ℕ, Q^r)*(X^4-2*X^3+X^2-2*X+1)) := by
      dsimp [expectedBad]; ring
    _ = G*(1-X)*(X^4-2*X^3+X^2-2*X+1) + X*(G*(1-X))^3 := by
      rw [ht]; ring
    _ = _ := by rw [G_mul]; ring

lemma coeff_fixedSeries_zero (r k n : ℕ) (hrk : r ≤ k) (hnk : n < k) :
    coeff n (fixedSeries r k) = 0 := by
  rw [fixedSeries_closed r k hrk, mul_assoc, mul_comm (X^(r+k)), coeff_mul_X_pow',
    if_neg (by omega)]

lemma coeff_expectedBad (n : ℕ) :
    coeff n expectedBad = 1 + ∑ r ∈ Finset.range (n+1),
      (coeff n (fixedSeries r (2*r+1)) + coeff n (fixedSeries r (2*r+2))) := by
  have hs : HasSum (fun r : ℕ => fixedSeries r (2*r+1)+fixedSeries r (2*r+2))
      (X*G^3*∑' r : ℕ, Q^r) := by
    simpa only [fixedSeries_pair] using
      (PowerSeries.WithPiTopology.summable_pow_of_constantCoeff_eq_zero Q_constant).hasSum.mul_left
        (X*G^3)
  have hc := (PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff ℤ).mp hs n
  have hf : HasSum (fun r : ℕ => coeff n (fixedSeries r (2*r+1)+fixedSeries r (2*r+2)))
      (∑ r ∈ Finset.range (n+1), coeff n (fixedSeries r (2*r+1)+fixedSeries r (2*r+2))) := by
    apply hasSum_sum_of_ne_finset_zero
    intro r hr
    have hnr : n < r := by simpa using hr
    rw [map_add, coeff_fixedSeries_zero r _ n (by omega) (by omega),
      coeff_fixedSeries_zero r _ n (by omega) (by omega), add_zero]
  have hg : coeff n G = 1 := by simp [G]
  simp only [expectedBad, map_add, hg]
  rw [hc.unique hf]
  simp only [map_add]

noncomputable def bySize : ℕ → PowerSeries ℤ
  | 0 => G
  | k+1 => fixedSeries (k/2) (k+1)

lemma bySize_odd (r : ℕ) : bySize (2*r+1) = fixedSeries r (2*r+1) := by
  simp [bySize]

lemma bySize_even (r : ℕ) : bySize (2*r+2) = fixedSeries r (2*r+2) := by
  change fixedSeries ((2*r+1)/2) (2*r+2) = _
  rw [show (2*r+1)/2=r by omega]

lemma coeff_bySize_zero (n k : ℕ) (hnk : n < k) : coeff n (bySize k) = 0 := by
  cases k with
  | zero => omega
  | succ k => exact coeff_fixedSeries_zero _ _ _ (by omega) hnk

lemma sum_bySize_pairs (n m : ℕ) :
    (∑ k ∈ Finset.range (2*m+1), coeff n (bySize k)) =
      1 + ∑ r ∈ Finset.range m,
        (coeff n (fixedSeries r (2*r+1)) + coeff n (fixedSeries r (2*r+2))) := by
  induction m with
  | zero => simp [bySize, G]
  | succ m ih =>
    rw [show 2*(m+1)+1=(2*m+1)+1+1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ,
      bySize_odd, show 2*m+1+1=2*m+2 by omega, bySize_even]
    ring

lemma coeff_expectedBad_bySize (n : ℕ) :
    coeff n expectedBad = ∑ k ∈ Finset.range (n+1), coeff n (bySize k) := by
  rw [coeff_expectedBad, ← sum_bySize_pairs]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega : n+1 ≤ 2*(n+1)+1))
  intro k hk hkn
  apply coeff_bySize_zero
  simpa using hkn

end A367396GF




namespace A367396Support
open PowerSeries A367396GF

theorem bad_series_of_fixed_count
    (hfixed : ∀ n k : ℕ, k ≤ n → badFixedCount n k =
      ∑ j ∈ Finset.range ((k-1)/2+1),
        ((k-1)/2).choose j * 2^j * (n-2*((k-1)/2)).choose (k-j)) :
    mk (fun n => (badCount n : ℤ)) = expectedBad := by
  ext n
  rw [coeff_mk, coeff_expectedBad_bySize, badCount_eq_sum_fixed, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro k hk
  cases k with
  | zero => simp [badFixedCount_zero, bySize, G]
  | succ k =>
    rw [bySize, coeff_fixedSeries (k/2) (k+1) n (by omega)]
    have hn : k+1 ≤ n := by simpa using Finset.mem_range.mp hk
    exact_mod_cast hfixed n (k+1) hn

theorem bad_gf_of_fixed_count
    (hfixed : ∀ n k : ℕ, k ≤ n → badFixedCount n k =
      ∑ j ∈ Finset.range ((k-1)/2+1),
        ((k-1)/2).choose j * 2^j * (n-2*((k-1)/2)).choose (k-j)) :
    mk (fun n => (badCount n : ℤ)) *
      ((1-X)*(X^4-2*X^3+X^2-2*X+1)) =
      (X^4-2*X^3+X^2-2*X+1) + X := by
  rw [bad_series_of_fixed_count hfixed]
  exact expectedBad_gf

end A367396Support

/-! Counting subsets that avoid disjoint forbidden pairs by their independence polynomial. -/
namespace A367396Matching
open Polynomial

variable {α : Type*} [DecidableEq α]

noncomputable def weight (U : Finset α) (P : Finset α → Prop) : Polynomial ℤ := by
  classical
  exact ∑ s ∈ U.powerset, if P s then X ^ s.card else 0

theorem weight_congr (U : Finset α) (P Q : Finset α → Prop)
    (h : ∀ s ⊆ U, P s ↔ Q s) : weight U P = weight U Q := by
  classical
  unfold weight
  apply Finset.sum_congr rfl
  intro s hs
  rw [h s (Finset.mem_powerset.mp hs)]

theorem weight_insert (U : Finset α) (P : Finset α → Prop) (x : α)
    (hx : x ∉ U) :
    weight (insert x U) P = weight U P + X * weight U (fun s => P (insert x s)) := by
  classical
  unfold weight
  rw [Finset.sum_powerset_insert hx, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  have hxs : x ∉ s := fun h => hx (Finset.mem_powerset.mp hs h)
  by_cases hp : P (insert x s) <;>
    simp [hp, Finset.card_insert_of_notMem hxs, pow_succ, mul_comm]

def pairPred (P : Finset α → Prop) (x y : α) (s : Finset α) : Prop :=
  P ((s.erase x).erase y) ∧ ¬(x ∈ s ∧ y ∈ s)

theorem weight_pair (U : Finset α) (P : Finset α → Prop) (x y : α)
    (hx : x ∉ U) (hy : y ∉ U) (hxy : x ≠ y) :
    weight (insert x (insert y U)) (pairPred P x y) =
      (1 + 2 * X) * weight U P := by
  classical
  have hyx : y ≠ x := Ne.symm hxy
  have h0 : weight U (pairPred P x y) = weight U P := by
    apply weight_congr
    intro s hs
    have hxs : x ∉ s := fun h => hx (hs h)
    have hys : y ∉ s := fun h => hy (hs h)
    simp [pairPred, hxs, hys]
  have h1 : weight U (fun s => pairPred P x y (insert x s)) = weight U P := by
    apply weight_congr
    intro s hs
    have hxs : x ∉ s := fun h => hx (hs h)
    have hys : y ∉ s := fun h => hy (hs h)
    simp [pairPred, hxs, hys, hxy, hyx]
  have h2 : weight U (fun s => pairPred P x y (insert y s)) = weight U P := by
    apply weight_congr
    intro s hs
    have hxs : x ∉ s := fun h => hx (hs h)
    have hys : y ∉ s := fun h => hy (hs h)
    simp [pairPred, hxs, hys, hxy, hyx]
  have h3 : weight U (fun s => pairPred P x y (insert x (insert y s))) = 0 := by
    simp [weight, pairPred]
  rw [weight_insert _ _ x (by simp [hx, hxy]), weight_insert _ _ y hy,
    weight_insert _ _ y hy, h0, h1, h2, h3]
  ring

theorem weight_all (U : Finset α) :
    weight U (fun _ => True) = (1 + X) ^ U.card := by
  classical
  induction U using Finset.induction_on with
  | empty => simp [weight]
  | @insert x U hx ih =>
      rw [weight_insert U (fun _ => True) x hx]
      change weight U (fun _ => True) + X * weight U (fun _ => True) = _
      rw [ih, Finset.card_insert_of_notMem hx, pow_succ]
      ring


variable {ι : Type*} [DecidableEq ι]

def vertices (F : Finset α) (L R : ι → α) (I : Finset ι) : Finset α :=
  F ∪ I.image L ∪ I.image R

def avoids (L R : ι → α) (I : Finset ι) (s : Finset α) : Prop :=
  ∀ i ∈ I, ¬(L i ∈ s ∧ R i ∈ s)

lemma left_mem_vertices (F : Finset α) (L R : ι → α) (I : Finset ι)
    {i : ι} (hi : i ∈ I) : L i ∈ vertices F L R I := by
  exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem L hi))

lemma right_mem_vertices (F : Finset α) (L R : ι → α) (I : Finset ι)
    {i : ι} (hi : i ∈ I) : R i ∈ vertices F L R I := by
  exact Finset.mem_union_right _ (Finset.mem_image_of_mem R hi)

lemma avoids_erase (F : Finset α) (L R : ι → α) (I : Finset ι)
    (s : Finset α) (x : α) (hx : x ∉ vertices F L R I) :
    avoids L R I (s.erase x) ↔ avoids L R I s := by
  unfold avoids
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  have hl : L i ≠ x := by
    intro he
    exact hx (he ▸ left_mem_vertices F L R I hi)
  have hr : R i ≠ x := by
    intro he
    exact hx (he ▸ right_mem_vertices F L R I hi)
  simp [Finset.mem_erase, hl, hr]

/-- The independence polynomial of a matching with free isolated vertices. -/
theorem weight_matching (F : Finset α) (L R : ι → α) (I : Finset ι)
    (hL : Function.Injective L) (hR : Function.Injective R)
    (hLR : ∀ i j, L i ≠ R j)
    (hfL : ∀ i, L i ∉ F) (hfR : ∀ i, R i ∉ F) :
    weight (vertices F L R I) (avoids L R I) =
      (1 + X) ^ F.card * (1 + 2 * X) ^ I.card := by
  classical
  induction I using Finset.induction_on with
  | empty =>
      have hp : avoids L R (∅ : Finset ι) = (fun _ : Finset α => True) := by
        funext s
        simp [avoids]
      simpa [vertices, hp] using weight_all F
  | @insert i I hi ih =>
      have hl : L i ∉ vertices F L R I := by
        simp only [vertices, Finset.mem_union, Finset.mem_image]
        rintro ((hf | ⟨j, hj, he⟩) | ⟨j, hj, he⟩)
        · exact hfL i hf
        · exact hi ((hL he) ▸ hj)
        · exact hLR i j he.symm
      have hr : R i ∉ vertices F L R I := by
        simp only [vertices, Finset.mem_union, Finset.mem_image]
        rintro ((hf | ⟨j, hj, he⟩) | ⟨j, hj, he⟩)
        · exact hfR i hf
        · exact hLR j i he
        · exact hi ((hR he) ▸ hj)
      have hv : vertices F L R (insert i I) =
          insert (L i) (insert (R i) (vertices F L R I)) := by
        ext z
        simp only [vertices, Finset.image_insert, Finset.mem_union, Finset.mem_insert]
        tauto
      calc
        weight (vertices F L R (insert i I)) (avoids L R (insert i I)) =
            weight (insert (L i) (insert (R i) (vertices F L R I)))
              (pairPred (avoids L R I) (L i) (R i)) := by
          rw [hv]
          apply weight_congr
          intro s hs
          dsimp only [pairPred]
          rw [avoids_erase F L R I (s.erase (L i)) (R i) hr,
            avoids_erase F L R I s (L i) hl]
          simp [avoids, and_comm]
        _ = (1 + 2 * X) * weight (vertices F L R I) (avoids L R I) :=
          weight_pair _ _ _ _ hl hr (hLR i i)
        _ = (1 + X) ^ F.card * (1 + 2 * X) ^ (insert i I).card := by
          rw [ih, Finset.card_insert_of_notMem hi, pow_succ]
          ring

noncomputable def countFixed (U : Finset α) (P : Finset α → Prop) (k : ℕ) : ℕ := by
  classical
  exact ((U.powersetCard k).filter P).card

/-- Extracting a coefficient from the weight polynomial counts sets of that size. -/
theorem weight_coeff (U : Finset α) (P : Finset α → Prop) (k : ℕ) :
    (weight U P).coeff k = (countFixed U P k : ℤ) := by
  classical
  unfold weight countFixed
  rw [Polynomial.finsetSum_coeff]
  calc
    (∑ s ∈ U.powerset, (if P s then (X : Polynomial ℤ) ^ s.card else 0).coeff k) =
        ∑ s ∈ (U.powersetCard k).filter P, (1 : ℤ) := by
      rw [Finset.powersetCard_eq_filter, Finset.filter_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro s hs
      by_cases hp : P s
      · by_cases hc : s.card = k
        · simp [hp, hc]
        · simp [hp, hc, Ne.symm hc]
      · simp [hp]
    _ = _ := by simp


/-- The forbidden pairs x,k-x in [1,n] form a matching, with n-2r free vertices. -/
theorem nat_pairs_weight (n k : ℕ) (hk : k ≤ n) :
    weight (Finset.Icc 1 n)
      (fun s => ∀ x ∈ Finset.Icc 1 ((k-1)/2), ¬(x ∈ s ∧ k-x ∈ s)) =
      (1 + 2 * X) ^ ((k-1)/2) * (1 + X) ^ (n - 2*((k-1)/2)) := by
  classical
  let r := (k-1)/2
  let I : Finset (Fin r) := Finset.univ
  let L : Fin r → ℕ := fun i => i.val + 1
  let R : Fin r → ℕ := fun i => k - (i.val + 1)
  let U := Finset.Icc 1 n
  let S := I.image L ∪ I.image R
  let F := U \ S
  have hL : Function.Injective L := by
    intro i j h
    apply Fin.ext
    dsimp [L] at h
    omega
  have hR : Function.Injective R := by
    intro i j h
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    dsimp [R] at h
    dsimp [r] at hi hj
    omega
  have hLR : ∀ i j, L i ≠ R j := by
    intro i j h
    have hi := i.isLt
    have hj := j.isLt
    dsimp [L, R] at h
    dsimp [r] at hi hj
    omega
  have hLb (i : Fin r) : L i ∈ U := by
    apply Finset.mem_Icc.mpr
    have hi := i.isLt
    dsimp [L]
    dsimp [r] at hi
    omega
  have hRb (i : Fin r) : R i ∈ U := by
    apply Finset.mem_Icc.mpr
    have hi := i.isLt
    dsimp [R]
    dsimp [r] at hi
    omega
  have hS : S ⊆ U := by
    intro x hx
    rcases Finset.mem_union.mp hx with hl | hr
    · rcases Finset.mem_image.mp hl with ⟨i, hi, rfl⟩
      exact hLb i
    · rcases Finset.mem_image.mp hr with ⟨i, hi, rfl⟩
      exact hRb i
  have hfL : ∀ i, L i ∉ F := by
    intro i hi
    exact (Finset.mem_sdiff.mp hi).2
      (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
  have hfR : ∀ i, R i ∉ F := by
    intro i hi
    exact (Finset.mem_sdiff.mp hi).2
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
  have hv : vertices F L R I = U := by
    change (U \ S) ∪ I.image L ∪ I.image R = U
    rw [Finset.union_assoc]
    exact Finset.sdiff_union_of_subset hS
  have hd : Disjoint (I.image L) (I.image R) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨j, hj, he⟩
    exact hLR i j he.symm
  have hScard : S.card = 2*r := by
    dsimp [S]
    rw [Finset.card_union_of_disjoint hd, Finset.card_image_of_injective I hL,
      Finset.card_image_of_injective I hR]
    simp [I, two_mul]
  have hFcard : F.card = n-2*r := by
    change (U \ S).card = n-2*r
    rw [Finset.card_sdiff_of_subset hS, hScard]
    simp [U]
  have hm := weight_matching F L R I hL hR hLR hfL hfR
  rw [hv, hFcard, show I.card = r by simp [I]] at hm
  have hp : ∀ s, avoids L R I s ↔
      ∀ x ∈ Finset.Icc 1 r, ¬(x ∈ s ∧ k-x ∈ s) := by
    intro s
    constructor
    · intro h x hx
      have hb := Finset.mem_Icc.mp hx
      let i : Fin r := ⟨x-1, by omega⟩
      have hi := h i (Finset.mem_univ _)
      have he : i.val+1=x := by dsimp [i]; omega
      simpa only [L, R, he] using hi
    · intro h i hi
      have hb : L i ∈ Finset.Icc 1 r := by
        apply Finset.mem_Icc.mpr
        have ht := i.isLt
        dsimp [L]
        omega
      exact h (L i) hb
  change weight U (fun s => ∀ x ∈ Finset.Icc 1 r, ¬(x ∈ s ∧ k-x ∈ s)) =
    (1 + 2*X)^r * (1+X)^(n-2*r)
  calc
    _ = weight U (avoids L R I) := weight_congr U _ _ (fun s hs => (hp s).symm)
    _ = _ := by rw [hm]; ring

end A367396Matching
namespace A367396Polynomial
open Polynomial

lemma matching_coeff (r m k : ℕ) (hrk : r < k) :
    (((1+2*X)^r * (1+X)^m : Polynomial ℤ).coeff k) =
      ∑ j ∈ Finset.range (r+1),
        (r.choose j : ℤ)*2^j*(m.choose (k-j) : ℤ) := by
  rw [show (1+2*X : Polynomial ℤ)=2*X+1 by ring, add_pow, Finset.sum_mul, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro j hj
  have hjr : j ≤ r := by simpa using Finset.mem_range.mp hj
  have he : ((2*X)^j * 1^(r-j) * (r.choose j : Polynomial ℤ)) * (1+X)^m =
      C ((r.choose j : ℤ)*2^j) * ((1+X)^m * X^j) := by
    simp only [map_mul, map_pow, map_natCast, map_ofNat, one_pow, mul_pow]
    ring
  rw [he, coeff_C_mul, coeff_mul_X_pow', if_pos (by omega), coeff_one_add_X_pow]

end A367396Polynomial
namespace A367396Support
open Polynomial A367396Matching

/-- The counted bad subsets are exactly the independent sets of the pair matching. -/
theorem badFixedCount_eq_matching_coeff (n k : ℕ) (hk : k ≤ n) :
    (badFixedCount n k : ℤ) =
      (((1+2*X)^((k-1)/2) * (1+X)^(n-2*((k-1)/2)) : Polynomial ℤ).coeff k) := by
  classical
  rw [← nat_pairs_weight n k hk, weight_coeff]
  congr 1
  unfold badFixedCount countFixed
  congr 1
  ext s
  simp only [Finset.mem_filter]
  by_cases hs : s ∈ (Finset.Icc 1 n).powersetCard k
  · simp only [hs, true_and]
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hs
    exact not_good_iff_avoids_pairs s k hcard (fun x hx =>
      (Finset.mem_Icc.mp (hsub hx)).1)
  · simp [hs]

/-- Universal finite counting formula; no generating-function hypothesis is used. -/
theorem badFixedCount_formula (n k : ℕ) (hk : k ≤ n) :
    badFixedCount n k =
      ∑ j ∈ Finset.range ((k-1)/2+1),
        ((k-1)/2).choose j * 2^j * (n-2*((k-1)/2)).choose (k-j) := by
  by_cases hz : k = 0
  · subst k
    simp [badFixedCount_zero]
  · have h := badFixedCount_eq_matching_coeff n k hk
    rw [A367396Polynomial.matching_coeff _ _ _ (by omega)] at h
    exact_mod_cast h

end A367396Support

set_option maxHeartbeats 2000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a367396.main := by
  have ha (n : ℕ) : A367396Support.goodCount n = OMA.S_oeis_a367396.a n := by
    classical
    unfold A367396Support.goodCount OMA.S_oeis_a367396.a
    congr 1
    apply Finset.filter_congr
    intro s hs
    rfl
  simpa only [ha] using A367396Support.conclusions_of_bad_gf
    (A367396Support.bad_gf_of_fixed_count A367396Support.badFixedCount_formula)
