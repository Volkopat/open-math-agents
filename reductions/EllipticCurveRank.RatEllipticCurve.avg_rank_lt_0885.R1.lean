import FormalConjectures.Wikipedia.EllipticCurveRank
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Set.Card
import Mathlib.Order.LiminfLimsup
import Mathlib.Tactic

/-!
# Reduction of `EllipticCurveRank.RatEllipticCurve.avg_rank_lt_0885`

Reduces Bhargava–Shankar's Theorem 3 (average Mordell–Weil rank of rational elliptic curves
ordered by naïve height is strictly less than `0.885`) to:
1. `H1`: Exponential-moment consequence of Bhargava–Shankar Theorem 1 (`limsup` of the average
   of `5 ^ E.rank` is at most `6`, since `5 ^ E.rank ≤ |Sel₅(E)|` and the average 5-Selmer size
   is `6`).
2. `H2`: Unrounded lower density of rank `0` curves from Bhargava–Shankar Theorem 5 / Section 6
   (`liminf` of the density of `E.rank = 0` is at least `0.5501 * (3 / 8) = 16503 / 80000`).

Inside `main`, we prove the sharp pointwise inequality
`20 * r + 16 * 1_{r = 0} ≤ 5 ^ r + 15` for all `r : ℕ`, sum it over `heightLE H`, normalize by
`(heightLE H).ncard`, and combine `H1` and `H2` to obtain an eventual upper bound of
`88499 / 100000 < 0.885` on the average rank, hence `limsup < 0.885`.

Reference:
- M. Bhargava & A. Shankar, *The average size of the 5-Selmer group of elliptic curves is 6,
  and the average rank is less than 1*, arXiv:1312.7859 (2013), Theorems 1, 3, 5 and Section 6.

Thanks to @kanishkrajtanwar and @JSuupaSellers for the sharp envelope
`20 * r + 16 * 1_{r = 0} ≤ 5^r + 15` and Bhargava–Shankar density-blend notes.
Credit: @tkaiman
-/

namespace OMA.R_EllipticCurveRank_RatEllipticCurve_avg_rank_lt_0885_R1

open EllipticCurveRank EllipticCurveRank.RatEllipticCurve Filter
open scoped BigOperators Topology

private lemma nat_cast_finsum_real {α : Type*} (f : α → ℕ) :
    ((∑ᶠ x, f x : ℕ) : ℝ) = ∑ᶠ x, (f x : ℝ) :=
  (Nat.castAddMonoidHom ℝ).map_finsum_of_injective Nat.cast_injective f

private lemma linear_rank_bound (n : ℕ) :
    20 * (n : ℝ) ≤ (5 : ℝ) ^ n + 15 := by
  have hsucc (k : ℕ) : 20 * ((k : ℝ) + 1) ≤ (5 : ℝ) ^ (k + 1) + 15 := by
    induction k with
    | zero => norm_num
    | succ k ih =>
      simp only [Nat.cast_succ, pow_succ] at ih ⊢
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith
  cases n with
  | zero => norm_num
  | succ n => simpa only [Nat.cast_succ] using hsucc n

private lemma corrected_rank_bound (n : ℕ) :
    20 * (n : ℝ) + 16 * (if n = 0 then (1 : ℝ) else 0) ≤ (5 : ℝ) ^ n + 15 := by
  by_cases hn : n = 0
  · subst hn; norm_num
  · simpa only [if_neg hn, mul_zero, add_zero] using linear_rank_bound n

private lemma sum_corrected_rank_bound {α : Type*} (s : Set α) (hs : s.Finite) (r : α → ℕ) :
    20 * (∑ᶠ x : s, (r x.1 : ℝ)) + 16 * ({x ∈ s | r x = 0}.ncard : ℝ) ≤
      (∑ᶠ x : s, (5 : ℝ) ^ r x.1) + 15 * (s.ncard : ℝ) := by
  classical
  have hz : {x ∈ s | r x = 0} = (↑(hs.toFinset.filter fun x => r x = 0) : Set α) := by
    ext x; simp
  rw [finsum_set_coe_eq_finsum_mem (f := fun x => (r x : ℝ)),
    finsum_set_coe_eq_finsum_mem (f := fun x => (5 : ℝ) ^ r x),
    finsum_mem_eq_finite_toFinset_sum _ hs, finsum_mem_eq_finite_toFinset_sum _ hs]
  rw [hz, Set.ncard_coe_finset, Set.ncard_eq_toFinset_card s hs]
  have hsum := Finset.sum_le_sum (s := hs.toFinset) (fun x _ => corrected_rank_bound (r x))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole,
    Finset.sum_const, nsmul_eq_mul] at hsum
  nlinarith [hsum]

/-- **Bhargava–Shankar Theorem 1 (exponential-moment consequence)**:
when rational elliptic curves are ordered by naïve height, the average of `5 ^ E.rank`
has limsup at most `6` (since `5 ^ E.rank ≤ |Sel₅(E)|` and the average 5-Selmer size is `6`). -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ H : ℕ in atTop,
    (∑ᶠ E : heightLE H, (5 : ℝ) ^ E.1.rank) / (heightLE H).ncard ≤ 6 + ε

/-- **Bhargava–Shankar Theorem 5 (unrounded lower density of rank 0)**:
when rational elliptic curves are ordered by naïve height, the lower density of curves with
Mordell–Weil rank `0` is at least `0.5501 * (3 / 8) = 16503 / 80000 = 0.2062875`
(Section 6 of Bhargava–Shankar 2013, arXiv:1312.7859). -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ H : ℕ in atTop,
    (16503 / 80000 : ℝ) - ε ≤
      ({E ∈ heightLE H | E.rank = 0}.ncard : ℝ) / (heightLE H).ncard

theorem main : H1 → H2 → type_of% @EllipticCurveRank.RatEllipticCurve.avg_rank_lt_0885 := by
  intro h1 h2
  have heps : (0 : ℝ) < 1 / 100000 := by norm_num
  have hev : ∀ᶠ H : ℕ in atTop,
      (∑ᶠ E : heightLE H, (E.1.rank : ℝ)) / (heightLE H).ncard ≤ (88499 / 100000 : ℝ) := by
    filter_upwards [h1 (1 / 100000) heps, h2 (1 / 100000) heps] with H hm hz
    have hn : (heightLE H).ncard ≠ 0 := by
      intro hn
      simp only [hn, Nat.cast_zero, div_zero] at hz
      norm_num at hz
    have hN : (0 : ℝ) < (heightLE H).ncard := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hs : (heightLE H).Finite := Set.finite_of_ncard_ne_zero hn
    have hsum := sum_corrected_rank_bound (heightLE H) hs rank
    have hnorm :
        20 * ((∑ᶠ E : heightLE H, (E.1.rank : ℝ)) / (heightLE H).ncard) +
          16 * (({E ∈ heightLE H | E.rank = 0}.ncard : ℝ) / (heightLE H).ncard) ≤
        (∑ᶠ E : heightLE H, (5 : ℝ) ^ E.1.rank) / (heightLE H).ncard + 15 := by
      have hd := div_le_div_of_nonneg_right hsum hN.le
      simpa only [add_div, mul_div_assoc, div_self hN.ne', mul_one] using hd
    nlinarith [hm, hz, hnorm]
  have hnonneg (H : ℕ) :
      0 ≤ (∑ᶠ E : heightLE H, (E.1.rank : ℝ)) / (heightLE H).ncard :=
    div_nonneg (finsum_nonneg fun E => Nat.cast_nonneg E.1.rank) (Nat.cast_nonneg _)
  have hlim : atTop.limsup
      (fun H : ℕ => (∑ᶠ E : heightLE H, (E.1.rank : ℝ)) / (heightLE H).ncard) ≤
        (88499 / 100000 : ℝ) :=
    Filter.limsup_le_of_le (Filter.isCoboundedUnder_le_of_le atTop hnonneg) hev
  simpa only [nat_cast_finsum_real] using
    (lt_of_le_of_lt hlim (by norm_num : (88499 / 100000 : ℝ) < 0.885))

end OMA.R_EllipticCurveRank_RatEllipticCurve_avg_rank_lt_0885_R1
