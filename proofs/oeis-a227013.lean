import OMAStatements.S_oeis_a227013
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.NormNum

/-!
# Counterexample to the printed closed form for A227013

At its published offset n = 1 the harmonic block contains just 1, and the
conjectured expression gives 40. The next block also disagrees.

Source: https://oeis.org/A227013
Credit: @ali-hamdan-007
-/

open OMA.S_oeis_a227013

private theorem initial_values :
    a 1 = 1 ∧ proposed 1 = 40 ∧ a 2 = 6 ∧ proposed 2 = 152 := by
  decide +kernel

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a227013.main) := by
  intro h
  have heq := h.1 1 (by decide)
  rw [initial_values.1, initial_values.2.1] at heq
  exact (by decide : ¬ (((1 : ℤ) : ℚ) = 40)) heq

namespace A227013.Analytic

def variance (L : ℕ) : ℚ := ((L : ℚ)^2 - 1)/12
def fourth (L : ℕ) : ℚ := (((L : ℚ)^2-1)*(3*(L:ℚ)^2-7))/240
def radius (L : ℕ) : ℚ := ((L : ℚ)-1)/2

private theorem centered_squares_aux (L : ℕ) (h : ℚ) :
    ∑ i ∈ Finset.range L, ((i : ℚ) - h)^2 =
      (L : ℚ)*((L:ℚ)-1)*(2*L-1)/6 - h*L*(L-1) + L*h^2 := by
  induction L with
  | zero => simp
  | succ L ih => rw [Finset.sum_range_succ, ih, Nat.cast_succ]; ring

private theorem centered_squares (L : ℕ) :
    ∑ i ∈ Finset.range L, ((i : ℚ) - radius L)^2 = L * variance L := by
  rw [centered_squares_aux, variance, radius]
  ring

private theorem double_recip (m t : ℚ) (hp : 0 < m+t) (hn : 0 < m-t) :
    1/(m+t) + 1/(m-t) = 2 * (m/(m^2-t^2)) := by
  rw [div_add_div 1 1 hp.ne' hn.ne', ← mul_div_assoc,
    show m^2-t^2 = (m+t)*(m-t) by ring]
  congr 1
  ring

private theorem paired (L : ℕ) (hL : 2 ≤ L) (m : ℚ) (hm : radius L < m) :
    (∑ i ∈ Finset.range L, (1:ℚ)/(m + ((i:ℚ)-radius L))) =
      ∑ i ∈ Finset.range L, m/(m^2-((i:ℚ)-radius L)^2) := by
  have hl' : 1 ≤ L := by omega
  have hr := Finset.sum_range_reflect (fun i : ℕ => (1:ℚ)/(m + ((i:ℚ)-radius L))) L
  have symm : (∑ i ∈ Finset.range L, (1:ℚ)/(m - ((i:ℚ)-radius L))) =
      ∑ i ∈ Finset.range L, (1:ℚ)/(m + ((i:ℚ)-radius L)) := by
    rw [← hr]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ L-1 := by have := Finset.mem_range.mp hi; omega
    rw [Nat.cast_sub hi', Nat.cast_sub hl']
    unfold radius
    push_cast
    ring
  have term : (∑ i ∈ Finset.range L,
      ((1:ℚ)/(m+((i:ℚ)-radius L)) + 1/(m-((i:ℚ)-radius L)))) =
      2 * ∑ i ∈ Finset.range L, m/(m^2-((i:ℚ)-radius L)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hh : (i:ℚ) ≤ (L:ℚ)-1 := by
      have hb := Finset.mem_range.mp hi
      have hcast : (i:ℚ)+1 ≤ L := by exact_mod_cast hb
      linarith
    apply double_recip
    · have : (0:ℚ) ≤ i := by positivity
      linarith
    · unfold radius at *
      linarith
  rw [Finset.sum_add_distrib, symm] at term
  linarith

private theorem centered_fourth_aux (L : ℕ) (h : ℚ) :
    (∑ i ∈ Finset.range L, ((i : ℚ)-h)^4) =
      (L : ℚ)*(L-1)*(2*L-1)*(3*L^2-3*L-1)/30
      - h*L^2*(L-1)^2 + h^2*L*(L-1)*(2*L-1) - 2*h^3*L*(L-1) + L*h^4 := by
  induction L with
  | zero => simp
  | succ L ih => rw [Finset.sum_range_succ, ih, Nat.cast_succ]; ring

private theorem centered_fourth (L : ℕ) :
    (∑ i ∈ Finset.range L, ((i : ℚ)-radius L)^4) = L * fourth L := by
  rw [centered_fourth_aux, fourth, radius]
  ring

private theorem expandTerm (m x : ℚ) (hm : 0 < m) (hx : 0 < m^2-x^2) :
    m*(m/(m^2-x^2)) = 1 + x^2/m^2 + x^4/(m^2*(m^2-x^2)) := by
  let d := m^2-x^2
  change m*(m/d) = 1 + x^2/m^2 + x^4/(m^2*d)
  have hd : d ≠ 0 := hx.ne'
  have hm' : m^2 ≠ 0 := pow_ne_zero _ hm.ne'
  have hmd := mul_ne_zero hm' hd
  have hleft : m*m/d = (m*m*m^2)/(m^2*d) := by
    apply (div_eq_div_iff hd hmd).mpr
    ring
  have hright : x^2*d/(m^2*d) = x^2/m^2 := by
    apply (div_eq_div_iff hmd hm').mpr
    ring
  rw [← mul_div_assoc, hleft, ← hright, ← div_self hmd]
  rw [← add_div, ← add_div]
  congr 1
  dsimp [d]
  ring

/-- Bounds on the harmonic mean using the second and fourth central moments. -/
theorem bounds (L : ℕ) (hL : 2 ≤ L) (m : ℚ) (hm : radius L < m) :
    let S := ∑ i ∈ Finset.range L, (1 : ℚ)/(m+((i : ℚ)-radius L))
    m/(1 + variance L/m^2 + fourth L/(m^2*(m^2-(radius L)^2))) ≤ (L : ℚ)/S ∧
    (L : ℚ)/S ≤ m/(1 + variance L/m^2 + fourth L/m^4) := by
  let t (i : ℕ) : ℚ := (i : ℚ)-radius L
  let d (i : ℕ) : ℚ := m^2-(t i)^2
  let h := radius L
  let S := ∑ i ∈ Finset.range L, (1 : ℚ)/(m+t i)
  have hl : (2 : ℚ) ≤ L := by exact_mod_cast hL
  have hh : 0 < h := by dsimp [h,radius]; linarith
  have hm0 : 0 < m := lt_trans hh hm
  have m2 : 0 < m^2 := by positivity
  have bottom : 0 < m^2-h^2 := by nlinarith [mul_pos (sub_pos.mpr hm) (show 0 < m+h by linarith)]
  have sqbound (i : ℕ) (hi : i ∈ Finset.range L) : (t i)^2 ≤ h^2 := by
    have hi1 : (i:ℚ)+1 ≤ L := by exact_mod_cast (Finset.mem_range.mp hi)
    have hi0 : 0 ≤ (i:ℚ) := by positivity
    have he : -h ≤ t i ∧ t i ≤ h := by dsimp [t,h,radius]; constructor <;> linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr he.2) (show 0 ≤ h+t i by linarith [he.1])]
  have den (i : ℕ) (hi : i ∈ Finset.range L) : 0 < d i := by
    dsimp [d]; linarith [sqbound i hi]
  have Spos : 0 < S := by
    apply Finset.sum_pos
    · intro i _
      have hi : 0 ≤ (i:ℚ) := by positivity
      apply div_pos (by norm_num)
      dsimp [t]
      linarith
    · exact ⟨0, Finset.mem_range.mpr (by omega)⟩
  have posV : 0 ≤ variance L := by unfold variance; nlinarith [sq_nonneg ((L:ℚ)-2)]
  have posW : 0 ≤ fourth L := by
    unfold fourth
    apply div_nonneg _ (by norm_num)
    exact mul_nonneg (by nlinarith [sq_nonneg ((L:ℚ)-2)]) (by nlinarith [sq_nonneg ((L:ℚ)-2)])
  have momentSum (D : ℚ) :
      (∑ i ∈ Finset.range L, (1 + (t i)^2/m^2 + (t i)^4/D)) =
        (L:ℚ)*(1 + variance L/m^2 + fourth L/D) := by
    have factor (f : ℕ → ℚ) (y : ℚ) :
        (∑ i ∈ Finset.range L, f i/y) = (∑ i ∈ Finset.range L, f i)/y := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, factor, factor]
    change (∑ _i ∈ Finset.range L, (1:ℚ)) +
      (∑ i ∈ Finset.range L, ((i : ℚ)-radius L)^2) / m^2 +
      (∑ i ∈ Finset.range L, ((i : ℚ)-radius L)^4) / D = _
    rw [centered_squares, centered_fourth]
    simp
    ring
  have eqSum : m*S = ∑ i ∈ Finset.range L, (1+(t i)^2/m^2+(t i)^4/(m^2*d i)) := by
    change m*(∑ i ∈ Finset.range L, (1:ℚ)/(m+((i:ℚ)-radius L))) = _
    rw [paired L hL m hm, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i hi => expandTerm m (t i) hm0 (den i hi)
  change m/(1+variance L/m^2+fourth L/(m^2*(m^2-h^2))) ≤ (L:ℚ)/S ∧
    (L:ℚ)/S ≤ m/(1+variance L/m^2+fourth L/m^4)
  constructor
  · apply (div_le_div_iff₀ (by positivity) Spos).mpr
    rw [eqSum, ← momentSum]
    apply Finset.sum_le_sum
    intro i hi
    apply add_le_add le_rfl
    apply div_le_div_of_nonneg_left (by positivity) (mul_pos m2 bottom)
    apply mul_le_mul_of_nonneg_left _ m2.le
    dsimp [d]
    linarith [sqbound i hi]
  · apply (div_le_div_iff₀ Spos (by positivity)).mpr
    rw [eqSum, ← momentSum]
    apply Finset.sum_le_sum
    intro i hi
    apply add_le_add le_rfl
    apply div_le_div_of_nonneg_left (by positivity) (mul_pos m2 (den i hi))
    dsimp [d]
    nlinarith [mul_nonneg m2.le (sq_nonneg (t i))]

end A227013.Analytic

namespace A227013.Polynomials

def span (n : ℚ) : ℚ := n^4 - (n-1)^4
def mid (n : ℚ) : ℚ := ((n-1)^4 + n^4 + 1)/2
def radius (n : ℚ) : ℚ := (span n - 1)/2
def variance (n : ℚ) : ℚ := (span n ^ 2 - 1)/12
def fourth (n : ℚ) : ℚ := (span n ^ 2 - 1)*(3*span n ^ 2 - 7)/240
def base (n : ℚ) : ℚ := n^4 - 2*n^3 + 5*n^2/3 - 2*n/3 - 1/9

set_option maxHeartbeats 2000000 in
private theorem bounds_shift (x : ℚ) (hx : 0 ≤ x) :
    base (x+11) + 1/9 <
      mid (x+11) / (1 + variance (x+11)/(mid (x+11))^2 +
        fourth (x+11)/((mid (x+11))^2*((mid (x+11))^2 - (radius (x+11))^2))) ∧
    mid (x+11) / (1 + variance (x+11)/(mid (x+11))^2 +
        fourth (x+11)/(mid (x+11))^4) < base (x+11) + 7/9 := by
  let m := mid (x+11)
  let h := radius (x+11)
  let v := variance (x+11)
  let w := fourth (x+11)
  let p := base (x+11)
  have hm : 0 < m := by dsimp [m, mid]; ring_nf; positivity
  have hd : 0 < m^2-h^2 := by dsimp [m, h, mid, radius, span]; ring_nf; positivity
  have hv : 0 < v := by dsimp [v, variance, span]; ring_nf; positivity
  have hw : 0 < w := by dsimp [w, fourth, span]; ring_nf; positivity
  have hlo : 0 < m^3*(m^2-h^2) - (p+1/9)*((m^2+v)*(m^2-h^2)+w) := by
    dsimp [m,h,v,w,p,mid,radius,variance,fourth,span,base]
    ring_nf
    positivity
  have hhi : 0 < (p+7/9)*(m^4+v*m^2+w) - m^5 := by
    dsimp [m,v,w,p,mid,variance,fourth,span,base]
    ring_nf
    positivity
  have blend₁ : (1+v/m^2+w/(m^2*(m^2-h^2))) * (m^2*(m^2-h^2)) =
      (m^2+v)*(m^2-h^2)+w := by
    rw [add_mul, div_mul_cancel₀ _ (by positivity), add_mul, one_mul,
      ← mul_assoc (v/m^2), div_mul_cancel₀ _ (by positivity), add_mul]
  have blend₂ : (1+v/m^2+w/m^4)*m^4 = m^4+v*m^2+w := by
    have h4 : v/m^2*m^4 = v*m^2 := by
      rw [show m^4 = m^2*m^2 by ring, ← mul_assoc, div_mul_cancel₀ _ (by positivity)]
    rw [add_mul, div_mul_cancel₀ _ (by positivity), add_mul, one_mul, h4]
  change p+1/9 < m/(1+v/m^2+w/(m^2*(m^2-h^2))) ∧
    m/(1+v/m^2+w/m^4) < p+7/9
  constructor
  · apply (lt_div_iff₀ (by positivity)).2
    apply (mul_lt_mul_iff_of_pos_right (show 0 < m^2*(m^2-h^2) by positivity)).mp
    rw [mul_assoc, blend₁]
    calc (p+1/9)*((m^2+v)*(m^2-h^2)+w) < m^3*(m^2-h^2) := sub_pos.mp hlo
      _ = m*(m^2*(m^2-h^2)) := by ring
  · apply (div_lt_iff₀ (by positivity)).2
    apply (mul_lt_mul_iff_of_pos_right (show 0 < m^4 by positivity)).mp
    rw [mul_assoc (p+7/9), blend₂]
    calc m*m^4 = m^5 := by ring
      _ < (p+7/9)*(m^4+v*m^2+w) := sub_pos.mp hhi

theorem bounds (n : ℕ) (hn : 11 ≤ n) :
    base n + 1/9 <
      mid n / (1 + variance n/(mid n)^2 +
        fourth n/((mid n)^2*((mid n)^2 - (radius n)^2))) ∧
    mid n / (1 + variance n/(mid n)^2 + fourth n/(mid n)^4) < base n + 7/9 := by
  have hx : (0 : ℚ) ≤ (n : ℚ) - 11 := sub_nonneg.mpr (by exact_mod_cast hn)
  simpa only [sub_add_cancel] using bounds_shift ((n : ℚ) - 11) hx

end A227013.Polynomials

namespace A227013.Floor

def B (n : ℕ) : ℚ := (n : ℚ)^4 - 2*n^3 + 5*n^2/3 - 2*n/3 - 1/9

/-- The residue modulo three determines which integer lies just below the
harmonic mean when it is in the specified interval. -/
theorem recover (n : ℕ) (hn : 3 ≤ n) (H : ℚ)
    (hl : B n + 1/9 < H) (hu : H < B n + 7/9) :
    9 * H.floor = 9*(n : ℤ)^4 - 18*n^3 + 15*n^2 - 6*n - 1
      - (if (n-2)%3=0 then 2 else -1) := by
  let U : ℤ := 9*(n : ℤ)^4 - 18*n^3 + 15*n^2 - 6*n - 1
  let d : ℤ := if (n-2)%3 = 0 then 2 else -1
  have hB : 9 * B n = (U : ℚ) := by
    dsimp [U, B]
    push_cast
    ring
  have existsQ : ∃ q : ℤ, 9*q = U-d := by
    let k := n/3
    have cases : n = 3*k ∨ n = 3*k+1 ∨ n = 3*k+2 := by dsimp [k]; omega
    rcases cases with h | h | h
    · refine ⟨(n:ℤ)^4 - 2*n^3 + n^2 + 6*(k:ℤ)^2 - 2*k, ?_⟩
      have hd : d = -1 := if_neg (by omega)
      have hc : (n:ℤ) = 3*(k:ℤ) := by exact_mod_cast h
      dsimp [U]
      rw [hd, hc]
      ring
    · refine ⟨(n:ℤ)^4 - 2*n^3 + n^2 + 6*(k:ℤ)^2 + 2*k, ?_⟩
      have hd : d = -1 := if_neg (by omega)
      have hc : (n:ℤ) = 3*(k:ℤ)+1 := by exact_mod_cast h
      dsimp [U]
      rw [hd, hc]
      ring
    · refine ⟨(n:ℤ)^4 - 2*n^3 + n^2 + 6*(k:ℤ)^2 + 6*k + 1, ?_⟩
      have hd : d = 2 := if_pos (by omega)
      have hc : (n:ℤ) = 3*(k:ℤ)+2 := by exact_mod_cast h
      dsimp [U]
      rw [hd, hc]
      ring
  obtain ⟨q, hq⟩ := existsQ
  have hq' : (9:ℚ)*q = (U:ℚ)-(d:ℚ) := by exact_mod_cast hq
  have hd : (-1:ℚ) ≤ d ∧ (d:ℚ) ≤ 2 := by dsimp [d]; split <;> norm_num
  have lo : q ≤ H.floor := Rat.le_floor_iff.mpr (by linarith [hd.1])
  have hi : H.floor < q+1 := Rat.floor_lt_iff.mpr (by push_cast; linarith [hd.2])
  change 9 * H.floor = U-d
  omega

end A227013.Floor

/-!
Exact small-index certificates for the harmonic blocks in OEIS A227013.
For a common scale c, the sum of floor(c/i) bounds the scaled reciprocal
sum from below. Adding one per term gives an upper bound. Comparing these
two integers to the endpoints of a candidate floor interval settles the floor.
-/

namespace A227013Small

open OMA.S_oeis_a227013

private def reciprocalSum (b k : ℕ) : ℚ :=
  ((List.range k).map fun i => (1 : ℚ) / ((b+i+1 : ℕ) : ℚ)).sum

private def roundedSum (c b : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => roundedSum c b k + c / (b+k+1)

private theorem rounded_bounds (c b k : ℕ) :
    (roundedSum c b k : ℚ) ≤ c * reciprocalSum b k ∧
      c * reciprocalSum b k ≤ (roundedSum c b k : ℚ) + k := by
  induction k with
  | zero => simp [roundedSum, reciprocalSum]
  | succ k ih =>
    let i := b+k+1
    have hi : 0 < i := by dsimp [i]; omega
    have lo : c / i * i ≤ c := Nat.div_mul_le_self c i
    have up : c < (c / i + 1) * i := by
      have hr := Nat.mod_lt c hi
      have hd := Nat.div_add_mod c i
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (c/i) i]
      omega
    have hi' : (0:ℚ) < i := by exact_mod_cast hi
    have lo' : (↑(c/i) : ℚ) ≤ (c : ℚ)/i := by
      apply (le_div_iff₀ hi').mpr
      exact_mod_cast lo
    have up' : (c : ℚ)/i ≤ (↑(c/i) : ℚ)+1 := by
      apply (div_le_iff₀ hi').mpr
      exact_mod_cast up.le
    have hs : reciprocalSum b (k+1) = reciprocalSum b k + 1/(i : ℚ) := by
      simp [reciprocalSum, List.range_succ, i]
    rw [hs, mul_add, mul_one_div]
    change (↑(roundedSum c b k + c/i) : ℚ) ≤ _ ∧
      _ ≤ (↑(roundedSum c b k + c/i) : ℚ) + ((k+1 : ℕ) : ℚ)
    push_cast
    constructor <;> linarith only [ih.1, ih.2, lo', up']

private theorem certify (n z c : ℕ) (hc : 0 < c)
    (b k : ℕ) (hb : (n-1)^4=b) (hk : n^4-b=k) (r : ℕ)
    (hr : roundedSum c b k = r) (hrpos : 0 < r)
    (hl : z*(r+k) ≤ k*c) (hu : k*c < (z+1)*r) :
    a n = (z : ℤ) := by
  let S := reciprocalSum b k
  obtain ⟨hL, hU⟩ := rounded_bounds c b k
  rw [hr] at hL hU
  change (r : ℚ) ≤ c*S at hL
  change (c : ℚ)*S ≤ r+k at hU
  have hc' : (0:ℚ) < c := by exact_mod_cast hc
  have hr' : (0:ℚ) < r := by exact_mod_cast hrpos
  have hS : (0:ℚ) < S := (mul_pos_iff_of_pos_left hc').mp (lt_of_lt_of_le hr' hL)
  have hl' : (z:ℚ)*(r+k) ≤ k*(c:ℚ) := by exact_mod_cast hl
  have hu' : (k:ℚ)*c < ((z:ℚ)+1)*r := by exact_mod_cast hu
  have zpos : (0:ℚ) ≤ z := by positivity
  have z1pos : (0:ℚ) ≤ (z:ℚ)+1 := by positivity
  have hfloorL : (z:ℚ) ≤ (k:ℚ)/S := by
    apply (le_div_iff₀ hS).mpr
    apply (le_of_mul_le_mul_right _ hc')
    calc (z:ℚ)*S*c = (z:ℚ)*(c*S) := by ring
         _ ≤ (z:ℚ)*(r+k) := mul_le_mul_of_nonneg_left hU zpos
         _ ≤ (k:ℚ)*c := hl'
  have hfloorU : (k:ℚ)/S < (z:ℚ)+1 := by
    apply (div_lt_iff₀ hS).mpr
    apply (lt_of_mul_lt_mul_right _ hc'.le)
    calc (k:ℚ)*c < ((z:ℚ)+1)*r := hu'
         _ ≤ ((z:ℚ)+1)*(c*S) := mul_le_mul_of_nonneg_left hL z1pos
         _ = ((z:ℚ)+1)*S*c := by ring
  change (((n^4-(n-1)^4 : ℕ) : ℚ) / reciprocalSum ((n-1)^4) (n^4-(n-1)^4)).floor = _
  rw [hb, hk]
  change ((k:ℚ)/S).floor = (z:ℤ)
  apply le_antisymm
  · have ht : ((k:ℚ)/S).floor < (z:ℤ)+1 := Rat.floor_lt_iff.mpr (by simpa using hfloorU)
    omega
  · exact Rat.le_floor_iff.mpr (by simpa using hfloorL)

theorem small_1 : a 1 = 1 := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 1000000 in
theorem small_2 : a 2 = 6 := by
  exact certify 2 6 268435456 (by decide) 1 15 (by decide) (by decide)
    639072069 (by decide +kernel) (by decide) (by decide) (by decide)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 1000000 in
theorem small_3 : a 3 = 40 := by
  exact certify 3 40 268435456 (by decide) 16 65 (by decide) (by decide)
    428717153 (by decide +kernel) (by decide) (by decide) (by decide)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 1000000 in
theorem small_4 : a 4 = 152 := by
  exact certify 4 152 268435456 (by decide) 81 175 (by decide) (by decide)
    307766548 (by decide +kernel) (by decide) (by decide) (by decide)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 1000000 in
theorem small_5 : a 5 = 413 := by
  exact certify 5 413 268435456 (by decide) 256 369 (by decide) (by decide)
    239289136 (by decide +kernel) (by decide) (by decide) (by decide)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 1000000 in
theorem small_6 : a 6 = 920 := by
  exact certify 6 920 268435456 (by decide) 625 671 (by decide) (by decide)
    195654817 (by decide +kernel) (by decide) (by decide) (by decide)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 1000000 in
theorem small_7 : a 7 = 1792 := by
  exact certify 7 1792 268435456 (by decide) 1296 1105 (by decide) (by decide)
    165469845 (by decide +kernel) (by decide) (by decide) (by decide)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 1000000 in
theorem small_8 : a 8 = 3173 := by
  exact certify 8 3173 268435456 (by decide) 2401 1695 (by decide) (by decide)
    143354264 (by decide +kernel) (by decide) (by decide) (by decide)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 1000000 in
theorem small_9 : a 9 = 5232 := by
  exact certify 9 5232 268435456 (by decide) 4096 2465 (by decide) (by decide)
    126455044 (by decide +kernel) (by decide) (by decide) (by decide)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 1000000 in
theorem small_10 : a 10 = 8160 := by
  exact certify 10 8160 268435456 (by decide) 6561 3439 (by decide) (by decide)
    113121240 (by decide +kernel) (by decide) (by decide) (by decide)

end A227013Small

namespace A227013Small

open OMA.S_oeis_a227013

theorem small_corrected {n : ℕ} (hlo : 3 ≤ n) (hhi : n < 11) :
    9 * a n = 9*(n : ℤ)^4 - 18*(n : ℤ)^3 + 15*(n : ℤ)^2 - 6*(n : ℤ) - 1
      - (if (n-2)%3 = 0 then 2 else -1) := by
  rcases (show n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 by omega)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [small_3, small_4, small_5, small_6, small_7, small_8, small_9, small_10]
  all_goals decide +kernel

theorem recurrence_exceptions :
    a 8 - (4*a 7 - 6*a 6 + 5*a 5 - 5*a 4 + 6*a 3 - 4*a 2 + a 1) = 3 ∧
    a 9 - (4*a 8 - 6*a 7 + 5*a 6 - 5*a 5 + 6*a 4 - 4*a 3 + a 2) = -1 := by
  simp only [small_1, small_2, small_3, small_4, small_5, small_6, small_7, small_8, small_9]
  decide +kernel

end A227013Small

namespace OMA.S_oeis_a227013

/-- The three-step difference cancels the cosine term and is cubic.
Its fourth finite difference therefore gives the seven-term recurrence. -/
theorem consequencesFromFloor
    (floorFormula : ∀ n : ℕ, 3 ≤ n →
      9 * a n = 9*(n : ℤ)^4 - 18*(n : ℤ)^3 + 15*(n : ℤ)^2 - 6*(n : ℤ) - 1
        - (if (n-2)%3 = 0 then 2 else -1)) :
    (∀ n : ℕ, 10 ≤ n →
      a n = 4*a (n-1) - 6*a (n-2) + 5*a (n-3) - 5*a (n-4)
        + 6*a (n-5) - 4*a (n-6) + a (n-7)) ∧
    (∀ n : ℕ, seriesCoeff n - 4*seriesCoeff ((n : ℤ)-1)
      + 6*seriesCoeff ((n : ℤ)-2) - 5*seriesCoeff ((n : ℤ)-3)
      + 5*seriesCoeff ((n : ℤ)-4) - 6*seriesCoeff ((n : ℤ)-5)
      + 4*seriesCoeff ((n : ℤ)-6) - seriesCoeff ((n : ℤ)-7) = numeratorCoeff n) := by
  have step (k : ℕ) : a (k+6) - a (k+3) =
      12*(k : ℤ)^3 + 144*(k : ℤ)^2 + 604*(k : ℤ) + 880 := by
    have high := floorFormula (k+6) (by omega)
    have low := floorFormula (k+3) (by omega)
    rw [show (k+6-2)%3 = (k+3-2)%3 by omega] at high
    push_cast at high low
    ring_nf at high low ⊢
    omega
  have recur (k : ℕ) : a (k+10) = 4*a (k+9) - 6*a (k+8) + 5*a (k+7)
      - 5*a (k+6) + 6*a (k+5) - 4*a (k+4) + a (k+3) := by
    have h₀ := step k
    have h₁ := step (k+1)
    have h₂ := step (k+2)
    have h₃ := step (k+3)
    have h₄ := step (k+4)
    push_cast at h₁ h₂ h₃ h₄
    ring_nf at h₀ h₁ h₂ h₃ h₄ ⊢
    omega
  constructor
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n=k+10 := ⟨n-10, by omega⟩
    simpa using recur k
  · have v1 : a 1 = 1 := by decide +kernel
    have v2 : a 2 = 6 := by decide +kernel
    have v3 : a 3 = 40 := by
      have h := floorFormula 3 (by decide)
      norm_num at h
      omega
    have v4 : a 4 = 152 := by
      have h := floorFormula 4 (by decide)
      norm_num at h
      omega
    have v5 : a 5 = 413 := by
      have h := floorFormula 5 (by decide)
      norm_num at h
      omega
    have v6 : a 6 = 920 := by
      have h := floorFormula 6 (by decide)
      norm_num at h
      omega
    have v7 : a 7 = 1792 := by
      have h := floorFormula 7 (by decide)
      norm_num at h
      omega
    have v8 : a 8 = 3173 := by
      have h := floorFormula 8 (by decide)
      norm_num at h
      omega
    have v9 : a 9 = 5232 := by
      have h := floorFormula 9 (by decide)
      norm_num at h
      omega
    intro n
    match n with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 =>
      all_goals norm_num [seriesCoeff, numeratorCoeff, Int.toNat, v1, v2, v3, v4, v5, v6, v7, v8, v9]
    | k+9 =>
      have idx (j : ℕ) : seriesCoeff (j : ℤ) = a (j+1) := by simp [seriesCoeff]
      have s1 : ((k+9 : ℕ) : ℤ)-1 = (↑(k+8 : ℕ) : ℤ) := by omega
      have s2 : ((k+9 : ℕ) : ℤ)-2 = (↑(k+7 : ℕ) : ℤ) := by omega
      have s3 : ((k+9 : ℕ) : ℤ)-3 = (↑(k+6 : ℕ) : ℤ) := by omega
      have s4 : ((k+9 : ℕ) : ℤ)-4 = (↑(k+5 : ℕ) : ℤ) := by omega
      have s5 : ((k+9 : ℕ) : ℤ)-5 = (↑(k+4 : ℕ) : ℤ) := by omega
      have s6 : ((k+9 : ℕ) : ℤ)-6 = (↑(k+3 : ℕ) : ℤ) := by omega
      have s7 : ((k+9 : ℕ) : ℤ)-7 = (↑(k+2 : ℕ) : ℤ) := by omega
      rw [s1, s2, s3, s4, s5, s6, s7, idx, idx, idx, idx, idx, idx, idx, idx]
      change a (k+10) - 4*a (k+9) + 6*a (k+8) - 5*a (k+7) + 5*a (k+6)
        - 6*a (k+5) + 4*a (k+4) - a (k+3) = 0
      have h := recur k
      omega

end OMA.S_oeis_a227013

namespace OMA.S_oeis_a227013

private theorem sum_of_list (f : ℕ → ℚ) (N : ℕ) :
    ((List.range N).map f).sum = ∑ i ∈ Finset.range N, f i := by
  induction N with
  | zero => simp
  | succ N ih => simp [List.range_succ, Finset.sum_range_succ, ih]

open A227013

private theorem large_floor (n : ℕ) (hn : 11 ≤ n) :
    9 * a n = 9*(n : ℤ)^4 - 18*n^3 + 15*n^2 - 6*n - 1
        - (if (n-2)%3=0 then 2 else -1) := by
  let b := (n-1)^4
  let L := n^4 - b
  let m := Polynomials.mid n
  let S := ∑ i ∈ Finset.range L, (1 : ℚ)/(m + ((i : ℚ)-Analytic.radius L))
  have hstep : n^4 = b + 4*(n-1)^3 + 6*(n-1)^2 + 4*(n-1) + 1 := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k+1 := ⟨n-1, by omega⟩
    dsimp [b]
    ring
  have hb : b ≤ n^4 := by omega
  have hL : 2 ≤ L := by dsimp [L]; omega
  have hn1 : 1 ≤ n := by omega
  have hspan : (L : ℚ) = Polynomials.span n := by
    dsimp [L, b, Polynomials.span]
    rw [Nat.cast_sub hb, Nat.cast_pow, Nat.cast_pow, Nat.cast_sub hn1, Nat.cast_one]
  have hr : Analytic.radius L = Polynomials.radius n := by
    rw [Analytic.radius, Polynomials.radius, hspan]
  have hv : Analytic.variance L = Polynomials.variance n := by
    rw [Analytic.variance, Polynomials.variance, hspan]
  have hw : Analytic.fourth L = Polynomials.fourth n := by
    rw [Analytic.fourth, Polynomials.fourth, hspan]
  have hm : Analytic.radius L < m := by
    rw [hr]
    dsimp [m, Polynomials.mid, Polynomials.radius, Polynomials.span]
    nlinarith [sq_nonneg (((n:ℚ)-1)^2)]
  have align (i : ℕ) : ((b+i+1 : ℕ) : ℚ) = m+((i : ℚ)-Analytic.radius L) := by
    rw [hr]
    dsimp [b,m,Polynomials.mid,Polynomials.radius,Polynomials.span]
    push_cast [Nat.cast_sub hn1]
    ring
  have ha : a n = ((L:ℚ)/S).floor := by
    unfold a
    change (((L:ℚ) / ((List.range L).map (fun i => (1:ℚ) / ((b+i+1 : ℕ) : ℚ))).sum)).floor = _
    rw [sum_of_list]
    simp only [align, S]
  obtain ⟨lo,hi⟩ := Analytic.bounds L hL m hm
  change _ ≤ (L : ℚ)/S at lo
  change (L : ℚ)/S ≤ _ at hi
  rw [hr, hv, hw] at lo
  rw [hv, hw] at hi
  obtain ⟨lower, upper⟩ := Polynomials.bounds n hn
  rw [ha]
  exact Floor.recover n (by omega) _ (lt_of_lt_of_le lower lo) (lt_of_le_of_lt hi upper)

end OMA.S_oeis_a227013

namespace OMA.S_oeis_a227013

theorem corrected_floor (n : ℕ) (hn : 3 ≤ n) :
    9 * a n = 9*(n : ℤ)^4 - 18*n^3 + 15*n^2 - 6*n - 1
        - (if (n-2)%3=0 then 2 else -1) := by
  by_cases h : 11 ≤ n
  · exact large_floor n h
  · exact A227013Small.small_corrected hn (by omega)

private theorem shifted (n : ℕ) (hn : 3 ≤ n) : (a n : ℚ) = proposed (n-2) := by
  have h := corrected_floor n hn
  unfold proposed
  rw [Nat.cast_sub (show 2 ≤ n by omega)]
  push_cast
  by_cases ht : (n-2)%3 = 0
  · rw [if_pos ht] at h ⊢
    have hq : 9*(a n : ℚ) = 9*(n : ℚ)^4 - 18*n^3 + 15*n^2 - 6*n - 1 - 2 := by
      exact_mod_cast h
    linarith only [hq]
  · rw [if_neg ht] at h ⊢
    have hq : 9*(a n : ℚ) = 9*(n : ℚ)^4 - 18*n^3 + 15*n^2 - 6*n - 1 - (-1) := by
      exact_mod_cast h
    linarith only [hq]

/-- The two exceptional terms, the corrected closed form, the recurrence from
its first valid index onward, and all coefficients of the generating function. -/
theorem all_formulas :
    (a 1 = 1 ∧ a 2 = 6) ∧
    (∀ n : ℕ, 3 ≤ n → (a n : ℚ) = proposed (n-2)) ∧
    (∀ n : ℕ, 10 ≤ n →
      a n = 4*a (n-1) - 6*a (n-2) + 5*a (n-3) - 5*a (n-4)
        + 6*a (n-5) - 4*a (n-6) + a (n-7)) ∧
    (∀ n : ℕ, seriesCoeff n - 4*seriesCoeff ((n : ℤ)-1)
      + 6*seriesCoeff ((n : ℤ)-2) - 5*seriesCoeff ((n : ℤ)-3)
      + 5*seriesCoeff ((n : ℤ)-4) - 6*seriesCoeff ((n : ℤ)-5)
      + 4*seriesCoeff ((n : ℤ)-6) - seriesCoeff ((n : ℤ)-7) = numeratorCoeff n) :=
  ⟨⟨A227013Small.small_1,A227013Small.small_2⟩, shifted, consequencesFromFloor corrected_floor⟩

end OMA.S_oeis_a227013
