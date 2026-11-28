-- Credit: @ptc-prover-bot
import OMAReductions.R_Erdos1221_erdos_1221_parts_ii_R1

/-!
Proof of step `H2` of @LordMike's reduction `Erdos1221.erdos_1221.parts.ii.R1` (Korsky,
arXiv:2609.07196, CC BY 4.0, Lemma 7.2 together with Halász's theorem): a short-arc `L¹`
discrepancy bound `B` valid for all large `n` and all `0 ≤ D ≤ S` forces `B ≥ c₄ √(log S)`.

* Namespace `Halasz`: Halász's `L¹` lower bound for planar discrepancy, `c_H = 1/5120`, by the complex
  Riesz product on a finite dyadic grid (`Halasz.halasz`).
* Namespace `E1221L72.Lemma72`: Lemma 7.2 — the regularity hypothesis with `4B ≤ ⌊S⌋` yields
  `P ⊆ (0,1]²` with `≥ ⌊S⌋/2` points and `∫∫|disc P| ≤ 3B`; `P_x` is the image of
  `i ↦ (fract (a i - x)/w, (i+1)/N)` over the indices in the arc `(x, x + w]`, `w = ⌊S⌋/N`, and a good
  anchor `x` is found by averaging over `x` (Tonelli, lower Lebesgue integrals).
* `E1221L72.reduce`: if `4B ≤ ⌊S⌋`, Halász on `P` gives `(c_H/3) √(log S / 4) ≤ B` (`log(S/4) ≥ log S/2`
  for `S ≥ 16`); otherwise `B > (S - 1)/4 ≥ √(log S)/8`. So `c₄ = min (c_H/6) (1/8)`, `S₀ = 16`.
-/

/-!
Halász's L¹ lower bound, part A: one-dimensional block sums, the block decomposition (BD)
and the key bound (KB). See `Halasz_blueprint.md`.
-/

namespace Halasz

open Finset

noncomputable def G (x y : ℝ) : ℝ := max (y - x) 0

noncomputable def hh (n : ℕ) : ℝ := 1 / 2 ^ (n + 1)

noncomputable def a (n i : ℕ) (x : ℝ) : ℝ := G x (((i : ℝ) + 1) * hh n) - G x ((i : ℝ) * hh n)

noncomputable def al (n i : ℕ) : ℝ := ((((i : ℝ) + 1) * hh n) ^ 2 - ((i : ℝ) * hh n) ^ 2) / 2

noncomputable def d (P : Finset (ℝ × ℝ)) (n i j : ℕ) : ℝ :=
  ∑ p ∈ P, a n i p.1 * a n j p.2 - (P.card : ℝ) * al n i * al n j

def blk (c i : ℕ) : ℕ := i / 2 ^ (c + 1)

noncomputable def rad (c i : ℕ) : ℝ := if (i / 2 ^ c) % 2 = 1 then 1 else -1

noncomputable def dl (n c : ℕ) : ℝ := 2 ^ c * hh n

noncomputable def Dl (x s δ : ℝ) : ℝ := G x (s + 2 * δ) - 2 * G x (s + δ) + G x s

noncomputable def K (P : Finset (ℝ × ℝ)) (n cx cy I J : ℕ) : ℝ :=
  ∑ p ∈ P, Dl p.1 (2 * I * dl n cx) (dl n cx) * Dl p.2 (2 * J * dl n cy) (dl n cy) -
    (P.card : ℝ) * dl n cx ^ 2 * dl n cy ^ 2

def Inv (cx cy : ℕ) (τ : ℕ → ℕ → ℂ) : Prop :=
  ∀ i i' j j', blk cx i = blk cx i' → blk cy j = blk cy j' → τ i j = τ i' j'

lemma rad_lo (c I t : ℕ) (ht : t < 2 ^ c) : rad c (I * 2 ^ (c + 1) + t) = -1 := by
  have hp : 0 < 2 ^ c := by positivity
  have e : (I * 2 ^ (c + 1) + t) / 2 ^ c = 2 * I := by
    rw [pow_succ, show I * (2 ^ c * 2) + t = t + (2 * I) * 2 ^ c by ring,
      Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt ht, zero_add]
  unfold rad
  rw [e, Nat.mul_mod_right]
  simp

lemma rad_hi (c I t : ℕ) (ht : t < 2 ^ c) : rad c (I * 2 ^ (c + 1) + (2 ^ c + t)) = 1 := by
  have hp : 0 < 2 ^ c := by positivity
  have e : (I * 2 ^ (c + 1) + (2 ^ c + t)) / 2 ^ c = 2 * I + 1 := by
    rw [pow_succ, show I * (2 ^ c * 2) + (2 ^ c + t) = t + (2 * I + 1) * 2 ^ c by ring,
      Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt ht, zero_add]
  unfold rad
  rw [e]
  simp [Nat.add_mod]

lemma T1 (F : ℝ → ℝ) (h : ℝ) (c I : ℕ) :
    ∑ t ∈ range (2 ^ (c + 1)), (F ((((I * 2 ^ (c + 1) + t : ℕ) : ℝ) + 1) * h) -
      F (((I * 2 ^ (c + 1) + t : ℕ) : ℝ) * h)) * rad c (I * 2 ^ (c + 1) + t) =
    F (((I * 2 ^ (c + 1) + 2 ^ c + 2 ^ c : ℕ) : ℝ) * h) -
      2 * F (((I * 2 ^ (c + 1) + 2 ^ c : ℕ) : ℝ) * h) + F (((I * 2 ^ (c + 1) : ℕ) : ℝ) * h) := by
  have e : range (2 ^ (c + 1)) = range (2 ^ c + 2 ^ c) := by rw [pow_succ, mul_two]
  rw [e, sum_range_add]
  have h1 : ∀ t ∈ range (2 ^ c), (F ((((I * 2 ^ (c + 1) + t : ℕ) : ℝ) + 1) * h) -
      F (((I * 2 ^ (c + 1) + t : ℕ) : ℝ) * h)) * rad c (I * 2 ^ (c + 1) + t) =
      -(F (((I * 2 ^ (c + 1) + (t + 1) : ℕ) : ℝ) * h) - F (((I * 2 ^ (c + 1) + t : ℕ) : ℝ) * h)) := by
    intro t ht
    rw [rad_lo c I t (mem_range.mp ht)]
    push_cast; ring_nf
  have h2 : ∀ t ∈ range (2 ^ c), (F ((((I * 2 ^ (c + 1) + (2 ^ c + t) : ℕ) : ℝ) + 1) * h) -
      F (((I * 2 ^ (c + 1) + (2 ^ c + t) : ℕ) : ℝ) * h)) * rad c (I * 2 ^ (c + 1) + (2 ^ c + t)) =
      (F (((I * 2 ^ (c + 1) + 2 ^ c + (t + 1) : ℕ) : ℝ) * h) -
        F (((I * 2 ^ (c + 1) + 2 ^ c + t : ℕ) : ℝ) * h)) := by
    intro t ht
    rw [rad_hi c I t (mem_range.mp ht)]
    push_cast; ring_nf
  rw [sum_congr rfl h1, sum_congr rfl h2, sum_neg_distrib,
    sum_range_sub (fun t => F (((I * 2 ^ (c + 1) + t : ℕ) : ℝ) * h)),
    sum_range_sub (fun t => F (((I * 2 ^ (c + 1) + 2 ^ c + t : ℕ) : ℝ) * h))]
  simp only [add_zero]
  ring_nf

lemma cast_blk1 (n c I : ℕ) :
    ((I * 2 ^ (c + 1) + 2 ^ c + 2 ^ c : ℕ) : ℝ) * hh n = 2 * I * dl n c + 2 * dl n c := by
  unfold dl; push_cast; ring

lemma cast_blk2 (n c I : ℕ) :
    ((I * 2 ^ (c + 1) + 2 ^ c : ℕ) : ℝ) * hh n = 2 * I * dl n c + dl n c := by
  unfold dl; push_cast; ring

lemma cast_blk3 (n c I : ℕ) :
    ((I * 2 ^ (c + 1) : ℕ) : ℝ) * hh n = 2 * I * dl n c := by
  unfold dl; push_cast; ring

lemma blockA (n c I : ℕ) (x : ℝ) :
    ∑ t ∈ range (2 ^ (c + 1)), a n (I * 2 ^ (c + 1) + t) x * rad c (I * 2 ^ (c + 1) + t) =
      Dl x (2 * I * dl n c) (dl n c) := by
  unfold a
  rw [T1 (G x) (hh n) c I, cast_blk1, cast_blk2, cast_blk3]
  unfold Dl
  ring_nf

lemma blockAl (n c I : ℕ) :
    ∑ t ∈ range (2 ^ (c + 1)), al n (I * 2 ^ (c + 1) + t) * rad c (I * 2 ^ (c + 1) + t) =
      dl n c ^ 2 := by
  have e : ∀ t ∈ range (2 ^ (c + 1)), al n (I * 2 ^ (c + 1) + t) * rad c (I * 2 ^ (c + 1) + t) =
      ((fun y : ℝ => y ^ 2 / 2) ((((I * 2 ^ (c + 1) + t : ℕ) : ℝ) + 1) * hh n) -
        (fun y : ℝ => y ^ 2 / 2) (((I * 2 ^ (c + 1) + t : ℕ) : ℝ) * hh n)) *
        rad c (I * 2 ^ (c + 1) + t) := by
    intro t _
    unfold al
    ring
  rw [sum_congr rfl e, T1 (fun y : ℝ => y ^ 2 / 2) (hh n) c I, cast_blk1, cast_blk2, cast_blk3]
  ring

lemma D1 {x s δ : ℝ} (hx : x ≤ s) (hδ : 0 ≤ δ) : Dl x s δ = 0 := by
  unfold Dl G
  rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_left (by linarith)]
  ring

lemma D2 {x s δ : ℝ} (hx : s + 2 * δ ≤ x) (hδ : 0 ≤ δ) : Dl x s δ = 0 := by
  unfold Dl G
  rw [max_eq_right (by linarith), max_eq_right (by linarith), max_eq_right (by linarith)]
  ring

lemma D3 (x s : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) : |Dl x s δ| ≤ δ := by
  rcases le_or_gt x s with h1 | h1
  · rw [D1 h1 hδ, abs_zero]; exact hδ
  rcases le_or_gt (s + 2 * δ) x with h2 | h2
  · rw [D2 h2 hδ, abs_zero]; exact hδ
  unfold Dl G
  rw [max_eq_left (by linarith : (0 : ℝ) ≤ s + 2 * δ - x), max_eq_right (by linarith : s - x ≤ 0)]
  rcases le_total (s + δ - x) 0 with h3 | h3
  · rw [max_eq_right h3, abs_le]; constructor <;> linarith
  · rw [max_eq_left h3, abs_le]; constructor <;> linarith

lemma D4 (x : ℝ) {δ : ℝ} (hδ : 0 < δ) (A : ℕ) :
    ∑ I ∈ range A, |Dl x (2 * I * δ) δ| ≤ δ := by
  set S := (range A).filter (fun I : ℕ => 2 * I * δ < x ∧ x < 2 * I * δ + 2 * δ) with hS
  have hpt : ∀ I ∈ range A, |Dl x (2 * I * δ) δ| ≤
      if (2 * I * δ < x ∧ x < 2 * I * δ + 2 * δ) then δ else 0 := by
    intro I _
    split_ifs with hc
    · exact D3 _ _ hδ.le
    · rw [not_and_or, not_lt, not_lt] at hc
      rcases hc with hc | hc
      · rw [D1 hc hδ.le, abs_zero]
      · rw [D2 hc hδ.le, abs_zero]
  refine (sum_le_sum hpt).trans ?_
  rw [← sum_filter, sum_const, ← hS, nsmul_eq_mul]
  have hc : S.card ≤ 1 := by
    rw [card_le_one]
    intro I hI J hJ
    rw [hS, mem_filter] at hI hJ
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have : (I : ℝ) + 1 ≤ J := by exact_mod_cast h
      nlinarith [hI.2.2, hJ.2.1]
    · have : (J : ℝ) + 1 ≤ I := by exact_mod_cast h
      nlinarith [hI.2.1, hJ.2.2]
  have : (S.card : ℝ) ≤ 1 := by exact_mod_cast hc
  nlinarith

lemma sum_blocks {M : Type*} [AddCommMonoid M] (A ℓ : ℕ) (F : ℕ → M) :
    ∑ i ∈ range (A * ℓ), F i = ∑ I ∈ range A, ∑ t ∈ range ℓ, F (I * ℓ + t) := by
  induction A with
  | zero => simp
  | succ A ih => rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]

lemma blk_eq (c I t : ℕ) (ht : t < 2 ^ (c + 1)) : blk c (I * 2 ^ (c + 1) + t) = I := by
  unfold blk
  have hp : 0 < 2 ^ (c + 1) := by positivity
  rw [add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt ht, zero_add]

lemma blockK (P : Finset (ℝ × ℝ)) (n cx cy I J : ℕ) :
    ∑ t ∈ range (2 ^ (cx + 1)), ∑ u ∈ range (2 ^ (cy + 1)),
      d P n (I * 2 ^ (cx + 1) + t) (J * 2 ^ (cy + 1) + u) * rad cx (I * 2 ^ (cx + 1) + t) *
        rad cy (J * 2 ^ (cy + 1) + u) = K P n cx cy I J := by
  have lhs : ∑ t ∈ range (2 ^ (cx + 1)), ∑ u ∈ range (2 ^ (cy + 1)),
      d P n (I * 2 ^ (cx + 1) + t) (J * 2 ^ (cy + 1) + u) * rad cx (I * 2 ^ (cx + 1) + t) *
        rad cy (J * 2 ^ (cy + 1) + u) =
      ∑ t ∈ range (2 ^ (cx + 1)), ∑ u ∈ range (2 ^ (cy + 1)), ∑ p ∈ P,
        (a n (I * 2 ^ (cx + 1) + t) p.1 * rad cx (I * 2 ^ (cx + 1) + t)) *
        (a n (J * 2 ^ (cy + 1) + u) p.2 * rad cy (J * 2 ^ (cy + 1) + u)) -
      (P.card : ℝ) * ∑ t ∈ range (2 ^ (cx + 1)), ∑ u ∈ range (2 ^ (cy + 1)),
        (al n (I * 2 ^ (cx + 1) + t) * rad cx (I * 2 ^ (cx + 1) + t)) *
        (al n (J * 2 ^ (cy + 1) + u) * rad cy (J * 2 ^ (cy + 1) + u)) := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun t _ => ?_
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun u _ => ?_
    unfold d
    rw [sub_mul, sub_mul, sum_mul, sum_mul]
    congr 1
    · refine sum_congr rfl fun p _ => ?_
      ring
    · ring
  have rhs : K P n cx cy I J =
      ∑ p ∈ P, ∑ t ∈ range (2 ^ (cx + 1)), ∑ u ∈ range (2 ^ (cy + 1)),
        (a n (I * 2 ^ (cx + 1) + t) p.1 * rad cx (I * 2 ^ (cx + 1) + t)) *
        (a n (J * 2 ^ (cy + 1) + u) p.2 * rad cy (J * 2 ^ (cy + 1) + u)) -
      (P.card : ℝ) * ∑ t ∈ range (2 ^ (cx + 1)), ∑ u ∈ range (2 ^ (cy + 1)),
        (al n (I * 2 ^ (cx + 1) + t) * rad cx (I * 2 ^ (cx + 1) + t)) *
        (al n (J * 2 ^ (cy + 1) + u) * rad cy (J * 2 ^ (cy + 1) + u)) := by
    unfold K
    rw [← sum_mul_sum, blockAl, blockAl]
    congr 1
    · refine sum_congr rfl fun p _ => ?_
      rw [← sum_mul_sum, blockA, blockA]
    · ring
  rw [lhs, rhs]
  congr 1
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun t _ => ?_
  rw [sum_comm]

lemma range_split (n c : ℕ) (hc : c ≤ n) :
    range (2 ^ (n + 1)) = range (2 ^ (n - c) * 2 ^ (c + 1)) := by
  rw [← pow_add, show n - c + (c + 1) = n + 1 by omega]

lemma BD (P : Finset (ℝ × ℝ)) (n cx cy : ℕ) (hcx : cx ≤ n) (hcy : cy ≤ n) (τ : ℕ → ℕ → ℂ)
    (hτ : Inv cx cy τ) :
    ∑ i ∈ range (2 ^ (n + 1)), ∑ j ∈ range (2 ^ (n + 1)),
      (d P n i j : ℂ) * τ i j * (rad cx i : ℂ) * (rad cy j : ℂ) =
    ∑ I ∈ range (2 ^ (n - cx)), ∑ J ∈ range (2 ^ (n - cy)),
      τ (I * 2 ^ (cx + 1)) (J * 2 ^ (cy + 1)) * (K P n cx cy I J : ℂ) := by
  have e1 : ∀ i ∈ range (2 ^ (n + 1)), ∑ j ∈ range (2 ^ (n + 1)),
      (d P n i j : ℂ) * τ i j * (rad cx i : ℂ) * (rad cy j : ℂ) =
      ∑ J ∈ range (2 ^ (n - cy)), ∑ u ∈ range (2 ^ (cy + 1)),
      (d P n i (J * 2 ^ (cy + 1) + u) : ℂ) * τ i (J * 2 ^ (cy + 1) + u) * (rad cx i : ℂ) *
        (rad cy (J * 2 ^ (cy + 1) + u) : ℂ) := by
    intro i _
    rw [range_split n cy hcy, sum_blocks]
  rw [sum_congr rfl e1, range_split n cx hcx, sum_blocks]
  refine sum_congr rfl fun I _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun J _ => ?_
  rw [← blockK P n cx cy I J]
  push_cast
  rw [mul_sum]
  refine sum_congr rfl fun t ht => ?_
  rw [mul_sum]
  refine sum_congr rfl fun u hu => ?_
  have hp1 : 0 < 2 ^ (cx + 1) := by positivity
  have hp2 : 0 < 2 ^ (cy + 1) := by positivity
  have : τ (I * 2 ^ (cx + 1) + t) (J * 2 ^ (cy + 1) + u) =
      τ (I * 2 ^ (cx + 1)) (J * 2 ^ (cy + 1)) := by
    apply hτ
    · rw [blk_eq _ _ _ (mem_range.mp ht), ← add_zero (I * 2 ^ (cx + 1)), blk_eq _ _ _ hp1]
    · rw [blk_eq _ _ _ (mem_range.mp hu), ← add_zero (J * 2 ^ (cy + 1)), blk_eq _ _ _ hp2]
  rw [this]
  ring

/-! ## Part B: the key bound and the main term -/

lemma idx_lt (n c I : ℕ) (hc : c ≤ n) (hI : I < 2 ^ (n - c)) : I * 2 ^ (c + 1) < 2 ^ (n + 1) := by
  have h1 : I * 2 ^ (c + 1) < 2 ^ (n - c) * 2 ^ (c + 1) :=
    Nat.mul_lt_mul_of_pos_right hI (by positivity)
  rwa [← pow_add, show n - c + (c + 1) = n + 1 by omega] at h1

lemma dl_pos (n c : ℕ) : 0 < dl n c := by unfold dl hh; positivity

lemma abs_K (P : Finset (ℝ × ℝ)) (n cx cy I J : ℕ) :
    |K P n cx cy I J| ≤ ∑ p ∈ P, |Dl p.1 (2 * I * dl n cx) (dl n cx)| *
      |Dl p.2 (2 * J * dl n cy) (dl n cy)| + (P.card : ℝ) * dl n cx ^ 2 * dl n cy ^ 2 := by
  unfold K
  refine (abs_sub _ _).trans (add_le_add ?_ (le_of_eq ?_))
  · refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    refine sum_congr rfl fun p _ => abs_mul _ _
  · rw [abs_of_nonneg (by positivity)]

lemma KB (P : Finset (ℝ × ℝ)) (n cx cy : ℕ) (hcx : cx ≤ n) (hcy : cy ≤ n) (τ : ℕ → ℕ → ℂ)
    (hτ : Inv cx cy τ) (B : ℝ)
    (hB : ∀ i < 2 ^ (n + 1), ∀ j < 2 ^ (n + 1), ‖τ i j‖ ≤ B) :
    ‖∑ i ∈ range (2 ^ (n + 1)), ∑ j ∈ range (2 ^ (n + 1)),
      (d P n i j : ℂ) * τ i j * (rad cx i : ℂ) * (rad cy j : ℂ)‖ ≤
    B * ((P.card : ℝ) * dl n cx * dl n cy +
      (2 ^ (n - cx) : ℝ) * 2 ^ (n - cy) * (P.card : ℝ) * dl n cx ^ 2 * dl n cy ^ 2) := by
  rw [BD P n cx cy hcx hcy τ hτ]
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by positivity) 0 (by positivity))
  have hx := dl_pos n cx
  have hy := dl_pos n cy
  calc ‖∑ I ∈ range (2 ^ (n - cx)), ∑ J ∈ range (2 ^ (n - cy)),
        τ (I * 2 ^ (cx + 1)) (J * 2 ^ (cy + 1)) * (K P n cx cy I J : ℂ)‖
      ≤ ∑ I ∈ range (2 ^ (n - cx)), ∑ J ∈ range (2 ^ (n - cy)),
        ‖τ (I * 2 ^ (cx + 1)) (J * 2 ^ (cy + 1)) * (K P n cx cy I J : ℂ)‖ :=
        (norm_sum_le _ _).trans (sum_le_sum fun I _ => norm_sum_le _ _)
    _ ≤ ∑ I ∈ range (2 ^ (n - cx)), ∑ J ∈ range (2 ^ (n - cy)),
        B * (∑ p ∈ P, |Dl p.1 (2 * I * dl n cx) (dl n cx)| *
          |Dl p.2 (2 * J * dl n cy) (dl n cy)| + (P.card : ℝ) * dl n cx ^ 2 * dl n cy ^ 2) := by
        refine sum_le_sum fun I hI => sum_le_sum fun J hJ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul (hB _ (idx_lt n cx I hcx (mem_range.mp hI)) _
          (idx_lt n cy J hcy (mem_range.mp hJ))) (abs_K P n cx cy I J) (abs_nonneg _) hB0
    _ = B * (∑ p ∈ P, (∑ I ∈ range (2 ^ (n - cx)), |Dl p.1 (2 * I * dl n cx) (dl n cx)|) *
          (∑ J ∈ range (2 ^ (n - cy)), |Dl p.2 (2 * J * dl n cy) (dl n cy)|) +
          (2 ^ (n - cx) : ℝ) * 2 ^ (n - cy) * (P.card : ℝ) * dl n cx ^ 2 * dl n cy ^ 2) := by
        have hpt : ∑ p ∈ P, (∑ I ∈ range (2 ^ (n - cx)), |Dl p.1 (2 * I * dl n cx) (dl n cx)|) *
            (∑ J ∈ range (2 ^ (n - cy)), |Dl p.2 (2 * J * dl n cy) (dl n cy)|) =
            ∑ I ∈ range (2 ^ (n - cx)), ∑ J ∈ range (2 ^ (n - cy)), ∑ p ∈ P,
              |Dl p.1 (2 * I * dl n cx) (dl n cx)| * |Dl p.2 (2 * J * dl n cy) (dl n cy)| := by
          simp_rw [sum_mul_sum]
          rw [sum_comm]
          refine sum_congr rfl fun I _ => ?_
          rw [sum_comm]
        rw [hpt]
        simp only [mul_add, sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ B * (∑ p ∈ P, dl n cx * dl n cy +
          (2 ^ (n - cx) : ℝ) * 2 ^ (n - cy) * (P.card : ℝ) * dl n cx ^ 2 * dl n cy ^ 2) := by
        have hpt2 : ∑ p ∈ P, (∑ I ∈ range (2 ^ (n - cx)), |Dl p.1 (2 * I * dl n cx) (dl n cx)|) *
            (∑ J ∈ range (2 ^ (n - cy)), |Dl p.2 (2 * J * dl n cy) (dl n cy)|) ≤
            ∑ p ∈ P, dl n cx * dl n cy :=
          sum_le_sum fun p _ => mul_le_mul (D4 _ hx _) (D4 _ hy _)
            (sum_nonneg fun _ _ => abs_nonneg _) hx.le
        exact mul_le_mul_of_nonneg_left (add_le_add hpt2 le_rfl) hB0
    _ = _ := by rw [sum_const, nsmul_eq_mul]; ring

lemma pow_dl (n c : ℕ) (hc : c ≤ n) : (2 : ℝ) ^ (n - c) * dl n c = 1 / 2 := by
  unfold dl hh
  rw [← mul_assoc, ← pow_add, show n - c + c = n by omega, pow_succ]
  field_simp

lemma KB' (P : Finset (ℝ × ℝ)) (n cx cy : ℕ) (hcx : cx ≤ n) (hcy : cy ≤ n) (τ : ℕ → ℕ → ℂ)
    (hτ : Inv cx cy τ) (B : ℝ)
    (hB : ∀ i < 2 ^ (n + 1), ∀ j < 2 ^ (n + 1), ‖τ i j‖ ≤ B) :
    ‖∑ i ∈ range (2 ^ (n + 1)), ∑ j ∈ range (2 ^ (n + 1)),
      (d P n i j : ℂ) * τ i j * (rad cx i : ℂ) * (rad cy j : ℂ)‖ ≤
    B * (5 / 4) * (P.card : ℝ) * dl n cx * dl n cy := by
  refine (KB P n cx cy hcx hcy τ hτ B hB).trans (le_of_eq ?_)
  have e : (2 ^ (n - cx) : ℝ) * 2 ^ (n - cy) * (P.card : ℝ) * dl n cx ^ 2 * dl n cy ^ 2 =
      ((2 : ℝ) ^ (n - cx) * dl n cx) * ((2 : ℝ) ^ (n - cy) * dl n cy) * (P.card : ℝ) *
        dl n cx * dl n cy := by ring
  rw [e, pow_dl n cx hcx, pow_dl n cy hcy]
  ring

/-- The block `(I, J)` of shape `2^{-k} × 2^{-(n-k)}` contains a point of `P` in its interior. -/
def occ (P : Finset (ℝ × ℝ)) (n k I J : ℕ) : Prop :=
  ∃ p ∈ P, 2 * I * dl n (n - k) < p.1 ∧ p.1 < 2 * I * dl n (n - k) + 2 * dl n (n - k) ∧
    2 * J * dl n k < p.2 ∧ p.2 < 2 * J * dl n k + 2 * dl n k

open Classical in
noncomputable def sig (P : Finset (ℝ × ℝ)) (n k I J : ℕ) : ℂ := if occ P n k I J then 0 else -1

noncomputable def f (P : Finset (ℝ × ℝ)) (n k i j : ℕ) : ℂ :=
  sig P n k (blk (n - k) i) (blk k j) * (rad (n - k) i : ℂ) * (rad k j : ℂ)

lemma K_unocc (P : Finset (ℝ × ℝ)) (n k I J : ℕ) (h : ¬ occ P n k I J) :
    K P n (n - k) k I J = -((P.card : ℝ) * dl n (n - k) ^ 2 * dl n k ^ 2) := by
  unfold K
  have hx := (dl_pos n (n - k)).le
  have hy := (dl_pos n k).le
  rw [sum_eq_zero, zero_sub]
  intro p hp
  unfold occ at h
  push Not at h
  have h' := h p hp
  by_cases h1 : 2 * I * dl n (n - k) < p.1
  · by_cases h2 : p.1 < 2 * I * dl n (n - k) + 2 * dl n (n - k)
    · by_cases h3 : 2 * J * dl n k < p.2
      · have h4 := h' h1 h2 h3
        rw [D2 h4 hy, mul_zero]
      · rw [D1 (not_lt.mp h3) hy, mul_zero]
    · rw [D2 (not_lt.mp h2) hx, zero_mul]
  · rw [D1 (not_lt.mp h1) hx, zero_mul]

open Classical in
lemma card_occ (P : Finset (ℝ × ℝ)) (n k : ℕ) :
    ((range (2 ^ (n - (n - k))) ×ˢ range (2 ^ (n - k))).filter
      (fun x => occ P n k x.1 x.2)).card ≤ P.card := by
  have hx := dl_pos n (n - k)
  have hy := dl_pos n k
  refine (card_le_card ?_).trans (card_image_le (s := P)
    (f := fun p => (⌊p.1 / (2 * dl n (n - k))⌋₊, ⌊p.2 / (2 * dl n k)⌋₊)))
  intro x hx'
  rw [mem_filter] at hx'
  obtain ⟨p, hp, h1, h2, h3, h4⟩ := hx'.2
  rw [mem_image]
  refine ⟨p, hp, ?_⟩
  have e1 : ⌊p.1 / (2 * dl n (n - k))⌋₊ = x.1 := by
    rw [Nat.floor_eq_iff (by
      have : 0 ≤ 2 * (x.1 : ℝ) * dl n (n - k) := by positivity
      exact div_nonneg (by linarith) (by positivity))]
    rw [le_div_iff₀ (by positivity), div_lt_iff₀ (by positivity)]
    constructor <;> nlinarith
  have e2 : ⌊p.2 / (2 * dl n k)⌋₊ = x.2 := by
    rw [Nat.floor_eq_iff (by
      have : 0 ≤ 2 * (x.2 : ℝ) * dl n k := by positivity
      exact div_nonneg (by linarith) (by positivity))]
    rw [le_div_iff₀ (by positivity), div_lt_iff₀ (by positivity)]
    constructor <;> nlinarith
  simp only [e1, e2]

lemma dl_prod (n k : ℕ) (hk : k ≤ n) :
    dl n (n - k) * dl n k = 1 / (4 * 2 ^ n) := by
  unfold dl hh
  have e : (2 : ℝ) ^ (n - k) * (1 / 2 ^ (n + 1)) * (2 ^ k * (1 / 2 ^ (n + 1))) =
      2 ^ (n - k + k) / (2 ^ (n + 1)) ^ 2 := by rw [pow_add]; ring
  rw [e, show n - k + k = n by omega, pow_succ]
  field_simp
  ring

lemma inv_f (P : Finset (ℝ × ℝ)) (n k : ℕ) :
    Inv (n - k) k (fun i j => sig P n k (blk (n - k) i) (blk k j)) := by
  intro i i' j j' h1 h2
  simp only [h1, h2]

open Classical in
lemma main_term (P : Finset (ℝ × ℝ)) (n k : ℕ) (hk : k ≤ n)
    (hN : 2 * (P.card : ℝ) ≤ 2 ^ n) :
    (P.card : ℝ) / (32 * 2 ^ n) ≤
      (∑ i ∈ range (2 ^ (n + 1)), ∑ j ∈ range (2 ^ (n + 1)), (d P n i j : ℂ) * f P n k i j).re := by
  have e0 : ∑ i ∈ range (2 ^ (n + 1)), ∑ j ∈ range (2 ^ (n + 1)), (d P n i j : ℂ) * f P n k i j =
      ∑ i ∈ range (2 ^ (n + 1)), ∑ j ∈ range (2 ^ (n + 1)), (d P n i j : ℂ) *
        (fun i j => sig P n k (blk (n - k) i) (blk k j)) i j *
        (rad (n - k) i : ℂ) * (rad k j : ℂ) := by
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    unfold f; ring
  rw [e0, BD P n (n - k) k (Nat.sub_le n k) hk _ (inv_f P n k)]
  have hb1 : ∀ I : ℕ, blk (n - k) (I * 2 ^ (n - k + 1)) = I := fun I => by
    rw [← add_zero (I * 2 ^ (n - k + 1))]; exact blk_eq _ _ _ (by positivity)
  have hb2 : ∀ J : ℕ, blk k (J * 2 ^ (k + 1)) = J := fun J => by
    rw [← add_zero (J * 2 ^ (k + 1))]; exact blk_eq _ _ _ (by positivity)
  simp only [hb1, hb2]
  set c0 : ℝ := (P.card : ℝ) * dl n (n - k) ^ 2 * dl n k ^ 2 with hc0
  have e1 : ∀ I J : ℕ, (sig P n k I J * (K P n (n - k) k I J : ℂ)).re =
      if occ P n k I J then 0 else c0 := by
    intro I J
    unfold sig
    split_ifs with h
    · simp
    · rw [K_unocc P n k I J h, ← hc0]; simp
  simp only [Complex.re_sum, e1]
  rw [← sum_product' (f := fun I J => if occ P n k I J then (0 : ℝ) else c0), sum_ite,
    sum_const_zero, zero_add, sum_const, nsmul_eq_mul]
  have hcard := card_filter_add_card_filter_not (s := range (2 ^ (n - (n - k))) ×ˢ
    range (2 ^ (n - k))) (fun x => occ P n k x.1 x.2)
  rw [card_product, card_range, card_range, ← pow_add,
    show n - (n - k) + (n - k) = n by omega] at hcard
  have hocc := card_occ P n k
  have hun : (2 : ℝ) ^ n - P.card ≤
      (((range (2 ^ (n - (n - k))) ×ˢ range (2 ^ (n - k))).filter
        (fun x => ¬ occ P n k x.1 x.2)).card : ℝ) := by
    have : (2 ^ n : ℕ) ≤ P.card + ((range (2 ^ (n - (n - k))) ×ˢ range (2 ^ (n - k))).filter
        (fun x => ¬ occ P n k x.1 x.2)).card := by omega
    have : ((2 ^ n : ℕ) : ℝ) ≤ P.card + (((range (2 ^ (n - (n - k))) ×ˢ range (2 ^ (n - k))).filter
        (fun x => ¬ occ P n k x.1 x.2)).card : ℝ) := by exact_mod_cast this
    push_cast at this
    linarith
  have hc0' : c0 = (P.card : ℝ) * (1 / (4 * 2 ^ n)) ^ 2 := by
    rw [hc0, ← dl_prod n k hk]; ring
  have hX : (0 : ℝ) < 2 ^ n := by positivity
  have hN0 : (0 : ℝ) ≤ P.card := Nat.cast_nonneg _
  calc (P.card : ℝ) / (32 * 2 ^ n) = (2 ^ n / 2) * ((P.card : ℝ) * (1 / (4 * 2 ^ n)) ^ 2) := by
        field_simp; ring
    _ ≤ (2 ^ n - P.card) * ((P.card : ℝ) * (1 / (4 * 2 ^ n)) ^ 2) := by
        gcongr; linarith
    _ ≤ _ := by rw [← hc0']; exact mul_le_mul_of_nonneg_right hun (by rw [hc0']; positivity)

/-! ## Part C: the Riesz product -/

open Classical in
noncomputable def fR (P : Finset (ℝ × ℝ)) (n k i j : ℕ) : ℝ :=
  (if occ P n k (blk (n - k) i) (blk k j) then 0 else -1) * rad (n - k) i * rad k j

lemma f_eq (P : Finset (ℝ × ℝ)) (n k i j : ℕ) : f P n k i j = (fR P n k i j : ℂ) := by
  unfold f sig fR
  split_ifs <;> push_cast <;> ring

lemma abs_rad (c i : ℕ) : |rad c i| = 1 := by
  unfold rad; split_ifs <;> simp

lemma norm_rad (c i : ℕ) : ‖(rad c i : ℂ)‖ = 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_rad]

lemma norm_sig (P : Finset (ℝ × ℝ)) (n k I J : ℕ) : ‖sig P n k I J‖ ≤ 1 := by
  unfold sig; split_ifs <;> simp

lemma abs_fR (P : Finset (ℝ × ℝ)) (n k i j : ℕ) : |fR P n k i j| ≤ 1 := by
  unfold fR
  rw [abs_mul, abs_mul, abs_rad, abs_rad]
  split_ifs <;> simp

noncomputable def R1 (P : Finset (ℝ × ℝ)) (n : ℕ) (ρ : ℝ) (k i j : ℕ) : ℂ :=
  1 + Complex.I * ((ρ : ℂ) * f P n k i j)

noncomputable def Pr (P : Finset (ℝ × ℝ)) (n : ℕ) (ρ : ℝ) (s m i j : ℕ) : ℂ :=
  ∏ k ∈ Ico s m, R1 P n ρ k i j

lemma norm_R1 (P : Finset (ℝ × ℝ)) (n : ℕ) (ρ : ℝ) (k i j : ℕ) :
    ‖R1 P n ρ k i j‖ ≤ 1 + ρ ^ 2 / 2 := by
  unfold R1
  rw [f_eq]
  have ht := abs_fR P n k i j
  set t := fR P n k i j
  have h2 : ‖(1 : ℂ) + Complex.I * ((ρ : ℂ) * (t : ℂ))‖ ^ 2 = 1 + (ρ * t) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have ht2 : t ^ 2 ≤ 1 := by
    have := sq_abs t
    nlinarith [abs_nonneg t]
  have h3 : (ρ * t) ^ 2 ≤ ρ ^ 2 := by rw [mul_pow]; nlinarith [sq_nonneg ρ]
  nlinarith [norm_nonneg ((1 : ℂ) + Complex.I * ((ρ : ℂ) * (t : ℂ))), sq_nonneg ρ]

lemma pow_bound (ρ : ℝ) (n : ℕ) (h : ρ ^ 2 * (n + 1) ≤ 1) : (1 + ρ ^ 2 / 2) ^ (n + 1) ≤ 2 := by
  have h1 : 1 + ρ ^ 2 / 2 ≤ Real.exp (ρ ^ 2 / 2) := by linarith [Real.add_one_le_exp (ρ ^ 2 / 2)]
  have h2 := pow_le_pow_left₀ (by positivity) h1 (n + 1)
  rw [← Real.exp_nat_mul] at h2
  have h3 : Real.exp (((n + 1 : ℕ) : ℝ) * (ρ ^ 2 / 2)) ≤ Real.exp (1 / 2) :=
    Real.exp_le_exp.mpr (by push_cast; nlinarith)
  have h4 : Real.exp (1 / 2) < 2 := by
    have := Real.exp_one_lt_d9
    have e : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (1 / 2)]
  linarith

lemma norm_Pr (P : Finset (ℝ × ℝ)) (n : ℕ) (ρ : ℝ) (hρ : ρ ^ 2 * (n + 1) ≤ 1) (s m i j : ℕ)
    (hm : m ≤ n + 1) : ‖Pr P n ρ s m i j‖ ≤ 2 := by
  unfold Pr
  calc ‖∏ k ∈ Ico s m, R1 P n ρ k i j‖ ≤ ∏ k ∈ Ico s m, ‖R1 P n ρ k i j‖ :=
        Finset.norm_prod_le _ _
    _ ≤ ∏ k ∈ Ico s m, (1 + ρ ^ 2 / 2) :=
        prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => norm_R1 _ _ _ _ _ _)
    _ = (1 + ρ ^ 2 / 2) ^ (m - s) := by rw [prod_const, Nat.card_Ico]
    _ ≤ (1 + ρ ^ 2 / 2) ^ (n + 1) :=
        pow_le_pow_right₀ (by nlinarith [sq_nonneg ρ]) (by omega)
    _ ≤ 2 := pow_bound ρ n hρ

lemma Tel1 (P : Finset (ℝ × ℝ)) (n : ℕ) (ρ : ℝ) (i j M : ℕ) :
    ∏ k ∈ range M, R1 P n ρ k i j =
      1 + ∑ m ∈ range M, Complex.I * ((ρ : ℂ) * f P n m i j) * ∏ k ∈ range m, R1 P n ρ k i j := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [prod_range_succ, sum_range_succ, ← add_assoc, ← ih]
    unfold R1
    ring

lemma Tel2 (P : Finset (ℝ × ℝ)) (n : ℕ) (ρ : ℝ) (i j m : ℕ) :
    ∏ k ∈ range m, R1 P n ρ k i j =
      1 + ∑ s ∈ range m, Complex.I * ((ρ : ℂ) * f P n s i j) * Pr P n ρ (s + 1) m i j := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [prod_range_succ, ih, sum_range_succ]
    have e1 : Pr P n ρ (m + 1) (m + 1) i j = 1 := by unfold Pr; simp
    have e2 : ∀ s ∈ range m, Complex.I * ((ρ : ℂ) * f P n s i j) * Pr P n ρ (s + 1) (m + 1) i j =
        Complex.I * ((ρ : ℂ) * f P n s i j) * Pr P n ρ (s + 1) m i j * R1 P n ρ m i j := by
      intro s hs
      unfold Pr
      rw [prod_Ico_succ_top (by have := mem_range.mp hs; omega)]
      ring
    rw [e1, sum_congr rfl e2, ← sum_mul]
    unfold R1
    ring

/-- The pairing of the grid array `d` with a test function. -/
noncomputable def ip (P : Finset (ℝ × ℝ)) (n : ℕ) (g : ℕ → ℕ → ℂ) : ℂ :=
  ∑ i ∈ range (2 ^ (n + 1)), ∑ j ∈ range (2 ^ (n + 1)), (d P n i j : ℂ) * g i j

lemma ip_add (P : Finset (ℝ × ℝ)) (n : ℕ) (g h : ℕ → ℕ → ℂ) :
    ip P n (fun i j => g i j + h i j) = ip P n g + ip P n h := by
  unfold ip
  rw [← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  ring

lemma ip_smul (P : Finset (ℝ × ℝ)) (n : ℕ) (c : ℂ) (g : ℕ → ℕ → ℂ) :
    ip P n (fun i j => c * g i j) = c * ip P n g := by
  unfold ip
  rw [mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun j _ => ?_
  ring

lemma ip_sum (P : Finset (ℝ × ℝ)) (n : ℕ) (S : Finset ℕ) (g : ℕ → ℕ → ℕ → ℂ) :
    ip P n (fun i j => ∑ m ∈ S, g m i j) = ∑ m ∈ S, ip P n (g m) := by
  unfold ip
  simp only [mul_sum]
  rw [Finset.sum_comm (s := S)]
  refine sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm (s := S)]

lemma ip_one_im (P : Finset (ℝ × ℝ)) (n : ℕ) : (ip P n (fun _ _ => 1)).im = 0 := by
  unfold ip
  simp [Complex.im_sum]

lemma norm_ip (P : Finset (ℝ × ℝ)) (n : ℕ) (g : ℕ → ℕ → ℂ) (B : ℝ)
    (hg : ∀ i j, ‖g i j‖ ≤ B) :
    ‖ip P n g‖ ≤ B * ∑ i ∈ range (2 ^ (n + 1)), ∑ j ∈ range (2 ^ (n + 1)), |d P n i j| := by
  unfold ip
  rw [mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)
  rw [mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun j _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
  exact mul_le_mul_of_nonneg_right (hg i j) (abs_nonneg _)

lemma blk_mono {c c' i i' : ℕ} (h : c ≤ c') (he : blk c i = blk c i') : blk c' i = blk c' i' := by
  unfold blk at *
  have e : ∀ x : ℕ, x / 2 ^ (c' + 1) = x / 2 ^ (c + 1) / 2 ^ (c' - c) := by
    intro x
    rw [Nat.div_div_eq_div_mul, ← pow_add, show c + 1 + (c' - c) = c' + 1 by omega]
  rw [e i, e i', he]

lemma rad_mono {c c' i i' : ℕ} (h : c < c') (he : blk c i = blk c i') : rad c' i = rad c' i' := by
  unfold blk at he
  unfold rad
  have e : ∀ x : ℕ, x / 2 ^ c' = x / 2 ^ (c + 1) / 2 ^ (c' - (c + 1)) := by
    intro x
    rw [Nat.div_div_eq_div_mul, ← pow_add, show c + 1 + (c' - (c + 1)) = c' by omega]
  rw [e i, e i', he]

lemma f_inv (P : Finset (ℝ × ℝ)) (n k cx cy i i' j j' : ℕ) (hx : cx < n - k) (hy : cy < k)
    (h1 : blk cx i = blk cx i') (h2 : blk cy j = blk cy j') : f P n k i j = f P n k i' j' := by
  unfold f
  rw [blk_mono hx.le h1, blk_mono hy.le h2, rad_mono hx h1, rad_mono hy h2]

/-- The coefficient function of the product term `f m · f s · Π_{s<k<m} (1 + iρ f k)`. -/
noncomputable def tau (P : Finset (ℝ × ℝ)) (n : ℕ) (ρ : ℝ) (s m i j : ℕ) : ℂ :=
  (sig P n m (blk (n - m) i) (blk m j) * (rad m j : ℂ)) *
    (sig P n s (blk (n - s) i) (blk s j) * (rad (n - s) i : ℂ)) * Pr P n ρ (s + 1) m i j

lemma tau_inv (P : Finset (ℝ × ℝ)) (n : ℕ) (ρ : ℝ) (s m : ℕ) (hsm : s < m) (hm : m ≤ n) :
    Inv (n - m) s (tau P n ρ s m) := by
  intro i i' j j' h1 h2
  unfold tau
  have hPr : Pr P n ρ (s + 1) m i j = Pr P n ρ (s + 1) m i' j' := by
    unfold Pr
    refine prod_congr rfl fun k hk => ?_
    rw [mem_Ico] at hk
    unfold R1
    rw [f_inv P n k (n - m) s i i' j j' (by omega) (by omega) h1 h2]
  rw [hPr, h1, blk_mono (show s ≤ m by omega) h2, rad_mono hsm h2,
    blk_mono (show n - m ≤ n - s by omega) h1, h2, rad_mono (show n - m < n - s by omega) h1]

lemma norm_tau (P : Finset (ℝ × ℝ)) (n : ℕ) (ρ : ℝ) (hρ : ρ ^ 2 * (n + 1) ≤ 1) (s m : ℕ)
    (hm : m ≤ n) (i j : ℕ) : ‖tau P n ρ s m i j‖ ≤ 2 := by
  unfold tau
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_rad, norm_rad, mul_one, mul_one]
  have h1 := norm_sig P n m (blk (n - m) i) (blk m j)
  have h2 := norm_sig P n s (blk (n - s) i) (blk s j)
  have h3 := norm_Pr P n ρ hρ (s + 1) m i j (by omega)
  have h4 := norm_nonneg (sig P n m (blk (n - m) i) (blk m j))
  have h5 := norm_nonneg (sig P n s (blk (n - s) i) (blk s j))
  have h6 := norm_nonneg (Pr P n ρ (s + 1) m i j)
  have h7 := mul_le_mul (mul_le_mul h1 h2 h5 zero_le_one) h3 h6 (by norm_num)
  linarith

lemma prod_term (P : Finset (ℝ × ℝ)) (n : ℕ) (ρ : ℝ) (hρ : ρ ^ 2 * (n + 1) ≤ 1) (s m : ℕ)
    (hsm : s < m) (hm : m ≤ n) :
    ‖ip P n (fun i j => f P n m i j * f P n s i j * Pr P n ρ (s + 1) m i j)‖ ≤
      2 * (5 / 4) * (P.card : ℝ) * dl n (n - m) * dl n s := by
  have e : ip P n (fun i j => f P n m i j * f P n s i j * Pr P n ρ (s + 1) m i j) =
      ∑ i ∈ range (2 ^ (n + 1)), ∑ j ∈ range (2 ^ (n + 1)),
        (d P n i j : ℂ) * tau P n ρ s m i j * (rad (n - m) i : ℂ) * (rad s j : ℂ) := by
    unfold ip
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    unfold tau f
    ring
  rw [e]
  exact KB' P n (n - m) s (Nat.sub_le n m) (by omega) _ (tau_inv P n ρ s m hsm hm) 2
    (fun i _ j _ => norm_tau P n ρ hρ s m hm i j)

lemma geom2 (m : ℕ) : ∑ s ∈ range m, (2 : ℝ) ^ s ≤ 2 ^ m := by
  have : ∀ m : ℕ, ∑ s ∈ range m, (2 : ℝ) ^ s + 1 = 2 ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [sum_range_succ, pow_succ]; linarith
  linarith [this m]

lemma sum_dl (n m : ℕ) : ∑ s ∈ range m, dl n s ≤ dl n m := by
  unfold dl
  rw [← sum_mul]
  exact mul_le_mul_of_nonneg_right (geom2 m) (by unfold hh; positivity)

lemma prod_terms_sum (P : Finset (ℝ × ℝ)) (n : ℕ) (ρ : ℝ) (hρ : ρ ^ 2 * (n + 1) ≤ 1) (m : ℕ)
    (hm : m ≤ n) :
    ∑ s ∈ range m,
      ‖ip P n (fun i j => f P n m i j * f P n s i j * Pr P n ρ (s + 1) m i j)‖ ≤
      (5 / 2) * (P.card : ℝ) / (4 * 2 ^ n) := by
  calc _ ≤ ∑ s ∈ range m, 2 * (5 / 4) * (P.card : ℝ) * dl n (n - m) * dl n s :=
        sum_le_sum fun s hs => prod_term P n ρ hρ s m (mem_range.mp hs) hm
    _ = 2 * (5 / 4) * (P.card : ℝ) * dl n (n - m) * ∑ s ∈ range m, dl n s := by rw [mul_sum]
    _ ≤ 2 * (5 / 4) * (P.card : ℝ) * dl n (n - m) * dl n m := by
        have := (dl_pos n (n - m)).le
        exact mul_le_mul_of_nonneg_left (sum_dl n m) (by positivity)
    _ = 2 * (5 / 4) * (P.card : ℝ) * (dl n (n - m) * dl n m) := by ring
    _ = (5 / 2) * (P.card : ℝ) / (4 * 2 ^ n) := by
        rw [dl_prod n m hm]; ring

/-- The expansion of the Riesz product. -/
lemma riesz_expand (P : Finset (ℝ × ℝ)) (n : ℕ) (ρ : ℝ) (i j : ℕ) :
    ∏ k ∈ range (n + 1), R1 P n ρ k i j =
      1 + ((Complex.I * (ρ : ℂ)) * ∑ m ∈ range (n + 1), f P n m i j +
        (-(ρ : ℂ) ^ 2) * ∑ m ∈ range (n + 1), ∑ s ∈ range m,
          f P n m i j * f P n s i j * Pr P n ρ (s + 1) m i j) := by
  rw [Tel1]
  congr 1
  simp_rw [Tel2]
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun m _ => ?_
  rw [mul_sum]
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have e : ∀ s ∈ range m, -(ρ : ℂ) ^ 2 * (f P n m i j * f P n s i j * Pr P n ρ (s + 1) m i j) =
      Complex.I * ((ρ : ℂ) * f P n m i j) *
        (Complex.I * ((ρ : ℂ) * f P n s i j) * Pr P n ρ (s + 1) m i j) := by
    intro s _
    linear_combination (-(ρ : ℂ) ^ 2 * f P n m i j * f P n s i j * Pr P n ρ (s + 1) m i j) * hI
  rw [sum_congr rfl e, ← mul_sum]
  ring

lemma riesz_lower (P : Finset (ℝ × ℝ)) (n : ℕ) (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ : ρ ^ 2 * (n + 1) ≤ 1) (hN : 2 * (P.card : ℝ) ≤ 2 ^ n) :
    ρ * ((n + 1) * ((P.card : ℝ) / (32 * 2 ^ n))) -
        ρ ^ 2 * ((n + 1) * ((5 / 2) * (P.card : ℝ) / (4 * 2 ^ n))) ≤
      2 * ∑ i ∈ range (2 ^ (n + 1)), ∑ j ∈ range (2 ^ (n + 1)), |d P n i j| := by
  set Z := ip P n (fun i j => ∏ k ∈ range (n + 1), R1 P n ρ k i j) with hZ
  have hZ1 : Z.im ≤ 2 * ∑ i ∈ range (2 ^ (n + 1)), ∑ j ∈ range (2 ^ (n + 1)), |d P n i j| := by
    refine (Complex.im_le_norm Z).trans (norm_ip P n _ 2 fun i j => ?_)
    have := norm_Pr P n ρ hρ 0 (n + 1) i j le_rfl
    unfold Pr at this
    rwa [← range_eq_Ico] at this
  set M := ∑ m ∈ range (n + 1), ip P n (f P n m) with hM
  set E := ∑ m ∈ range (n + 1), ∑ s ∈ range m,
    ip P n (fun i j => f P n m i j * f P n s i j * Pr P n ρ (s + 1) m i j) with hEd
  have hZ2 : Z = ip P n (fun _ _ => 1) + ((Complex.I * (ρ : ℂ)) * M + (-(ρ : ℂ) ^ 2) * E) := by
    rw [hZ]
    simp_rw [riesz_expand]
    rw [ip_add, ip_add, ip_smul, ip_smul, ip_sum]
    congr 3
    rw [ip_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [ip_sum]
  have hMre : (n + 1) * ((P.card : ℝ) / (32 * 2 ^ n)) ≤ M.re := by
    rw [hM, Complex.re_sum]
    calc (n + 1) * ((P.card : ℝ) / (32 * 2 ^ n)) =
          ∑ m ∈ range (n + 1), (P.card : ℝ) / (32 * 2 ^ n) := by
          rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
      _ ≤ _ := sum_le_sum fun m hm => main_term P n m (by have := mem_range.mp hm; omega) hN
  have hE : ‖E‖ ≤ (n + 1) * ((5 / 2) * (P.card : ℝ) / (4 * 2 ^ n)) := by
    rw [hEd]
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ m ∈ range (n + 1), (5 / 2) * (P.card : ℝ) / (4 * 2 ^ n) :=
          sum_le_sum fun m hm => (norm_sum_le _ _).trans
            (prod_terms_sum P n ρ hρ m (by have := mem_range.mp hm; omega))
      _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
  have hZim : Z.im = ρ * M.re - ρ ^ 2 * E.im := by
    rw [hZ2]
    simp [ip_one_im, Complex.add_im, Complex.mul_im]
    rw [show ((ρ : ℂ)) ^ 2 = ((ρ ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_im,
      Complex.ofReal_re]
    ring
  have hEim : E.im ≤ ‖E‖ := Complex.im_le_norm E
  have hρ2 : 0 ≤ ρ ^ 2 := sq_nonneg ρ
  nlinarith

/-! ## Part D: the discrete theorem -/

lemma norm_f (P : Finset (ℝ × ℝ)) (n k i j : ℕ) : ‖f P n k i j‖ ≤ 1 := by
  rw [f_eq, Complex.norm_real, Real.norm_eq_abs]; exact abs_fR P n k i j

theorem disc_bound (P : Finset (ℝ × ℝ)) (n : ℕ) (hN1 : 2 * (P.card : ℝ) ≤ 2 ^ n)
    (hN2 : (2 : ℝ) ^ n ≤ 4 * P.card) :
    Real.sqrt (n + 1) / 5120 ≤
      ∑ i ∈ range (2 ^ (n + 1)), ∑ j ∈ range (2 ^ (n + 1)), |d P n i j| := by
  set S := ∑ i ∈ range (2 ^ (n + 1)), ∑ j ∈ range (2 ^ (n + 1)), |d P n i j| with hS
  have hX : (0 : ℝ) < 2 ^ n := by positivity
  set Y : ℝ := (P.card : ℝ) / 2 ^ n with hY
  have hY1 : 1 / 4 ≤ Y := by rw [hY, le_div_iff₀ hX]; linarith
  have hY2 : Y ≤ 1 / 2 := by rw [hY, div_le_iff₀ hX]; linarith
  -- the single-function bound
  have h0 : Y / 32 ≤ S := by
    have hm := main_term P n 0 (Nat.zero_le n) hN1
    have hn := norm_ip P n (f P n 0) 1 (fun i j => norm_f P n 0 i j)
    have hre := Complex.re_le_norm (ip P n (f P n 0))
    have e : (P.card : ℝ) / (32 * 2 ^ n) = Y / 32 := by rw [hY]; field_simp
    unfold ip at hn hre
    rw [e] at hm
    linarith
  -- the Riesz product bound
  set q := Real.sqrt (n + 1) with hq
  have hq0 : 0 < q := Real.sqrt_pos.mpr (by positivity)
  have hqq : q ^ 2 = n + 1 := Real.sq_sqrt (by positivity)
  have hρ0 : 0 ≤ 1 / q := by positivity
  have hρ : (1 / q) ^ 2 * (n + 1) ≤ 1 := by
    rw [div_pow, hqq]; field_simp; exact le_refl _
  have hR := riesz_lower P n (1 / q) hρ0 hρ hN1
  have e1 : 1 / q * ((n + 1) * ((P.card : ℝ) / (32 * 2 ^ n))) = q * Y / 32 := by
    rw [← hqq, hY]; field_simp
  have e2 : (1 / q) ^ 2 * ((n + 1) * ((5 / 2) * (P.card : ℝ) / (4 * 2 ^ n))) = 5 / 8 * Y := by
    rw [← hqq, hY]; field_simp; ring
  rw [e1, e2] at hR
  by_cases hc : q ≤ 40
  · nlinarith
  · push Not at hc
    nlinarith

/-! ## Part E: the grid lemma (the only measure theory) and the final theorem -/

open MeasureTheory

/-- The anchored-box discrepancy `#(P ∩ (0,u] × (0,v]) - |P| u v` (as in the brief). -/
noncomputable def disc (P : Finset (ℝ × ℝ)) (u v : ℝ) : ℝ :=
  ((P.filter fun p => 0 < p.1 ∧ p.1 ≤ u ∧ 0 < p.2 ∧ p.2 ≤ v).card : ℝ) - P.card * u * v

noncomputable def ind (x v : ℝ) : ℝ := if x ≤ v then 1 else 0

lemma ind_mono (x : ℝ) : Monotone (ind x) := by
  intro a b hab
  unfold ind
  split_ifs with h1 h2 h2 <;> first | exact absurd (h1.trans hab) h2 | norm_num

lemma ind_nonneg (x v : ℝ) : 0 ≤ ind x v := by unfold ind; split_ifs <;> norm_num

lemma mono_sum (P : Finset (ℝ × ℝ)) (w sel : ℝ × ℝ → ℝ) (hw : ∀ p, 0 ≤ w p) :
    Monotone (fun v => ∑ p ∈ P, w p * ind (sel p) v) := by
  intro a b hab
  exact sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (ind_mono _ hab) (hw p)

lemma F1 (x c e : ℝ) (hce : c ≤ e) : ∫ v in c..e, ind x v = G x e - G x c := by
  unfold G
  rcases le_or_gt x c with h1 | h1
  · rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) (fun v hv => by
      rw [Set.uIcc_of_le hce] at hv
      simp [ind, h1.trans hv.1])]
    rw [max_eq_left (by linarith), max_eq_left (by linarith)]
    simp
  rcases lt_or_ge e x with h2 | h2
  · rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun v hv => by
      rw [Set.uIcc_of_le hce] at hv
      have : ¬ x ≤ v := by linarith [hv.2]
      simp [ind, this])]
    rw [max_eq_right (by linarith), max_eq_right (by linarith)]
    simp
  · rw [← intervalIntegral.integral_add_adjacent_intervals (b := x)
      ((ind_mono x).intervalIntegrable) ((ind_mono x).intervalIntegrable)]
    have hA : ∫ v in c..x, ind x v = 0 := by
      have hae : ∀ᵐ v ∂(volume : Measure ℝ), v ≠ x := by
        rw [ae_iff]; simp
      rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ)) ?_]
      · simp
      filter_upwards [hae] with v hv hvI
      rw [Set.uIoc_of_le h1.le] at hvI
      have : ¬ x ≤ v := by
        intro h; exact hv (le_antisymm hvI.2 h)
      simp [ind, this]
    have hB : ∫ v in x..e, ind x v = e - x := by
      rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) (fun v hv => by
        rw [Set.uIcc_of_le h2] at hv
        simp [ind, hv.1])]
      simp
    rw [hA, hB, max_eq_left (by linarith), max_eq_right (by linarith)]
    ring

lemma disc_eq (P : Finset (ℝ × ℝ)) (hP : ∀ p ∈ P, 0 < p.1 ∧ p.1 ≤ 1 ∧ 0 < p.2 ∧ p.2 ≤ 1)
    (u v : ℝ) : disc P u v = ∑ p ∈ P, ind p.1 u * ind p.2 v - P.card * u * v := by
  unfold disc
  rw [natCast_card_filter]
  congr 1
  refine sum_congr rfl fun p hp => ?_
  obtain ⟨h1, -, h3, -⟩ := hP p hp
  unfold ind
  by_cases hu : p.1 ≤ u <;> by_cases hv : p.2 ≤ v <;> simp [hu, hv, h1, h3]

lemma hh_pos (n : ℕ) : 0 < hh n := by unfold hh; positivity

lemma cell_le (n i : ℕ) : (i : ℝ) * hh n ≤ ((i : ℝ) + 1) * hh n := by
  have := hh_pos n; nlinarith

lemma a_nonneg (n j : ℕ) (x : ℝ) : 0 ≤ a n j x := by
  unfold a G
  have := cell_le n j
  have : max ((j : ℝ) * hh n - x) 0 ≤ max (((j : ℝ) + 1) * hh n - x) 0 :=
    max_le_max (by linarith) le_rfl
  linarith

/-- The inner cell integral `∫_{cell j} disc P u v dv`. -/
noncomputable def g (P : Finset (ℝ × ℝ)) (n j : ℕ) (u : ℝ) : ℝ :=
  ∑ p ∈ P, a n j p.2 * ind p.1 u - P.card * u * al n j

lemma int_disc_v (P : Finset (ℝ × ℝ)) (hP : ∀ p ∈ P, 0 < p.1 ∧ p.1 ≤ 1 ∧ 0 < p.2 ∧ p.2 ≤ 1)
    (u c e : ℝ) : IntervalIntegrable (fun v => disc P u v) volume c e := by
  simp_rw [disc_eq P hP u]
  have h1 : IntervalIntegrable (fun v => ∑ p ∈ P, ind p.1 u * ind p.2 v) volume c e :=
    (mono_sum P (fun p => ind p.1 u) (fun p => p.2) (fun p => ind_nonneg _ _)).intervalIntegrable
  exact h1.sub (Continuous.intervalIntegrable (by fun_prop) _ _)

lemma int_g (P : Finset (ℝ × ℝ)) (n j : ℕ) (c e : ℝ) :
    IntervalIntegrable (g P n j) volume c e := by
  unfold g
  have h1 : IntervalIntegrable (fun u => ∑ p ∈ P, a n j p.2 * ind p.1 u) volume c e :=
    (mono_sum P (fun p => a n j p.2) (fun p => p.1) (fun p => a_nonneg _ _ _)).intervalIntegrable
  exact h1.sub (Continuous.intervalIntegrable (by fun_prop) _ _)

lemma inner_eq (P : Finset (ℝ × ℝ)) (hP : ∀ p ∈ P, 0 < p.1 ∧ p.1 ≤ 1 ∧ 0 < p.2 ∧ p.2 ≤ 1)
    (n j : ℕ) (u : ℝ) :
    ∫ v in ((j : ℝ) * hh n)..(((j : ℝ) + 1) * hh n), disc P u v = g P n j u := by
  simp_rw [disc_eq P hP u]
  have hle := cell_le n j
  have hlin : ∫ v in ((j : ℝ) * hh n)..(((j : ℝ) + 1) * hh n), (P.card : ℝ) * u * v =
      (P.card : ℝ) * u * (((((j : ℝ) + 1) * hh n) ^ 2 - ((j : ℝ) * hh n) ^ 2) / 2) := by
    rw [intervalIntegral.integral_const_mul, integral_id]
  rw [intervalIntegral.integral_sub
    ((mono_sum P (fun p => ind p.1 u) (fun p => p.2) (fun p => ind_nonneg _ _)).intervalIntegrable)
    (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_finsetSum (fun p _ =>
      ((ind_mono p.2).intervalIntegrable).const_mul _)]
  rw [hlin]
  simp only [intervalIntegral.integral_const_mul, F1 _ _ _ hle]
  unfold g a al
  rw [mul_comm]
  congr 1
  exact sum_congr rfl fun p _ => by ring

lemma outer_eq (P : Finset (ℝ × ℝ)) (n i j : ℕ) :
    ∫ u in ((i : ℝ) * hh n)..(((i : ℝ) + 1) * hh n), g P n j u = d P n i j := by
  unfold g
  have hle := cell_le n i
  have hlin : ∫ x in ((i : ℝ) * hh n)..(((i : ℝ) + 1) * hh n), (P.card : ℝ) * x * al n j =
      (P.card : ℝ) * (((((i : ℝ) + 1) * hh n) ^ 2 - ((i : ℝ) * hh n) ^ 2) / 2) * al n j := by
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, integral_id]
  rw [intervalIntegral.integral_sub
    ((mono_sum P (fun p => a n j p.2) (fun p => p.1) (fun p => a_nonneg _ _ _)).intervalIntegrable)
    (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_finsetSum (fun p _ =>
      ((ind_mono p.1).intervalIntegrable).const_mul _)]
  rw [hlin]
  simp only [intervalIntegral.integral_const_mul, F1 _ _ _ hle]
  unfold d a al
  congr 1
  exact sum_congr rfl fun p _ => by ring

lemma hh_total (n : ℕ) : (2 : ℝ) ^ (n + 1) * hh n = 1 := by
  unfold hh; field_simp

lemma split1 (n : ℕ) (φ : ℝ → ℝ) (hφ : IntervalIntegrable φ volume 0 1) :
    ∑ i ∈ range (2 ^ (n + 1)), |∫ u in ((i : ℝ) * hh n)..(((i : ℝ) + 1) * hh n), φ u| ≤
      ∫ u in (0 : ℝ)..1, |φ u| := by
  have hpt : ∀ k : ℕ, k < 2 ^ (n + 1) → IntervalIntegrable (fun u => |φ u|) volume
      ((k : ℝ) * hh n) (((k : ℝ) + 1) * hh n) := by
    intro k hk
    have h0 : (0 : ℝ) ≤ (k : ℝ) * hh n := by have := hh_pos n; positivity
    have h1 : ((k : ℝ) + 1) * hh n ≤ 1 := by
      have : ((k : ℝ) + 1) ≤ 2 ^ (n + 1) := by exact_mod_cast hk
      have := hh_pos n
      nlinarith [hh_total n]
    refine hφ.abs.mono_set (Set.uIcc_subset_uIcc ?_ ?_)
    · rw [Set.uIcc_of_le zero_le_one]; exact ⟨h0, by linarith [cell_le n k]⟩
    · rw [Set.uIcc_of_le zero_le_one]; exact ⟨by linarith [cell_le n k], h1⟩
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ => (k : ℝ) * hh n) (n := 2 ^ (n + 1)) (f := fun u => |φ u|) (μ := volume)
    (fun k hk => by
      have := hpt k hk
      simpa using this)
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, Nat.cast_pow, Nat.cast_ofNat,
    hh_total] at hsum
  rw [← hsum]
  exact sum_le_sum fun i _ => intervalIntegral.abs_integral_le_integral_abs (cell_le n i)

lemma abs_disc_le (P : Finset (ℝ × ℝ)) (u v : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (hv : v ∈ Set.Icc (0 : ℝ) 1) : |disc P u v| ≤ 2 * P.card := by
  unfold disc
  have h1 : ((P.filter fun p => 0 < p.1 ∧ p.1 ≤ u ∧ 0 < p.2 ∧ p.2 ≤ v).card : ℝ) ≤ P.card := by
    exact_mod_cast card_filter_le _ _
  have h2 : (0 : ℝ) ≤ ((P.filter fun p => 0 < p.1 ∧ p.1 ≤ u ∧ 0 < p.2 ∧ p.2 ≤ v).card : ℝ) :=
    Nat.cast_nonneg _
  have hN : (0 : ℝ) ≤ P.card := Nat.cast_nonneg _
  have h3 : 0 ≤ (P.card : ℝ) * u * v := by
    have := hu.1; have := hv.1; positivity
  have h4 : (P.card : ℝ) * u * v ≤ P.card := by
    have : u * v ≤ 1 := by nlinarith [hu.1, hu.2, hv.1, hv.2]
    nlinarith
  rw [abs_le]; constructor <;> linarith

lemma meas_disc (P : Finset (ℝ × ℝ)) (hP : ∀ p ∈ P, 0 < p.1 ∧ p.1 ≤ 1 ∧ 0 < p.2 ∧ p.2 ≤ 1) :
    Measurable fun q : ℝ × ℝ => |disc P q.1 q.2| := by
  have e : (fun q : ℝ × ℝ => |disc P q.1 q.2|) =
      fun q => |∑ p ∈ P, ind p.1 q.1 * ind p.2 q.2 - P.card * q.1 * q.2| := by
    funext q; rw [disc_eq P hP]
  rw [e]
  refine Measurable.abs (Measurable.sub ?_ (by fun_prop))
  refine Finset.measurable_sum _ fun p _ => Measurable.mul ?_ ?_
  · unfold ind
    exact Measurable.ite (measurableSet_le measurable_const measurable_fst) measurable_const
      measurable_const
  · unfold ind
    exact Measurable.ite (measurableSet_le measurable_const measurable_snd) measurable_const
      measurable_const

lemma int_F (P : Finset (ℝ × ℝ)) (hP : ∀ p ∈ P, 0 < p.1 ∧ p.1 ≤ 1 ∧ 0 < p.2 ∧ p.2 ≤ 1) :
    IntervalIntegrable (fun u => ∫ v in (0 : ℝ)..1, |disc P u v|) volume 0 1 := by
  have e : (fun u => ∫ v in (0 : ℝ)..1, |disc P u v|) =
      fun u => ∫ v, (fun q : ℝ × ℝ => |disc P q.1 q.2|) (u, v) ∂(volume.restrict (Set.Ioc 0 1)) := by
    funext u; exact intervalIntegral.integral_of_le zero_le_one
  have hsm : StronglyMeasurable (fun u => ∫ v in (0 : ℝ)..1, |disc P u v|) := by
    rw [e]; exact (meas_disc P hP).stronglyMeasurable.integral_prod_right'
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine IntegrableOn.of_bound measure_Ioc_lt_top hsm.aestronglyMeasurable (2 * P.card)
    (ae_restrict_of_forall_mem measurableSet_Ioc fun u hu => ?_)
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (C := 2 * P.card) (f := fun v => |disc P u v|) (fun v hv => by
      rw [Set.uIoc_of_le zero_le_one] at hv
      rw [Real.norm_eq_abs, abs_abs]
      exact abs_disc_le P u v ⟨hu.1.le, hu.2⟩ ⟨hv.1.le, hv.2⟩)
  simpa using this

theorem grid (P : Finset (ℝ × ℝ)) (hP : ∀ p ∈ P, 0 < p.1 ∧ p.1 ≤ 1 ∧ 0 < p.2 ∧ p.2 ≤ 1) (n : ℕ) :
    ∑ i ∈ range (2 ^ (n + 1)), ∑ j ∈ range (2 ^ (n + 1)), |d P n i j| ≤
      ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, |disc P u v| := by
  have hin : ∀ u, ∑ j ∈ range (2 ^ (n + 1)), |g P n j u| ≤ ∫ v in (0 : ℝ)..1, |disc P u v| := by
    intro u
    have := split1 n (fun v => disc P u v) (int_disc_v P hP u 0 1)
    simpa only [inner_eq P hP] using this
  have hout : ∀ j, ∑ i ∈ range (2 ^ (n + 1)), |d P n i j| ≤ ∫ u in (0 : ℝ)..1, |g P n j u| := by
    intro j
    have := split1 n (g P n j) (int_g P n j 0 1)
    simpa only [outer_eq P] using this
  have hsumint : IntervalIntegrable (fun u => ∑ j ∈ range (2 ^ (n + 1)), |g P n j u|) volume 0 1 := by
    have := IntervalIntegrable.sum (range (2 ^ (n + 1))) (f := fun j u => |g P n j u|)
      (μ := volume) (a := 0) (b := 1) (fun j _ => (int_g P n j 0 1).abs)
    rw [Finset.sum_fn] at this
    exact this
  rw [sum_comm]
  calc ∑ j ∈ range (2 ^ (n + 1)), ∑ i ∈ range (2 ^ (n + 1)), |d P n i j|
      ≤ ∑ j ∈ range (2 ^ (n + 1)), ∫ u in (0 : ℝ)..1, |g P n j u| := sum_le_sum fun j _ => hout j
    _ = ∫ u in (0 : ℝ)..1, ∑ j ∈ range (2 ^ (n + 1)), |g P n j u| :=
        (intervalIntegral.integral_finsetSum fun j _ => (int_g P n j 0 1).abs).symm
    _ ≤ ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, |disc P u v| :=
        intervalIntegral.integral_mono_on zero_le_one hsumint (int_F P hP) fun u _ => hin u

/-- **Halász's theorem** (hypothesis `H1`): `c √(log |P|) ≤ ∫∫ |disc P|`, with `c = 1/5120`. -/
theorem halasz : ∃ cH : ℝ, 0 < cH ∧ ∀ P : Finset (ℝ × ℝ), 2 ≤ P.card →
    (∀ p ∈ P, 0 < p.1 ∧ p.1 ≤ 1 ∧ 0 < p.2 ∧ p.2 ≤ 1) →
    cH * Real.sqrt (Real.log P.card) ≤ ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, |disc P u v| := by
  refine ⟨1 / 5120, by norm_num, fun P hP2 hP => ?_⟩
  set N := P.card with hNd
  have hN0 : N ≠ 0 := by omega
  set l := Nat.log 2 N with hl
  have h1 : 2 ^ l ≤ N := Nat.pow_log_le_self 2 hN0
  have h2 : N < 2 ^ (l + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  set n := l + 2 with hn
  have hA : 2 * (N : ℝ) ≤ 2 ^ n := by
    have : 2 * N ≤ 2 ^ n := by rw [hn, pow_succ]; omega
    exact_mod_cast this
  have hB : (2 : ℝ) ^ n ≤ 4 * N := by
    have : 2 ^ n ≤ 4 * N := by rw [hn, pow_add]; omega
    exact_mod_cast this
  have hD := disc_bound P n hA hB
  have hG := grid P hP n
  have hlog : Real.log N ≤ n + 1 := by
    have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
    have hle : (N : ℝ) ≤ 2 ^ n := by linarith
    have h3 : Real.log N ≤ Real.log ((2 : ℝ) ^ n) := Real.log_le_log hNpos hle
    rw [Real.log_pow] at h3
    have h4 := Real.log_two_lt_d9
    have h5 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith
  have hsq : Real.sqrt (Real.log N) ≤ Real.sqrt (n + 1) := Real.sqrt_le_sqrt hlog
  linarith

end Halasz

namespace E1221L72

open Filter MeasureTheory Set
open scoped ENNReal

/-- Number of the first `n` points in the arc `(x, x + len]` of the circle `ℝ/ℤ`. -/
noncomputable def cnt (a : ℕ → ℝ) (n : ℕ) (x len : ℝ) : ℕ :=
  ((Finset.range n).filter fun j => 0 < Int.fract (a j - x) ∧ Int.fract (a j - x) ≤ len).card

/-- The anchored-box discrepancy `#(P ∩ (0,u] × (0,v]) - |P| u v`. -/
noncomputable def disc (P : Finset (ℝ × ℝ)) (u v : ℝ) : ℝ :=
  ((P.filter fun p => 0 < p.1 ∧ p.1 ≤ u ∧ 0 < p.2 ∧ p.2 ≤ v).card : ℝ) - P.card * u * v

/-- Halász's `L¹` lower bound for planar discrepancy (the paper's Theorem 7.1). -/
def H1 : Prop :=
  ∃ cH : ℝ, 0 < cH ∧ ∀ P : Finset (ℝ × ℝ), 2 ≤ P.card →
    (∀ p ∈ P, 0 < p.1 ∧ p.1 ≤ 1 ∧ 0 < p.2 ∧ p.2 ≤ 1) →
    cH * Real.sqrt (Real.log P.card) ≤ ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, |disc P u v|

/-- The statement of Lemma 7.2 (proved below). -/
def L72 : Prop :=
  ∀ a : ℕ → ℝ, Function.Injective (fun k ↦ Int.fract (a k)) → ∀ B S : ℝ, 1 ≤ B → 8 ≤ S →
    4 * B ≤ ⌊S⌋₊ →
    (∀ᶠ n : ℕ in atTop, ∀ D : ℝ, 0 ≤ D → D ≤ S →
      ∫ x in (0 : ℝ)..1, |(cnt a n x (D / n) : ℝ) - D| ≤ B) →
    ∃ P : Finset (ℝ × ℝ), (∀ p ∈ P, 0 < p.1 ∧ p.1 ≤ 1 ∧ 0 < p.2 ∧ p.2 ≤ 1) ∧
      (⌊S⌋₊ : ℝ) / 2 ≤ P.card ∧
      ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, |disc P u v| ≤ 3 * B

namespace Lemma72
open scoped ENNReal

lemma meas_card {X : Type*} [MeasurableSpace X] (N : ℕ) (P : ℕ → X → Prop)
    [∀ i x, Decidable (P i x)] (hP : ∀ i, MeasurableSet {x | P i x}) :
    Measurable fun x => ((((Finset.range N).filter fun i => P i x).card : ℕ) : ℝ) := by
  simp_rw [Finset.card_filter]
  push_cast
  exact Finset.measurable_sum _ fun i _ => Measurable.ite (hP i) measurable_const measurable_const

lemma meas_fract (c : ℝ) {X : Type*} [MeasurableSpace X] {f : X → ℝ} (hf : Measurable f) :
    Measurable fun x => Int.fract (c - f x) :=
  measurable_fract.comp (measurable_const.sub hf)

lemma meas_cnt (a : ℕ → ℝ) (n : ℕ) (len : ℝ) : Measurable fun x => (cnt a n x len : ℝ) := by
  unfold cnt
  exact meas_card n (fun i x => 0 < Int.fract (a i - x) ∧ Int.fract (a i - x) ≤ len) fun i =>
    (measurableSet_lt measurable_const (meas_fract _ measurable_id)).inter
      (measurableSet_le (meas_fract _ measurable_id) measurable_const)

lemma cnt_le (a : ℕ → ℝ) (n : ℕ) (x len : ℝ) : (cnt a n x len : ℝ) ≤ n := by
  unfold cnt
  exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_range n).le

lemma vol1 : volume (Ioc (0 : ℝ) 1) = 1 := by simp [Real.volume_Ioc]

lemma hyp_lint (a : ℕ → ℝ) (n : ℕ) (len D B : ℝ)
    (h : ∫ x in (0 : ℝ)..1, |(cnt a n x len : ℝ) - D| ≤ B) :
    ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal |(cnt a n x len : ℝ) - D| ≤ ENNReal.ofReal B := by
  rw [intervalIntegral.integral_of_le zero_le_one] at h
  have hi : IntegrableOn (fun x => |(cnt a n x len : ℝ) - D|) (Ioc (0 : ℝ) 1) := by
    refine IntegrableOn.of_bound measure_Ioc_lt_top
      ((meas_cnt a n len).sub measurable_const).abs.aestronglyMeasurable (n + |D|)
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_abs]
    have h0 : (0 : ℝ) ≤ cnt a n x len := Nat.cast_nonneg _
    have h1 := cnt_le a n x len
    have h2 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    rw [abs_le]
    constructor <;> linarith [neg_abs_le D, neg_le_abs D, le_abs_self D]
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal h

lemma int_le_lint (f : ℝ → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∫ x in (0 : ℝ)..1, f x ≤ (∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (f x)).toReal := by
  rw [intervalIntegral.integral_of_le zero_le_one]
  by_cases hi : Integrable f (volume.restrict (Ioc (0 : ℝ) 1))
  · rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf) hi.aestronglyMeasurable]
  · rw [integral_undef hi]; exact ENNReal.toReal_nonneg

/-- The count `G_x(u,v)`. -/
noncomputable def ct (a : ℕ → ℝ) (N : ℕ) (w x u v : ℝ) : ℕ :=
  ((Finset.range N).filter fun i =>
    0 < Int.fract (a i - x) ∧ Int.fract (a i - x) ≤ u * w ∧ (i : ℝ) + 1 ≤ N * v).card

/-- The point set `P_x`. -/
noncomputable def PP (a : ℕ → ℝ) (N : ℕ) (w x : ℝ) : Finset (ℝ × ℝ) :=
  ((Finset.range N).filter fun i => 0 < Int.fract (a i - x) ∧ Int.fract (a i - x) ≤ w).image
    fun i => (Int.fract (a i - x) / w, ((i : ℝ) + 1) / N)

lemma PP_inj (a : ℕ → ℝ) (N : ℕ) (w x : ℝ) (hN : 0 < N) :
    Function.Injective fun i : ℕ => (Int.fract (a i - x) / w, ((i : ℝ) + 1) / N) := by
  intro i j h
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have h2 : ((i : ℝ) + 1) / N = ((j : ℝ) + 1) / N := congrArg Prod.snd h
  rw [div_left_inj' hN'] at h2
  exact_mod_cast (by linarith : (i : ℝ) = j)

lemma PP_card (a : ℕ → ℝ) (N : ℕ) (w x : ℝ) (hN : 0 < N) :
    (PP a N w x).card = cnt a N x w := by
  unfold PP cnt
  rw [Finset.card_image_of_injective _ (PP_inj a N w x hN)]

lemma PP_mem (a : ℕ → ℝ) (N : ℕ) (w x : ℝ) (hN : 0 < N) (hw : 0 < w) :
    ∀ p ∈ PP a N w x, 0 < p.1 ∧ p.1 ≤ 1 ∧ 0 < p.2 ∧ p.2 ≤ 1 := by
  intro p hp
  unfold PP at hp
  rw [Finset.mem_image] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  rw [Finset.mem_filter, Finset.mem_range] at hi
  obtain ⟨hiN, h1, h2⟩ := hi
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hiN' : (i : ℝ) + 1 ≤ N := by exact_mod_cast hiN
  refine ⟨div_pos h1 hw, (div_le_one hw).mpr h2, by positivity, (div_le_one hNr).mpr hiN'⟩

lemma disc_card (a : ℕ → ℝ) (N : ℕ) (w x u v : ℝ) (hN : 0 < N) (hw : 0 < w) (hu1 : u ≤ 1) :
    ((PP a N w x).filter fun p => 0 < p.1 ∧ p.1 ≤ u ∧ 0 < p.2 ∧ p.2 ≤ v).card =
      ct a N w x u v := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  unfold PP ct
  rw [Finset.filter_image, Finset.card_image_of_injective _ (PP_inj a N w x hN),
    Finset.filter_filter]
  congr 1
  refine Finset.filter_congr fun i _ => ?_
  simp only
  rw [div_le_iff₀ hw, div_le_iff₀ hNr]
  constructor
  · rintro ⟨⟨h1, -⟩, -, h3, -, h4⟩
    exact ⟨h1, h3, by linarith⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, by nlinarith⟩, div_pos h1 hw, h2, by positivity, by linarith⟩

lemma disc_eq (a : ℕ → ℝ) (N : ℕ) (w x u v : ℝ) (hN : 0 < N) (hw : 0 < w) (hu1 : u ≤ 1) :
    disc (PP a N w x) u v = (ct a N w x u v : ℝ) - cnt a N x w * u * v := by
  unfold disc
  rw [disc_card a N w x u v hN hw hu1, PP_card a N w x hN]

lemma ct_eq_cnt (a : ℕ → ℝ) (N : ℕ) (w x u v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    ct a N w x u v = cnt a ⌊(N : ℝ) * v⌋₊ x (u * w) := by
  unfold ct cnt
  have hfl : ⌊(N : ℝ) * v⌋₊ ≤ N := Nat.floor_le_of_le (by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    nlinarith)
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  have key : (i : ℝ) + 1 ≤ N * v ↔ i < ⌊(N : ℝ) * v⌋₊ := by
    rw [Nat.lt_iff_add_one_le, Nat.le_floor_iff (by positivity)]
    push_cast
    rfl
  constructor
  · rintro ⟨-, h1, h2, h3⟩
    exact ⟨key.mp h3, h1, h2⟩
  · rintro ⟨hin, h1, h2⟩
    exact ⟨by omega, h1, h2, key.mpr hin⟩

lemma meas_ct (a : ℕ → ℝ) (N : ℕ) (w : ℝ) :
    Measurable fun p : (ℝ × ℝ) × ℝ => (ct a N w p.1.1 p.1.2 p.2 : ℝ) := by
  have hS : ∀ i : ℕ, MeasurableSet {p : (ℝ × ℝ) × ℝ | 0 < Int.fract (a i - p.1.1) ∧
      Int.fract (a i - p.1.1) ≤ p.1.2 * w ∧ (i : ℝ) + 1 ≤ N * p.2} := by
    intro i
    have hf : Measurable fun p : (ℝ × ℝ) × ℝ => Int.fract (a i - p.1.1) :=
      meas_fract _ measurable_fst.fst
    have hg : Measurable fun p : (ℝ × ℝ) × ℝ => p.1.2 * w := measurable_fst.snd.mul_const w
    have hh : Measurable fun p : (ℝ × ℝ) × ℝ => (N : ℝ) * p.2 := measurable_snd.const_mul _
    exact (measurableSet_lt measurable_const hf).inter
      ((measurableSet_le hf hg).inter (measurableSet_le measurable_const hh))
  exact meas_card (X := (ℝ × ℝ) × ℝ) N (fun i p => 0 < Int.fract (a i - p.1.1) ∧
    Int.fract (a i - p.1.1) ≤ p.1.2 * w ∧ (i : ℝ) + 1 ≤ N * p.2) hS

lemma swap3 (k : (ℝ × ℝ) × ℝ → ℝ≥0∞) (hk : Measurable k) (μ : Measure ℝ) [SFinite μ] :
    ∫⁻ x, ∫⁻ u, ∫⁻ v, k ((x, u), v) ∂μ ∂μ ∂μ = ∫⁻ u, ∫⁻ v, ∫⁻ x, k ((x, u), v) ∂μ ∂μ ∂μ := by
  rw [lintegral_lintegral_swap (f := fun x u => ∫⁻ v, k ((x, u), v) ∂μ)
    (hk.lintegral_prod_right').aemeasurable]
  refine lintegral_congr fun u => ?_
  exact lintegral_lintegral_swap (f := fun x v => k ((x, u), v))
    ((hk.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)).aemeasurable)

lemma inner_bound (a : ℕ → ℝ) (N L n0 : ℕ) (B S : ℝ) (hN : 0 < N) (hn0 : 1 ≤ n0) (hB : 0 ≤ B)
    (hLS : (L : ℝ) ≤ S)
    (hreg : ∀ n ≥ n0, ∀ D : ℝ, 0 ≤ D → D ≤ S →
      ∫ x in (0 : ℝ)..1, |(cnt a n x (D / n) : ℝ) - D| ≤ B)
    (u v : ℝ) (hu : u ∈ Ioc (0 : ℝ) 1) (hv : v ∈ Ioc (0 : ℝ) 1) :
    ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal |(ct a N ((L : ℝ) / N) x u v : ℝ) - L * u * v| ≤
      ENNReal.ofReal (B + L / N) +
        (Iio ((n0 : ℝ) / N)).indicator (fun _ => ENNReal.ofReal (n0 + L)) v := by
  obtain ⟨hu0, hu1⟩ := hu
  obtain ⟨hv0, hv1⟩ := hv
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set w : ℝ := L / N with hw
  have hwN : w * N = L := by rw [hw]; field_simp
  have hw0 : 0 ≤ w := by positivity
  set n := ⌊(N : ℝ) * v⌋₊ with hn
  have hnv : (n : ℝ) ≤ N * v := Nat.floor_le (by positivity)
  have hnv' : (N : ℝ) * v < n + 1 := Nat.lt_floor_add_one _
  have hct : ∀ x, ct a N w x u v = cnt a n x (u * w) := fun x =>
    ct_eq_cnt a N w x u v hv0.le hv1
  by_cases hnn : n0 ≤ n
  · have hnpos : (0 : ℝ) < n := by
      have : 1 ≤ n := hn0.trans hnn
      exact_mod_cast this
    have hD := hreg n hnn (n * u * w) (by positivity) (by
      have h1 : (n : ℝ) ≤ N := by nlinarith
      have h2 : (n : ℝ) * u ≤ N := by nlinarith
      have h3 : (n : ℝ) * u * w ≤ N * w := mul_le_mul_of_nonneg_right h2 hw0
      linarith)
    have hDn : (n : ℝ) * u * w / n = u * w := by field_simp
    rw [hDn] at hD
    have hL := hyp_lint a n (u * w) _ B hD
    calc ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal |(ct a N w x u v : ℝ) - L * u * v|
        ≤ ∫⁻ x in Ioc (0 : ℝ) 1, (ENNReal.ofReal |(cnt a n x (u * w) : ℝ) - n * u * w| +
            ENNReal.ofReal w) := by
          refine lintegral_mono fun x => ?_
          rw [hct x, ← ENNReal.ofReal_add (abs_nonneg _) hw0]
          refine ENNReal.ofReal_le_ofReal ?_
          have e : (cnt a n x (u * w) : ℝ) - L * u * v =
              ((cnt a n x (u * w) : ℝ) - n * u * w) + u * w * (n - N * v) := by
            rw [← hwN]; ring
          rw [e]
          refine (abs_add_le _ _).trans (add_le_add_right ?_ _)
          have h1 : 0 ≤ u * w := by positivity
          rw [abs_le]
          constructor
          · nlinarith [mul_le_mul_of_nonneg_left (le_of_lt (by linarith : (N : ℝ) * v - n < 1)) h1,
              mul_le_mul_of_nonneg_right hu1 hw0]
          · nlinarith [mul_nonneg h1 (by linarith : (0 : ℝ) ≤ N * v - n)]
      _ = (∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal |(cnt a n x (u * w) : ℝ) - n * u * w|) +
            ENNReal.ofReal w := by
          rw [lintegral_add_right _ measurable_const, setLIntegral_const, vol1, mul_one]
      _ ≤ ENNReal.ofReal B + ENNReal.ofReal w := add_le_add hL le_rfl
      _ = ENNReal.ofReal (B + w) := (ENNReal.ofReal_add hB hw0).symm
      _ ≤ _ := le_self_add
  · push Not at hnn
    have hvn : v ∈ Iio ((n0 : ℝ) / N) := by
      rw [mem_Iio, lt_div_iff₀ hNr]
      have : (n : ℝ) + 1 ≤ n0 := by exact_mod_cast hnn
      linarith
    rw [indicator_of_mem hvn]
    refine le_trans ?_ le_add_self
    calc ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal |(ct a N w x u v : ℝ) - L * u * v|
        ≤ ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (n0 + L) := by
          refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
          rw [hct x]
          have h0 : (0 : ℝ) ≤ cnt a n x (u * w) := Nat.cast_nonneg _
          have h1 := cnt_le a n x (u * w)
          have h2 : (n : ℝ) ≤ n0 := by exact_mod_cast hnn.le
          have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
          have h3 : 0 ≤ (L : ℝ) * u * v := by positivity
          have h4 : (L : ℝ) * u * v ≤ L := by
            have : u * v ≤ 1 := by nlinarith
            nlinarith
          rw [abs_le]
          constructor <;> linarith
      _ = ENNReal.ofReal (n0 + L) := by rw [setLIntegral_const, vol1, mul_one]

lemma outer_bound (a : ℕ → ℝ) (N L n0 : ℕ) (B S : ℝ) (hN : 0 < N) (hn0 : 1 ≤ n0) (hB : 0 ≤ B)
    (hLS : (L : ℝ) ≤ S)
    (hreg : ∀ n ≥ n0, ∀ D : ℝ, 0 ≤ D → D ≤ S →
      ∫ x in (0 : ℝ)..1, |(cnt a n x (D / n) : ℝ) - D| ≤ B) :
    ∫⁻ u in Ioc (0 : ℝ) 1, ∫⁻ v in Ioc (0 : ℝ) 1, ∫⁻ x in Ioc (0 : ℝ) 1,
        ENNReal.ofReal |(ct a N ((L : ℝ) / N) x u v : ℝ) - L * u * v| ≤
      ENNReal.ofReal (B + L / N) + ENNReal.ofReal (n0 + L) * ENNReal.ofReal (n0 / N) := by
  have hc : ∀ u : ℝ, ∫⁻ v in Ioc (0 : ℝ) 1, (ENNReal.ofReal (B + L / N) +
      (Iio ((n0 : ℝ) / N)).indicator (fun _ => ENNReal.ofReal (n0 + L)) v) =
      ENNReal.ofReal (B + L / N) +
        ENNReal.ofReal (n0 + L) * volume.restrict (Ioc (0 : ℝ) 1) (Iio ((n0 : ℝ) / N)) := by
    intro u
    rw [lintegral_add_left measurable_const, setLIntegral_const, vol1, mul_one,
      lintegral_indicator_const measurableSet_Iio]
  have hm : volume.restrict (Ioc (0 : ℝ) 1) (Iio ((n0 : ℝ) / N)) ≤ ENNReal.ofReal (n0 / N) := by
    rw [Measure.restrict_apply measurableSet_Iio]
    calc volume (Iio ((n0 : ℝ) / N) ∩ Ioc 0 1) ≤ volume (Ioc (0 : ℝ) (n0 / N)) :=
          measure_mono fun y hy => ⟨hy.2.1, le_of_lt hy.1⟩
      _ = ENNReal.ofReal (n0 / N) := by rw [Real.volume_Ioc, sub_zero]
  calc ∫⁻ u in Ioc (0 : ℝ) 1, ∫⁻ v in Ioc (0 : ℝ) 1, ∫⁻ x in Ioc (0 : ℝ) 1,
        ENNReal.ofReal |(ct a N ((L : ℝ) / N) x u v : ℝ) - L * u * v|
      ≤ ∫⁻ u in Ioc (0 : ℝ) 1, ∫⁻ v in Ioc (0 : ℝ) 1, (ENNReal.ofReal (B + L / N) +
          (Iio ((n0 : ℝ) / N)).indicator (fun _ => ENNReal.ofReal (n0 + L)) v) :=
        setLIntegral_mono' measurableSet_Ioc fun u hu => setLIntegral_mono' measurableSet_Ioc
          fun v hv => inner_bound a N L n0 B S hN hn0 hB hLS hreg u v hu hv
    _ = ENNReal.ofReal (B + L / N) +
          ENNReal.ofReal (n0 + L) * volume.restrict (Ioc (0 : ℝ) 1) (Iio ((n0 : ℝ) / N)) := by
        rw [lintegral_congr fun u => hc u, setLIntegral_const, vol1, mul_one]
    _ ≤ _ := by gcongr

theorem solution : L72 := by
  intro a ha B S hB hS hBL hev
  obtain ⟨n1, hn1⟩ := eventually_atTop.mp hev
  set n0 := n1 + 1 with hn0d
  have hn0 : 1 ≤ n0 := by omega
  have hreg : ∀ n ≥ n0, ∀ D : ℝ, 0 ≤ D → D ≤ S →
      ∫ x in (0 : ℝ)..1, |(cnt a n x (D / n) : ℝ) - D| ≤ B := fun n hn => hn1 n (by omega)
  set L := ⌊S⌋₊ with hLd
  have hLS : (L : ℝ) ≤ S := Nat.floor_le (by linarith)
  have hB0 : 0 ≤ B := by linarith
  set K := L + (n0 + L) * n0 with hKd
  set N := n0 + 4 * K + 1 with hNd
  have hN : 0 < N := by omega
  have hNn0 : n0 ≤ N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hLpos : (0 : ℝ) < L := by linarith
  set w : ℝ := L / N with hw
  have hw0 : 0 < w := by positivity
  have hsmall : (L : ℝ) / N + (n0 + L) * (n0 / N) < 1 / 2 := by
    have h4 : (4 * K : ℝ) < N := by exact_mod_cast (by omega : 4 * K < N)
    have hK : (K : ℝ) = L + (n0 + L) * n0 := by rw [hKd]; push_cast; ring
    have e : (L : ℝ) / N + (n0 + L) * (n0 / N) = K / N := by rw [hK]; field_simp
    rw [e, div_lt_iff₀ hNr]
    linarith
  -- the regularity at `n = N`, `D = L`
  have hM : ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal |(cnt a N x w : ℝ) - L| ≤ ENNReal.ofReal B :=
    hyp_lint a N w L B (hreg N hNn0 L (Nat.cast_nonneg _) hLS)
  have hMmeas : Measurable fun x => ENNReal.ofReal (3 / 2 * |(cnt a N x w : ℝ) - L|) :=
    ENNReal.measurable_ofReal.comp
      ((((meas_cnt a N w).sub measurable_const).abs).const_mul _)
  have hk : Measurable fun p : (ℝ × ℝ) × ℝ =>
      ENNReal.ofReal |(ct a N w p.1.1 p.1.2 p.2 : ℝ) - L * p.1.2 * p.2| :=
    ENNReal.measurable_ofReal.comp
      (((meas_ct a N w).sub ((measurable_const.mul measurable_fst.snd).mul measurable_snd)).abs)
  have hswap : (∫⁻ x in Ioc (0 : ℝ) 1, ∫⁻ u in Ioc (0 : ℝ) 1, ∫⁻ v in Ioc (0 : ℝ) 1,
      ENNReal.ofReal |(ct a N w x u v : ℝ) - L * u * v|) =
      ∫⁻ u in Ioc (0 : ℝ) 1, ∫⁻ v in Ioc (0 : ℝ) 1, ∫⁻ x in Ioc (0 : ℝ) 1,
      ENNReal.ofReal |(ct a N w x u v : ℝ) - L * u * v| := swap3 _ hk _
  have hH : (∫⁻ x in Ioc (0 : ℝ) 1, ∫⁻ u in Ioc (0 : ℝ) 1, ∫⁻ v in Ioc (0 : ℝ) 1,
      ENNReal.ofReal |(ct a N w x u v : ℝ) - L * u * v|) ≤
      ENNReal.ofReal (B + L / N) + ENNReal.ofReal (n0 + L) * ENNReal.ofReal (n0 / N) := by
    rw [hswap]; exact outer_bound a N L n0 B S hN hn0 hB0 hLS hreg
  have htotal : ∫⁻ x in Ioc (0 : ℝ) 1, ((∫⁻ u in Ioc (0 : ℝ) 1, ∫⁻ v in Ioc (0 : ℝ) 1,
      ENNReal.ofReal |(ct a N w x u v : ℝ) - L * u * v|) +
      ENNReal.ofReal (3 / 2 * |(cnt a N x w : ℝ) - L|)) < ENNReal.ofReal (3 * B) := by
    rw [lintegral_add_right _ hMmeas]
    have e2 : ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (3 / 2 * |(cnt a N x w : ℝ) - L|) =
        ENNReal.ofReal (3 / 2) *
          ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal |(cnt a N x w : ℝ) - L| := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact lintegral_congr fun x => ENNReal.ofReal_mul (by norm_num)
    rw [e2]
    calc _ ≤ ENNReal.ofReal (B + L / N) + ENNReal.ofReal (n0 + L) * ENNReal.ofReal (n0 / N) +
          ENNReal.ofReal (3 / 2) * ENNReal.ofReal B := add_le_add hH (by gcongr)
      _ = ENNReal.ofReal (B + L / N + (n0 + L) * (n0 / N) + 3 / 2 * B) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
      _ < ENNReal.ofReal (3 * B) := by
          rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
          linarith
  obtain ⟨x, hx⟩ : ∃ x : ℝ, (∫⁻ u in Ioc (0 : ℝ) 1, ∫⁻ v in Ioc (0 : ℝ) 1,
      ENNReal.ofReal |(ct a N w x u v : ℝ) - L * u * v|) +
      ENNReal.ofReal (3 / 2 * |(cnt a N x w : ℝ) - L|) < ENNReal.ofReal (3 * B) := by
    by_contra hcon
    push Not at hcon
    have : ENNReal.ofReal (3 * B) ≤ ∫⁻ x in Ioc (0 : ℝ) 1, ((∫⁻ u in Ioc (0 : ℝ) 1,
        ∫⁻ v in Ioc (0 : ℝ) 1, ENNReal.ofReal |(ct a N w x u v : ℝ) - L * u * v|) +
        ENNReal.ofReal (3 / 2 * |(cnt a N x w : ℝ) - L|)) := by
      calc ENNReal.ofReal (3 * B) = ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (3 * B) := by
            rw [setLIntegral_const, vol1, mul_one]
        _ ≤ _ := lintegral_mono hcon
    exact absurd (this.trans_lt htotal) (lt_irrefl _)
  -- the chosen anchor `x`
  have h1 : ENNReal.ofReal (3 / 2 * |(cnt a N x w : ℝ) - L|) < ENNReal.ofReal (3 * B) :=
    lt_of_le_of_lt le_add_self hx
  rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)] at h1
  have hF : ∫⁻ u in Ioc (0 : ℝ) 1, ∫⁻ v in Ioc (0 : ℝ) 1,
      ENNReal.ofReal |disc (PP a N w x) u v| ≤
      (∫⁻ u in Ioc (0 : ℝ) 1, ∫⁻ v in Ioc (0 : ℝ) 1,
        ENNReal.ofReal |(ct a N w x u v : ℝ) - L * u * v|) +
        ENNReal.ofReal |(cnt a N x w : ℝ) - L| := by
    calc _ ≤ ∫⁻ u in Ioc (0 : ℝ) 1, ∫⁻ v in Ioc (0 : ℝ) 1,
          (ENNReal.ofReal |(ct a N w x u v : ℝ) - L * u * v| +
            ENNReal.ofReal |(cnt a N x w : ℝ) - L|) := by
          refine setLIntegral_mono' measurableSet_Ioc fun u hu => setLIntegral_mono'
            measurableSet_Ioc fun v hv => ?_
          rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _),
            disc_eq a N w x u v hN hw0 hu.2]
          refine ENNReal.ofReal_le_ofReal ?_
          have e : (ct a N w x u v : ℝ) - cnt a N x w * u * v =
              ((ct a N w x u v : ℝ) - L * u * v) + (L - cnt a N x w) * (u * v) := by ring
          rw [e]
          refine (abs_add_le _ _).trans (add_le_add_right ?_ _)
          rw [abs_mul, abs_sub_comm]
          have huv0 : 0 ≤ u * v := mul_nonneg hu.1.le hv.1.le
          have huv : |u * v| ≤ 1 := by
            rw [abs_of_nonneg huv0]; nlinarith [hu.1, hu.2, hv.1, hv.2]
          calc |(cnt a N x w : ℝ) - L| * |u * v| ≤ |(cnt a N x w : ℝ) - L| * 1 :=
                mul_le_mul_of_nonneg_left huv (abs_nonneg _)
            _ = _ := mul_one _
      _ = _ := by
          have hin : ∀ u : ℝ, ∫⁻ v in Ioc (0 : ℝ) 1,
              (ENNReal.ofReal |(ct a N w x u v : ℝ) - L * u * v| +
                ENNReal.ofReal |(cnt a N x w : ℝ) - L|) =
              (∫⁻ v in Ioc (0 : ℝ) 1, ENNReal.ofReal |(ct a N w x u v : ℝ) - L * u * v|) +
                ENNReal.ofReal |(cnt a N x w : ℝ) - L| := by
            intro u
            rw [lintegral_add_right _ measurable_const, setLIntegral_const, vol1, mul_one]
          simp_rw [hin]
          rw [lintegral_add_right _ measurable_const, setLIntegral_const, vol1, mul_one]
  have hF2 : ∫⁻ u in Ioc (0 : ℝ) 1, ∫⁻ v in Ioc (0 : ℝ) 1,
      ENNReal.ofReal |disc (PP a N w x) u v| < ENNReal.ofReal (3 * B) := by
    refine lt_of_le_of_lt (hF.trans ?_) hx
    gcongr
    linarith [abs_nonneg ((cnt a N x w : ℝ) - L)]
  refine ⟨PP a N w x, PP_mem a N w x hN hw0, ?_, ?_⟩
  · rw [PP_card a N w x hN]
    have := (abs_lt.mp (by linarith : |(cnt a N x w : ℝ) - L| < 2 * B)).1
    have h4 : 4 * B ≤ (L : ℝ) := hBL
    linarith
  · have hne : ∫⁻ u in Ioc (0 : ℝ) 1, ∫⁻ v in Ioc (0 : ℝ) 1,
        ENNReal.ofReal |disc (PP a N w x) u v| ≠ ⊤ := (hF2.trans ENNReal.ofReal_lt_top).ne
    calc ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, |disc (PP a N w x) u v|
        ≤ (∫⁻ u in Ioc (0 : ℝ) 1, ENNReal.ofReal
            (∫ v in (0 : ℝ)..1, |disc (PP a N w x) u v|)).toReal :=
          int_le_lint _ fun u =>
            intervalIntegral.integral_nonneg zero_le_one fun v _ => abs_nonneg _
      _ ≤ (∫⁻ u in Ioc (0 : ℝ) 1, ∫⁻ v in Ioc (0 : ℝ) 1,
            ENNReal.ofReal |disc (PP a N w x) u v|).toReal := by
          refine ENNReal.toReal_mono hne (lintegral_mono fun u => ?_)
          exact (ENNReal.ofReal_le_ofReal (int_le_lint _ fun v => abs_nonneg _)).trans
            ENNReal.ofReal_toReal_le
      _ ≤ 3 * B := ENNReal.toReal_le_of_le_ofReal (by positivity) hF2.le

end Lemma72

theorem reduce : H1 → OMA.R_Erdos1221_erdos_1221_parts_ii_R1.H2 := by
  rintro ⟨cH, hcH, hH⟩
  unfold OMA.R_Erdos1221_erdos_1221_parts_ii_R1.H2
  refine ⟨min (cH / 6) (1 / 8), lt_min (by positivity) (by norm_num), 16, ?_⟩
  intro S hS B hB a ha hreg
  have e : ∀ (n : ℕ) (x D : ℝ), (cnt a n x (D / n) : ℝ) =
      (((Finset.range n).filter
        (fun j => Int.fract (a j - x) ∈ Set.Ioc (0 : ℝ) (D / n))).card : ℝ) := by
    intro n x D
    simp only [cnt, Set.mem_Ioc]
  have hreg' : ∀ᶠ n : ℕ in atTop, ∀ D : ℝ, 0 ≤ D → D ≤ S →
      ∫ x in (0 : ℝ)..1, |(cnt a n x (D / n) : ℝ) - D| ≤ B := by
    filter_upwards [hreg] with n hn D h0 h1
    simp_rw [e]
    exact hn D h0 h1
  have hS0 : (0 : ℝ) < S := by linarith
  have hfl : S - 1 < (⌊S⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one S; linarith
  have hlogS : Real.log S ≤ S := (Real.log_le_sub_one_of_pos hS0).trans (by linarith)
  by_cases hc : 4 * B ≤ ⌊S⌋₊
  · obtain ⟨P, hP, hcard, hint⟩ := Lemma72.solution a ha B S hB (by linarith) hc hreg'
    have hS4 : S / 4 ≤ (P.card : ℝ) := by linarith
    have h2 : 2 ≤ P.card := by
      have : (2 : ℝ) ≤ P.card := by linarith
      exact_mod_cast this
    have hH' := hH P h2 hP
    have hlog : Real.log S / 2 ≤ Real.log P.card := by
      have h1 : Real.log (S / 4) ≤ Real.log P.card :=
        Real.log_le_log (by positivity) hS4
      have h3 : Real.log (S / 4) = Real.log S - Real.log 4 := Real.log_div hS0.ne' (by norm_num)
      have h4 : 2 * Real.log 4 ≤ Real.log S := by
        have h5 : Real.log (4 * 4) ≤ Real.log S := Real.log_le_log (by norm_num) (by linarith)
        rw [Real.log_mul (by norm_num) (by norm_num)] at h5
        linarith
      linarith
    have hsq : Real.sqrt (Real.log S) / 2 ≤ Real.sqrt (Real.log P.card) := by
      have hl0 : 0 ≤ Real.log S := Real.log_nonneg (by linarith)
      have e : Real.sqrt (Real.log S) / 2 = Real.sqrt (Real.log S / 4) := by
        rw [Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 4), show (4:ℝ) = 2 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]
      rw [e]; exact Real.sqrt_le_sqrt (by linarith)
    have hsq0 : 0 ≤ Real.sqrt (Real.log S) := Real.sqrt_nonneg _
    calc min (cH / 6) (1 / 8) * Real.sqrt (Real.log S)
        ≤ cH / 6 * Real.sqrt (Real.log S) := mul_le_mul_of_nonneg_right (min_le_left _ _) hsq0
      _ = (cH / 3) * (Real.sqrt (Real.log S) / 2) := by ring
      _ ≤ (cH / 3) * Real.sqrt (Real.log P.card) := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ ≤ (3 * B) / 3 := by linarith
      _ = B := by ring
  · push_neg at hc
    have hsq0 : 0 ≤ Real.sqrt (Real.log S) := Real.sqrt_nonneg _
    have hsqS : Real.sqrt (Real.log S) ≤ Real.sqrt S := Real.sqrt_le_sqrt hlogS
    have hsS : Real.sqrt S ≤ S / 2 := by
      exact Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
    calc min (cH / 6) (1 / 8) * Real.sqrt (Real.log S)
        ≤ 1 / 8 * Real.sqrt (Real.log S) := mul_le_mul_of_nonneg_right (min_le_right _ _) hsq0
      _ ≤ B := by linarith
end E1221L72

theorem OMA.solution : OMA.R_Erdos1221_erdos_1221_parts_ii_R1.H2 := E1221L72.reduce Halasz.halasz

