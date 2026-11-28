import OMAStatements.S_arxiv_2602_21687

/-!
# Disproof of Open Question 1 of arXiv:2602.21687 (Adams and Segal-Halevi)

There is no `2`-balanced permutation sequence for `n = 2^(2^22 + 2)`.

Proof, following the remark in the statement file (Halász's `L¹` discrepancy bound), done with
finite sums on the `n × n` grid only.

1. Balanced side. For a `2`-balanced sequence every player `i` has
   `countUpTo s i t B ≥ t B / n - 3` (`count_lower`), and summing over players gives exactly
   `t B` (`sum_count`). Hence `∑ᵢ |countUpTo s i t B - t B / n| ≤ 6 n` and, by pigeonhole, one
   player has `L¹` discrepancy at most `6 n²` over the grid (`exists_good`).
2. Halász side. For any `n = 2^(N+2)` points, the dyadic Roth functions `f r` (Haar sign
   patterns on the empty blocks of shape `2^(N-r) × 2^(r+1)`) and the Riesz product
   `∏ (1 + i t f r)` give `L¹` discrepancy at least `n² t N (1 - 2t) / 192` (`halasz`).
   The product is expanded by telescoping; the cross terms are controlled by a one-dimensional
   martingale identity (`RP_mart`) and a first-moment bound (`RG_bound`), both by induction.
3. With `N = 2^22` and `t = 1/2048` the two bounds contradict each other.
-/

open Finset Complex

namespace OMADisproofAux

section OneD

variable (t : ℝ) (ψ : ℕ → ℕ → ℝ)

/-- Partial Riesz product along one coordinate. -/
noncomputable def RP (j b : ℕ) : ℂ :=
  ∏ r ∈ range j, (1 + I * (t : ℂ) * (ψ r (b / 2 ^ r) : ℂ))

lemma RP_zero (b : ℕ) : RP t ψ 0 b = 1 := by simp [RP]

lemma RP_succ (j b : ℕ) :
    RP t ψ (j+1) b = RP t ψ j b * (1 + I * (t:ℂ) * (ψ j (b / 2^j) : ℂ)) := by
  simp [RP, prod_range_succ]

lemma idx_lo (c h β : ℕ) (hh : 0 < h) (hβ : β < h) : (c * (h + h) + β) / h = 2 * c := by
  rw [show c * (h + h) + β = β + (2*c) * h by ring, Nat.add_mul_div_right _ _ hh,
    Nat.div_eq_of_lt hβ, zero_add]

lemma idx_hi (c h β : ℕ) (hh : 0 < h) (hβ : β < h) :
    (c * (h + h) + (h + β)) / h = 2 * c + 1 := by
  rw [show c * (h + h) + (h + β) = β + (2*c+1) * h by ring, Nat.add_mul_div_right _ _ hh,
    Nat.div_eq_of_lt hβ, zero_add]

variable {t ψ}

lemma RP_lo (j c β : ℕ) (hβ : β < 2^j) :
    RP t ψ (j+1) (c * (2^j + 2^j) + β) =
      RP t ψ j ((2*c) * 2^j + β) * (1 + I * (t:ℂ) * (ψ j (2*c) : ℂ)) := by
  rw [RP_succ, idx_lo c _ β (by positivity) hβ, show c * (2^j + 2^j) + β = (2*c) * 2^j + β by ring]

lemma RP_hi (j c β : ℕ) (hβ : β < 2^j) :
    RP t ψ (j+1) (c * (2^j + 2^j) + (2^j + β)) =
      RP t ψ j ((2*c+1) * 2^j + β) * (1 + I * (t:ℂ) * (ψ j (2*c+1) : ℂ)) := by
  rw [RP_succ, idx_hi c _ β (by positivity) hβ,
    show c * (2^j + 2^j) + (2^j + β) = (2*c+1) * 2^j + β by ring]

/-- Martingale property of the partial Riesz products. -/
lemma RP_mart (hanti : ∀ r γ, ψ r (2*γ+1) = - ψ r (2*γ)) :
    ∀ j c, ∑ β ∈ range (2^j), RP t ψ j (c * 2^j + β) = 2^j := by
  intro j
  induction j with
  | zero => intro c; simp [RP]
  | succ j ih =>
    intro c
    rw [show (2:ℕ)^(j+1) = 2^j + 2^j by ring, sum_range_add]
    rw [sum_congr rfl (fun β hβ => RP_lo (t := t) (ψ := ψ) j c β (mem_range.mp hβ)),
      sum_congr rfl (fun β hβ => RP_hi (t := t) (ψ := ψ) j c β (mem_range.mp hβ)),
      ← sum_mul, ← sum_mul, ih, ih, hanti]
    push_cast
    ring

/-- First moment of the partial Riesz products. -/
noncomputable def RG (t : ℝ) (ψ : ℕ → ℕ → ℝ) (j c : ℕ) : ℂ :=
  ∑ β ∈ range (2^j), (β : ℂ) * (RP t ψ j (c * 2^j + β) - 1)

lemma norm_factor (t x : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hx : |x| ≤ 1) :
    ‖1 + I * (t:ℂ) * (x:ℂ)‖ ≤ 3/2 := by
  have : (1 + I * (t:ℂ) * (x:ℂ)) = ((1:ℝ):ℂ) + ((t*x : ℝ):ℂ) * I := by push_cast; ring
  rw [this, Complex.norm_add_mul_I, Real.sqrt_le_iff]
  refine ⟨by norm_num, ?_⟩
  have h1 : |t * x| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg ht0]; nlinarith [abs_nonneg x]
  have h2 : (t*x)^2 ≤ 1 := by
    rw [← sq_abs]; nlinarith [abs_nonneg (t*x)]
  nlinarith

lemma RG_bound (hanti : ∀ r γ, ψ r (2*γ+1) = - ψ r (2*γ)) (hbd : ∀ r γ, |ψ r γ| ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : ∀ j c, ‖RG t ψ j c‖ ≤ t * 4^j := by
  intro j
  induction j with
  | zero => intro c; simpa [RG] using ht0
  | succ j ih =>
    intro c
    set w0 : ℂ := 1 + I * (t:ℂ) * (ψ j (2*c) : ℂ) with hw0
    set w1 : ℂ := 1 + I * (t:ℂ) * (ψ j (2*c+1) : ℂ) with hw1
    have hw : w0 - 1 = -(w1 - 1) := by
      rw [hw0, hw1, hanti]; push_cast; ring
    have hmart := RP_mart (t := t) hanti j (2*c+1)
    have key : RG t ψ (j+1) c = w0 * RG t ψ j (2*c) + w1 * RG t ψ j (2*c+1)
        + (w1 - 1) * ((2:ℂ)^j * 2^j) := by
      unfold RG
      rw [show (2:ℕ)^(j+1) = 2^j + 2^j by ring, sum_range_add]
      have e1 : ∑ x ∈ range (2^j), (x:ℂ) * (RP t ψ (j+1) (c * (2^j + 2^j) + x) - 1)
          = w0 * ∑ x ∈ range (2^j), (x:ℂ) * (RP t ψ j ((2*c) * 2^j + x) - 1)
            + (w0 - 1) * ∑ x ∈ range (2^j), (x:ℂ) := by
        rw [mul_sum, mul_sum, ← sum_add_distrib]
        refine sum_congr rfl (fun x hx => ?_)
        rw [RP_lo j c x (mem_range.mp hx)]; ring
      have e2 : ∑ x ∈ range (2^j), ((2^j + x : ℕ):ℂ) *
            (RP t ψ (j+1) (c * (2^j + 2^j) + (2^j + x)) - 1)
          = w1 * ∑ x ∈ range (2^j), (x:ℂ) * (RP t ψ j ((2*c+1) * 2^j + x) - 1)
            + w1 * (2:ℂ)^j * ∑ x ∈ range (2^j), (RP t ψ j ((2*c+1) * 2^j + x) - 1)
            + (w1 - 1) * ∑ x ∈ range (2^j), ((2:ℂ)^j + (x:ℂ)) := by
        rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
        refine sum_congr rfl (fun x hx => ?_)
        rw [RP_hi j c x (mem_range.mp hx)]; push_cast; ring
      have e3 : ∑ x ∈ range (2^j), (RP t ψ j ((2*c+1) * 2^j + x) - 1) = 0 := by
        rw [sum_sub_distrib, hmart]; simp
      have e4 : ∑ x ∈ range (2^j), ((2:ℂ)^j + (x:ℂ))
          = (2:ℂ)^j * 2^j + ∑ x ∈ range (2^j), (x:ℂ) := by
        rw [sum_add_distrib]; simp
      rw [e1, e2, e3, e4]
      linear_combination (∑ x ∈ range (2^j), (x:ℂ)) * hw
    rw [key]
    have hn0 : ‖w0‖ ≤ 3/2 := norm_factor t _ ht0 ht1 (hbd _ _)
    have hn1 : ‖w1‖ ≤ 3/2 := norm_factor t _ ht0 ht1 (hbd _ _)
    have hn2 : ‖w1 - 1‖ ≤ t := by
      rw [hw1, add_sub_cancel_left, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ht0]
      nlinarith [hbd j (2*c+1), abs_nonneg (ψ j (2*c+1))]
    have h4 : ‖((2:ℂ)^j * 2^j)‖ = 4^j := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ← mul_pow]; norm_num
    calc ‖w0 * RG t ψ j (2*c) + w1 * RG t ψ j (2*c+1) + (w1 - 1) * ((2:ℂ)^j * 2^j)‖
        ≤ ‖w0‖ * ‖RG t ψ j (2*c)‖ + ‖w1‖ * ‖RG t ψ j (2*c+1)‖ + ‖w1 - 1‖ * 4^j := by
          rw [← h4, ← norm_mul, ← norm_mul, ← norm_mul]; exact norm_add₃_le
      _ ≤ 3/2 * (t * 4^j) + 3/2 * (t * 4^j) + t * 4^j := by
          gcongr
          · exact ih _
          · exact ih _
      _ = t * 4^(j+1) := by ring

end OneD

lemma sum_blocks {M : Type*} [AddCommMonoid M] (U W : ℕ) (F : ℕ → M) :
    ∑ a ∈ range (U * W), F a = ∑ u ∈ range U, ∑ α ∈ range W, F (u * W + α) := by
  induction U with
  | zero => simp
  | succ U ih => rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]

lemma div2_eq (x u h : ℕ) (lo : u * (h+h) ≤ x) (hi : x < u * (h+h) + (h+h)) :
    x / h / 2 = u := by
  rw [Nat.div_div_eq_div_mul]
  apply Nat.div_eq_of_lt_le
  · rw [show u * (h*2) = u*(h+h) by ring]; exact lo
  · rw [show (u+1) * (h*2) = u*(h+h) + (h+h) by ring]; exact hi

lemma sign_split (c h : ℕ) (hh : 0 < h) (F : ℕ → ℂ) :
    ∑ α ∈ range (h + h), (-1:ℂ)^((c * (h+h) + α) / h) * F α
      = ∑ α ∈ range h, F α - ∑ α ∈ range h, F (h + α) := by
  rw [sum_range_add, sub_eq_add_neg, ← sum_neg_distrib]
  congr 1
  · refine sum_congr rfl (fun α hα => ?_)
    rw [idx_lo c h α hh (mem_range.mp hα), pow_mul]; simp
  · refine sum_congr rfl (fun α hα => ?_)
    rw [idx_hi c h α hh (mem_range.mp hα), pow_succ, pow_mul]; simp

lemma RP_moment {t : ℝ} {ψ : ℕ → ℕ → ℝ} (hanti : ∀ r γ, ψ r (2*γ+1) = - ψ r (2*γ))
    (j c : ℕ) (K : ℂ) :
    ∑ β ∈ range (2^j), (K + (β:ℂ)) * RP t ψ j (c * 2^j + β)
      = K * 2^j + RG t ψ j c + ∑ β ∈ range (2^j), (β:ℂ) := by
  rw [← RP_mart (t := t) hanti j c, RG, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
  exact sum_congr rfl (fun _ _ => by ring)

section TwoD

variable {n : ℕ} (N : ℕ) (px py : Fin n → ℕ) (t : ℝ)

/-- Number of points strictly below and to the left of `(a, b)`. -/
def C (a b : ℕ) : ℕ := ∑ d : Fin n, if px d < a ∧ py d < b then 1 else 0

/-- Number of points in the strip `x0 ≤ x < x1`, `y < y0`. -/
def C2 (x0 x1 y0 : ℕ) : ℕ := ∑ d : Fin n, if x0 ≤ px d ∧ px d < x1 ∧ py d < y0 then 1 else 0

/-- The discrepancy (area minus count) at `(a, b)`. -/
noncomputable def Dsc (a b : ℕ) : ℝ := (a:ℝ) * b / n - (C px py a b : ℝ)

/-- The dyadic block `(μ, ν)` of level `r` contains no point. -/
def E (r μ ν : ℕ) : Prop := ∀ d : Fin n, ¬ (px d / 2^(N-1-r) / 2 = μ ∧ py d / 2^r / 2 = ν)

open Classical in
/-- Haar-type sign pattern on empty blocks. -/
noncomputable def g (r μ ν : ℕ) : ℝ :=
  if E N px py r (μ/2) (ν/2) then (-1)^μ * (-1)^ν else 0

/-- The Roth function of level `r`. -/
noncomputable def f (r a b : ℕ) : ℝ := g N px py r (a / 2^(N-1-r)) (b / 2^r)

/-- Partial two-dimensional Riesz product. -/
noncomputable def P (j a b : ℕ) : ℂ := ∏ r ∈ range j, (1 + I * (t:ℂ) * (f N px py r a b : ℂ))

lemma g_anti (r μ γ : ℕ) : g N px py r μ (2*γ+1) = - g N px py r μ (2*γ) := by
  unfold g
  rw [show (2*γ+1)/2 = (2*γ)/2 by omega]
  split_ifs <;> ring

lemma g_bd (r μ ν : ℕ) : |g N px py r μ ν| ≤ 1 := by
  unfold g; split_ifs <;> simp

variable {N px py t}

lemma f_low {j k : ℕ} (hN : N = j + k + 1) (r : ℕ) (hr : r < j) (u α b : ℕ)
    (hα : α < 2^k + 2^k) :
    f N px py r (u * (2^k+2^k) + α) b = f N px py r (u * (2^k+2^k)) b := by
  unfold f
  have h1 : 2^(N-1-r) = (2^k + 2^k) * 2^(j-1-r) := by
    rw [show N - 1 - r = (k+1) + (j-1-r) by omega, pow_add, pow_succ]; ring
  have hW : 0 < 2^k + 2^k := by positivity
  have e1 : (u * (2^k+2^k) + α) / (2^k+2^k) = u := by
    rw [show u * (2^k+2^k) + α = α + u * (2^k+2^k) by ring, Nat.add_mul_div_right _ _ hW,
      Nat.div_eq_of_lt hα, zero_add]
  have e2 : (u * (2^k+2^k)) / (2^k+2^k) = u := Nat.mul_div_cancel _ hW
  rw [h1, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, e1, e2]

lemma P_low {j k : ℕ} (hN : N = j + k + 1) (u α b : ℕ) (hα : α < 2^k + 2^k) :
    P N px py t j (u * (2^k+2^k) + α) b = P N px py t j (u * (2^k+2^k)) b := by
  unfold P
  exact prod_congr rfl (fun r hr => by rw [f_low hN r (mem_range.mp hr) u α b hα])

open Classical in
lemma f_top {j k : ℕ} (hN : N = j + k + 1) (u v α β : ℕ) (hα : α < 2^k + 2^k)
    (hβ : β < 2^j + 2^j) :
    f N px py j (u * (2^k+2^k) + α) (v * (2^j+2^j) + β) =
      if E N px py j u v then
        (-1)^((u * (2^k+2^k) + α) / 2^k) * (-1)^((v * (2^j+2^j) + β) / 2^j) else 0 := by
  unfold f g
  rw [show N - 1 - j = k by omega, div2_eq _ u _ (by omega) (by omega),
    div2_eq _ v _ (by omega) (by omega)]

lemma C_split {j k : ℕ} (hN : N = j + k + 1) (u v α β : ℕ) (hα : α < 2^k + 2^k)
    (hβ : β < 2^j + 2^j) (hE : E N px py j u v) :
    C px py (u * (2^k+2^k) + α) (v * (2^j+2^j) + β) =
      C px py (u * (2^k+2^k)) (v * (2^j+2^j) + β) +
      C2 px py (u * (2^k+2^k)) (u * (2^k+2^k) + α) (v * (2^j+2^j)) := by
  unfold C C2
  rw [← sum_add_distrib]
  refine sum_congr rfl (fun d _ => ?_)
  have hd := hE d
  rw [show N - 1 - j = k by omega] at hd
  have : ¬ (u * (2^k+2^k) ≤ px d ∧ px d < u * (2^k+2^k) + (2^k+2^k) ∧
      v * (2^j+2^j) ≤ py d ∧ py d < v * (2^j+2^j) + (2^j+2^j)) := by
    rintro ⟨h1, h2, h3, h4⟩
    exact hd ⟨div2_eq _ _ _ h1 h2, div2_eq _ _ _ h3 h4⟩
  split_ifs <;> omega


lemma sum_sum_three (s s' : Finset ℕ) (A A' B B' Q Q' : ℕ → ℂ) :
    ∑ α ∈ s, ∑ β ∈ s', (A α * A' β - B α * B' β - Q α * Q' β)
      = (∑ α ∈ s, A α) * (∑ β ∈ s', A' β) - (∑ α ∈ s, B α) * (∑ β ∈ s', B' β)
        - (∑ α ∈ s, Q α) * (∑ β ∈ s', Q' β) := by
  simp only [sum_sub_distrib, sum_mul_sum]

open Classical in
lemma block_re {j k : ℕ} (hN : N = j + k + 1) (hn0 : 0 < n) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (u v : ℕ) :
    (if E N px py j u v then (4:ℝ)^k * (4^j - 2 * t * 4^j) / n else 0) ≤
    (∑ α ∈ range (2^k+2^k), ∑ β ∈ range (2^j+2^j),
      (Dsc px py (u * (2^k+2^k) + α) (v * (2^j+2^j) + β) : ℂ) *
      (f N px py j (u * (2^k+2^k) + α) (v * (2^j+2^j) + β) : ℂ) *
      P N px py t j (u * (2^k+2^k) + α) (v * (2^j+2^j) + β)).re := by
  split_ifs with hE
  · set ψ : ℕ → ℕ → ℝ := fun r ν => g N px py r (u * (2^k+2^k) / 2^(N-1-r)) ν with hψ
    have hanti : ∀ r γ, ψ r (2*γ+1) = - ψ r (2*γ) := fun r γ => g_anti N px py r _ γ
    have hbd : ∀ r γ, |ψ r γ| ≤ 1 := fun r γ => g_bd N px py r _ γ
    have hPR : ∀ b, P N px py t j (u * (2^k+2^k)) b = RP t ψ j b := fun b => rfl
    have hsum :
        ∑ α ∈ range (2^k+2^k), ∑ β ∈ range (2^j+2^j),
          (Dsc px py (u * (2^k+2^k) + α) (v * (2^j+2^j) + β) : ℂ) *
          (f N px py j (u * (2^k+2^k) + α) (v * (2^j+2^j) + β) : ℂ) *
          P N px py t j (u * (2^k+2^k) + α) (v * (2^j+2^j) + β)
        = (∑ α ∈ range (2^k+2^k),
              (-1:ℂ)^((u * (2^k+2^k) + α) / 2^k) * (((u * (2^k+2^k) + α : ℕ) : ℂ) / n)) *
            (∑ β ∈ range (2^j+2^j), (-1:ℂ)^((v * (2^j+2^j) + β) / 2^j) *
              (((v * (2^j+2^j) + β : ℕ) : ℂ) * RP t ψ j (v * (2^j+2^j) + β)))
          - (∑ α ∈ range (2^k+2^k), (-1:ℂ)^((u * (2^k+2^k) + α) / 2^k) * 1) *
            (∑ β ∈ range (2^j+2^j), (-1:ℂ)^((v * (2^j+2^j) + β) / 2^j) *
              ((C px py (u * (2^k+2^k)) (v * (2^j+2^j) + β) : ℂ) *
                RP t ψ j (v * (2^j+2^j) + β)))
          - (∑ α ∈ range (2^k+2^k), (-1:ℂ)^((u * (2^k+2^k) + α) / 2^k) *
              (C2 px py (u * (2^k+2^k)) (u * (2^k+2^k) + α) (v * (2^j+2^j)) : ℂ)) *
            (∑ β ∈ range (2^j+2^j), (-1:ℂ)^((v * (2^j+2^j) + β) / 2^j) *
              RP t ψ j (v * (2^j+2^j) + β)) := by
      rw [← sum_sum_three]
      refine sum_congr rfl (fun α hα => sum_congr rfl (fun β hβ => ?_))
      rw [mem_range] at hα hβ
      rw [f_top hN u v α β hα hβ, if_pos hE, P_low hN u α _ hα, hPR, Dsc,
        C_split hN u v α β hα hβ hE]
      push_cast
      ring
    have hk0 : 0 < 2^k := by positivity
    have hj0 : 0 < 2^j := by positivity
    have hx0 : ∑ α ∈ range (2^k+2^k), (-1:ℂ)^((u * (2^k+2^k) + α) / 2^k) * 1 = 0 := by
      rw [sign_split u _ hk0 (fun _ => (1:ℂ))]; simp
    have hx1 : ∑ α ∈ range (2^k+2^k),
        (-1:ℂ)^((u * (2^k+2^k) + α) / 2^k) * (((u * (2^k+2^k) + α : ℕ) : ℂ) / n)
          = -((2:ℂ)^k * 2^k) / n := by
      rw [sign_split u _ hk0 (fun α => (((u * (2^k+2^k) + α : ℕ) : ℂ) / n)), ← sum_sub_distrib]
      rw [sum_congr rfl (fun α _ => show (((u * (2^k+2^k) + α : ℕ) : ℂ) / n) -
          (((u * (2^k+2^k) + (2^k + α) : ℕ) : ℂ) / n) = -(2:ℂ)^k / n by push_cast; ring)]
      rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
    have elo : ∀ β, v * (2^j+2^j) + β = (2*v) * 2^j + β := fun β => by ring
    have ehi : ∀ β, v * (2^j+2^j) + (2^j + β) = (2*v+1) * 2^j + β := fun β => by ring
    have hy0 : ∑ β ∈ range (2^j+2^j), (-1:ℂ)^((v * (2^j+2^j) + β) / 2^j) *
        RP t ψ j (v * (2^j+2^j) + β) = 0 := by
      rw [sign_split v _ hj0 (fun β => RP t ψ j (v * (2^j+2^j) + β))]
      simp only [ehi]; simp only [elo]
      rw [RP_mart hanti, RP_mart hanti, sub_self]
    have hy1 : ∑ β ∈ range (2^j+2^j), (-1:ℂ)^((v * (2^j+2^j) + β) / 2^j) *
        (((v * (2^j+2^j) + β : ℕ) : ℂ) * RP t ψ j (v * (2^j+2^j) + β))
          = -((2:ℂ)^j * 2^j) + RG t ψ j (2*v) - RG t ψ j (2*v+1) := by
      rw [sign_split v _ hj0 (fun β => (((v * (2^j+2^j) + β : ℕ) : ℂ) *
        RP t ψ j (v * (2^j+2^j) + β)))]
      simp only [ehi]; simp only [elo]
      have m0 := RP_moment (t := t) hanti j (2*v) ((v:ℂ) * (2^j+2^j))
      have m1 := RP_moment (t := t) hanti j (2*v+1) ((v:ℂ) * (2^j+2^j) + 2^j)
      rw [sum_congr rfl (fun β _ => show (((2*v) * 2^j + β : ℕ) : ℂ) *
          RP t ψ j ((2*v) * 2^j + β) = ((v:ℂ) * (2^j+2^j) + β) * RP t ψ j ((2*v) * 2^j + β)
          by push_cast; ring), m0]
      rw [sum_congr rfl (fun β _ => show (((2*v+1) * 2^j + β : ℕ) : ℂ) *
          RP t ψ j ((2*v+1) * 2^j + β) = ((v:ℂ) * (2^j+2^j) + 2^j + β) *
            RP t ψ j ((2*v+1) * 2^j + β) by push_cast; ring), m1]
      ring
    rw [hsum, hx0, hy0, hx1, hy1, zero_mul, mul_zero, sub_zero, sub_zero]
    have hre : (-((2:ℂ)^k * 2^k) / n * (-((2:ℂ)^j * 2^j) + RG t ψ j (2*v) - RG t ψ j (2*v+1))).re
        = (-((4:ℝ)^k) / n) * (-(4:ℝ)^j + (RG t ψ j (2*v) - RG t ψ j (2*v+1)).re) := by
      have : (-((2:ℂ)^k * 2^k) / n * (-((2:ℂ)^j * 2^j) + RG t ψ j (2*v) - RG t ψ j (2*v+1)))
          = ((-((4:ℝ)^k) / n : ℝ) : ℂ) * (((-(4:ℝ)^j : ℝ) : ℂ)
            + (RG t ψ j (2*v) - RG t ψ j (2*v+1))) := by
        push_cast; rw [show (4:ℂ) = 2 * 2 by norm_num, mul_pow, mul_pow]; ring
      rw [this, Complex.re_ofReal_mul, Complex.add_re, Complex.ofReal_re]
    rw [hre]
    have hG : (RG t ψ j (2*v) - RG t ψ j (2*v+1)).re ≤ 2 * t * 4^j := by
      calc (RG t ψ j (2*v) - RG t ψ j (2*v+1)).re ≤ ‖RG t ψ j (2*v) - RG t ψ j (2*v+1)‖ :=
            Complex.re_le_norm _
        _ ≤ ‖RG t ψ j (2*v)‖ + ‖RG t ψ j (2*v+1)‖ := norm_sub_le _ _
        _ ≤ t * 4^j + t * 4^j :=
            add_le_add (RG_bound hanti hbd ht0 ht1 j _) (RG_bound hanti hbd ht0 ht1 j _)
        _ = 2 * t * 4^j := by ring
    have hA : 0 ≤ (4:ℝ)^k / n := by positivity
    rw [show (-((4:ℝ)^k) / n) * (-(4:ℝ)^j + (RG t ψ j (2*v) - RG t ψ j (2*v+1)).re)
        = (4:ℝ)^k / n * ((4:ℝ)^j - (RG t ψ j (2*v) - RG t ψ j (2*v+1)).re) by ring,
      show (4:ℝ)^k * (4^j - 2 * t * 4^j) / n = (4:ℝ)^k / n * (4^j - 2 * t * 4^j) by ring]
    exact mul_le_mul_of_nonneg_left (by linarith) hA
  · rw [sum_eq_zero (fun α hα => sum_eq_zero (fun β hβ => by
      rw [f_top hN u v α β (mem_range.mp hα) (mem_range.mp hβ), if_neg hE]; simp))]
    simp


lemma sum_grid (U W V H : ℕ) (T : ℕ → ℕ → ℂ) :
    ∑ a ∈ range (U * W), ∑ b ∈ range (V * H), T a b =
      ∑ u ∈ range U, ∑ v ∈ range V, ∑ α ∈ range W, ∑ β ∈ range H, T (u * W + α) (v * H + β) := by
  rw [sum_blocks]
  refine sum_congr rfl (fun u _ => ?_)
  rw [sum_congr rfl (fun α _ => sum_blocks V H (fun b => T (u * W + α) b)), sum_comm]

open Classical in
lemma card_empty {j k : ℕ} (hN : N = j + k + 1) (hn : n = 2^(N+2)) :
    n ≤ ((range (2^(j+2)) ×ˢ range (2^(k+2))).filter (fun x => E N px py j x.1 x.2)).card := by
  have h1 := card_filter_add_card_filter_not (s := range (2^(j+2)) ×ˢ range (2^(k+2)))
    (fun x => E N px py j x.1 x.2)
  have h2 : ((range (2^(j+2)) ×ˢ range (2^(k+2))).filter
      (fun x => ¬ E N px py j x.1 x.2)).card ≤ n := by
    calc _ ≤ (univ.image (fun d : Fin n => (px d / 2^(N-1-j) / 2, py d / 2^j / 2))).card := by
          apply card_le_card
          intro x hx
          rw [mem_filter] at hx
          obtain ⟨_, hx⟩ := hx
          unfold E at hx
          push_neg at hx
          obtain ⟨d, hd1, hd2⟩ := hx
          rw [mem_image]; exact ⟨d, mem_univ _, Prod.ext hd1 hd2⟩
      _ ≤ (univ : Finset (Fin n)).card := card_image_le
      _ = n := by simp
  rw [card_product, card_range, card_range] at h1
  have h3 : 2^(j+2) * 2^(k+2) = 2 * n := by rw [hn, hN]; ring
  omega

open Classical in
lemma level_re (hn : n = 2^(N+2)) (ht0 : 0 ≤ t) (ht1 : t ≤ 1/2) (j : ℕ) (hj : j < N) :
    (n:ℝ)^2 * (1 - 2*t) / 64 ≤
      (∑ a ∈ range n, ∑ b ∈ range n,
        (Dsc px py a b : ℂ) * (f N px py j a b : ℂ) * P N px py t j a b).re := by
  obtain ⟨k, hk⟩ : ∃ k, N = j + k + 1 := ⟨N - j - 1, by omega⟩
  have hn0 : 0 < n := by rw [hn]; positivity
  have hU : n = 2^(j+2) * (2^k+2^k) := by rw [hn, hk]; ring
  have hV : n = 2^(k+2) * (2^j+2^j) := by rw [hn, hk]; ring
  have hg := sum_grid (2^(j+2)) (2^k+2^k) (2^(k+2)) (2^j+2^j)
    (fun a b => (Dsc px py a b : ℂ) * (f N px py j a b : ℂ) * P N px py t j a b)
  rw [← hU, ← hV] at hg
  rw [hg]
  set κ : ℝ := (4:ℝ)^k * (4^j - 2 * t * 4^j) / n with hκ
  have hκ0 : 0 ≤ κ := by
    rw [hκ]; apply div_nonneg _ (by positivity)
    apply mul_nonneg (by positivity); nlinarith [pow_pos (show (0:ℝ) < 4 by norm_num) j]
  have h4j : (4:ℝ)^j = 2^j * 2^j := by rw [← mul_pow]; norm_num
  have h4k : (4:ℝ)^k = 2^k * 2^k := by rw [← mul_pow]; norm_num
  have hnR : (n:ℝ) ≠ 0 := by positivity
  calc (n:ℝ)^2 * (1 - 2*t) / 64 = (n:ℝ) * κ := by
        rw [hκ, h4j, h4k]; field_simp; rw [hU]; push_cast; ring
    _ ≤ (((range (2^(j+2)) ×ˢ range (2^(k+2))).filter
          (fun x => E N px py j x.1 x.2)).card : ℝ) * κ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast card_empty hk hn) hκ0
    _ = ∑ u ∈ range (2^(j+2)), ∑ v ∈ range (2^(k+2)), (if E N px py j u v then κ else 0) := by
        rw [← sum_product' (f := fun u v => if E N px py j u v then κ else 0), sum_ite,
          sum_const, sum_const_zero, add_zero, nsmul_eq_mul]
    _ ≤ _ := by
        rw [Complex.re_sum]
        refine sum_le_sum (fun u _ => ?_)
        rw [Complex.re_sum]
        exact sum_le_sum (fun v _ => block_re hk hn0 ht0 (by linarith) u v)

lemma P_zero (a b : ℕ) : P N px py t 0 a b = 1 := by simp [P]

lemma P_succ (j a b : ℕ) :
    P N px py t (j+1) a b = P N px py t j a b * (1 + I * (t:ℂ) * (f N px py j a b : ℂ)) := by
  simp [P, prod_range_succ]

lemma norm_factor' (t x : ℝ) (hx : |x| ≤ 1) : ‖1 + I * (t:ℂ) * (x:ℂ)‖ ≤ 1 + t^2/2 := by
  have : (1 + I * (t:ℂ) * (x:ℂ)) = ((1:ℝ):ℂ) + ((t*x : ℝ):ℂ) * I := by push_cast; ring
  rw [this, Complex.norm_add_mul_I, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have hx2 : x^2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg x]
  nlinarith [mul_le_mul_of_nonneg_left hx2 (sq_nonneg t), sq_nonneg t]

lemma P_norm (hNt : (N:ℝ) * t^2 ≤ 1) (a b : ℕ) : ‖P N px py t N a b‖ ≤ 2 := by
  unfold P
  rw [norm_prod]
  calc ∏ r ∈ range N, ‖1 + I * (t:ℂ) * (f N px py r a b : ℂ)‖
        ≤ ∏ r ∈ range N, (1 + t^2/2) :=
        prod_le_prod (fun _ _ => norm_nonneg _) (fun r _ => norm_factor' t _ (g_bd N px py r _ _))
    _ = (1 + t^2/2)^N := by rw [prod_const, card_range]
    _ ≤ (Real.exp (t^2/2))^N :=
        pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (t^2/2)]) N
    _ = Real.exp (N * (t^2/2)) := by rw [Real.exp_nat_mul]
    _ ≤ Real.exp (1/2) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ 2 := by
        have h1 := Real.exp_one_lt_d9
        have h2 : Real.exp (1/2) * Real.exp (1/2) = Real.exp 1 := by
          rw [← Real.exp_add]; norm_num
        nlinarith [Real.exp_pos (1/2)]

/-- Halász-type lower bound for the `L¹` discrepancy of `n = 2^(N+2)` points. -/
theorem halasz (hn : n = 2^(N+2)) (ht0 : 0 ≤ t) (ht1 : t ≤ 1/2) (hNt : (N:ℝ) * t^2 ≤ 1) :
    (n:ℝ)^2 * (t * N * (1 - 2*t)) / 64 ≤
      3 * ∑ a ∈ range n, ∑ b ∈ range n, |Dsc px py a b| := by
  have htel : ∀ a b, P N px py t N a b - 1 =
      ∑ j ∈ range N, I * t * ((f N px py j a b : ℂ) * P N px py t j a b) := by
    intro a b
    have := sum_range_sub (fun j => P N px py t j a b) N
    simp only [P_zero] at this
    rw [← this]
    exact sum_congr rfl (fun j _ => by rw [P_succ]; ring)
  set Z : ℂ := ∑ a ∈ range n, ∑ b ∈ range n, (Dsc px py a b : ℂ) * (P N px py t N a b - 1)
    with hZ
  have hZ2 : Z = I * t * ∑ j ∈ range N, ∑ a ∈ range n, ∑ b ∈ range n,
      (Dsc px py a b : ℂ) * (f N px py j a b : ℂ) * P N px py t j a b := by
    calc Z = ∑ a ∈ range n, ∑ b ∈ range n, ∑ j ∈ range N,
          (Dsc px py a b : ℂ) * (I * t * ((f N px py j a b : ℂ) * P N px py t j a b)) := by
          simp only [hZ, htel, mul_sum]
      _ = ∑ a ∈ range n, ∑ j ∈ range N, ∑ b ∈ range n,
          (Dsc px py a b : ℂ) * (I * t * ((f N px py j a b : ℂ) * P N px py t j a b)) :=
          sum_congr rfl (fun a _ => sum_comm)
      _ = ∑ j ∈ range N, ∑ a ∈ range n, ∑ b ∈ range n,
          (Dsc px py a b : ℂ) * (I * t * ((f N px py j a b : ℂ) * P N px py t j a b)) := sum_comm
      _ = _ := by
          simp only [mul_sum]
          exact sum_congr rfl (fun _ _ => sum_congr rfl (fun _ _ => sum_congr rfl
            (fun _ _ => by ring)))
  have hlow : t * N * ((n:ℝ)^2 * (1 - 2*t) / 64) ≤ Z.im := by
    rw [hZ2]
    have him : ∀ W : ℂ, (I * (t:ℂ) * W).im = t * W.re := by
      intro W; simp [Complex.mul_im, Complex.mul_re]
    rw [him, Complex.re_sum]
    calc t * N * ((n:ℝ)^2 * (1 - 2*t) / 64)
        = t * ∑ j ∈ range N, ((n:ℝ)^2 * (1 - 2*t) / 64) := by
          rw [sum_const, card_range, nsmul_eq_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
          (sum_le_sum (fun j hj => level_re hn ht0 ht1 j (mem_range.mp hj))) ht0
  have hup : Z.im ≤ 3 * ∑ a ∈ range n, ∑ b ∈ range n, |Dsc px py a b| := by
    calc Z.im ≤ ‖Z‖ := Complex.im_le_norm Z
      _ ≤ ∑ a ∈ range n, ∑ b ∈ range n, ‖(Dsc px py a b : ℂ) * (P N px py t N a b - 1)‖ :=
          (norm_sum_le _ _).trans (sum_le_sum (fun a _ => norm_sum_le _ _))
      _ ≤ ∑ a ∈ range n, ∑ b ∈ range n, |Dsc px py a b| * 3 := by
          refine sum_le_sum (fun a _ => sum_le_sum (fun b _ => ?_))
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          calc ‖P N px py t N a b - 1‖ ≤ ‖P N px py t N a b‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
            _ ≤ 2 + 1 := by rw [norm_one]; linarith [P_norm (px := px) (py := py) hNt a b]
            _ = 3 := by norm_num
      _ = 3 * ∑ a ∈ range n, ∑ b ∈ range n, |Dsc px py a b| := by
          simp only [mul_sum]
          exact sum_congr rfl (fun a _ => sum_congr rfl (fun b _ => by ring))
  have : (n:ℝ)^2 * (t * N * (1 - 2*t)) / 64 = t * N * ((n:ℝ)^2 * (1 - 2*t) / 64) := by ring
  linarith

end TwoD

section Balanced

open OMA.S_arxiv_2602_21687

variable {n : ℕ} (s : Fin n → Equiv.Perm (Fin n))

lemma countUpTo_mono (i : Fin n) (t B B' : ℕ) (h : B ≤ B') :
    countUpTo s i t B ≤ countUpTo s i t B' := by
  unfold countUpTo
  apply card_le_card
  intro d
  simp only [mem_filter, mem_univ, true_and]
  exact fun hd => ⟨hd.1, hd.2.trans h⟩

/-- A `2`-balanced sequence has one-sided discrepancy at least `-3`. -/
lemma count_lower (hs : IsBalanced 2 s) (i : Fin n) (t B : ℕ) (ht : t ≤ n) (hB : B ≤ n) :
    (t:ℝ) * B / n - 3 ≤ countUpTo s i t B := by
  have hn : 0 < n := Fin.pos i
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hc0 : (0:ℝ) ≤ countUpTo s i t B := Nat.cast_nonneg _
  rcases Nat.eq_zero_or_pos t with rfl | htp
  · simp; linarith
  rcases Nat.eq_zero_or_pos B with rfl | hBp
  · simp; linarith
  set q := (B - 1) * t / n with hq
  have hlt : (B - 1) * t < n * (q + 1) := by rw [hq]; exact Nat.lt_mul_div_succ _ hn
  have htn : (t:ℝ) ≤ n := by exact_mod_cast ht
  have hBR : ((B - 1 : ℕ) : ℝ) = (B:ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hltR : ((B:ℝ) - 1) * t < n * ((q:ℝ) + 1) := by
    rw [← hBR]; exact_mod_cast hlt
  have hlt2 : (t:ℝ) * B / n < q + 2 := by
    rw [div_lt_iff₀ hnR]; nlinarith
  by_cases hq2 : q ≤ 1
  · have hqR : (q:ℝ) ≤ 1 := by exact_mod_cast hq2
    linarith
  · push_neg at hq2
    have hqt : q < t := by
      rw [hq, Nat.div_lt_iff_lt_mul hn]
      have : B - 1 < n := by omega
      nlinarith
    have hbal := hs i t (q - 1) (by omega) (by omega) ht
    rw [show q - 1 + 2 - 1 = q by omega] at hbal
    have hle : q * n / t + 1 ≤ B := by
      have h1 : q * n ≤ (B - 1) * t := by rw [hq]; exact Nat.div_mul_le_self _ _
      have h2 : q * n / t ≤ B - 1 := Nat.div_le_of_le_mul (by linarith)
      omega
    have hcnt : q - 1 ≤ countUpTo s i t B := hbal.trans (countUpTo_mono s i t _ _ hle)
    have hcntR : (q:ℝ) - 1 ≤ countUpTo s i t B := by
      have : ((q - 1 : ℕ) : ℝ) = (q:ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
      rw [← this]; exact_mod_cast hcnt
    linarith

/-- Summing over players counts every day exactly `B` times. -/
lemma sum_count (t B : ℕ) (ht : t ≤ n) (hB : B ≤ n) :
    ∑ i : Fin n, countUpTo s i t B = t * B := by
  unfold countUpTo item
  simp only [card_filter]
  rw [sum_comm]
  have key : ∀ d : Fin n, (∑ i : Fin n,
      if d.val < t ∧ ((s d).symm i).val + 1 ≤ B then 1 else 0) = if d.val < t then B else 0 := by
    intro d
    split_ifs with hd
    · simp only [hd, true_and]
      rw [Equiv.sum_comp (s d).symm (fun k : Fin n => if k.val + 1 ≤ B then 1 else 0)]
      simp only [Nat.add_one_le_iff]
      rw [← card_filter, Fin.card_filter_val_lt, min_eq_right hB]
    · simp [hd]
  rw [sum_congr rfl (fun d _ => key d), sum_ite, sum_const_zero, add_zero, sum_const,
    smul_eq_mul, Fin.card_filter_val_lt, min_eq_right ht]

/-- Some player has `L¹` discrepancy at most `6 n²`. -/
lemma exists_good (hs : IsBalanced 2 s) (hn : 0 < n) :
    ∃ i : Fin n, ∑ a ∈ range n, ∑ b ∈ range n,
      |(countUpTo s i a b : ℝ) - a * b / n| ≤ 6 * (n:ℝ)^2 := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have key : ∀ a ∈ range n, ∀ b ∈ range n,
      ∑ i : Fin n, |(countUpTo s i a b : ℝ) - a * b / n| ≤ 6 * n := by
    intro a ha b hb
    rw [mem_range] at ha hb
    have hsum : ∑ i : Fin n, ((countUpTo s i a b : ℝ) - a * b / n) = 0 := by
      rw [sum_sub_distrib, ← Nat.cast_sum, sum_count s a b ha.le hb.le, sum_const, card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      push_cast; field_simp; ring
    calc ∑ i : Fin n, |(countUpTo s i a b : ℝ) - a * b / n|
        ≤ ∑ i : Fin n, (((countUpTo s i a b : ℝ) - a * b / n) + 6) := by
          refine sum_le_sum (fun i _ => ?_)
          have := count_lower s hs i a b ha.le hb.le
          rw [abs_le]; constructor <;> linarith
      _ = 6 * n := by rw [sum_add_distrib, hsum]; simp [mul_comm]
  have htot : ∑ i : Fin n, ∑ a ∈ range n, ∑ b ∈ range n,
      |(countUpTo s i a b : ℝ) - a * b / n| ≤ ∑ i : Fin n, 6 * (n:ℝ)^2 := by
    rw [sum_comm]
    calc ∑ a ∈ range n, ∑ i : Fin n, ∑ b ∈ range n, |(countUpTo s i a b : ℝ) - a * b / n|
        = ∑ a ∈ range n, ∑ b ∈ range n, ∑ i : Fin n,
            |(countUpTo s i a b : ℝ) - a * b / n| := sum_congr rfl (fun a _ => sum_comm)
      _ ≤ ∑ a ∈ range n, ∑ b ∈ range n, 6 * (n:ℝ) :=
          sum_le_sum (fun a ha => sum_le_sum (fun b hb => key a ha b hb))
      _ = ∑ i : Fin n, 6 * (n:ℝ)^2 := by
          simp only [sum_const, card_range, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  obtain ⟨i, _, hi⟩ := exists_le_of_sum_le (univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) htot
  exact ⟨i, hi⟩

lemma countUpTo_eq_C (i : Fin n) (a b : ℕ) :
    countUpTo s i a b = C (fun d => d.val) (fun d => ((s d).symm i).val) a b := by
  unfold countUpTo item C
  rw [card_filter]
  simp only [Nat.add_one_le_iff]

/-- A `2`-balanced sequence of size `2^(N+2)` forces `t N (1 - 2t) ≤ 1152`. -/
theorem balanced_bound (N : ℕ) (s : Fin (2^(N+2)) → Equiv.Perm (Fin (2^(N+2))))
    (hs : IsBalanced 2 s) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1/2) (hNt : (N:ℝ) * t^2 ≤ 1) :
    t * N * (1 - 2*t) ≤ 1152 := by
  have hn : 0 < 2^(N+2) := by positivity
  obtain ⟨i, hi⟩ := exists_good s hs hn
  have hH := halasz (N := N) (px := fun d => d.val) (py := fun d => ((s d).symm i).val) rfl
    ht0 ht1 hNt
  have heq : ∑ a ∈ range (2^(N+2)), ∑ b ∈ range (2^(N+2)),
      |Dsc (fun d => d.val) (fun d => ((s d).symm i).val) a b|
      = ∑ a ∈ range (2^(N+2)), ∑ b ∈ range (2^(N+2)),
      |(countUpTo s i a b : ℝ) - a * b / ((2^(N+2) : ℕ) : ℝ)| := by
    refine sum_congr rfl (fun a _ => sum_congr rfl (fun b _ => ?_))
    rw [Dsc, countUpTo_eq_C, abs_sub_comm]
  rw [heq] at hH
  have hnR : (0:ℝ) < ((2^(N+2) : ℕ) : ℝ) := by exact_mod_cast hn
  have h2 : ((2^(N+2) : ℕ) : ℝ)^2 * (t * N * (1 - 2*t)) / 64
      ≤ ((2^(N+2) : ℕ) : ℝ)^2 * 18 := by linarith
  have h3 : 0 < ((2^(N+2) : ℕ) : ℝ)^2 := by positivity
  nlinarith

end Balanced

end OMADisproofAux

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2602_21687.main) := by
  intro h
  obtain ⟨s, hs⟩ := h (2^(2^22+2)) Nat.one_le_two_pow
  have := OMADisproofAux.balanced_bound (2^22) s hs (1/2048) (by norm_num) (by norm_num)
    (by norm_num)
  norm_num at this
