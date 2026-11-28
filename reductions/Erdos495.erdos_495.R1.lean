import FormalConjectures.ErdosProblems.«495»

-- Reduction Erdos495.erdos_495.R1 of Erdős Problem 495
-- Credit: @rickmanelius
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The Littlewood conjecture: liminf of n ||n alpha|| ||n beta|| is 0 for all real alpha, beta,
-- where ||x|| is the distance to the nearest integer (distToNearestInt).
--
-- PROVED BELOW (the classical easy cases):
--   freq_of_not_ba: if alpha is not badly approximable (no c > 0 with c <= n ||n alpha|| for all
--     n >= 1), then n ||n alpha|| ||n beta|| <= n ||n alpha|| / 2 is frequently small. This covers
--     rational alpha (freq_of_int_mul: the product vanishes along multiples of a denominator).
--     By symmetry the same holds for beta.
--   freq_of_dep: if alpha is badly approximable and a + b alpha + c beta = 0 with c nonzero, take
--     k <= Q from Dirichlet with ||k alpha|| <= 1/(Q + 1) and n = c^2 k. Then ||n alpha|| <= c^2 ||k alpha||
--     and ||n beta|| = ||c b k alpha|| <= |c b| ||k alpha||, so the product is at most
--     c^4 |c b| k ||k alpha||^2 <= c^4 |c b|/(Q + 1). Bad approximability gives k >= C (Q + 1), so
--     n is large. With c = 0 the relation makes alpha rational, contradicting bad approximability.
--   liminf_eq_zero_of: a nonnegative sequence frequently below every eps > 0 has liminf 0.
--
-- What remains is the classical open core: alpha and beta badly approximable with 1, alpha, beta
-- linearly independent over Q. It is split by algebraicity.
-- H1 (OPEN): both algebraic. It contains the famous open case alpha = sqrt 2, beta = sqrt 3
--   (Cassels and Swinnerton-Dyer settled pairs from one cubic field).
-- H2 (OPEN): at least one of them transcendental.

namespace OMA.R_Erdos495_erdos_495_R1

open Filter

def H1 : Prop :=
  ∀ α β : ℝ,
    (∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n → c ≤ n * distToNearestInt (n * α)) →
    (∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n → c ≤ n * distToNearestInt (n * β)) →
    (∀ a b c : ℤ, (a : ℝ) + b * α + c * β = 0 → a = 0 ∧ b = 0 ∧ c = 0) →
    IsAlgebraic ℚ α → IsAlgebraic ℚ β →
    liminf (fun n : ℕ ↦ (n : ℝ) * distToNearestInt (n * α) * distToNearestInt (n * β)) atTop = 0

def H2 : Prop :=
  ∀ α β : ℝ,
    (∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n → c ≤ n * distToNearestInt (n * α)) →
    (∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n → c ≤ n * distToNearestInt (n * β)) →
    (∀ a b c : ℤ, (a : ℝ) + b * α + c * β = 0 → a = 0 ∧ b = 0 ∧ c = 0) →
    (Transcendental ℚ α ∨ Transcendental ℚ β) →
    liminf (fun n : ℕ ↦ (n : ℝ) * distToNearestInt (n * α) * distToNearestInt (n * β)) atTop = 0

lemma dist_le_half (x : ℝ) : distToNearestInt x ≤ 1 / 2 := abs_sub_round x

lemma dist_int (z : ℤ) : distToNearestInt (z : ℝ) = 0 := by
  unfold distToNearestInt
  rw [round_intCast]
  simp

lemma dist_add_int (x : ℝ) (z : ℤ) : distToNearestInt (x + z) = distToNearestInt x := by
  apply le_antisymm
  · calc distToNearestInt (x + z) ≤ |x + z - ((round x + z : ℤ) : ℝ)| := round_le _ _
      _ = distToNearestInt x := by
          unfold distToNearestInt
          push_cast
          congr 1
          ring
  · calc distToNearestInt x ≤ |x - ((round (x + z) - z : ℤ) : ℝ)| := round_le _ _
      _ = distToNearestInt (x + z) := by
          unfold distToNearestInt
          push_cast
          congr 1
          ring

lemma dist_neg (x : ℝ) : distToNearestInt (-x) = distToNearestInt x := by
  apply le_antisymm
  · calc distToNearestInt (-x) ≤ |-x - ((-round x : ℤ) : ℝ)| := round_le _ _
      _ = distToNearestInt x := by
          unfold distToNearestInt
          push_cast
          rw [show -x - -(round x : ℝ) = -(x - round x) by ring, abs_neg]
  · calc distToNearestInt x ≤ |x - ((-round (-x) : ℤ) : ℝ)| := round_le _ _
      _ = distToNearestInt (-x) := by
          unfold distToNearestInt
          push_cast
          rw [show x - -(round (-x) : ℝ) = -(-x - round (-x)) by ring, abs_neg]

lemma dist_int_mul_le (k : ℤ) (x : ℝ) :
    distToNearestInt (k * x) ≤ |(k : ℝ)| * distToNearestInt x := by
  calc distToNearestInt (k * x) ≤ |k * x - ((k * round x : ℤ) : ℝ)| := round_le _ _
    _ = |(k : ℝ)| * distToNearestInt x := by
        unfold distToNearestInt
        push_cast
        rw [← abs_mul]
        congr 1
        ring

lemma prod_nonneg (α β : ℝ) (n : ℕ) :
    0 ≤ (n : ℝ) * distToNearestInt (n * α) * distToNearestInt (n * β) :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (distToNearestInt_nonneg _))
    (distToNearestInt_nonneg _)

/-- A nonnegative sequence that is frequently below every `ε > 0` has `liminf` zero. -/
lemma liminf_eq_zero_of {u : ℕ → ℝ} (hnn : ∀ n, 0 ≤ u n)
    (hfreq : ∀ ε > 0, ∀ N : ℕ, ∃ n ≥ N, u n < ε) : liminf u atTop = 0 := by
  have hbdd : IsBoundedUnder (· ≥ ·) atTop u := isBoundedUnder_of ⟨0, hnn⟩
  have hcobdd : IsCoboundedUnder (· ≥ ·) atTop u := by
    refine ⟨1, fun a ha => ?_⟩
    rw [Filter.eventually_map, Filter.eventually_atTop] at ha
    obtain ⟨N, hN⟩ := ha
    obtain ⟨n, hn, hu⟩ := hfreq 1 one_pos N
    have := hN n hn
    show a ≤ 1
    linarith
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    rw [zero_add]
    apply Filter.liminf_le_of_frequently_le _ hbdd
    rw [Filter.frequently_atTop]
    intro N
    obtain ⟨n, hn, hu⟩ := hfreq ε hε N
    exact ⟨n, hn, hu.le⟩
  · exact Filter.le_liminf_of_le hcobdd (Filter.Eventually.of_forall hnn)

/-- If `k α` is an integer for some `k ≥ 1`, the product vanishes along the multiples of `k`. -/
lemma freq_of_int_mul {α : ℝ} (β : ℝ) {k : ℕ} (hk : 0 < k)
    (hint : distToNearestInt (k * α) = 0) :
    ∀ ε > 0, ∀ N : ℕ, ∃ n ≥ N,
      (n : ℝ) * distToNearestInt (n * α) * distToNearestInt (n * β) < ε := by
  intro ε hε N
  refine ⟨k * (N + 1), by nlinarith, ?_⟩
  have h0 : distToNearestInt (((k * (N + 1) : ℕ) : ℝ) * α) = 0 := by
    have hle := dist_int_mul_le ((N + 1 : ℕ) : ℤ) (k * α)
    have e : (((k * (N + 1) : ℕ) : ℝ) * α) = (((N + 1 : ℕ) : ℤ) : ℝ) * (k * α) := by
      push_cast
      ring
    rw [e]
    rw [hint, mul_zero] at hle
    exact le_antisymm hle (distToNearestInt_nonneg _)
  rw [h0]
  simpa using hε

/-- If `α` is not badly approximable, the product is frequently small. -/
lemma freq_of_not_ba {α : ℝ} (β : ℝ)
    (h : ¬ ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n → c ≤ n * distToNearestInt (n * α)) :
    ∀ ε > 0, ∀ N : ℕ, ∃ n ≥ N,
      (n : ℝ) * distToNearestInt (n * α) * distToNearestInt (n * β) < ε := by
  intro ε hε N
  push Not at h
  by_cases hz : ∃ k ∈ Finset.Icc 1 N, distToNearestInt (k * α) = 0
  · obtain ⟨k, hk, hk0⟩ := hz
    have hk1 : 0 < k := by
      simp only [Finset.mem_Icc] at hk
      omega
    exact freq_of_int_mul β hk1 hk0 ε hε N
  · push Not at hz
    obtain ⟨m, hm, hmle⟩ : ∃ m : ℝ, 0 < m ∧
        ∀ k ∈ Finset.Icc 1 N, m ≤ k * distToNearestInt (k * α) := by
      rcases (Finset.Icc 1 N).eq_empty_or_nonempty with he | hne
      · exact ⟨1, one_pos, by simp [he]⟩
      · obtain ⟨k₀, hk₀, hmin⟩ := Finset.exists_min_image _
          (fun k : ℕ => (k : ℝ) * distToNearestInt (k * α)) hne
        refine ⟨k₀ * distToNearestInt (k₀ * α), ?_, hmin⟩
        have h1 : (0 : ℝ) < k₀ := by
          simp only [Finset.mem_Icc] at hk₀
          exact_mod_cast (by omega : 0 < k₀)
        have h2 : 0 < distToNearestInt (k₀ * α) :=
          lt_of_le_of_ne (distToNearestInt_nonneg _) (Ne.symm (hz k₀ hk₀))
        positivity
    obtain ⟨n, hn, hlt⟩ := h (min (2 * ε) m) (by positivity)
    refine ⟨n, ?_, ?_⟩
    · by_contra hlt'
      push Not at hlt'
      have h1 := hmle n (by simp only [Finset.mem_Icc]; omega)
      have h2 : min (2 * ε) m ≤ m := min_le_right _ _
      linarith
    · have hd := dist_le_half (n * β)
      have hnn : 0 ≤ (n : ℝ) * distToNearestInt (n * α) :=
        mul_nonneg (Nat.cast_nonneg n) (distToNearestInt_nonneg _)
      have h3 : min (2 * ε) m ≤ 2 * ε := min_le_left _ _
      calc (n : ℝ) * distToNearestInt (n * α) * distToNearestInt (n * β)
          ≤ (n : ℝ) * distToNearestInt (n * α) * (1 / 2) := by gcongr
        _ < min (2 * ε) m * (1 / 2) := by gcongr
        _ ≤ 2 * ε * (1 / 2) := by gcongr
        _ = ε := by ring

/-- If `α` is badly approximable and `a + b α + c β = 0` with `c ≠ 0`, then at `n = c^2 k`,
with `k` from Dirichlet, the product is at most `|c|^5 |b| / (Q + 1)`. -/
lemma freq_of_dep {α β : ℝ}
    (hba : ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n → c ≤ n * distToNearestInt (n * α))
    {a b c : ℤ} (hc : c ≠ 0) (hdep : (a : ℝ) + b * α + c * β = 0) :
    ∀ ε > 0, ∀ N : ℕ, ∃ n ≥ N,
      (n : ℝ) * distToNearestInt (n * α) * distToNearestInt (n * β) < ε := by
  intro ε hε N
  obtain ⟨C, hC, hCle⟩ := hba
  set D : ℝ := (c : ℝ) ^ 4 * |(c : ℝ) * b| with hD
  have hD0 : 0 ≤ D := by positivity
  obtain ⟨Q, hQ⟩ := exists_nat_gt (max (N / C) ((D + 1) / ε))
  have hQ1 : (N : ℝ) / C < Q := lt_of_le_of_lt (le_max_left _ _) hQ
  have hQ2 : (D + 1) / ε < Q := lt_of_le_of_lt (le_max_right _ _) hQ
  have hQpos : 0 < Q := by
    have : (0 : ℝ) < (D + 1) / ε := by positivity
    exact_mod_cast this.trans hQ2
  obtain ⟨j, k, hk, hkQ, hdir⟩ := Real.exists_int_int_abs_mul_sub_le α hQpos
  lift k to ℕ using hk.le
  have hk0 : 0 < k := by exact_mod_cast hk
  have hkQ' : (k : ℝ) ≤ Q := by exact_mod_cast hkQ
  have hQR : (0 : ℝ) < Q + 1 := by positivity
  have hdk : distToNearestInt (k * α) ≤ 1 / (Q + 1) := by
    have := round_le ((k : ℝ) * α) j
    push_cast at hdir
    exact this.trans hdir
  have hd0 := distToNearestInt_nonneg ((k : ℝ) * α)
  -- bad approximability forces k > N
  have hkN : N < k := by
    have h1 := hCle k hk0
    have h2 : (k : ℝ) * distToNearestInt (k * α) ≤ k * (1 / (Q + 1)) := by gcongr
    have h3 : C * (Q + 1) ≤ k := by
      have := h1.trans h2
      rw [mul_one_div, le_div_iff₀ hQR] at this
      exact this
    have h4 : (N : ℝ) < C * (Q + 1) := by
      rw [div_lt_iff₀ hC] at hQ1
      nlinarith
    exact_mod_cast h4.trans_le h3
  refine ⟨c.natAbs ^ 2 * k, ?_, ?_⟩
  · have : 1 ≤ c.natAbs ^ 2 := Nat.one_le_pow _ _ (Int.natAbs_pos.mpr hc)
    nlinarith
  · have hcast : ((c.natAbs ^ 2 * k : ℕ) : ℝ) = (c : ℝ) ^ 2 * k := by
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_natAbs, Int.cast_abs, sq_abs]
    rw [hcast]
    have h1 : distToNearestInt ((c : ℝ) ^ 2 * k * α) ≤ (c : ℝ) ^ 2 * distToNearestInt (k * α) := by
      have := dist_int_mul_le (c ^ 2) (k * α)
      push_cast at this
      rw [abs_of_nonneg (sq_nonneg _)] at this
      rw [show (c : ℝ) ^ 2 * k * α = (c : ℝ) ^ 2 * (k * α) by ring]
      exact this
    have h2 : distToNearestInt ((c : ℝ) ^ 2 * k * β) ≤
        |(c : ℝ) * b| * distToNearestInt (k * α) := by
      have hcb : (c : ℝ) * β = -a - b * α := by linarith
      have hβ : (c : ℝ) ^ 2 * k * β = -(((c * b : ℤ) : ℝ) * (k * α)) + ((-(c * k * a) : ℤ) : ℝ) := by
        push_cast
        linear_combination ((c : ℝ) * k) * hcb
      rw [hβ, dist_add_int, dist_neg]
      have := dist_int_mul_le (c * b) (k * α)
      rw [Int.cast_mul] at this ⊢
      exact this
    have hkd : (k : ℝ) * distToNearestInt (k * α) ^ 2 ≤ 1 / ((Q : ℝ) + 1) := by
      have e1 : distToNearestInt (k * α) ^ 2 ≤ (1 / ((Q : ℝ) + 1)) ^ 2 := by gcongr
      calc (k : ℝ) * distToNearestInt (k * α) ^ 2 ≤ ((Q : ℝ) + 1) * (1 / ((Q : ℝ) + 1)) ^ 2 := by
            apply mul_le_mul (by linarith) e1 (sq_nonneg _) (by positivity)
        _ = 1 / ((Q : ℝ) + 1) := by
            field_simp
    have hc2 : (0 : ℝ) ≤ (c : ℝ) ^ 2 := sq_nonneg _
    have hck : (0 : ℝ) ≤ (c : ℝ) ^ 2 * k := by positivity
    calc (c : ℝ) ^ 2 * k * distToNearestInt ((c : ℝ) ^ 2 * k * α) *
          distToNearestInt ((c : ℝ) ^ 2 * k * β)
        ≤ (c : ℝ) ^ 2 * k * ((c : ℝ) ^ 2 * distToNearestInt (k * α)) *
          (|(c : ℝ) * b| * distToNearestInt (k * α)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 hck) h2 (distToNearestInt_nonneg _)
            (mul_nonneg hck (mul_nonneg hc2 hd0))
      _ = D * ((k : ℝ) * distToNearestInt (k * α) ^ 2) := by
          rw [hD]
          ring
      _ ≤ D * (1 / ((Q : ℝ) + 1)) := mul_le_mul_of_nonneg_left hkd hD0
      _ < ε := by
          rw [mul_one_div, div_lt_iff₀ hQR]
          rw [div_lt_iff₀ hε] at hQ2
          nlinarith

theorem main : H1 → H2 → type_of% @Erdos495.erdos_495 := by
  intro h1 h2 α β
  by_cases hA : ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n → c ≤ n * distToNearestInt (n * α)
  swap
  · exact liminf_eq_zero_of (prod_nonneg α β) (freq_of_not_ba β hA)
  by_cases hB : ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n → c ≤ n * distToNearestInt (n * β)
  swap
  · apply liminf_eq_zero_of (prod_nonneg α β)
    intro ε hε N
    obtain ⟨n, hn, h⟩ := freq_of_not_ba α hB ε hε N
    refine ⟨n, hn, ?_⟩
    calc (n : ℝ) * distToNearestInt (n * α) * distToNearestInt (n * β)
        = (n : ℝ) * distToNearestInt (n * β) * distToNearestInt (n * α) := by ring
      _ < ε := h
  by_cases hI : ∀ a b c : ℤ, (a : ℝ) + b * α + c * β = 0 → a = 0 ∧ b = 0 ∧ c = 0
  swap
  · push Not at hI
    obtain ⟨a, b, c, hdep, hne⟩ := hI
    by_cases hc : c = 0
    · exfalso
      subst hc
      have hb : b ≠ 0 := by
        intro hb
        subst hb
        have ha : a = 0 := by
          have : (a : ℝ) = 0 := by simpa using hdep
          exact_mod_cast this
        exact hne ha rfl rfl
      obtain ⟨C, hC, hCle⟩ := hA
      have hle := hCle b.natAbs (Int.natAbs_pos.mpr hb)
      have h0 : distToNearestInt (b.natAbs * α) = 0 := by
        have hba : (b : ℝ) * α = -a := by
          push_cast at hdep
          linarith
        rw [Nat.cast_natAbs, Int.cast_abs]
        rcases le_or_gt 0 (b : ℝ) with hb0 | hb0
        · rw [abs_of_nonneg hb0, hba]
          have := dist_int (-a)
          push_cast at this
          exact this
        · rw [abs_of_neg hb0, neg_mul, hba, neg_neg]
          exact dist_int a
      rw [h0, mul_zero] at hle
      linarith
    · exact liminf_eq_zero_of (prod_nonneg α β) (freq_of_dep hA hc hdep)
  by_cases halg : IsAlgebraic ℚ α ∧ IsAlgebraic ℚ β
  · exact h1 α β hA hB hI halg.1 halg.2
  · rw [not_and_or] at halg
    exact h2 α β hA hB hI halg

end OMA.R_Erdos495_erdos_495_R1
