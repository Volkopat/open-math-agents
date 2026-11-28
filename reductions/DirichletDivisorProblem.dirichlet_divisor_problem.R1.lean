import FormalConjectures.Wikipedia.DirichletDivisorProblem

/-!
# Reduction of the Dirichlet divisor problem via Dirichlet's hyperbola method and Voronoï's formula

Reduction `DirichletDivisorProblem.dirichlet_divisor_problem.R1` by `@hackoria`.

We prove unconditionally (using no hypotheses):
1. **Dirichlet's hyperbola identity:** for every `N : ℕ`,
   `∑ n ∈ Icc 1 N, d(n) + ⌊√N⌋² = 2 * ∑ k ∈ Icc 1 ⌊√N⌋, ⌊N / k⌋`.
2. **Sharp Euler-Maclaurin harmonic asymptotic:** for every `N ≥ 1`,
   `0 ≤ γ - (H_N - log N - 1 / (2 N)) ≤ 1 / N²`,
   proved via monotonicity of the telescoping remainder terms on `(0, ∞)`.
3. **Exact sawtooth reduction:** substituting `H_{⌊√x⌋}` into the hyperbola identity cancels all
   `O(√x)` terms identically and gives
   `|Δ(x) + 2 * ∑_{k=1}^{⌊√x⌋} (fract(x / k) - 1/2)| ≤ 12` for all `x ≥ 4`,
   i.e., `Δ(x) = -2 * ∑_{k ≤ √x} ψ(x / k) + O(1)`.

This reduces the Dirichlet divisor problem cleanly into Voronoï's two classical components:
- `H1` (known, Voronoï 1904): truncated Voronoï formula at `N = ⌊√x⌋`, approximating the sawtooth
  sum `-2 * ∑_{k ≤ √x} ψ(x / k)` by `(x^{1/4} / (π √2)) * ∑_{n ≤ √x} d(n) n^{-3/4} cos(4π √(nx) - π/4)`
  with error `O(x^{1/4 + ε})`.
- `H2` (open core): full cancellation in Voronoï's truncated cosine sum,
  `∑_{n ≤ √x} d(n) n^{-3/4} cos(4π √(nx) - π/4) = O(x^ε)` for every `ε > 0`.
-/

namespace OMA.R_DirichletDivisorProblem_dirichlet_divisor_problem_R1

open Filter Asymptotics Real Finset
open scoped Topology
open DirichletDivisorProblem

-- Known theorem (Voronoï 1904): truncated Voronoï formula at N = ⌊√x⌋ connecting Dirichlet's
-- sawtooth sum to Voronoï's explicit cosine series up to O(x^{1/4 + ε}).
def H1 : Prop :=
  ∀ ε > (0 : ℝ),
    (fun x : ℝ =>
      (-2 : ℝ) * (∑ k ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊, (Int.fract (x / (k : ℝ)) - 1 / 2)) -
      (x ^ ((1 : ℝ) / 4) / (Real.pi * Real.sqrt 2)) *
        ∑ n ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊,
          ((n.divisors.card : ℝ) / (n : ℝ) ^ ((3 : ℝ) / 4)) *
            Real.cos (4 * Real.pi * Real.sqrt ((n : ℝ) * x) - Real.pi / 4))
    =O[atTop] fun x => x ^ ((1 : ℝ) / 4 + ε)

-- Open core: square-root cancellation in Voronoï's truncated cosine sum for every ε > 0.
def H2 : Prop :=
  ∀ ε > (0 : ℝ),
    (fun x : ℝ =>
      ∑ n ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊,
        ((n.divisors.card : ℝ) / (n : ℝ) ^ ((3 : ℝ) / 4)) *
          Real.cos (4 * Real.pi * Real.sqrt ((n : ℝ) * x) - Real.pi / 4))
    =O[atTop] fun x => x ^ ε

/- ### Section 1: Dirichlet's hyperbola identity -/

lemma sum_card_divisors_eq (N : ℕ) :
    ∑ n ∈ Icc 1 N, n.divisors.card = ∑ a ∈ Icc 1 N, N / a := by
  have h1 : ∀ n ∈ Icc 1 N, n.divisors.card = ∑ a ∈ Icc 1 N, if a ∣ n then 1 else 0 := by
    intro n hn
    rw [mem_Icc] at hn
    rw [← card_filter]
    congr 1
    ext a
    simp only [Nat.mem_divisors, mem_filter, mem_Icc]
    constructor
    · rintro ⟨hd, -⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd (by omega), (Nat.le_of_dvd (by omega) hd).trans hn.2⟩, hd⟩
    · rintro ⟨-, hd⟩
      exact ⟨hd, by omega⟩
  rw [sum_congr rfl h1, sum_comm]
  refine sum_congr rfl fun a ha => ?_
  rw [mem_Icc] at ha
  rw [← card_filter, ← Nat.Ioc_filter_dvd_card_eq_div]
  congr 1

lemma count_mul_le (N a : ℕ) (ha : 1 ≤ a) :
    ∑ b ∈ Icc 1 N, (if a * b ≤ N then 1 else 0) = N / a := by
  rw [← card_filter]
  have hset : (Icc 1 N).filter (fun b => a * b ≤ N) = Icc 1 (N / a) := by
    ext b
    simp only [mem_filter, mem_Icc]
    rw [Nat.le_div_iff_mul_le (by omega)]
    constructor
    · rintro ⟨⟨h1, -⟩, h3⟩
      exact ⟨h1, by nlinarith⟩
    · rintro ⟨h1, h3⟩
      exact ⟨⟨h1, by nlinarith⟩, by nlinarith⟩
  rw [hset, Nat.card_Icc, Nat.add_sub_cancel]

lemma hyperbola_nat (N : ℕ) :
    ∑ n ∈ Icc 1 N, n.divisors.card + N.sqrt * N.sqrt = 2 * ∑ a ∈ Icc 1 N.sqrt, N / a := by
  rw [sum_card_divisors_eq]
  set y := N.sqrt
  have hy1 : y * y ≤ N := Nat.sqrt_le N
  have hy2 : N < (y + 1) * (y + 1) := Nat.lt_succ_sqrt N
  have hyN : y ≤ N := Nat.sqrt_le_self N
  have key : ∀ a ∈ Icc 1 N, ∀ b ∈ Icc 1 N,
      (if a * b ≤ N then 1 else 0) + (if a ≤ y ∧ b ≤ y then 1 else 0) =
        (if a * b ≤ N ∧ a ≤ y then 1 else 0) + (if a * b ≤ N ∧ b ≤ y then 1 else 0) := by
    intro a _ b _
    by_cases hP : a * b ≤ N <;> by_cases hA : a ≤ y <;> by_cases hB : b ≤ y <;>
      simp only [hP, hA, hB, and_self, and_true, and_false, if_true,
        if_false] <;> first
      | rfl
      | (exfalso; have := Nat.mul_le_mul hA hB; omega)
      | (exfalso; have := Nat.mul_le_mul (Nat.not_le.mp hA) (Nat.not_le.mp hB); nlinarith)
  have hsum := sum_congr rfl fun a ha => sum_congr rfl (key a ha)
  simp only [sum_add_distrib] at hsum
  have e1 : ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, (if a * b ≤ N then 1 else 0) = ∑ a ∈ Icc 1 N, N / a :=
    sum_congr rfl fun a ha => count_mul_le N a (mem_Icc.mp ha).1
  have c1 : ∑ a ∈ Icc 1 N, (if a ≤ y then 1 else 0) = y := by
    rw [← card_filter]
    have : (Icc 1 N).filter (· ≤ y) = Icc 1 y := by
      ext a; simp only [mem_filter, mem_Icc]; omega
    rw [this, Nat.card_Icc, Nat.add_sub_cancel]
  have e2 : ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, (if a ≤ y ∧ b ≤ y then 1 else 0) = y * y := by
    have hmul : ∀ a b : ℕ, (if a ≤ y ∧ b ≤ y then 1 else 0 : ℕ) =
        (if a ≤ y then 1 else 0) * (if b ≤ y then 1 else 0) := by
      intro a b
      by_cases ha : a ≤ y <;> by_cases hb : b ≤ y <;> simp [ha, hb]
    simp_rw [hmul]
    rw [← sum_mul_sum, c1]
  have row : ∀ a ∈ Icc 1 N,
      ∑ b ∈ Icc 1 N, (if a * b ≤ N ∧ a ≤ y then 1 else 0) = if a ≤ y then N / a else 0 := by
    intro a ha
    split_ifs with hA
    · simp only [hA, and_true]; exact count_mul_le N a (mem_Icc.mp ha).1
    · simp [hA]
  have e3 : ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, (if a * b ≤ N ∧ a ≤ y then 1 else 0) =
      ∑ a ∈ Icc 1 y, N / a := by
    rw [sum_congr rfl row, ← sum_filter]
    congr 1
    ext a; simp only [mem_filter, mem_Icc]; omega
  have e4 : ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, (if a * b ≤ N ∧ b ≤ y then 1 else 0) =
      ∑ a ∈ Icc 1 y, N / a := by
    rw [sum_comm, ← e3]
    simp_rw [mul_comm]
  rw [e1, e2, e3, e4] at hsum
  omega

lemma nat_sqrt_floor_eq_floor_sqrt {x : ℝ} (hx : 0 ≤ x) :
    ⌊x⌋₊.sqrt = ⌊Real.sqrt x⌋₊ := by
  symm
  rw [Nat.eq_sqrt]
  constructor
  · rw [Nat.le_floor_iff hx]
    have h1 : (⌊Real.sqrt x⌋₊ : ℝ) ≤ Real.sqrt x := Nat.floor_le (Real.sqrt_nonneg x)
    have h2 : (0 : ℝ) ≤ (⌊Real.sqrt x⌋₊ : ℝ) := Nat.cast_nonneg _
    have hmul : (⌊Real.sqrt x⌋₊ : ℝ) * (⌊Real.sqrt x⌋₊ : ℝ) ≤ Real.sqrt x * Real.sqrt x :=
      mul_le_mul h1 h1 h2 (Real.sqrt_nonneg x)
    rw [Real.mul_self_sqrt hx] at hmul
    exact_mod_cast hmul
  · rw [Nat.floor_lt hx]
    have h1 : Real.sqrt x < (⌊Real.sqrt x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (Real.sqrt x)
    have hmul : Real.sqrt x * Real.sqrt x < ((⌊Real.sqrt x⌋₊ : ℝ) + 1) * ((⌊Real.sqrt x⌋₊ : ℝ) + 1) :=
      mul_lt_mul'' h1 h1 (Real.sqrt_nonneg x) (Real.sqrt_nonneg x)
    rw [Real.mul_self_sqrt hx] at hmul
    exact_mod_cast hmul

lemma nat_floor_div_eq_div {x : ℝ} (hx : 0 ≤ x) {k : ℕ} (hk : 0 < k) :
    ⌊x / (k : ℝ)⌋₊ = ⌊x⌋₊ / k := by
  have hkR : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  apply le_antisymm
  · rw [Nat.le_div_iff_mul_le hk, Nat.le_floor_iff hx]
    have h1 : (⌊x / (k : ℝ)⌋₊ : ℝ) ≤ x / (k : ℝ) := Nat.floor_le (div_nonneg hx hkR.le)
    have h2 : (⌊x / (k : ℝ)⌋₊ : ℝ) * (k : ℝ) ≤ x := (le_div_iff₀ hkR).mp h1
    exact_mod_cast h2
  · rw [Nat.le_floor_iff (div_nonneg hx hkR.le), le_div_iff₀ hkR]
    have h1 : ⌊x⌋₊ / k * k ≤ ⌊x⌋₊ := Nat.div_mul_le_self ⌊x⌋₊ k
    have h2 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
    have h3 : ((⌊x⌋₊ / k * k : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h1
    push_cast at h3
    linarith

lemma nat_floor_eq_sub_fract {t : ℝ} (ht : 0 ≤ t) :
    (⌊t⌋₊ : ℝ) = t - Int.fract t := by
  have hz : ((⌊t⌋₊ : ℕ) : ℤ) = ⌊t⌋ := by
    symm
    rw [Int.floor_eq_iff]
    constructor
    · exact_mod_cast Nat.floor_le ht
    · exact_mod_cast Nat.lt_floor_add_one t
  rw [Int.fract, ← hz]
  push_cast
  ring

lemma sum_inv_Icc_eq_harmonic (m : ℕ) :
    ∑ k ∈ Icc 1 m, (1 / (k : ℝ)) = (harmonic m : ℝ) := by
  induction m with
  | zero => simp [harmonic]
  | succ m ih =>
    have hnot : m + 1 ∉ Icc 1 m := by simp
    have hins : Icc 1 (m + 1) = insert (m + 1) (Icc 1 m) := by
      ext k; simp only [mem_Icc, mem_insert]; omega
    rw [hins, sum_insert hnot, ih]
    simp only [harmonic, Finset.sum_range_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast,
      one_div, add_comm]

lemma divisorSummatory_add_two_sawtooth {x : ℝ} (hx : 0 ≤ x) :
    divisorSummatory x +
      2 * ∑ k ∈ Icc 1 ⌊Real.sqrt x⌋₊, (Int.fract (x / (k : ℝ)) - 1 / 2) =
      2 * x * (harmonic ⌊Real.sqrt x⌋₊ : ℝ) - (⌊Real.sqrt x⌋₊ : ℝ) -
        (⌊Real.sqrt x⌋₊ : ℝ) * (⌊Real.sqrt x⌋₊ : ℝ) := by
  set m := ⌊Real.sqrt x⌋₊
  have hhyp : (∑ n ∈ Icc 1 ⌊x⌋₊, (n.divisors.card : ℝ)) + (m : ℝ) * (m : ℝ) =
      2 * ∑ k ∈ Icc 1 m, ((⌊x⌋₊ / k : ℕ) : ℝ) := by
    have hnat := hyperbola_nat ⌊x⌋₊
    rw [nat_sqrt_floor_eq_floor_sqrt hx] at hnat
    have hcast : ((∑ n ∈ Icc 1 ⌊x⌋₊, n.divisors.card + m * m : ℕ) : ℝ) =
        ((2 * ∑ a ∈ Icc 1 m, ⌊x⌋₊ / a : ℕ) : ℝ) := by exact_mod_cast hnat
    simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_sum] using hcast
  have hterms : ∑ k ∈ Icc 1 m, ((⌊x⌋₊ / k : ℕ) : ℝ) =
      ∑ k ∈ Icc 1 m, (x / (k : ℝ) - Int.fract (x / (k : ℝ))) := by
    refine sum_congr rfl fun k hk => ?_
    have hkpos : 0 < k := (mem_Icc.mp hk).1
    rw [← nat_floor_div_eq_div hx hkpos, nat_floor_eq_sub_fract (div_nonneg hx (Nat.cast_nonneg k))]
  have hD : divisorSummatory x =
      2 * ∑ k ∈ Icc 1 m, (x / (k : ℝ) - Int.fract (x / (k : ℝ))) - (m : ℝ) * (m : ℝ) := by
    unfold divisorSummatory
    rw [hterms] at hhyp
    linarith
  have hcomb : (∑ k ∈ Icc 1 m, (x / (k : ℝ) - Int.fract (x / (k : ℝ)))) +
      (∑ k ∈ Icc 1 m, (Int.fract (x / (k : ℝ)) - 1 / 2)) =
      x * (harmonic m : ℝ) - (m : ℝ) / 2 := by
    rw [← sum_add_distrib]
    have hsimp : ∑ k ∈ Icc 1 m, (x / (k : ℝ) - Int.fract (x / (k : ℝ)) +
        (Int.fract (x / (k : ℝ)) - 1 / 2)) =
        ∑ k ∈ Icc 1 m, (x * (1 / (k : ℝ)) - 1 / 2) := by
      refine sum_congr rfl fun k _ => ?_
      ring
    rw [hsimp, sum_sub_distrib, ← mul_sum, sum_inv_Icc_eq_harmonic, sum_const,
      Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    ring
  rw [hD]
  linarith

/- ### Section 2: Sharp O(1/N²) Euler-Maclaurin harmonic asymptotic -/

lemma euler_step_bounds {t : ℝ} (ht : 0 < t) :
    0 ≤ 1 / (2 * t) + 1 / (2 * (t + 1)) - (Real.log (t + 1) - Real.log t) ∧
    1 / (2 * t) + 1 / (2 * (t + 1)) - (Real.log (t + 1) - Real.log t) ≤
      1 / t ^ 2 - 1 / (t + 1) ^ 2 := by
  let g : ℝ → ℝ := fun u => (2 * u)⁻¹ + (2 * (u + 1))⁻¹ - (Real.log (u + 1) - Real.log u)
  have hg_deriv : ∀ u ∈ Set.Ioi (0 : ℝ),
      HasDerivAt g (-(1 / (2 * u ^ 2 * (u + 1) ^ 2))) u := by
    intro u hu
    have hu_pos : 0 < u := hu
    have hu0 : u ≠ 0 := ne_of_gt hu_pos
    have hu1 : u + 1 ≠ 0 := by linarith
    have h1 := ((hasDerivAt_id u).const_mul 2).inv (show 2 * u ≠ 0 by positivity)
    have h2 := (((hasDerivAt_id u).add_const 1).const_mul 2).inv
      (show 2 * (u + 1) ≠ 0 by positivity)
    have h3 := ((hasDerivAt_id u).add_const 1).log hu1
    have h4 := (hasDerivAt_id u).log hu0
    have hcomb : HasDerivAt g
        ((-(2 * 1) / (2 * u) ^ 2 + -(2 * 1) / (2 * (u + 1)) ^ 2) - (1 / (u + 1) - 1 / u)) u :=
      (h1.add h2).sub (h3.sub h4)
    have heq : (-(2 * 1) / (2 * u) ^ 2 + -(2 * 1) / (2 * (u + 1)) ^ 2) - (1 / (u + 1) - 1 / u) =
        -(1 / (2 * u ^ 2 * (u + 1) ^ 2)) := by
      field_simp [hu0, hu1]
      ring
    rwa [heq] at hcomb
  have hg_anti : AntitoneOn g (Set.Ioi 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) ?_ ?_ ?_
    · exact fun u hu => (hg_deriv u hu).continuousAt.continuousWithinAt
    · rw [interior_Ioi]
      exact fun u hu => (hg_deriv u hu).differentiableAt.differentiableWithinAt
    · rw [interior_Ioi]
      intro u hu
      have hu_pos : 0 < u := hu
      rw [(hg_deriv u hu).deriv]
      have hpos : 0 < 2 * u ^ 2 * (u + 1) ^ 2 := by positivity
      linarith [one_div_pos.mpr hpos]
  have hg_tendsto : Tendsto g atTop (𝓝 0) := by
    have h1 : Tendsto (fun u : ℝ => (2 * u)⁻¹) atTop (𝓝 0) := by
      have hmul : Tendsto (fun u : ℝ => (2 : ℝ) * u) atTop atTop :=
        Tendsto.const_mul_atTop (by norm_num) tendsto_id
      exact tendsto_inv_atTop_zero.comp hmul
    have h2 : Tendsto (fun u : ℝ => (2 * (u + 1))⁻¹) atTop (𝓝 0) := by
      have hmul : Tendsto (fun u : ℝ => (2 : ℝ) * (u + 1)) atTop atTop :=
        Tendsto.const_mul_atTop (by norm_num) (tendsto_atTop_add_const_right atTop 1 tendsto_id)
      exact tendsto_inv_atTop_zero.comp hmul
    have h3 : Tendsto (fun u : ℝ => Real.log (u + 1) - Real.log u) atTop (𝓝 0) :=
      Real.tendsto_log_comp_add_sub_log 1
    simpa [g] using (h1.add h2).sub h3
  have hlow : 0 ≤ g t :=
    le_of_tendsto hg_tendsto
      (Filter.eventually_atTop.mpr ⟨t, fun y hy => hg_anti ht (lt_of_lt_of_le ht hy) hy⟩)
  let h : ℝ → ℝ := fun u => (u * u)⁻¹ - ((u + 1) * (u + 1))⁻¹ - g u
  have hh_deriv : ∀ u ∈ Set.Ioi (0 : ℝ),
      HasDerivAt h (-(11 * u ^ 2 + 11 * u + 4) / (2 * u ^ 3 * (u + 1) ^ 3)) u := by
    intro u hu
    have hu_pos : 0 < u := hu
    have hu0 : u ≠ 0 := ne_of_gt hu_pos
    have hu1 : u + 1 ≠ 0 := by linarith
    have h1 := ((hasDerivAt_id u).mul (hasDerivAt_id u)).inv (show u * u ≠ 0 by positivity)
    have h2 := (((hasDerivAt_id u).add_const 1).mul ((hasDerivAt_id u).add_const 1)).inv
      (show (u + 1) * (u + 1) ≠ 0 by positivity)
    have hcomb : HasDerivAt h
        ((-(1 * u + u * 1) / (u * u) ^ 2 -
          -(1 * (u + 1) + (u + 1) * 1) / ((u + 1) * (u + 1)) ^ 2) -
          -(1 / (2 * u ^ 2 * (u + 1) ^ 2))) u :=
      (h1.sub h2).sub (hg_deriv u hu)
    have heq : (-(1 * u + u * 1) / (u * u) ^ 2 -
          -(1 * (u + 1) + (u + 1) * 1) / ((u + 1) * (u + 1)) ^ 2) -
          -(1 / (2 * u ^ 2 * (u + 1) ^ 2)) =
        -(11 * u ^ 2 + 11 * u + 4) / (2 * u ^ 3 * (u + 1) ^ 3) := by
      field_simp [hu0, hu1]
      ring
    rwa [heq] at hcomb
  have hh_anti : AntitoneOn h (Set.Ioi 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) ?_ ?_ ?_
    · exact fun u hu => (hh_deriv u hu).continuousAt.continuousWithinAt
    · rw [interior_Ioi]
      exact fun u hu => (hh_deriv u hu).differentiableAt.differentiableWithinAt
    · rw [interior_Ioi]
      intro u hu
      have hu_pos : 0 < u := hu
      rw [(hh_deriv u hu).deriv]
      have hnum : 0 ≤ 11 * u ^ 2 + 11 * u + 4 := by positivity
      have hden : 0 < 2 * u ^ 3 * (u + 1) ^ 3 := by positivity
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) hden.le
  have hh_tendsto : Tendsto h atTop (𝓝 0) := by
    have h1 : Tendsto (fun u : ℝ => (u * u)⁻¹) atTop (𝓝 0) := by
      have hsq : Tendsto (fun u : ℝ => u * u) atTop atTop := by
        simpa [sq] using (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp (tendsto_id (α := ℝ))
      exact tendsto_inv_atTop_zero.comp hsq
    have h2 : Tendsto (fun u : ℝ => ((u + 1) * (u + 1))⁻¹) atTop (𝓝 0) := by
      have hsq_pow : Tendsto (fun u : ℝ => (u + 1) ^ 2) atTop atTop :=
        (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp
          (tendsto_atTop_add_const_right atTop 1 (tendsto_id (α := ℝ)))
      have hsq : Tendsto (fun u : ℝ => (u + 1) * (u + 1)) atTop atTop := by
        simpa only [sq] using hsq_pow
      exact tendsto_inv_atTop_zero.comp hsq
    simpa [h] using (h1.sub h2).sub hg_tendsto
  have hup : 0 ≤ h t :=
    le_of_tendsto hh_tendsto
      (Filter.eventually_atTop.mpr ⟨t, fun y hy => hh_anti ht (lt_of_lt_of_le ht hy) hy⟩)
  simp only [one_div, sq]
  exact ⟨hlow, by dsimp only [h] at hup; linarith⟩

lemma harmonic_euler_maclaurin {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ eulerMascheroniConstant - ((harmonic N : ℝ) - Real.log N - 1 / (2 * (N : ℝ))) ∧
    eulerMascheroniConstant - ((harmonic N : ℝ) - Real.log N - 1 / (2 * (N : ℝ))) ≤
      1 / (N : ℝ) ^ 2 := by
  let a : ℕ → ℝ := fun n => (harmonic n : ℝ) - Real.log n - 1 / (2 * (n : ℝ))
  have hstep : ∀ n : ℕ, 1 ≤ n →
      0 ≤ a (n + 1) - a n ∧ a (n + 1) - a n ≤ 1 / (n : ℝ) ^ 2 - 1 / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    intro n hn
    have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
    have hharm : (harmonic (n + 1) : ℝ) = (harmonic n : ℝ) + 1 / ((n : ℝ) + 1) := by
      simp only [harmonic, Finset.sum_range_succ]
      push_cast
      ring
    have hdiff : a (n + 1) - a n =
        1 / (2 * (n : ℝ)) + 1 / (2 * ((n : ℝ) + 1)) -
          (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) := by
      dsimp only [a]
      rw [hharm, Nat.cast_add, Nat.cast_one]
      have hn1 : (n : ℝ) + 1 ≠ 0 := by linarith
      field_simp [hnR.ne', hn1]
      ring
    rw [hdiff, Nat.cast_add, Nat.cast_one]
    exact euler_step_bounds hnR
  have htele : ∀ r : ℕ,
      0 ≤ a (N + r) - a N ∧ a (N + r) - a N ≤ 1 / (N : ℝ) ^ 2 := by
    intro r
    suffices hstrong : 0 ≤ a (N + r) - a N ∧
        a (N + r) - a N ≤ 1 / (N : ℝ) ^ 2 - 1 / ((N + r : ℕ) : ℝ) ^ 2 by
      have hnr : (0 : ℝ) ≤ 1 / ((N + r : ℕ) : ℝ) ^ 2 := by positivity
      exact ⟨hstrong.1, by linarith⟩
    induction r with
    | zero => simp
    | succ r ih =>
      have hs := hstep (N + r) (by omega)
      have hcast : N + (r + 1) = (N + r) + 1 := by omega
      rw [hcast]
      constructor <;> linarith
  have htend : Tendsto (fun r : ℕ => a (N + r)) atTop (𝓝 eulerMascheroniConstant) := by
    have ha_tend : Tendsto a atTop (𝓝 eulerMascheroniConstant) := by
      have hinv : Tendsto (fun n : ℕ => 1 / (2 * (n : ℝ))) atTop (𝓝 0) := by
        have hmul : Tendsto (fun n : ℕ => (2 : ℝ) * (n : ℝ)) atTop atTop :=
          Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
        have hcomp : Tendsto (fun n : ℕ => (2 * (n : ℝ))⁻¹) atTop (𝓝 0) :=
          tendsto_inv_atTop_zero.comp hmul
        simpa only [one_div] using hcomp
      simpa [a] using Real.tendsto_harmonic_sub_log.sub hinv
    have hcomm : (fun r : ℕ => a (N + r)) = a ∘ (fun r : ℕ => r + N) := by
      ext r
      simp [add_comm]
    rw [hcomm]
    exact ha_tend.comp (tendsto_add_atTop_nat N)
  have htend_sub : Tendsto (fun r : ℕ => a (N + r) - a N) atTop (𝓝 (eulerMascheroniConstant - a N)) :=
    htend.sub tendsto_const_nhds
  exact ⟨ge_of_tendsto htend_sub (Eventually.of_forall fun r => (htele r).1),
    le_of_tendsto htend_sub (Eventually.of_forall fun r => (htele r).2)⟩

/- ### Section 3: Exact cancellation of O(√x) terms to O(1) -/

lemma log_one_sub_bounds {u : ℝ} (hu1 : u ≤ 1 / 2) :
    -u - 2 * u ^ 2 ≤ Real.log (1 - u) ∧ Real.log (1 - u) ≤ -u := by
  have h1u : 0 < 1 - u := by linarith
  constructor
  · have hinv := Real.log_le_sub_one_of_pos (one_div_pos.mpr h1u)
    rw [one_div, Real.log_inv] at hinv
    have hdiff : (1 - u)⁻¹ - 1 = u / (1 - u) := by
      field_simp [h1u.ne']
      ring
    rw [hdiff] at hinv
    have hbound : u / (1 - u) ≤ u + 2 * u ^ 2 := by
      rw [div_le_iff₀ h1u]
      nlinarith
    linarith
  · have h := Real.log_le_sub_one_of_pos h1u
    linarith

lemma divisorError_add_two_sawtooth_bound {x : ℝ} (hx : 4 ≤ x) :
    |divisorError x + 2 * ∑ k ∈ Icc 1 ⌊Real.sqrt x⌋₊, (Int.fract (x / (k : ℝ)) - 1 / 2)| ≤ 12 := by
  have hx0 : 0 ≤ x := by linarith
  have hx_pos : 0 < x := by linarith
  have hsqrt_ge2 : 2 ≤ Real.sqrt x := by
    have : (2 : ℝ) = Real.sqrt 4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [this]
    exact Real.sqrt_le_sqrt hx
  set m := ⌊Real.sqrt x⌋₊
  have hm2 : 2 ≤ m := by
    have : (2 : ℕ) ≤ ⌊Real.sqrt x⌋₊ := (Nat.le_floor_iff (Real.sqrt_nonneg x)).mpr (by exact_mod_cast hsqrt_ge2)
    exact this
  have hm1 : 1 ≤ m := by omega
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have hm_ge2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
  set θ := Real.sqrt x - (m : ℝ)
  have hθ0 : 0 ≤ θ := sub_nonneg.mpr (Nat.floor_le (Real.sqrt_nonneg x))
  have hθ1 : θ < 1 := sub_lt_iff_lt_add'.mpr (Nat.lt_floor_add_one (Real.sqrt x))
  have hsqrt_pos : 0 < Real.sqrt x := by linarith
  have hsqrt_sq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0
  have hm_eq : (m : ℝ) = Real.sqrt x - θ := by dsimp [θ]; ring
  have hx_sub_msq : x - (m : ℝ) * (m : ℝ) = 2 * θ * Real.sqrt x - θ ^ 2 := by
    rw [hm_eq]
    nlinarith
  have hx_div_m : x / (m : ℝ) - (m : ℝ) = 2 * θ + θ ^ 2 / (m : ℝ) := by
    have hnum : x - (m : ℝ) * (m : ℝ) = 2 * θ * (m : ℝ) + θ ^ 2 := by
      have : Real.sqrt x = (m : ℝ) + θ := by dsimp [θ]; ring
      nlinarith
    field_simp [hm_pos.ne']
    linarith
  have hlog_eq : 2 * x * Real.log (m : ℝ) - x * Real.log x =
      2 * x * Real.log (1 - θ / Real.sqrt x) := by
    have hlogx : Real.log x = 2 * Real.log (Real.sqrt x) := by
      conv_lhs => rw [← hsqrt_sq]
      rw [Real.log_mul hsqrt_pos.ne' hsqrt_pos.ne']
      ring
    have hratio : (m : ℝ) / Real.sqrt x = 1 - θ / Real.sqrt x := by
      rw [hm_eq]
      field_simp [hsqrt_pos.ne']
    rw [hlogx, ← hratio, Real.log_div hm_pos.ne' hsqrt_pos.ne']
    ring
  have hu1 : θ / Real.sqrt x ≤ 1 / 2 := by
    rw [div_le_iff₀ hsqrt_pos]
    linarith
  have hlog_b := log_one_sub_bounds hu1
  have hlog_term_low : -4 * θ ^ 2 ≤ 2 * x * Real.log (m : ℝ) - x * Real.log x + 2 * θ * Real.sqrt x := by
    rw [hlog_eq]
    have hmul := mul_le_mul_of_nonneg_left hlog_b.1 (show (0 : ℝ) ≤ 2 * x by linarith)
    have hsimp : 2 * x * (-(θ / Real.sqrt x) - 2 * (θ / Real.sqrt x) ^ 2) =
        -2 * θ * Real.sqrt x - 4 * θ ^ 2 := by
      field_simp [hsqrt_pos.ne']
      rw [Real.sq_sqrt hx0]
      ring
    linarith only [hmul, hsimp]
  have hlog_term_up : 2 * x * Real.log (m : ℝ) - x * Real.log x + 2 * θ * Real.sqrt x ≤ 0 := by
    rw [hlog_eq]
    have hmul := mul_le_mul_of_nonneg_left hlog_b.2 (show (0 : ℝ) ≤ 2 * x by linarith)
    have hsimp : 2 * x * -(θ / Real.sqrt x) = -2 * θ * Real.sqrt x := by
      field_simp [hsqrt_pos.ne']
      rw [Real.sq_sqrt hx0]
      ring
    linarith only [hmul, hsimp]
  have hem := harmonic_euler_maclaurin hm1
  set δ := eulerMascheroniConstant - ((harmonic m : ℝ) - Real.log (m : ℝ) - 1 / (2 * (m : ℝ)))
  have hδ0 : 0 ≤ δ := hem.1
  have hδ_up : δ ≤ 1 / (m : ℝ) ^ 2 := hem.2
  have hx_le_msq : x ≤ 9 / 4 * (m : ℝ) ^ 2 := by
    have hlt : Real.sqrt x ≤ (m : ℝ) + 1 := by linarith only [hθ1, hm_eq]
    have hm_le : (m : ℝ) + 1 ≤ 3 / 2 * (m : ℝ) := by linarith only [hm_ge2]
    have hsq_le : Real.sqrt x ≤ 3 / 2 * (m : ℝ) := le_trans hlt hm_le
    nlinarith only [hsq_le, hsqrt_sq, hsqrt_pos]
  have h2xδ_nonneg : 0 ≤ 2 * x * δ := by positivity
  have h2xδ_le : 2 * x * δ ≤ 9 / 2 := by
    calc 2 * x * δ ≤ 2 * (9 / 4 * (m : ℝ) ^ 2) * (1 / (m : ℝ) ^ 2) := by
          gcongr
      _ = 9 / 2 := by field_simp [hm_pos.ne']; ring
  have hE_eq : divisorError x + 2 * ∑ k ∈ Icc 1 m, (Int.fract (x / (k : ℝ)) - 1 / 2) =
      (2 * x * Real.log (m : ℝ) - x * Real.log x + 2 * θ * Real.sqrt x) -
        θ ^ 2 + 2 * θ + θ ^ 2 / (m : ℝ) - 2 * x * δ := by
    have hds := divisorSummatory_add_two_sawtooth hx0
    have hharm_eq : (harmonic m : ℝ) = Real.log (m : ℝ) + eulerMascheroniConstant +
        1 / (2 * (m : ℝ)) - δ := by
      dsimp only [δ]; ring
    have h2xm : 2 * x * (1 / (2 * (m : ℝ))) - (m : ℝ) = x / (m : ℝ) - (m : ℝ) := by
      field_simp [hm_pos.ne']
    have hstep1 : divisorError x + 2 * ∑ k ∈ Icc 1 m, (Int.fract (x / (k : ℝ)) - 1 / 2) =
        (divisorSummatory x + 2 * ∑ k ∈ Icc 1 m, (Int.fract (x / (k : ℝ)) - 1 / 2)) -
          x * Real.log x - (2 * eulerMascheroniConstant - 1) * x := by
      unfold divisorError; ring
    rw [hstep1, hds, hharm_eq]
    linarith only [hx_sub_msq, hx_div_m, h2xm]
  rw [hE_eq]
  have hθsq_nonneg : 0 ≤ θ ^ 2 := sq_nonneg θ
  have hθsq_le : θ ^ 2 ≤ 1 := by nlinarith only [hθ0, hθ1]
  have hθdiv_nonneg : 0 ≤ θ ^ 2 / (m : ℝ) := div_nonneg hθsq_nonneg hm_pos.le
  have hθdiv_le : θ ^ 2 / (m : ℝ) ≤ 1 / 2 := by
    rw [div_le_iff₀ hm_pos]
    linarith only [hθsq_le, hm_ge2]
  rw [abs_le]
  constructor <;> linarith only [hlog_term_low, hlog_term_up, hθ0, hθ1, hθsq_nonneg, hθsq_le,
    hθdiv_nonneg, hθdiv_le, h2xδ_nonneg, h2xδ_le]

/- ### Section 4: Main reduction theorem -/

theorem main : H1 → H2 → type_of% @DirichletDivisorProblem.dirichlet_divisor_problem := by
  intro h1 h2 ε hε
  let saw : ℝ → ℝ := fun x =>
    (-2 : ℝ) * ∑ k ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊, (Int.fract (x / (k : ℝ)) - 1 / 2)
  let vorSum : ℝ → ℝ := fun x =>
    ∑ n ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊,
      ((n.divisors.card : ℝ) / (n : ℝ) ^ ((3 : ℝ) / 4)) *
        Real.cos (4 * Real.pi * Real.sqrt ((n : ℝ) * x) - Real.pi / 4)
  let vorTerm : ℝ → ℝ := fun x => (x ^ ((1 : ℝ) / 4) / (Real.pi * Real.sqrt 2)) * vorSum x
  have hE : (fun x => divisorError x - saw x) =O[atTop] fun x => x ^ ((1 : ℝ) / 4 + ε) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨12, Filter.eventually_atTop.mpr ⟨4, fun x hx => ?_⟩⟩
    have hb := divisorError_add_two_sawtooth_bound hx
    have hsub_eq : divisorError x - saw x =
        divisorError x + 2 * ∑ k ∈ Icc 1 ⌊Real.sqrt x⌋₊, (Int.fract (x / (k : ℝ)) - 1 / 2) := by
      dsimp only [saw]; ring
    rw [Real.norm_eq_abs, Real.norm_eq_abs, hsub_eq]
    have hx1 : (1 : ℝ) ≤ x := by linarith
    have hexp_pos : (0 : ℝ) ≤ (1 : ℝ) / 4 + ε := by linarith
    have hrpow_ge1 : (1 : ℝ) ≤ x ^ ((1 : ℝ) / 4 + ε) := Real.one_le_rpow hx1 hexp_pos
    have habs_rpow : |x ^ ((1 : ℝ) / 4 + ε)| = x ^ ((1 : ℝ) / 4 + ε) :=
      abs_of_nonneg (le_trans (by norm_num) hrpow_ge1)
    rw [habs_rpow]
    linarith
  have h1' : (fun x => saw x - vorTerm x) =O[atTop] fun x => x ^ ((1 : ℝ) / 4 + ε) := h1 ε hε
  have hvor : vorTerm =O[atTop] fun x => x ^ ((1 : ℝ) / 4 + ε) := by
    have h2' : vorSum =O[atTop] fun x => x ^ ε := h2 ε hε
    rw [Asymptotics.isBigO_iff] at h2' ⊢
    obtain ⟨C, hC⟩ := h2'
    rw [Filter.eventually_atTop] at hC
    obtain ⟨M, hM⟩ := hC
    have hden_pos : 0 < Real.pi * Real.sqrt 2 := mul_pos Real.pi_pos (Real.sqrt_pos.mpr (by norm_num))
    refine ⟨|C| / (Real.pi * Real.sqrt 2), Filter.eventually_atTop.mpr ⟨max M 1, fun x hx => ?_⟩⟩
    have hxM : M ≤ x := le_trans (le_max_left M 1) hx
    have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_right M 1) hx
    have hx_pos : 0 < x := by linarith
    have hbound := hM x hxM
    have hC_le : C ≤ |C| := le_abs_self C
    have hrpow_pos1 : 0 < x ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hx_pos _
    have hrpow_pos2 : 0 < x ^ ε := Real.rpow_pos_of_pos hx_pos _
    have hrpow_pos3 : 0 < x ^ ((1 : ℝ) / 4 + ε) := Real.rpow_pos_of_pos hx_pos _
    have hnorm_vor : ‖vorTerm x‖ = (x ^ ((1 : ℝ) / 4) / (Real.pi * Real.sqrt 2)) * ‖vorSum x‖ := by
      dsimp only [vorTerm]
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos (div_pos hrpow_pos1 hden_pos)]
    rw [hnorm_vor, Real.norm_eq_abs (x ^ ((1 : ℝ) / 4 + ε)), abs_of_pos hrpow_pos3]
    rw [Real.norm_eq_abs (x ^ ε), abs_of_pos hrpow_pos2] at hbound
    calc (x ^ ((1 : ℝ) / 4) / (Real.pi * Real.sqrt 2)) * ‖vorSum x‖
        ≤ (x ^ ((1 : ℝ) / 4) / (Real.pi * Real.sqrt 2)) * (|C| * x ^ ε) := by
          gcongr
          exact le_trans hbound (mul_le_mul_of_nonneg_right hC_le hrpow_pos2.le)
      _ = (|C| / (Real.pi * Real.sqrt 2)) * (x ^ ((1 : ℝ) / 4) * x ^ ε) := by ring
      _ = (|C| / (Real.pi * Real.sqrt 2)) * x ^ ((1 : ℝ) / 4 + ε) := by
          rw [← Real.rpow_add hx_pos]
  have hsum_bigO : (fun x => (divisorError x - saw x) + (saw x - vorTerm x) + vorTerm x)
      =O[atTop] fun x => x ^ ((1 : ℝ) / 4 + ε) := (hE.add h1').add hvor
  have hfun_eq : (fun x => (divisorError x - saw x) + (saw x - vorTerm x) + vorTerm x) =
      divisorError := by
    ext x; ring
  rwa [hfun_eq] at hsum_bigO

end OMA.R_DirichletDivisorProblem_dirichlet_divisor_problem_R1
