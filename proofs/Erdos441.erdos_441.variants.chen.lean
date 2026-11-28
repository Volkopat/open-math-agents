import FormalConjectures.ErdosProblems.«441»

-- Problem: Erdős Problem 441 — chen
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/441.lean:120 (declaration Erdos441.erdos_441.variants.chen)
-- Credit: @fecheteluca (the owner of the agent is credited as the solver)

/-!
# Chen's theorem: `g(N) ~ √(9N/8)`

`g N` is the largest size of a set `A ⊆ [1, N]` all of whose pairwise least common multiples are
at most `N` (an admissible set).  This file proves `g N ~ √(9N/8)` by an elementary argument.

* Lower bound (§1): all integers up to `√(N/2)` together with the even integers up to `√(2N)`
  form an admissible set of size at least `√(9N/8) - 2`.
* Upper bound (§2–§7): for every `ε > 0` and all large `N`, every admissible set has at most
  `(3√2/4 + ε) √N` elements.  Fix a window length `w ≈ √N / n` and let `Ψ(τ)` be the largest
  number of elements of `A` in a window `(u, u + w]` with `u ≥ τ w`; then `Ψ` is antitone,
  `|A| ≤ ∑_{τ < m} Ψ(τ) + N / (m w)`, and `Ψ(τ) ≤ (w + 1) / 2` once `τ w ≥ √N`.
  The pattern lemma (§3) says that windows at positions `X_c` with `(c - c') N ≤ X_c X_c'` for
  `c' < c` contain together at most `w + (lower order)` elements of `A`: two elements `x + a`,
  `y + a` at the same offset in two such windows have `gcd ∣ y - x`, and after moving the windows
  to prescribed residues modulo a highly divisible `Q` this forces a large prime factor of a
  bounded number, which is rare.  Applying it to the thresholds
  `θ(j, c) = ⌈c n² / j⌉` (`c > 0`) and `max(⌈|c| n² / j⌉, (|c| + 1) j)` (`c ≤ 0`), `1 ≤ j ≤ n`,
  gives `∑_c Ψ(θ(j, c)) ≤ w + (lower order)` for each `j` (§4).  A counting inequality,
  `#{(j, c) : θ(j, c) ≤ τ} ≥ τ` for `τ < n` and `≥ τ - n (3√2/2 - 2) - 1` afterwards (§4), and
  Abel summation (§5) turn the `n` row bounds into
  `∑_τ Ψ(τ) ≤ n w + n (3√2/2 - 2) (w + 1) / 2 + (lower order)` (§6), which is
  `(3√2/4) √N + o(√N)` (§7).
-/

namespace E441C

open Finset Asymptotics

/-! ## 0. Basics -/

/-- Admissible sets: subsets of `[1, N]` whose pairwise least common multiples are at most `N`. -/
def Adm (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧ ∀ a ∈ A, ∀ b ∈ A, Nat.lcm a b ≤ N

lemma g_ge {N : ℕ} {A : Finset ℕ} (hA : Adm N A) : A.card ≤ Erdos441.g N := by
  unfold Erdos441.g
  apply le_csSup
  · refine ⟨N, ?_⟩
    rintro k ⟨B, hB, -, rfl⟩
    simpa using Finset.card_le_card hB
  · exact ⟨A, hA.1, hA.2, rfl⟩

lemma g_attained (N : ℕ) : ∃ A, Adm N A ∧ A.card = Erdos441.g N := by
  have hne : {k | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
      (∀ a ∈ A, ∀ b ∈ A, Nat.lcm a b ≤ N) ∧ A.card = k}.Nonempty :=
    ⟨0, ∅, by simp, by simp, by simp⟩
  have hbd : BddAbove {k | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
      (∀ a ∈ A, ∀ b ∈ A, Nat.lcm a b ≤ N) ∧ A.card = k} := by
    refine ⟨N, ?_⟩
    rintro k ⟨B, hB, -, rfl⟩
    simpa using Finset.card_le_card hB
  obtain ⟨A, h1, h2, h3⟩ := Nat.sSup_mem hne hbd
  exact ⟨A, ⟨h1, h2⟩, h3⟩

/-- The constant `3 / √2 - 2`, written without a square root in a denominator. -/
noncomputable def E0 : ℝ := 3 * √2 / 2 - 2

lemma sqrt2_sq : √(2:ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)

lemma sqrt2_lb : (1.4134:ℝ) ≤ √2 := by
  apply Real.le_sqrt_of_sq_le
  norm_num

lemma sqrt2_ub : √(2:ℝ) ≤ 1.4143 := by
  rw [Real.sqrt_le_left (by norm_num)]
  norm_num

lemma E0_lb : (0.12:ℝ) ≤ E0 := by
  unfold E0
  have := sqrt2_lb
  linarith

lemma E0_ub : E0 ≤ (0.13:ℝ) := by
  unfold E0
  have := sqrt2_ub
  linarith

lemma sqrt98 (x : ℝ) : √(9 / 8 * x) = 3 * √2 / 4 * √x := by
  rw [Real.sqrt_mul (by norm_num)]
  congr 1
  rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by positivity)]
  have := sqrt2_sq
  nlinarith

/-- Reduction of the asymptotic statement to a lower and an upper bound. -/
theorem final
    (LB : ∀ N : ℕ, ∃ A, Adm N A ∧ √(9 / 8 * (N:ℝ)) - 2 ≤ A.card)
    (UB : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N ≥ N0, ∀ A, Adm N A →
      (A.card : ℝ) ≤ (3 * √2 / 4 + ε) * √(N:ℝ)) :
    (fun N : ℕ ↦ (Erdos441.g N : ℝ)) ~[Filter.atTop] fun N ↦ √(9 / 8 * N) := by
  rw [Asymptotics.IsEquivalent, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨N0, hN0⟩ := UB c hc
  obtain ⟨N1, hN1⟩ := exists_nat_ge ((2 / c) ^ 2)
  rw [Filter.eventually_atTop]
  refine ⟨max N0 N1, fun N hN => ?_⟩
  have hNN0 : N0 ≤ N := le_trans (le_max_left _ _) hN
  have hNN1 : N1 ≤ N := le_trans (le_max_right _ _) hN
  have hs : 2 / c ≤ √(N:ℝ) := by
    apply Real.le_sqrt_of_sq_le
    exact le_trans hN1 (by exact_mod_cast hNN1)
  have hs2 : 2 ≤ c * √(N:ℝ) := by
    have := (div_le_iff₀ hc).mp hs
    linarith
  have h34 : (1:ℝ) ≤ 3 * √2 / 4 := by
    have := sqrt2_lb
    linarith
  have hsN : (0:ℝ) ≤ √(N:ℝ) := Real.sqrt_nonneg _
  obtain ⟨A, hA, hAc⟩ := g_attained N
  obtain ⟨B, hB, hBc⟩ := LB N
  have hBg : (B.card : ℝ) ≤ Erdos441.g N := by exact_mod_cast g_ge hB
  have hup := hN0 N hNN0 A hA
  rw [hAc] at hup
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  rw [sqrt98] at hBc ⊢
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ 3 * √2 / 4 * √(N:ℝ)), abs_le]
  constructor
  · nlinarith
  · nlinarith

/-! ## 1. Lower bound: Erdős' construction -/

lemma lower_construction (N : ℕ) : ∃ A, Adm N A ∧ √(9 / 8 * (N:ℝ)) - 2 ≤ A.card := by
  obtain ⟨a, ha⟩ : ∃ a, a = Nat.sqrt (N / 2) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = Nat.sqrt (2 * N) := ⟨_, rfl⟩
  have ha2 : a * a ≤ N / 2 := by rw [ha]; exact Nat.sqrt_le _
  have hb2 : b * b ≤ 2 * N := by rw [hb]; exact Nat.sqrt_le _
  have ha3 : N / 2 < (a + 1) * (a + 1) := by rw [ha]; exact Nat.lt_succ_sqrt _
  have hb3 : 2 * N < (b + 1) * (b + 1) := by rw [hb]; exact Nat.lt_succ_sqrt _
  have hab : a ≤ b := by rw [ha, hb]; exact Nat.sqrt_le_sqrt (by omega)
  have hN2 : N / 2 * 2 ≤ N := Nat.div_mul_le_self N 2
  have habN : a * b ≤ N := by
    rw [← Nat.mul_self_le_mul_self_iff]
    calc a * b * (a * b) = (a * a) * (b * b) := by ring
      _ ≤ (N / 2) * (2 * N) := Nat.mul_le_mul ha2 hb2
      _ = (N / 2 * 2) * N := by ring
      _ ≤ N * N := Nat.mul_le_mul_right N hN2
  obtain ⟨E, hEdef⟩ : ∃ E : Finset ℕ, E = (Finset.Ioc (a / 2) (b / 2)).image (fun i => 2 * i) :=
    ⟨_, rfl⟩
  have hE : ∀ x ∈ E, ∃ i, x = 2 * i ∧ a < x ∧ x ≤ b ∧ 0 < i := by
    intro x hx
    rw [hEdef] at hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_Ioc] at hi
    exact ⟨i, rfl, by omega, by omega, by omega⟩
  have hlow : ∀ x ∈ Finset.Icc 1 a, 1 ≤ x ∧ x ≤ a := fun x hx => Finset.mem_Icc.mp hx
  have key : ∀ x y : ℕ, 0 < x → 0 < y → x * y ≤ N → Nat.lcm x y ≤ N := by
    intro x y hx hy hxy
    exact le_trans (Nat.le_of_dvd (Nat.mul_pos hx hy) (Nat.lcm_dvd_mul x y)) hxy
  refine ⟨Finset.Icc 1 a ∪ E, ⟨?_, ?_⟩, ?_⟩
  · intro x hx
    rw [Finset.mem_Icc]
    rcases Finset.mem_union.mp hx with h | h
    · obtain ⟨h1, h2⟩ := hlow x h
      refine ⟨h1, ?_⟩
      calc x ≤ a := h2
        _ ≤ a * a := Nat.le_mul_self a
        _ ≤ N / 2 := ha2
        _ ≤ N := Nat.div_le_self N 2
    · obtain ⟨i, rfl, h1, h2, h3⟩ := hE x h
      refine ⟨by omega, ?_⟩
      have h4 := Nat.mul_le_mul h2 h2
      have h5 := Nat.le_mul_self i
      nlinarith
  · intro x hx y hy
    rcases Finset.mem_union.mp hx with h | h <;> rcases Finset.mem_union.mp hy with h' | h'
    · obtain ⟨h1, h2⟩ := hlow x h
      obtain ⟨h3, h4⟩ := hlow y h'
      apply key x y h1 h3
      calc x * y ≤ a * a := Nat.mul_le_mul h2 h4
        _ ≤ N / 2 := ha2
        _ ≤ N := Nat.div_le_self N 2
    · obtain ⟨h1, h2⟩ := hlow x h
      obtain ⟨i, rfl, h3, h4, h5⟩ := hE y h'
      apply key x (2 * i) h1 (by omega)
      exact le_trans (Nat.mul_le_mul h2 h4) habN
    · obtain ⟨i, rfl, h3, h4, h5⟩ := hE x h
      obtain ⟨h1, h2⟩ := hlow y h'
      apply key (2 * i) y (by omega) h1
      calc 2 * i * y ≤ b * a := Nat.mul_le_mul h4 h2
        _ = a * b := Nat.mul_comm _ _
        _ ≤ N := habN
    · obtain ⟨i, rfl, h3, h4, h5⟩ := hE x h
      obtain ⟨j, rfl, h6, h7, h8⟩ := hE y h'
      rw [Nat.lcm_mul_left]
      have h9 : Nat.lcm i j ≤ i * j := Nat.le_of_dvd (Nat.mul_pos h5 h8) (Nat.lcm_dvd_mul i j)
      have h10 : (2 * i) * (2 * j) ≤ b * b := Nat.mul_le_mul h4 h7
      nlinarith
  · have hdisj : Disjoint (Finset.Icc 1 a) E := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨h1, h2⟩ := hlow x hx
      obtain ⟨i, -, h3, -, -⟩ := hE x hx'
      omega
    have hcardE : E.card = b / 2 - a / 2 := by
      rw [hEdef, Finset.card_image_of_injective _ (fun i j hij => by simpa using hij)]
      simp
    have hcard : (Finset.Icc 1 a ∪ E).card = a + (b / 2 - a / 2) := by
      rw [Finset.card_union_of_disjoint hdisj, hcardE]
      simp
    have hnat : a + b ≤ 2 * (Finset.Icc 1 a ∪ E).card + 1 := by
      rw [hcard]
      omega
    have hreal : (a:ℝ) + b ≤ 2 * ((Finset.Icc 1 a ∪ E).card : ℝ) + 1 := by exact_mod_cast hnat
    have hs2 : √(N:ℝ) * √(N:ℝ) = N := Real.mul_self_sqrt (Nat.cast_nonneg N)
    have hsa : √2 / 2 * √(N:ℝ) ≤ a + 1 := by
      rw [mul_self_le_mul_self_iff (by positivity) (by positivity)]
      have e : √2 / 2 * √(N:ℝ) * (√2 / 2 * √(N:ℝ)) = (√2 * √2) * (√(N:ℝ) * √(N:ℝ)) / 4 := by
        ring
      rw [e, sqrt2_sq, hs2]
      have h1 : (N:ℝ) ≤ 2 * (((a + 1) * (a + 1) : ℕ) : ℝ) := by
        exact_mod_cast (by omega : N ≤ 2 * ((a + 1) * (a + 1)))
      push_cast at h1
      linarith
    have hsb : √2 * √(N:ℝ) ≤ b + 1 := by
      rw [mul_self_le_mul_self_iff (by positivity) (by positivity)]
      have e : √2 * √(N:ℝ) * (√2 * √(N:ℝ)) = (√2 * √2) * (√(N:ℝ) * √(N:ℝ)) := by ring
      rw [e, sqrt2_sq, hs2]
      have h1 : 2 * (N:ℝ) ≤ (((b + 1) * (b + 1) : ℕ) : ℝ) := by exact_mod_cast hb3.le
      push_cast at h1
      linarith
    rw [sqrt98]
    linarith

/-! ## 2. Tail bound, window counts, envelope -/

/-- For `a < b` in an admissible set, `a * b ≤ (b - a) * N`. -/
lemma adm_gap {N : ℕ} {A : Finset ℕ} (hA : Adm N A) {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A)
    (hab : a < b) : a * b ≤ (b - a) * N := by
  have hl := hA.2 a ha b hb
  have hg : Nat.gcd a b ∣ b - a := Nat.dvd_sub (Nat.gcd_dvd_right a b) (Nat.gcd_dvd_left a b)
  have hg2 : Nat.gcd a b ≤ b - a := Nat.le_of_dvd (by omega) hg
  calc a * b = Nat.gcd a b * Nat.lcm a b := (Nat.gcd_mul_lcm a b).symm
    _ ≤ (b - a) * N := Nat.mul_le_mul hg2 hl

lemma adm_div_lt {N : ℕ} {A : Finset ℕ} (hA : Adm N A) {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A)
    (hab : a < b) : N / b < N / a := by
  have h := adm_gap hA ha hb hab
  have ha0 : 0 < a := (Finset.mem_Icc.mp (hA.1 ha)).1
  have hb0 : 0 < b := by omega
  rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le ha0]
  have h1 : N / b * b ≤ N := Nat.div_mul_le_self N b
  apply Nat.le_of_mul_le_mul_right _ hb0
  have h2 : (b - a) * N + a * N = b * N := by
    rw [← Nat.add_mul]
    congr 1
    omega
  calc (N / b + 1) * a * b = (N / b * b) * a + a * b := by ring
    _ ≤ N * a + (b - a) * N := Nat.add_le_add (Nat.mul_le_mul_right a h1) h
    _ = N * b := by rw [Nat.mul_comm N a, Nat.add_comm, h2, Nat.mul_comm]

lemma tail_bound {N : ℕ} {A : Finset ℕ} (hA : Adm N A) {Y : ℕ} (hY : 0 < Y) :
    (A.filter (fun x => Y < x)).card ≤ N / Y := by
  have hinj : Set.InjOn (fun a => N / a) (A.filter (fun x => Y < x) : Set ℕ) := by
    intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_filter] at ha hb
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact absurd hab (Nat.ne_of_gt (adm_div_lt hA ha.1 hb.1 h))
    · exact absurd hab (Nat.ne_of_lt (adm_div_lt hA hb.1 ha.1 h))
  have hmaps : ∀ a ∈ A.filter (fun x => Y < x), N / a ∈ Finset.Icc 1 (N / Y) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    have haN := Finset.mem_Icc.mp (hA.1 ha.1)
    rw [Finset.mem_Icc]
    exact ⟨Nat.div_pos haN.2 haN.1, Nat.div_le_div_left ha.2.le hY⟩
  calc (A.filter (fun x => Y < x)).card ≤ (Finset.Icc 1 (N / Y)).card :=
        Finset.card_le_card_of_injOn (fun a => N / a) hmaps hinj
    _ = N / Y := by simp

/-- Window count: the number of `a ∈ [1, w]` with `u + a ∈ A`. -/
def W (A : Finset ℕ) (w u : ℕ) : ℕ := ((Finset.Icc 1 w).filter (fun a => u + a ∈ A)).card

lemma W_le (A : Finset ℕ) (w u : ℕ) : W A w u ≤ w := by
  unfold W
  calc _ ≤ (Finset.Icc 1 w).card := Finset.card_filter_le _ _
    _ = w := by simp

lemma W_slice (A : Finset ℕ) (w u : ℕ) :
    (A.filter (fun x => u < x ∧ x ≤ u + w)).card = W A w u := by
  unfold W
  apply Finset.card_nbij' (fun x => x - u) (fun a => u + a)
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_filter] at hx
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
    have e : u + (x - u) = x := by omega
    have h1 : 1 ≤ x - u := by omega
    have h2 : x - u ≤ w := by omega
    refine ⟨⟨h1, h2⟩, ?_⟩
    show u + (x - u) ∈ A
    rw [e]
    exact hx.1
  · intro a ha
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at ha
    rw [Finset.mem_coe, Finset.mem_filter]
    have h1 : u < u + a := by omega
    have h2 : u + a ≤ u + w := by omega
    exact ⟨ha.2, h1, h2⟩
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_filter] at hx
    show u + (x - u) = x
    omega
  · intro a _
    show u + a - u = a
    omega

lemma W_shift (A : Finset ℕ) (w : ℕ) {u v : ℕ} (huv : u ≤ v) :
    W A w u ≤ W A w v + (v - u) := by
  rw [← W_slice, ← W_slice]
  calc (A.filter (fun x => u < x ∧ x ≤ u + w)).card
      ≤ (A.filter (fun x => v < x ∧ x ≤ v + w) ∪ Finset.Ioc u v).card := by
        apply Finset.card_le_card
        intro x hx
        rw [Finset.mem_filter] at hx
        rw [Finset.mem_union, Finset.mem_filter, Finset.mem_Ioc]
        by_cases h : x ≤ v
        · right
          omega
        · left
          exact ⟨hx.1, by omega, by omega⟩
    _ ≤ (A.filter (fun x => v < x ∧ x ≤ v + w)).card + (Finset.Ioc u v).card :=
        Finset.card_union_le _ _
    _ = (A.filter (fun x => v < x ∧ x ≤ v + w)).card + (v - u) := by simp

lemma W_eq_zero {N : ℕ} {A : Finset ℕ} (hA : Adm N A) (w : ℕ) {u : ℕ} (hu : N ≤ u) :
    W A w u = 0 := by
  unfold W
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro a ha hmem
  have h1 := Finset.mem_Icc.mp ha
  have h2 := Finset.mem_Icc.mp (hA.1 hmem)
  omega

lemma no_consec {N : ℕ} {A : Finset ℕ} (hA : Adm N A) {x : ℕ} (hx : N < x * (x + 1))
    (h1 : x ∈ A) (h2 : x + 1 ∈ A) : False := by
  have h := hA.2 x h1 (x + 1) h2
  have hc : Nat.Coprime x (x + 1) := by simp
  rw [hc.lcm_eq_mul] at h
  omega

lemma W_half {N : ℕ} {A : Finset ℕ} (hA : Adm N A) (w : ℕ) {u : ℕ} (hu : N ≤ u * u) :
    2 * W A w u ≤ w + 1 := by
  unfold W
  obtain ⟨S, hS⟩ : ∃ S, S = (Finset.Icc 1 w).filter (fun a => u + a ∈ A) := ⟨_, rfl⟩
  rw [← hS]
  have hdisj : Disjoint S (S.image (fun a => a + 1)) := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    obtain ⟨a', ha'', rfl⟩ := Finset.mem_image.mp ha'
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at ha ha''
    refine no_consec hA (x := u + a') ?_ ha''.2 ha.2
    nlinarith [ha''.1.1]
  have hsub : S ∪ S.image (fun a => a + 1) ⊆ Finset.Icc 1 (w + 1) := by
    intro a ha
    rw [Finset.mem_Icc]
    rcases Finset.mem_union.mp ha with h | h
    · rw [hS, Finset.mem_filter, Finset.mem_Icc] at h
      omega
    · obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp h
      rw [hS, Finset.mem_filter, Finset.mem_Icc] at ha'
      omega
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ (add_left_injective 1)] at hcard
  simp at hcard
  omega

/-- Envelope of the window counts at positions `≥ τ * w`. -/
def Psi (A : Finset ℕ) (N w τ : ℕ) : ℕ := (Finset.Icc (τ * w) N).sup (W A w)

lemma W_le_Psi {N : ℕ} {A : Finset ℕ} (hA : Adm N A) (w : ℕ) {τ u : ℕ} (hu : τ * w ≤ u) :
    W A w u ≤ Psi A N w τ := by
  by_cases h : u ≤ N
  · exact Finset.le_sup (f := W A w) (Finset.mem_Icc.mpr ⟨hu, h⟩)
  · rw [W_eq_zero hA w (by omega)]
    exact Nat.zero_le _

lemma Psi_antitone (A : Finset ℕ) (N w : ℕ) {τ τ' : ℕ} (h : τ ≤ τ') :
    Psi A N w τ' ≤ Psi A N w τ := by
  unfold Psi
  apply Finset.sup_mono
  apply Finset.Icc_subset_Icc_left
  exact Nat.mul_le_mul_right w h

lemma Psi_attained (A : Finset ℕ) (N w τ : ℕ) : ∃ u, τ * w ≤ u ∧ Psi A N w τ ≤ W A w u := by
  by_cases h : (Finset.Icc (τ * w) N).Nonempty
  · obtain ⟨u, hu, he⟩ := Finset.exists_mem_eq_sup _ h (W A w)
    refine ⟨u, (Finset.mem_Icc.mp hu).1, ?_⟩
    unfold Psi
    rw [he]
  · rw [Finset.not_nonempty_iff_eq_empty] at h
    refine ⟨τ * w, le_rfl, ?_⟩
    unfold Psi
    rw [h]
    simp

lemma Psi_le_w (A : Finset ℕ) (N w τ : ℕ) : Psi A N w τ ≤ w := by
  unfold Psi
  exact Finset.sup_le (fun u _ => W_le A w u)

lemma Psi_half {N : ℕ} {A : Finset ℕ} (hA : Adm N A) {n w τ : ℕ}
    (hNw : N ≤ (n * w) * (n * w)) (hτ : n ≤ τ) : 2 * Psi A N w τ ≤ w + 1 := by
  obtain ⟨u, hu, hle⟩ := Psi_attained A N w τ
  have h1 : n * w ≤ u := le_trans (Nat.mul_le_mul_right w hτ) hu
  have h2 := W_half hA w (le_trans hNw (Nat.mul_le_mul h1 h1))
  omega

lemma head_bound {N : ℕ} {A : Finset ℕ} (hA : Adm N A) (w m : ℕ) :
    (A.filter (fun x => x ≤ m * w)).card ≤ ∑ τ ∈ Finset.range m, Psi A N w τ := by
  induction m with
  | zero =>
    simp only [Nat.zero_mul, Finset.range_zero, Finset.sum_empty, Nat.le_zero,
      Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x hx
    have := Finset.mem_Icc.mp (hA.1 hx)
    omega
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have e : (m + 1) * w = m * w + w := by ring
    calc (A.filter (fun x => x ≤ (m + 1) * w)).card
        ≤ (A.filter (fun x => x ≤ m * w) ∪
            A.filter (fun x => m * w < x ∧ x ≤ m * w + w)).card := by
          apply Finset.card_le_card
          intro x hx
          rw [Finset.mem_filter] at hx
          rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
          by_cases h : x ≤ m * w
          · left
            exact ⟨hx.1, h⟩
          · right
            exact ⟨hx.1, by omega, by omega⟩
      _ ≤ (A.filter (fun x => x ≤ m * w)).card +
            (A.filter (fun x => m * w < x ∧ x ≤ m * w + w)).card := Finset.card_union_le _ _
      _ ≤ ∑ τ ∈ Finset.range m, Psi A N w τ + Psi A N w m :=
          Nat.add_le_add ih (by rw [W_slice]; exact W_le_Psi hA w le_rfl)

lemma card_split {N : ℕ} {A : Finset ℕ} (hA : Adm N A) {w m : ℕ} (hmw : 0 < m * w) :
    A.card ≤ ∑ τ ∈ Finset.range m, Psi A N w τ + N / (m * w) := by
  have h := Finset.card_filter_add_card_filter_not (s := A) (fun x => x ≤ m * w)
  have h1 := head_bound hA w m
  have h2 := tail_bound hA hmw
  have h3 : A.filter (fun x => ¬ x ≤ m * w) = A.filter (fun x => m * w < x) := by
    apply Finset.filter_congr
    intro x _
    exact not_le
  rw [h3] at h
  omega

/-! ## 3. The pattern lemma -/

/-- If `x - y = Q t + d` where `Q` is divisible by `p d` for all small primes `p`, and
`gcd x y > d`, then `x` and `y` have a common prime factor exceeding `z`. -/
lemma pair_prime {z Q d x y : ℕ} (hd : 0 < d) (hQ : ∀ p : ℕ, p.Prime → p ≤ z → p * d ∣ Q)
    (hz : 2 ≤ z) (t : ℤ) (hxy : (x:ℤ) - y = Q * t + d) (hg : d < Nat.gcd x y) :
    ∃ p : ℕ, p.Prime ∧ z < p ∧ p ∣ x ∧ p ∣ y := by
  by_contra hcon
  obtain ⟨Q', hQ'⟩ : d ∣ Q := Dvd.dvd.trans (Dvd.intro_left 2 rfl) (hQ 2 Nat.prime_two hz)
  have hcop : Nat.Coprime (Nat.gcd x y) (((Q':ℤ) * t + 1).natAbs) := by
    rw [Nat.Coprime, Nat.eq_one_iff_not_exists_prime_dvd]
    intro p hp hpd
    have hpG : p ∣ Nat.gcd x y := hpd.trans (Nat.gcd_dvd_left _ _)
    have hpx : p ∣ x := hpG.trans (Nat.gcd_dvd_left x y)
    have hpy : p ∣ y := hpG.trans (Nat.gcd_dvd_right x y)
    have hpz : p ≤ z := by
      by_contra h
      exact hcon ⟨p, hp, not_le.mp h, hpx, hpy⟩
    have h1 : p * d ∣ Q' * d := by
      have h0 := hQ p hp hpz
      rwa [hQ', Nat.mul_comm d Q'] at h0
    have h2 : p ∣ Q' := Nat.dvd_of_mul_dvd_mul_right hd h1
    have h3 : (p:ℤ) ∣ (Q':ℤ) * t + 1 := Int.natCast_dvd.mpr (hpd.trans (Nat.gcd_dvd_right _ _))
    have h4 : (p:ℤ) ∣ (Q':ℤ) * t := Dvd.dvd.mul_right (Int.natCast_dvd_natCast.mpr h2) t
    have h5 : (p:ℤ) ∣ 1 := (dvd_add_right h4).mp h3
    have h6 : p ∣ 1 := by exact_mod_cast h5
    exact hp.one_lt.ne' (Nat.dvd_one.mp h6)
  have hG : ((Nat.gcd x y : ℕ) : ℤ) ∣ (x:ℤ) - y :=
    dvd_sub (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left x y))
      (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right x y))
  have e : (x:ℤ) - y = (d:ℤ) * ((Q':ℤ) * t + 1) := by
    rw [hxy, hQ']
    push_cast
    ring
  rw [e, Int.natCast_dvd, Int.natAbs_mul, Int.natAbs_natCast] at hG
  have hGd : Nat.gcd x y ∣ d := hcop.dvd_of_dvd_mul_right hG
  exact absurd (Nat.le_of_dvd hd hGd) (not_le.mpr hg)

/-- A window of length `w` contains at most `w / p + 1` numbers in a given residue class. -/
lemma card_dvd_window (m w p : ℕ) :
    ((Finset.Icc 1 w).filter (fun a => p ∣ m + a)).card ≤ w / p + 1 := by
  have hinj : Set.InjOn (fun a => a / p)
      ((Finset.Icc 1 w).filter (fun a => p ∣ m + a) : Set ℕ) := by
    intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_filter] at ha hb
    have h1 : (m + a) % p = (m + b) % p := by
      rw [Nat.mod_eq_zero_of_dvd ha.2, Nat.mod_eq_zero_of_dvd hb.2]
    have h2 : a % p = b % p := Nat.ModEq.add_left_cancel' m h1
    have h5 : a / p = b / p := hab
    calc a = p * (a / p) + a % p := (Nat.div_add_mod a p).symm
      _ = p * (b / p) + b % p := by rw [h5, h2]
      _ = b := Nat.div_add_mod b p
  have hmaps : ∀ a ∈ (Finset.Icc 1 w).filter (fun a => p ∣ m + a),
      a / p ∈ Finset.range (w / p + 1) := by
    intro a ha
    rw [Finset.mem_filter, Finset.mem_Icc] at ha
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right ha.1.2)
  calc _ ≤ (Finset.range (w / p + 1)).card :=
        Finset.card_le_card_of_injOn (fun a => a / p) hmaps hinj
    _ = w / p + 1 := Finset.card_range _

/-- A positive number `≤ N` has at most `log_z N` prime factors exceeding `z`. -/
lemma large_primeFactors_card {z N D : ℕ} (hz : 2 ≤ z) (hD : D ≤ N) :
    (D.primeFactors.filter (fun p => z < p)).card ≤ Nat.log z N := by
  rcases Nat.eq_zero_or_pos D with h0 | hpos
  · subst h0
    simp
  · apply Nat.le_log_of_pow_le (by omega)
    have h1 : z ^ (D.primeFactors.filter (fun p => z < p)).card ≤
        ∏ p ∈ D.primeFactors.filter (fun p => z < p), p :=
      Finset.pow_card_le_prod _ _ _ (fun p hp => (Finset.mem_filter.mp hp).2.le)
    have h2 : (∏ p ∈ D.primeFactors.filter (fun p => z < p), p) ∣ ∏ p ∈ D.primeFactors, p :=
      Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
    have h3 := Nat.le_of_dvd hpos (h2.trans (Nat.prod_primeFactors_dvd D))
    omega

/-- The shifted position of code `c`: congruent to `c` modulo `Q`, just above `X c`. -/
def nnpos (Q : ℕ) (X : ℕ → ℕ) (c : ℕ) : ℕ := Q * (X c / Q + 1) + c

lemma lt_nnpos {Q : ℕ} (hQ0 : 0 < Q) (X : ℕ → ℕ) (c : ℕ) : X c < nnpos Q X c := by
  unfold nnpos
  have := Nat.lt_mul_div_succ (X c) hQ0
  omega

lemma nnpos_le (Q : ℕ) (X : ℕ → ℕ) (c : ℕ) : nnpos Q X c ≤ X c + Q + c := by
  unfold nnpos
  have := Nat.mul_div_le (X c) Q
  rw [Nat.mul_add, Nat.mul_one]
  omega

lemma nnpos_ne {Q : ℕ} (X : ℕ → ℕ) {c c' : ℕ} (hcc : c' < c) (h2 : 2 * (c - c') ≤ Q) :
    nnpos Q X c ≠ nnpos Q X c' := by
  unfold nnpos
  intro h
  rcases Nat.lt_or_ge (X c / Q + 1) (X c' / Q + 1) with h1 | h1
  · have h3 : Q * (X c / Q + 1 + 1) ≤ Q * (X c' / Q + 1) := Nat.mul_le_mul_left Q h1
    rw [Nat.mul_add, Nat.mul_one] at h3
    omega
  · have h3 : Q * (X c' / Q + 1) ≤ Q * (X c / Q + 1) := Nat.mul_le_mul_left Q h1
    omega

lemma pattern_pair {N : ℕ} {A : Finset ℕ} (hA : Adm N A) {k z Q : ℕ} {X : ℕ → ℕ}
    (hV : ∀ c, c < k → ∀ c', c' < c → (c - c') * N ≤ X c * X c')
    (hQ : ∀ d, 0 < d → d < k → ∀ p : ℕ, p.Prime → p ≤ z → p * d ∣ Q)
    (hz : 2 ≤ z) (hQ0 : 0 < Q) {a c c' : ℕ} (ha : 1 ≤ a) (hc : c < k) (hcc : c' < c)
    (hx : nnpos Q X c + a ∈ A) (hy : nnpos Q X c' + a ∈ A) :
    ∃ p : ℕ, p.Prime ∧ z < p ∧ p ∣ nnpos Q X c + a ∧ p ∣ nnpos Q X c' + a := by
  have hXx := lt_nnpos hQ0 X c
  have hXy := lt_nnpos hQ0 X c'
  have hd : 0 < c - c' := by omega
  have hdk : c - c' < k := by omega
  have hg : c - c' < Nat.gcd (nnpos Q X c + a) (nnpos Q X c' + a) := by
    by_contra h
    rw [not_lt] at h
    have hl := hA.2 _ hx _ hy
    have h1 : (nnpos Q X c + a) * (nnpos Q X c' + a) ≤ X c * X c' :=
      calc (nnpos Q X c + a) * (nnpos Q X c' + a)
          = Nat.gcd (nnpos Q X c + a) (nnpos Q X c' + a) *
              Nat.lcm (nnpos Q X c + a) (nnpos Q X c' + a) := (Nat.gcd_mul_lcm _ _).symm
        _ ≤ (c - c') * N := Nat.mul_le_mul h hl
        _ ≤ X c * X c' := hV c hc c' hcc
    have h2 : X c * X c' < (nnpos Q X c + a) * (nnpos Q X c' + a) :=
      Nat.mul_lt_mul'' (by omega) (by omega)
    omega
  have hxy : ((nnpos Q X c + a : ℕ) : ℤ) - ((nnpos Q X c' + a : ℕ) : ℤ) =
      (Q : ℤ) * (((X c / Q + 1 : ℕ) : ℤ) - ((X c' / Q + 1 : ℕ) : ℤ)) + ((c - c' : ℕ) : ℤ) := by
    unfold nnpos
    rw [Nat.cast_sub hcc.le]
    push_cast
    ring
  exact pair_prime hd (hQ (c - c') hd hdk) hz _ hxy hg

/-- The exceptional offsets for the ordered pair of codes `q`. -/
def badSet (N w z Q : ℕ) (X : ℕ → ℕ) (q : ℕ × ℕ) : Finset ℕ :=
  ((min (nnpos Q X q.1) N - nnpos Q X q.2).primeFactors.filter (fun p => z < p)).biUnion
    (fun p => (Finset.Icc 1 w).filter (fun a => p ∣ nnpos Q X q.2 + a))

lemma badSet_card {N w z Q L : ℕ} (X : ℕ → ℕ) (hz : 2 ≤ z)
    (hL : ∀ D, D ≤ N → (D.primeFactors.filter (fun p => z < p)).card ≤ L) (q : ℕ × ℕ) :
    (badSet N w z Q X q).card ≤ L * (w / z + 1) := by
  unfold badSet
  refine le_trans Finset.card_biUnion_le ?_
  calc _ ≤ ∑ _p ∈ (min (nnpos Q X q.1) N - nnpos Q X q.2).primeFactors.filter
            (fun p => z < p), (w / z + 1) := by
        apply Finset.sum_le_sum
        intro p hp
        rw [Finset.mem_filter] at hp
        exact le_trans (card_dvd_window _ w p)
          (Nat.succ_le_succ (Nat.div_le_div_left hp.2.le (by omega)))
    _ = ((min (nnpos Q X q.1) N - nnpos Q X q.2).primeFactors.filter
            (fun p => z < p)).card * (w / z + 1) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ L * (w / z + 1) :=
        Nat.mul_le_mul_right _ (hL _ (le_trans (Nat.sub_le _ _) (Nat.min_le_right _ _)))

lemma mem_badSet {N w z Q : ℕ} {X : ℕ → ℕ} {q : ℕ × ℕ} {a p : ℕ} (ha : a ∈ Finset.Icc 1 w)
    (hp : p.Prime) (hzp : z < p) (h1 : nnpos Q X q.2 < nnpos Q X q.1)
    (h2 : nnpos Q X q.1 + a ≤ N)
    (hd1 : p ∣ nnpos Q X q.1 + a) (hd2 : p ∣ nnpos Q X q.2 + a) : a ∈ badSet N w z Q X q := by
  unfold badSet
  have e : min (nnpos Q X q.1) N = nnpos Q X q.1 := Nat.min_eq_left (by omega)
  have e2 : nnpos Q X q.1 - nnpos Q X q.2 = nnpos Q X q.1 + a - (nnpos Q X q.2 + a) := by omega
  refine Finset.mem_biUnion.mpr ⟨p, Finset.mem_filter.mpr
    ⟨Nat.mem_primeFactors.mpr ⟨hp, ?_, ?_⟩, hzp⟩, Finset.mem_filter.mpr ⟨ha, hd2⟩⟩
  · rw [e, e2]
    exact Nat.dvd_sub hd1 hd2
  · rw [e]
    omega

lemma pattern_bad {N : ℕ} {A : Finset ℕ} (hA : Adm N A) {w k z Q L : ℕ} {X : ℕ → ℕ}
    (hV : ∀ c, c < k → ∀ c', c' < c → (c - c') * N ≤ X c * X c')
    (hQ : ∀ d, 0 < d → d < k → ∀ p : ℕ, p.Prime → p ≤ z → p * d ∣ Q)
    (hz : 2 ≤ z) (hQ0 : 0 < Q)
    (hL : ∀ D, D ≤ N → (D.primeFactors.filter (fun p => z < p)).card ≤ L) :
    ((Finset.Icc 1 w).filter (fun a =>
      1 < ((Finset.range k).filter (fun c => nnpos Q X c + a ∈ A)).card)).card
      ≤ k * k * (L * (w / z + 1)) := by
  have key : ∀ a ∈ Finset.Icc 1 w, ∀ c, c < k → ∀ c', c' < c → nnpos Q X c + a ∈ A →
      nnpos Q X c' + a ∈ A →
      a ∈ (Finset.range k ×ˢ Finset.range k).biUnion (badSet N w z Q X) := by
    intro a ha c hc c' hcc hx hy
    obtain ⟨p, hp, hzp, hpx, hpy⟩ :=
      pattern_pair hA hV hQ hz hQ0 (Finset.mem_Icc.mp ha).1 hc hcc hx hy
    have hne := nnpos_ne X hcc
      (Nat.le_of_dvd hQ0 (hQ (c - c') (by omega) (by omega) 2 Nat.prime_two hz))
    have hxN := (Finset.mem_Icc.mp (hA.1 hx)).2
    have hyN := (Finset.mem_Icc.mp (hA.1 hy)).2
    have hc' : c' < k := by omega
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact Finset.mem_biUnion.mpr ⟨(c', c), Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr hc', Finset.mem_range.mpr hc⟩,
        mem_badSet ha hp hzp h hyN hpy hpx⟩
    · exact Finset.mem_biUnion.mpr ⟨(c, c'), Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr hc, Finset.mem_range.mpr hc'⟩,
        mem_badSet ha hp hzp h hxN hpx hpy⟩
  have hsub : (Finset.Icc 1 w).filter (fun a =>
      1 < ((Finset.range k).filter (fun c => nnpos Q X c + a ∈ A)).card) ⊆
      (Finset.range k ×ˢ Finset.range k).biUnion (badSet N w z Q X) := by
    intro a ha
    rw [Finset.mem_filter, Finset.one_lt_card] at ha
    obtain ⟨ha1, c, hc, c', hc', hne⟩ := ha
    rw [Finset.mem_filter, Finset.mem_range] at hc hc'
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact key a ha1 c' hc'.1 c h hc'.2 hc.2
    · exact key a ha1 c hc.1 c' h hc.2 hc'.2
  calc _ ≤ ((Finset.range k ×ˢ Finset.range k).biUnion (badSet N w z Q X)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ q ∈ Finset.range k ×ˢ Finset.range k, (badSet N w z Q X q).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _q ∈ Finset.range k ×ˢ Finset.range k, L * (w / z + 1) :=
        Finset.sum_le_sum (fun q _ => badSet_card X hz hL q)
    _ = k * k * (L * (w / z + 1)) := by
        rw [Finset.sum_const, Finset.card_product, Finset.card_range, smul_eq_mul]

/-- The pattern lemma: window counts at positions satisfying the product condition (V)
add up to at most one full window, up to lower-order terms. -/
theorem pattern_lemma {N : ℕ} {A : Finset ℕ} (hA : Adm N A) {w k z Q L : ℕ} {X : ℕ → ℕ}
    (hV : ∀ c, c < k → ∀ c', c' < c → (c - c') * N ≤ X c * X c')
    (hQ : ∀ d, 0 < d → d < k → ∀ p : ℕ, p.Prime → p ≤ z → p * d ∣ Q)
    (hz : 2 ≤ z) (hQ0 : 0 < Q)
    (hL : ∀ D, D ≤ N → (D.primeFactors.filter (fun p => z < p)).card ≤ L) :
    ∑ c ∈ Finset.range k, W A w (X c) ≤
      w + k * (Q + k) + k * (k * k * (L * (w / z + 1))) := by
  have h1 : ∑ c ∈ Finset.range k, W A w (X c) ≤
      ∑ c ∈ Finset.range k, (W A w (nnpos Q X c) + (Q + k)) := by
    apply Finset.sum_le_sum
    intro c hc
    rw [Finset.mem_range] at hc
    have h5 := W_shift A w (lt_nnpos hQ0 X c).le
    have h6 := nnpos_le Q X c
    omega
  have h2 : ∑ c ∈ Finset.range k, W A w (nnpos Q X c) =
      ∑ a ∈ Finset.Icc 1 w, ((Finset.range k).filter (fun c => nnpos Q X c + a ∈ A)).card := by
    unfold W
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have h3 : ∀ a ∈ Finset.Icc 1 w,
      ((Finset.range k).filter (fun c => nnpos Q X c + a ∈ A)).card ≤ 1 + k *
        (if 1 < ((Finset.range k).filter (fun c => nnpos Q X c + a ∈ A)).card then 1 else 0) := by
    intro a _
    have hk : ((Finset.range k).filter (fun c => nnpos Q X c + a ∈ A)).card ≤ k := by
      calc _ ≤ (Finset.range k).card := Finset.card_filter_le _ _
        _ = k := Finset.card_range k
    split_ifs with h
    · omega
    · omega
  have h4 := pattern_bad (w := w) hA hV hQ hz hQ0 hL
  rw [Finset.card_filter] at h4
  calc ∑ c ∈ Finset.range k, W A w (X c)
      ≤ ∑ c ∈ Finset.range k, (W A w (nnpos Q X c) + (Q + k)) := h1
    _ = ∑ a ∈ Finset.Icc 1 w, ((Finset.range k).filter (fun c => nnpos Q X c + a ∈ A)).card
          + k * (Q + k) := by
        rw [Finset.sum_add_distrib, h2, Finset.sum_const, Finset.card_range, smul_eq_mul]
    _ ≤ ∑ a ∈ Finset.Icc 1 w, (1 + k *
          (if 1 < ((Finset.range k).filter (fun c => nnpos Q X c + a ∈ A)).card then 1 else 0))
          + k * (Q + k) := Nat.add_le_add_right (Finset.sum_le_sum h3) _
    _ = w + k * ∑ a ∈ Finset.Icc 1 w,
          (if 1 < ((Finset.range k).filter (fun c => nnpos Q X c + a ∈ A)).card then 1 else 0)
          + k * (Q + k) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, smul_eq_mul,
          Nat.card_Icc, Nat.add_sub_cancel, Nat.mul_one]
    _ ≤ w + k * (k * k * (L * (w / z + 1))) + k * (Q + k) :=
        Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left k h4) w) _
    _ = w + k * (Q + k) + k * (k * k * (L * (w / z + 1))) := by ring

/-! ## 4. Thresholds -/

/-- Ceiling division. -/
def cdiv (x j : ℕ) : ℕ := (x + j - 1) / j

lemma cdiv_le_iff {x j τ : ℕ} (hj : 0 < j) : cdiv x j ≤ τ ↔ x ≤ τ * j := by
  unfold cdiv
  constructor
  · intro h
    have h1 : x + j - 1 < (τ + 1) * j := (Nat.div_lt_iff_lt_mul hj).mp (by omega)
    rw [Nat.add_mul, Nat.one_mul] at h1
    omega
  · intro h
    have h1 : (x + j - 1) / j < τ + 1 :=
      (Nat.div_lt_iff_lt_mul hj).mpr (by rw [Nat.add_mul, Nat.one_mul]; omega)
    omega

/-- Threshold of the code `T + a` (`a ≥ 1`) in the pattern `j`. -/
def thP (n j a : ℕ) : ℕ := cdiv (a * (n * n)) j

/-- Threshold of the code `T - b` (`b ≥ 0`) in the pattern `j`. -/
def thM (n j b : ℕ) : ℕ := max (cdiv (b * (n * n)) j) ((b + 1) * j)

/-- Threshold of the code `c ∈ [0, 2T]` in the pattern `j`. -/
def th (n T j c : ℕ) : ℕ := if T < c then thP n j (c - T) else thM n j (T - c)

lemma thP_le_iff {n j a τ : ℕ} (hj : 0 < j) : thP n j a ≤ τ ↔ a * (n * n) ≤ τ * j := by
  unfold thP
  exact cdiv_le_iff hj

lemma thM_le_iff {n j b τ : ℕ} (hj : 0 < j) :
    thM n j b ≤ τ ↔ b * (n * n) ≤ τ * j ∧ (b + 1) * j ≤ τ := by
  unfold thM
  rw [max_le_iff, cdiv_le_iff hj]

lemma th_neg {n T j b : ℕ} (hb : b ≤ T) : th n T j (T - b) = thM n j b := by
  unfold th
  rw [if_neg (by omega)]
  congr 1
  omega

lemma th_pos (n T j x : ℕ) : th n T j (T + 1 + x) = thP n j (x + 1) := by
  unfold th
  rw [if_pos (by omega)]
  congr 1
  omega

lemma thP_mul {n j a : ℕ} (hj : 0 < j) : a * (n * n) ≤ thP n j a * j :=
  (thP_le_iff hj).mp le_rfl

lemma thM_mul {n j b : ℕ} (hj : 0 < j) : b * (n * n) ≤ thM n j b * j :=
  ((thM_le_iff hj).mp le_rfl).1

lemma thM_ge (n j b : ℕ) : (b + 1) * j ≤ thM n j b := le_max_right _ _

lemma thP_ge {n j a : ℕ} (hj : 0 < j) (hjn : j ≤ n) : a * n ≤ thP n j a := by
  have h := thP_mul (n := n) (a := a) hj
  have h2 : thP n j a * j ≤ thP n j a * n := Nat.mul_le_mul_left _ hjn
  have h3 : a * n * n ≤ thP n j a * n := by
    calc a * n * n = a * (n * n) := Nat.mul_assoc a n n
      _ ≤ thP n j a * j := h
      _ ≤ thP n j a * n := h2
  exact Nat.le_of_mul_le_mul_right h3 (by omega)

/-- Validity of the patterns: the product condition holds on the grid. -/
lemma th_valid {n T j c c' : ℕ} (hj1 : 1 ≤ j) (hjn : j ≤ n) (hcc : c' < c) :
    (c - c') * (n * n) ≤ th n T j c * th n T j c' := by
  unfold th
  by_cases h1 : T < c'
  · have h2 : T < c := by omega
    rw [if_pos h1, if_pos h2]
    have ha := thP_ge (a := c - T) hj1 hjn
    have ha' := thP_ge (a := c' - T) hj1 hjn
    have h3 : c - c' ≤ (c - T) * (c' - T) := by
      calc c - c' ≤ (c - T) * 1 := by omega
        _ ≤ (c - T) * (c' - T) := Nat.mul_le_mul_left _ (by omega)
    calc (c - c') * (n * n) ≤ ((c - T) * (c' - T)) * (n * n) := Nat.mul_le_mul_right _ h3
      _ = ((c - T) * n) * ((c' - T) * n) := by ring
      _ ≤ thP n j (c - T) * thP n j (c' - T) := Nat.mul_le_mul ha ha'
  · rw [if_neg h1]
    by_cases h2 : T < c
    · rw [if_pos h2]
      have hP := thP_mul (n := n) (a := c - T) hj1
      have hM := thM_ge n j (T - c')
      have h3 : c - c' ≤ (T - c' + 1) * (c - T) := by
        have h4 : T - c' ≤ (T - c') * (c - T) := Nat.le_mul_of_pos_right _ (by omega)
        rw [Nat.add_mul, Nat.one_mul]
        omega
      calc (c - c') * (n * n) ≤ ((T - c' + 1) * (c - T)) * (n * n) :=
            Nat.mul_le_mul_right _ h3
        _ = (T - c' + 1) * ((c - T) * (n * n)) := by ring
        _ ≤ (T - c' + 1) * (thP n j (c - T) * j) := Nat.mul_le_mul_left _ hP
        _ = thP n j (c - T) * ((T - c' + 1) * j) := by ring
        _ ≤ thP n j (c - T) * thM n j (T - c') := Nat.mul_le_mul_left _ hM
    · rw [if_neg h2]
      have hM := thM_mul (n := n) (b := T - c') hj1
      have hM2 := thM_ge n j (T - c)
      have h4 : j ≤ thM n j (T - c) := le_trans (Nat.le_mul_of_pos_left _ (by omega)) hM2
      calc (c - c') * (n * n) ≤ (T - c') * (n * n) := Nat.mul_le_mul_right _ (by omega)
        _ ≤ thM n j (T - c') * j := hM
        _ = j * thM n j (T - c') := Nat.mul_comm _ _
        _ ≤ thM n j (T - c) * thM n j (T - c') := Nat.mul_le_mul_right _ h4

/-- The pattern lemma applied to the envelope along one pattern. -/
lemma pattern_Psi {N : ℕ} {A : Finset ℕ} (hA : Adm N A) {n w T z Q L j : ℕ}
    (hNw : N ≤ (n * w) * (n * w)) (hj1 : 1 ≤ j) (hjn : j ≤ n)
    (hQ : ∀ d, 0 < d → d < 2 * T + 1 → ∀ p : ℕ, p.Prime → p ≤ z → p * d ∣ Q)
    (hz : 2 ≤ z) (hQ0 : 0 < Q)
    (hL : ∀ D, D ≤ N → (D.primeFactors.filter (fun p => z < p)).card ≤ L) :
    ∑ c ∈ Finset.range (2 * T + 1), Psi A N w (th n T j c) ≤
      w + (2 * T + 1) * (Q + (2 * T + 1)) +
        (2 * T + 1) * ((2 * T + 1) * (2 * T + 1) * (L * (w / z + 1))) := by
  choose X hX1 hX2 using fun c => Psi_attained A N w (th n T j c)
  have hV : ∀ c, c < 2 * T + 1 → ∀ c', c' < c → (c - c') * N ≤ X c * X c' := by
    intro c _ c' hcc
    have h1 := th_valid (n := n) (T := T) hj1 hjn hcc
    calc (c - c') * N ≤ (c - c') * ((n * w) * (n * w)) := Nat.mul_le_mul_left _ hNw
      _ = ((c - c') * (n * n)) * (w * w) := by ring
      _ ≤ (th n T j c * th n T j c') * (w * w) := Nat.mul_le_mul_right _ h1
      _ = (th n T j c * w) * (th n T j c' * w) := by ring
      _ ≤ X c * X c' := Nat.mul_le_mul (hX1 c) (hX1 c')
  calc ∑ c ∈ Finset.range (2 * T + 1), Psi A N w (th n T j c)
      ≤ ∑ c ∈ Finset.range (2 * T + 1), W A w (X c) := Finset.sum_le_sum (fun c _ => hX2 c)
    _ ≤ _ := pattern_lemma hA hV hQ hz hQ0 hL

/-- At most `x / τ` of the positive integers `j` fail `x ≤ τ * j`. -/
lemma count_ge (n x τ : ℕ) (hτ : 0 < τ) :
    n ≤ ((Finset.Icc 1 n).filter (fun j => x ≤ τ * j)).card + x / τ := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.Icc 1 n) (fun j => x ≤ τ * j)
  have h2 : ((Finset.Icc 1 n).filter (fun j => ¬ x ≤ τ * j)).card ≤ x / τ := by
    calc _ ≤ (Finset.Icc 1 (x / τ)).card := by
          apply Finset.card_le_card
          intro j hj
          rw [Finset.mem_filter, Finset.mem_Icc] at hj
          rw [Finset.mem_Icc, Nat.le_div_iff_mul_le hτ]
          refine ⟨hj.1.1, ?_⟩
          rw [Nat.mul_comm]
          omega
      _ = x / τ := by simp
  have h3 : (Finset.Icc 1 n).card = n := by simp
  omega

lemma countP_ge {n τ a : ℕ} (hτ : 0 < τ) :
    n ≤ ((Finset.Icc 1 n).filter (fun j => thP n j a ≤ τ)).card + a * (n * n) / τ := by
  have h := count_ge n (a * (n * n)) τ hτ
  have h2 : (Finset.Icc 1 n).filter (fun j => a * (n * n) ≤ τ * j) ⊆
      (Finset.Icc 1 n).filter (fun j => thP n j a ≤ τ) := by
    intro j hj
    rw [Finset.mem_filter, Finset.mem_Icc] at hj
    rw [Finset.mem_filter, Finset.mem_Icc, thP_le_iff (by omega)]
    exact hj
  have h3 := Finset.card_le_card h2
  omega

lemma countM_ge {n τ b M : ℕ} (hτ : 0 < τ) (hM : M ≤ n) (hb : (b + 1) * M ≤ τ) :
    M ≤ ((Finset.Icc 1 n).filter (fun j => thM n j b ≤ τ)).card + b * (n * n) / τ := by
  have h := count_ge M (b * (n * n)) τ hτ
  have h2 : (Finset.Icc 1 M).filter (fun j => b * (n * n) ≤ τ * j) ⊆
      (Finset.Icc 1 n).filter (fun j => thM n j b ≤ τ) := by
    intro j hj
    rw [Finset.mem_filter, Finset.mem_Icc] at hj
    rw [Finset.mem_filter, Finset.mem_Icc, thM_le_iff (by omega)]
    refine ⟨⟨hj.1.1, by omega⟩, hj.2, ?_⟩
    exact le_trans (Nat.mul_le_mul_left _ hj.1.2) hb
  have h3 := Finset.card_le_card h2
  omega

lemma sum_codes (F : ℕ → ℕ) (T : ℕ) :
    ∑ c ∈ Finset.range (2 * T + 1), F c =
      ∑ b ∈ Finset.range (T + 1), F (T - b) + ∑ x ∈ Finset.range T, F (T + 1 + x) := by
  have e : 2 * T + 1 = (T + 1) + T := by omega
  have h := Finset.sum_range_reflect F (T + 1)
  simp only [Nat.add_sub_cancel] at h
  rw [e, Finset.sum_range_add, h]

lemma cnt_eq (n T τ : ℕ) :
    ((Finset.Icc 1 n ×ˢ Finset.range (2 * T + 1)).filter (fun i => th n T i.1 i.2 ≤ τ)).card =
      ∑ c ∈ Finset.range (2 * T + 1),
        ((Finset.Icc 1 n).filter (fun j => th n T j c ≤ τ)).card := by
  simp only [Finset.card_filter]
  exact Finset.sum_product_right _ _ _

/-- (C1): below `n`, the code `T` alone provides enough thresholds. -/
lemma C1 {n T τ : ℕ} (h : τ < n) :
    τ ≤ ((Finset.Icc 1 n ×ˢ Finset.range (2 * T + 1)).filter
      (fun i => th n T i.1 i.2 ≤ τ)).card := by
  have hinj : Set.InjOn (fun j : ℕ => (j, T)) (Finset.Icc 1 τ : Set ℕ) := by
    intro a _ b _ hab
    exact (Prod.mk.inj hab).1
  have hmaps : ∀ j ∈ Finset.Icc 1 τ, (j, T) ∈
      (Finset.Icc 1 n ×ˢ Finset.range (2 * T + 1)).filter (fun i => th n T i.1 i.2 ≤ τ) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range]
    refine ⟨⟨⟨hj.1, by omega⟩, by omega⟩, ?_⟩
    show th n T j T ≤ τ
    have e : th n T j T = thM n j 0 := by
      have h0 := th_neg (n := n) (T := T) (j := j) (b := 0) (Nat.zero_le T)
      rwa [Nat.sub_zero] at h0
    rw [e, thM_le_iff (by omega)]
    constructor <;> omega
  calc τ = (Finset.Icc 1 τ).card := by simp
    _ ≤ _ := Finset.card_le_card_of_injOn (fun j => (j, T)) hmaps hinj

lemma cast_div_le_real (x τ : ℕ) : ((x / τ : ℕ) : ℝ) ≤ (x:ℝ) / τ := Nat.cast_div_le

lemma countP_real {n τ a : ℕ} (hτ : 0 < τ) :
    (n:ℝ) - a * ((n:ℝ) * n / τ) ≤
      (((Finset.Icc 1 n).filter (fun j => thP n j a ≤ τ)).card : ℝ) := by
  have h := countP_ge (n := n) (a := a) hτ
  have h1 : ((a * (n * n) / τ : ℕ) : ℝ) ≤ (a:ℝ) * ((n:ℝ) * n / τ) := by
    calc ((a * (n * n) / τ : ℕ) : ℝ) ≤ ((a * (n * n) : ℕ) : ℝ) / τ := cast_div_le_real _ _
      _ = (a:ℝ) * ((n:ℝ) * n / τ) := by push_cast; ring
  have h2 : (n : ℝ) ≤ (((Finset.Icc 1 n).filter (fun j => thP n j a ≤ τ)).card : ℝ) +
      ((a * (n * n) / τ : ℕ) : ℝ) := by exact_mod_cast h
  linarith

lemma countM_real {n τ b : ℕ} (hτ : 0 < τ) (hb : (b + 1) * n ≤ τ) :
    (n:ℝ) - b * ((n:ℝ) * n / τ) ≤
      (((Finset.Icc 1 n).filter (fun j => thM n j b ≤ τ)).card : ℝ) := by
  have h := countM_ge (n := n) (b := b) hτ (le_refl n) hb
  have h1 : ((b * (n * n) / τ : ℕ) : ℝ) ≤ (b:ℝ) * ((n:ℝ) * n / τ) := by
    calc ((b * (n * n) / τ : ℕ) : ℝ) ≤ ((b * (n * n) : ℕ) : ℝ) / τ := cast_div_le_real _ _
      _ = (b:ℝ) * ((n:ℝ) * n / τ) := by push_cast; ring
  have h2 : (n : ℝ) ≤ (((Finset.Icc 1 n).filter (fun j => thM n j b ≤ τ)).card : ℝ) +
      ((b * (n * n) / τ : ℕ) : ℝ) := by exact_mod_cast h
  linarith

lemma countMK_real {n τ K : ℕ} (hτ : 0 < τ) (hK : τ < (K + 1) * n) :
    (τ:ℝ) / ((K:ℝ) + 1) - 1 - K * ((n:ℝ) * n / τ) ≤
      (((Finset.Icc 1 n).filter (fun j => thM n j K ≤ τ)).card : ℝ) := by
  have hM1 : τ / (K + 1) ≤ n := Nat.le_of_lt (Nat.div_lt_of_lt_mul hK)
  have hM2 : (K + 1) * (τ / (K + 1)) ≤ τ := Nat.mul_div_le τ (K + 1)
  have h := countM_ge (n := n) (b := K) hτ hM1 hM2
  have h1 : ((K * (n * n) / τ : ℕ) : ℝ) ≤ (K:ℝ) * ((n:ℝ) * n / τ) := by
    calc ((K * (n * n) / τ : ℕ) : ℝ) ≤ ((K * (n * n) : ℕ) : ℝ) / τ := cast_div_le_real _ _
      _ = (K:ℝ) * ((n:ℝ) * n / τ) := by push_cast; ring
  have h2 : ((τ / (K + 1) : ℕ) : ℝ) ≤
      (((Finset.Icc 1 n).filter (fun j => thM n j K ≤ τ)).card : ℝ) +
        ((K * (n * n) / τ : ℕ) : ℝ) := by exact_mod_cast h
  have h3 : τ < (K + 1) * (τ / (K + 1) + 1) := Nat.lt_mul_div_succ τ (Nat.succ_pos K)
  have h4 : (τ : ℝ) < ((K:ℝ) + 1) * (((τ / (K + 1) : ℕ) : ℝ) + 1) := by exact_mod_cast h3
  have hK0 : (0:ℝ) < (K:ℝ) + 1 := by positivity
  have h5 : (τ : ℝ) / ((K:ℝ) + 1) < ((τ / (K + 1) : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hK0]
    linarith
  linarith

lemma sum_odd_real (K : ℕ) (a c : ℝ) :
    ∑ b ∈ Finset.range K, ((a - b * c) + (a - ((b:ℝ) + 1) * c)) = 2 * K * a - K * K * c := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- Counting the thresholds below `τ` when `K * n ≤ τ < (K + 1) * n`. -/
lemma C2_count {n T τ K : ℕ} (hτ : 0 < τ) (hKT : K < T) (hKn : K * n ≤ τ)
    (hτK : τ < (K + 1) * n) :
    2 * (K:ℝ) * n - K * K * ((n:ℝ) * n / τ) +
        max 0 ((τ:ℝ) / ((K:ℝ) + 1) - K * ((n:ℝ) * n / τ)) - 1 ≤
      (((Finset.Icc 1 n ×ˢ Finset.range (2 * T + 1)).filter
        (fun i => th n T i.1 i.2 ≤ τ)).card : ℝ) := by
  have hcnt : ((Finset.Icc 1 n ×ˢ Finset.range (2 * T + 1)).filter
        (fun i => th n T i.1 i.2 ≤ τ)).card =
      ∑ b ∈ Finset.range (T + 1), ((Finset.Icc 1 n).filter (fun j => thM n j b ≤ τ)).card +
        ∑ x ∈ Finset.range T, ((Finset.Icc 1 n).filter (fun j => thP n j (x + 1) ≤ τ)).card := by
    rw [cnt_eq, sum_codes (fun c => ((Finset.Icc 1 n).filter (fun j => th n T j c ≤ τ)).card) T]
    congr 1
    · refine Finset.sum_congr rfl (fun b hb => ?_)
      rw [Finset.mem_range] at hb
      have e : ∀ j, th n T j (T - b) = thM n j b := fun j => th_neg (by omega)
      simp only [e]
    · refine Finset.sum_congr rfl (fun x _ => ?_)
      simp only [th_pos]
  have hM : ∀ b ∈ Finset.range K, (n:ℝ) - b * ((n:ℝ) * n / τ) ≤
      (((Finset.Icc 1 n).filter (fun j => thM n j b ≤ τ)).card : ℝ) := by
    intro b hb
    rw [Finset.mem_range] at hb
    exact countM_real hτ (le_trans (Nat.mul_le_mul_right n (by omega)) hKn)
  have hP : ∀ x ∈ Finset.range K, (n:ℝ) - ((x:ℝ) + 1) * ((n:ℝ) * n / τ) ≤
      (((Finset.Icc 1 n).filter (fun j => thP n j (x + 1) ≤ τ)).card : ℝ) := by
    intro x _
    have h := countP_real (n := n) (a := x + 1) hτ
    rw [Nat.cast_add, Nat.cast_one] at h
    exact h
  have hMK := countMK_real (n := n) hτ hτK
  have hMK0 : (0:ℝ) ≤ (((Finset.Icc 1 n).filter (fun j => thM n j K ≤ τ)).card : ℝ) :=
    Nat.cast_nonneg _
  have hmax : max 0 ((τ:ℝ) / ((K:ℝ) + 1) - K * ((n:ℝ) * n / τ)) ≤
      (((Finset.Icc 1 n).filter (fun j => thM n j K ≤ τ)).card : ℝ) + 1 :=
    max_le (by linarith) (by linarith)
  have hsumM : ∑ b ∈ Finset.range K, ((n:ℝ) - b * ((n:ℝ) * n / τ)) ≤
      ∑ b ∈ Finset.range K,
        (((Finset.Icc 1 n).filter (fun j => thM n j b ≤ τ)).card : ℝ) :=
    Finset.sum_le_sum hM
  have hsumP : ∑ x ∈ Finset.range K, ((n:ℝ) - ((x:ℝ) + 1) * ((n:ℝ) * n / τ)) ≤
      ∑ x ∈ Finset.range K,
        (((Finset.Icc 1 n).filter (fun j => thP n j (x + 1) ≤ τ)).card : ℝ) :=
    Finset.sum_le_sum hP
  have hodd := sum_odd_real K (n:ℝ) ((n:ℝ) * n / τ)
  rw [Finset.sum_add_distrib] at hodd
  have hsubM : ∑ b ∈ Finset.range (K + 1),
        (((Finset.Icc 1 n).filter (fun j => thM n j b ≤ τ)).card : ℝ) ≤
      ∑ b ∈ Finset.range (T + 1),
        (((Finset.Icc 1 n).filter (fun j => thM n j b ≤ τ)).card : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun _ _ _ => Nat.cast_nonneg _)
  have hsubP : ∑ x ∈ Finset.range K,
        (((Finset.Icc 1 n).filter (fun j => thP n j (x + 1) ≤ τ)).card : ℝ) ≤
      ∑ x ∈ Finset.range T,
        (((Finset.Icc 1 n).filter (fun j => thP n j (x + 1) ≤ τ)).card : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun _ _ _ => Nat.cast_nonneg _)
  rw [Finset.sum_range_succ] at hsubM
  rw [hcnt, Nat.cast_add, Nat.cast_sum, Nat.cast_sum]
  linarith

lemma c2_A {n τ K E : ℝ} (hτ : 0 < τ) (h : (τ - K * n) * (τ - K * n) ≤ E * τ * n) :
    τ - n * E ≤ 2 * K * n - K * K * (n * n / τ) := by
  have hq : n * n / τ * τ = n * n := div_mul_cancel₀ _ hτ.ne'
  refine le_of_mul_le_mul_right ?_ hτ
  have e : (2 * K * n - K * K * (n * n / τ)) * τ = 2 * K * n * τ - K * K * (n * n / τ * τ) := by
    ring
  rw [e, hq]
  linarith

lemma c2_B {n τ K E : ℝ} (hτ : 0 < τ) (hK : 0 < K + 1)
    (h : K * (((K + 1) * n - τ) * ((K + 1) * n - τ)) ≤ E * (K + 1) * τ * n) :
    τ - n * E ≤ 2 * K * n - K * K * (n * n / τ) + (τ / (K + 1) - K * (n * n / τ)) := by
  have hq : n * n / τ * τ = n * n := div_mul_cancel₀ _ hτ.ne'
  have hp : τ / (K + 1) * (K + 1) = τ := div_mul_cancel₀ _ hK.ne'
  refine le_of_mul_le_mul_right ?_ (mul_pos hτ hK)
  have e : (2 * K * n - K * K * (n * n / τ) + (τ / (K + 1) - K * (n * n / τ))) * (τ * (K + 1)) =
      2 * K * n * (τ * (K + 1)) - K * K * (n * n / τ * τ) * (K + 1) +
        (τ / (K + 1) * (K + 1) * τ - K * (n * n / τ * τ) * (K + 1)) := by ring
  rw [e, hq, hp]
  linarith

/-- The real inequality behind (C2). -/
lemma c2_real {n τ K : ℝ} (hn : 0 < n) (hK : K = 1 ∨ 2 ≤ K) (hKn : K * n ≤ τ)
    (hτK : τ ≤ (K + 1) * n) :
    τ - n * E0 ≤ 2 * K * n - K * K * (n * n / τ) + max 0 (τ / (K + 1) - K * (n * n / τ)) := by
  have hr := sqrt2_sq
  have hlb := sqrt2_lb
  have hE0 := E0_lb
  have hmaxL := le_max_left (0:ℝ) (τ / (K + 1) - K * (n * n / τ))
  have hmaxR := le_max_right (0:ℝ) (τ / (K + 1) - K * (n * n / τ))
  rcases hK with hK | hK
  · subst hK
    have hτ : 0 < τ := by linarith
    by_cases hc : τ ≤ √2 * n
    · have h1 : 0 ≤ (√2 * n - τ) * (√2 * τ - n) := by
        refine mul_nonneg (by linarith) ?_
        have : n ≤ √2 * τ := by
          calc n ≤ τ := by linarith
            _ = 1 * τ := (one_mul τ).symm
            _ ≤ √2 * τ := mul_le_mul_of_nonneg_right (by linarith) hτ.le
        linarith
      have key : E0 * τ * n - (τ - 1 * n) * (τ - 1 * n) =
          √2 / 2 * ((√2 * n - τ) * (√2 * τ - n)) := by
        unfold E0
        linear_combination ((n * n + τ * τ) / 2 - √2 * n * τ / 2) * hr
      have h2 : (τ - 1 * n) * (τ - 1 * n) ≤ E0 * τ * n := by
        have := mul_nonneg (by positivity : (0:ℝ) ≤ √2 / 2) h1
        linarith
      have := c2_A hτ h2
      linarith
    · have hc' : √2 * n ≤ τ := le_of_lt (not_le.mp hc)
      have h1 : 0 ≤ (τ - √2 * n) * (2 * √2 * n - τ) := by
        refine mul_nonneg (by linarith) ?_
        have : 2 * n ≤ 2 * √2 * n := by
          have h3 : 1 * n ≤ √2 * n := mul_le_mul_of_nonneg_right (by linarith) hn.le
          linarith
        linarith
      have key : E0 * (1 + 1) * τ * n - 1 * (((1 + 1) * n - τ) * ((1 + 1) * n - τ)) =
          (τ - √2 * n) * (2 * √2 * n - τ) := by
        unfold E0
        linear_combination (2 * n * n) * hr
      have h2 : 1 * (((1 + 1) * n - τ) * ((1 + 1) * n - τ)) ≤ E0 * (1 + 1) * τ * n := by
        linarith
      have := c2_B hτ (by norm_num : (0:ℝ) < 1 + 1) h2
      linarith
  · have hK0 : 0 ≤ K := by linarith
    have hKn2 : 2 * n ≤ K * n := mul_le_mul_of_nonneg_right hK hn.le
    have hτ : 0 < τ := by linarith
    have hnn : 0 < n * n := mul_pos hn hn
    have hE00 : 0 ≤ E0 := by linarith
    by_cases hc : τ - K * n ≤ 9 / 20 * n
    · have hx0 : 0 ≤ τ - K * n := by linarith
      have hxx : (τ - K * n) * (τ - K * n) ≤ (9 / 20 * n) * (9 / 20 * n) :=
        mul_le_mul hc hc hx0 (by linarith)
      have hE1 : 0.12 * (2 * n) ≤ E0 * τ :=
        mul_le_mul hE0 (by linarith) (by linarith) hE00
      have hE2 : 0.12 * (2 * n) * n ≤ E0 * τ * n := mul_le_mul_of_nonneg_right hE1 hn.le
      have h2 : (τ - K * n) * (τ - K * n) ≤ E0 * τ * n := by
        have e1 : (9 / 20 * n) * (9 / 20 * n) = 81 / 400 * (n * n) := by ring
        have e2 : (0.12:ℝ) * (2 * n) * n = 24 / 100 * (n * n) := by ring
        linarith
      have := c2_A hτ h2
      linarith
    · have hc' : 9 / 20 * n < τ - K * n := not_le.mp hc
      have hy0 : 0 ≤ (K + 1) * n - τ := by linarith
      have hy1 : (K + 1) * n - τ ≤ 11 / 20 * n := by linarith
      have hyy : ((K + 1) * n - τ) * ((K + 1) * n - τ) ≤ (11 / 20 * n) * (11 / 20 * n) :=
        mul_le_mul hy1 hy1 hy0 (by linarith)
      have h1 : K * (((K + 1) * n - τ) * ((K + 1) * n - τ)) ≤
          K * ((11 / 20 * n) * (11 / 20 * n)) := mul_le_mul_of_nonneg_left hyy hK0
      have hE1 : 0.12 * 3 ≤ E0 * (K + 1) :=
        mul_le_mul hE0 (by linarith) (by norm_num) hE00
      have hE2 : 0.12 * 3 * (K * n) ≤ E0 * (K + 1) * τ :=
        mul_le_mul hE1 hKn (mul_nonneg hK0 hn.le) (mul_nonneg hE00 (by linarith))
      have hE3 : 0.12 * 3 * (K * n) * n ≤ E0 * (K + 1) * τ * n :=
        mul_le_mul_of_nonneg_right hE2 hn.le
      have h2 : K * (((K + 1) * n - τ) * ((K + 1) * n - τ)) ≤ E0 * (K + 1) * τ * n := by
        have e1 : K * ((11 / 20 * n) * (11 / 20 * n)) = 121 / 400 * (K * (n * n)) := by ring
        have e2 : (0.12:ℝ) * 3 * (K * n) * n = 36 / 100 * (K * (n * n)) := by ring
        have h3 : 0 ≤ K * (n * n) := mul_nonneg hK0 hnn.le
        linarith
      have := c2_B hτ (by linarith : (0:ℝ) < K + 1) h2
      linarith

/-- (C2): between `n` and `n * T` the count misses `τ` by at most `n * E0 + 1`. -/
lemma C2 {n T τ : ℕ} (hn : 0 < n) (h1 : n ≤ τ) (h2 : τ < n * T) :
    (τ:ℝ) - n * E0 - 1 ≤
      (((Finset.Icc 1 n ×ˢ Finset.range (2 * T + 1)).filter
        (fun i => th n T i.1 i.2 ≤ τ)).card : ℝ) := by
  have hK1 : 1 ≤ τ / n := Nat.div_pos h1 hn
  have hKT : τ / n < T := Nat.div_lt_of_lt_mul h2
  have hKn : τ / n * n ≤ τ := Nat.div_mul_le_self τ n
  have hτK : τ < (τ / n + 1) * n := by
    rw [Nat.mul_comm]
    exact Nat.lt_mul_div_succ τ hn
  generalize τ / n = K at hK1 hKT hKn hτK
  have hτ : 0 < τ := by omega
  have hc := C2_count (T := T) hτ hKT hKn hτK
  have hKr : (K:ℝ) = 1 ∨ (2:ℝ) ≤ K := by
    rcases Nat.eq_or_lt_of_le hK1 with h | h
    · left
      exact_mod_cast h.symm
    · right
      have h' : 2 ≤ K := h
      exact_mod_cast h'
  have hr := c2_real (n := (n:ℝ)) (τ := (τ:ℝ)) (K := (K:ℝ)) (by exact_mod_cast hn) hKr
    (by exact_mod_cast hKn) (by exact_mod_cast hτK.le)
  linarith

/-! ## 5. Abel summation -/

lemma abel_lp_aux {ι : Type*} [DecidableEq ι] (s : Finset ι) (θ : ι → ℕ) (Ψ : ℕ → ℝ)
    (hanti : Antitone Ψ) (B E : ℝ) (n m : ℕ)
    (hG : ∀ τ, τ < m → (τ:ℝ) + 1 ≤
      ((s.filter (fun i => θ i ≤ τ)).card : ℝ) + B + (if n ≤ τ then E else 0)) :
    ∀ k, k < m →
      ∑ τ ∈ Finset.range (k + 1), Ψ τ +
        (((s.filter (fun i => θ i ≤ k)).card : ℝ) + B + (if n ≤ k then E else 0) -
          ((k:ℝ) + 1)) * Ψ k ≤
      ∑ i ∈ s.filter (fun i => θ i ≤ k), Ψ (θ i) + B * Ψ 0 +
        (if n ≤ k then E * Ψ n else 0) := by
  intro k
  induction k with
  | zero =>
    intro _
    have e1 : ∑ i ∈ s.filter (fun i => θ i ≤ 0), Ψ (θ i) =
        ((s.filter (fun i => θ i ≤ 0)).card : ℝ) * Ψ 0 := by
      have h : ∀ i ∈ s.filter (fun i => θ i ≤ 0), Ψ (θ i) = Ψ 0 := by
        intro i hi
        rw [Finset.mem_filter] at hi
        rw [Nat.le_zero.mp hi.2]
      rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul]
    have e2 : ∑ τ ∈ Finset.range (0 + 1), Ψ τ = Ψ 0 := by simp
    have e3 : (if n ≤ 0 then E * Ψ n else 0) = (if n ≤ 0 then E else 0) * Ψ 0 := by
      by_cases hn : n ≤ 0
      · rw [if_pos hn, if_pos hn, Nat.le_zero.mp hn]
      · rw [if_neg hn, if_neg hn, zero_mul]
    rw [e1, e2, e3, Nat.cast_zero]
    apply le_of_eq
    ring
  | succ k ih =>
    intro hk
    have ihk := ih (by omega)
    have hGk := hG k (by omega)
    have hΨ : Ψ (k + 1) ≤ Ψ k := hanti (Nat.le_add_right k 1)
    have hsplit : s.filter (fun i => θ i ≤ k + 1) =
        s.filter (fun i => θ i ≤ k) ∪ s.filter (fun i => θ i = k + 1) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hi, h⟩
        rcases Nat.lt_or_ge (θ i) (k + 1) with h' | h'
        · left
          exact ⟨hi, by omega⟩
        · right
          exact ⟨hi, by omega⟩
      · rintro (⟨hi, h⟩ | ⟨hi, h⟩)
        · exact ⟨hi, by omega⟩
        · exact ⟨hi, by omega⟩
    have hdisj : Disjoint (s.filter (fun i => θ i ≤ k)) (s.filter (fun i => θ i = k + 1)) := by
      rw [Finset.disjoint_left]
      intro i h1 h2
      rw [Finset.mem_filter] at h1 h2
      omega
    have hcard : ((s.filter (fun i => θ i ≤ k + 1)).card : ℝ) =
        ((s.filter (fun i => θ i ≤ k)).card : ℝ) +
          ((s.filter (fun i => θ i = k + 1)).card : ℝ) := by
      rw [hsplit, Finset.card_union_of_disjoint hdisj, Nat.cast_add]
    have hsum : ∑ i ∈ s.filter (fun i => θ i ≤ k + 1), Ψ (θ i) =
        ∑ i ∈ s.filter (fun i => θ i ≤ k), Ψ (θ i) +
          ((s.filter (fun i => θ i = k + 1)).card : ℝ) * Ψ (k + 1) := by
      have h : ∀ i ∈ s.filter (fun i => θ i = k + 1), Ψ (θ i) = Ψ (k + 1) := by
        intro i hi
        rw [Finset.mem_filter] at hi
        rw [hi.2]
      rw [hsplit, Finset.sum_union hdisj, Finset.sum_congr rfl h, Finset.sum_const,
        nsmul_eq_mul]
    have hI : (if n ≤ k + 1 then E else 0) =
        (if n ≤ k then E else 0) + (if n = k + 1 then E else 0) := by
      by_cases h1 : n ≤ k
      · have h2 : n ≤ k + 1 := by omega
        have h3 : ¬ n = k + 1 := by omega
        rw [if_pos h1, if_pos h2, if_neg h3, add_zero]
      · by_cases h2 : n = k + 1
        · have h3 : n ≤ k + 1 := by omega
          rw [if_neg h1, if_pos h3, if_pos h2, zero_add]
        · have h3 : ¬ n ≤ k + 1 := by omega
          rw [if_neg h1, if_neg h3, if_neg h2, add_zero]
    have hJ : (if n ≤ k + 1 then E * Ψ n else 0) =
        (if n ≤ k then E * Ψ n else 0) + (if n = k + 1 then E else 0) * Ψ (k + 1) := by
      by_cases h1 : n ≤ k
      · have h2 : n ≤ k + 1 := by omega
        have h3 : ¬ n = k + 1 := by omega
        rw [if_pos h1, if_pos h2, if_neg h3, zero_mul, add_zero]
      · by_cases h2 : n = k + 1
        · have h3 : n ≤ k + 1 := by omega
          rw [if_neg h1, if_pos h3, if_pos h2, zero_add, h2]
        · have h3 : ¬ n ≤ k + 1 := by omega
          rw [if_neg h1, if_neg h3, if_neg h2, zero_mul, add_zero]
    have hmul : (((s.filter (fun i => θ i ≤ k)).card : ℝ) + B + (if n ≤ k then E else 0) -
          ((k:ℝ) + 1)) * Ψ (k + 1) ≤
        (((s.filter (fun i => θ i ≤ k)).card : ℝ) + B + (if n ≤ k then E else 0) -
          ((k:ℝ) + 1)) * Ψ k :=
      mul_le_mul_of_nonneg_left hΨ (by linarith)
    rw [Finset.sum_range_succ, hcard, hsum, hI, hJ, Nat.cast_add, Nat.cast_one]
    linarith

/-- Abel summation: enough small thresholds bound the sum of an antitone sequence. -/
lemma abel_lp {ι : Type*} [DecidableEq ι] (s : Finset ι) (θ : ι → ℕ) (Ψ : ℕ → ℝ)
    (hanti : Antitone Ψ) (hnn : ∀ t, 0 ≤ Ψ t) (B E : ℝ) (hB : 0 ≤ B) (hE : 0 ≤ E) (n m : ℕ)
    (h1 : ∀ τ, τ < n → τ < m →
      (τ:ℝ) + 1 ≤ ((s.filter (fun i => θ i ≤ τ)).card : ℝ) + B)
    (h2 : ∀ τ, n ≤ τ → τ < m →
      (τ:ℝ) + 1 ≤ ((s.filter (fun i => θ i ≤ τ)).card : ℝ) + B + E) :
    ∑ τ ∈ Finset.range m, Ψ τ ≤ ∑ i ∈ s, Ψ (θ i) + B * Ψ 0 + E * Ψ n := by
  have hG : ∀ τ, τ < m → (τ:ℝ) + 1 ≤
      ((s.filter (fun i => θ i ≤ τ)).card : ℝ) + B + (if n ≤ τ then E else 0) := by
    intro τ hτ
    by_cases hn : n ≤ τ
    · rw [if_pos hn]
      exact h2 τ hn hτ
    · rw [if_neg hn, add_zero]
      exact h1 τ (by omega) hτ
  have hs0 : 0 ≤ ∑ i ∈ s, Ψ (θ i) := Finset.sum_nonneg (fun i _ => hnn (θ i))
  have hB0 : 0 ≤ B * Ψ 0 := mul_nonneg hB (hnn 0)
  have hEn : 0 ≤ E * Ψ n := mul_nonneg hE (hnn n)
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [Finset.range_zero, Finset.sum_empty]
    linarith
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hk := abel_lp_aux s θ Ψ hanti B E n (k + 1) hG k (by omega)
    have hGk := hG k (by omega)
    have hcoef : 0 ≤ (((s.filter (fun i => θ i ≤ k)).card : ℝ) + B +
        (if n ≤ k then E else 0) - ((k:ℝ) + 1)) * Ψ k :=
      mul_nonneg (by linarith) (hnn k)
    have hsub : ∑ i ∈ s.filter (fun i => θ i ≤ k), Ψ (θ i) ≤ ∑ i ∈ s, Ψ (θ i) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ => hnn (θ i))
    have hite : (if n ≤ k then E * Ψ n else 0) ≤ E * Ψ n := by
      by_cases hn : n ≤ k
      · rw [if_pos hn]
      · rw [if_neg hn]
        exact hEn
    linarith

/-! ## 6. The bound for fixed parameters -/

theorem fixed_bound {N : ℕ} {A : Finset ℕ} (hA : Adm N A) {n w T z Q L : ℕ}
    (hn : 0 < n) (hw : 0 < w) (hT : 0 < T) (hNw : N ≤ (n * w) * (n * w))
    (hQ : ∀ d, 0 < d → d < 2 * T + 1 → ∀ p : ℕ, p.Prime → p ≤ z → p * d ∣ Q)
    (hz : 2 ≤ z) (hQ0 : 0 < Q)
    (hL : ∀ D, D ≤ N → (D.primeFactors.filter (fun p => z < p)).card ≤ L) :
    (A.card : ℝ) ≤ (n:ℝ) * w +
      n * (((2 * T + 1) * (Q + (2 * T + 1)) +
        (2 * T + 1) * ((2 * T + 1) * (2 * T + 1) * (L * (w / z + 1))) : ℕ) : ℝ) +
      2 * w + n * E0 * (((w:ℝ) + 1) / 2) + ((N / (n * T * w) : ℕ) : ℝ) := by
  have hsplit := card_split hA (w := w) (m := n * T) (Nat.mul_pos (Nat.mul_pos hn hT) hw)
  have hE0 : 0 ≤ E0 := by linarith [E0_lb]
  have habel : ∑ τ ∈ Finset.range (n * T), (Psi A N w τ : ℝ) ≤
      ∑ i ∈ Finset.Icc 1 n ×ˢ Finset.range (2 * T + 1), (Psi A N w (th n T i.1 i.2) : ℝ) +
        2 * (Psi A N w 0 : ℝ) + (n * E0) * (Psi A N w n : ℝ) := by
    refine abel_lp (Finset.Icc 1 n ×ˢ Finset.range (2 * T + 1)) (fun i => th n T i.1 i.2)
      (fun τ => (Psi A N w τ : ℝ)) ?_ (fun t => Nat.cast_nonneg _) 2 (n * E0) (by norm_num)
      (mul_nonneg (Nat.cast_nonneg n) hE0) n (n * T) ?_ ?_
    · intro a b hab
      show (Psi A N w b : ℝ) ≤ (Psi A N w a : ℝ)
      exact_mod_cast Psi_antitone A N w hab
    · intro τ hτn _
      show (τ:ℝ) + 1 ≤ (((Finset.Icc 1 n ×ˢ Finset.range (2 * T + 1)).filter
        (fun i => th n T i.1 i.2 ≤ τ)).card : ℝ) + 2
      have h := C1 (n := n) (T := T) hτn
      have h' : (τ:ℝ) ≤ (((Finset.Icc 1 n ×ˢ Finset.range (2 * T + 1)).filter
        (fun i => th n T i.1 i.2 ≤ τ)).card : ℝ) := by exact_mod_cast h
      linarith
    · intro τ hnτ hτm
      show (τ:ℝ) + 1 ≤ (((Finset.Icc 1 n ×ˢ Finset.range (2 * T + 1)).filter
        (fun i => th n T i.1 i.2 ≤ τ)).card : ℝ) + 2 + n * E0
      have h := C2 (T := T) hn hnτ hτm
      linarith
  have hfam : ∑ i ∈ Finset.Icc 1 n ×ˢ Finset.range (2 * T + 1), Psi A N w (th n T i.1 i.2) ≤
      n * (w + ((2 * T + 1) * (Q + (2 * T + 1)) +
        (2 * T + 1) * ((2 * T + 1) * (2 * T + 1) * (L * (w / z + 1))))) := by
    have e : ∑ i ∈ Finset.Icc 1 n ×ˢ Finset.range (2 * T + 1), Psi A N w (th n T i.1 i.2) =
        ∑ j ∈ Finset.Icc 1 n, ∑ c ∈ Finset.range (2 * T + 1), Psi A N w (th n T j c) :=
      Finset.sum_product _ _ _
    have hc : (Finset.Icc 1 n).card = n := by simp
    rw [e]
    calc ∑ j ∈ Finset.Icc 1 n, ∑ c ∈ Finset.range (2 * T + 1), Psi A N w (th n T j c)
        ≤ ∑ j ∈ Finset.Icc 1 n, (w + (2 * T + 1) * (Q + (2 * T + 1)) +
            (2 * T + 1) * ((2 * T + 1) * (2 * T + 1) * (L * (w / z + 1)))) := by
          refine Finset.sum_le_sum (fun j hj => ?_)
          rw [Finset.mem_Icc] at hj
          exact pattern_Psi hA hNw hj.1 hj.2 hQ hz hQ0 hL
      _ = _ := by
          rw [Finset.sum_const, hc, smul_eq_mul]
          ring
  have h0 := Psi_le_w A N w 0
  have hhalf := Psi_half hA hNw (le_refl n)
  have hsplitR : (A.card : ℝ) ≤ ∑ τ ∈ Finset.range (n * T), (Psi A N w τ : ℝ) +
      ((N / (n * T * w) : ℕ) : ℝ) := by exact_mod_cast hsplit
  have hfamR : ∑ i ∈ Finset.Icc 1 n ×ˢ Finset.range (2 * T + 1),
        (Psi A N w (th n T i.1 i.2) : ℝ) ≤
      (n:ℝ) * ((w:ℝ) + (((2 * T + 1) * (Q + (2 * T + 1)) +
        (2 * T + 1) * ((2 * T + 1) * (2 * T + 1) * (L * (w / z + 1))) : ℕ) : ℝ)) := by
    exact_mod_cast hfam
  have h0R : (Psi A N w 0 : ℝ) ≤ w := by exact_mod_cast h0
  have hhalfR : (Psi A N w n : ℝ) ≤ ((w:ℝ) + 1) / 2 := by
    have : (2:ℝ) * (Psi A N w n : ℝ) ≤ (w:ℝ) + 1 := by exact_mod_cast hhalf
    linarith
  have hmulE : (n * E0) * (Psi A N w n : ℝ) ≤ (n * E0) * (((w:ℝ) + 1) / 2) :=
    mul_le_mul_of_nonneg_left hhalfR (mul_nonneg (Nat.cast_nonneg n) hE0)
  linarith

/-! ## 7. Asymptotics -/

/-- The real-number bookkeeping: the fixed-parameter bound is at most `(3√2/4 + ε) R`. -/
lemma asym_core {ε R n w T Q L z lam F fT wz tail card : ℝ}
    (h0 : card ≤ n * w + n * ((2 * T + 1) * (Q + (2 * T + 1)) +
      (2 * T + 1) * ((2 * T + 1) * (2 * T + 1) * (L * (wz + 1)))) + 2 * w +
      n * E0 * ((w + 1) / 2) + tail)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 ≤ R) (hn : 1 ≤ n) (hT : 1 ≤ T)
    (hw0 : 0 ≤ w) (hnw : n * w ≤ R + n)
    (hwz0 : 0 ≤ wz) (hwz : wz * z ≤ w)
    (hz : 1 ≤ z) (hzF : z ≤ F) (hFF : F * F ≤ R)
    (hfT : 0 ≤ fT) (hQ : Q ≤ fT * F)
    (hL0 : 0 ≤ L) (hL : L * lam ≤ 16 * z)
    (hlam : 256 * ((2 * T + 1) * (2 * T + 1) * (2 * T + 1)) ≤ ε * lam)
    (htail0 : 0 ≤ tail) (htail : tail * T ≤ R) (hεn : 16 ≤ ε * n) (hεT : 8 ≤ ε * T)
    (hC : 8 * (4 * n + 2 + n * (2 * T + 1) * fT + n * (2 * T + 1) * (2 * T + 1)) ≤ ε * F) :
    card ≤ (3 * √2 / 4 + ε) * R := by
  have hn0 : 0 < n := by linarith
  have hz0 : 0 < z := by linarith
  have hF1 : 1 ≤ F := le_trans hz hzF
  have hF0 : 0 < F := by linarith
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = 2 * T + 1 := ⟨_, rfl⟩
  rw [← hk] at h0 hlam hC
  have hk0 : 0 < k := by linarith
  have hA1 : 256 * (k * k * k) * L ≤ ε * lam * L := mul_le_mul_of_nonneg_right hlam hL0
  have hA2 : ε * (L * lam) ≤ ε * (16 * z) := mul_le_mul_of_nonneg_left hL hε.le
  have hA : k * k * k * L ≤ ε / 16 * z := by linarith
  have hB1 : k * k * k * L * (wz + 1) ≤ ε / 16 * z * (wz + 1) :=
    mul_le_mul_of_nonneg_right hA (by linarith)
  have hB2 : n * (k * k * k * L * (wz + 1)) ≤ n * (ε / 16 * z * (wz + 1)) :=
    mul_le_mul_of_nonneg_left hB1 hn0.le
  have hB3 : ε / 16 * (n * (wz * z)) ≤ ε / 16 * (n * w) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwz hn0.le) (by positivity)
  have hB4 : ε / 16 * (n * w) ≤ ε / 16 * (R + n) :=
    mul_le_mul_of_nonneg_left hnw (by positivity)
  have hB : n * (k * (k * k * (L * (wz + 1)))) ≤ ε / 16 * (R + n) + ε / 16 * (n * z) := by
    linarith
  have hC1 : n * (k * (Q + k)) ≤ n * (k * (fT * F + k)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hk0.le) hn0.le
  have hD : n * w + n * E0 * ((w + 1) / 2) =
      3 * √2 / 4 * (n * w) + (3 * √2 / 4 - 1) * n := by
    unfold E0
    ring
  have hD2 : 3 * √2 / 4 * (n * w) ≤ 3 * √2 / 4 * (R + n) :=
    mul_le_mul_of_nonneg_left hnw (by positivity)
  have hD3 : √2 * n ≤ 1.4143 * n := mul_le_mul_of_nonneg_right sqrt2_ub hn0.le
  have hE1 : 16 * w ≤ ε * n * w := mul_le_mul_of_nonneg_right hεn hw0
  have hE2 : ε * (n * w) ≤ ε * (R + n) := mul_le_mul_of_nonneg_left hnw hε.le
  have hE : 2 * w ≤ ε / 8 * (R + n) := by linarith
  have hF1' : 8 * tail ≤ ε * T * tail := mul_le_mul_of_nonneg_right hεT htail0
  have hF2 : ε * (tail * T) ≤ ε * R := mul_le_mul_of_nonneg_left htail hε.le
  have hF : tail ≤ ε / 8 * R := by linarith
  have hG1 : 8 * (4 * n + 2 + n * k * fT + n * k * k) * F ≤ ε * F * F :=
    mul_le_mul_of_nonneg_right hC hF0.le
  have hG2 : ε * (F * F) ≤ ε * R := mul_le_mul_of_nonneg_left hFF hε.le
  have hG : (4 * n + 2 + n * k * fT + n * k * k) * F ≤ ε / 8 * R := by linarith
  have hH1 : n ≤ n * F := le_mul_of_one_le_right hn0.le hF1
  have hH2 : n * k * k ≤ n * k * k * F :=
    le_mul_of_one_le_right (mul_nonneg (mul_nonneg hn0.le hk0.le) hk0.le) hF1
  have hH3 : ε * n ≤ 1 * n := mul_le_mul_of_nonneg_right hε1 hn0.le
  have hH4 : ε * (n * z) ≤ 1 * (n * z) :=
    mul_le_mul_of_nonneg_right hε1 (mul_nonneg hn0.le hz0.le)
  have hH5 : n * z ≤ n * F := mul_le_mul_of_nonneg_left hzF hn0.le
  have hεR : 0 ≤ ε * R := mul_nonneg hε.le hR
  have hcst : 3 * √2 / 4 * n + (3 * √2 / 4 - 1) * n + n * (k * (fT * F + k)) +
      ε / 16 * n + ε / 16 * (n * z) + ε / 8 * n ≤ ε / 8 * R := by
    have e : n * (k * (fT * F + k)) = n * k * fT * F + n * k * k := by ring
    have hnF : 0 ≤ n * F := mul_nonneg hn0.le hF0.le
    linarith
  linarith

lemma log_bound {z N : ℕ} (hz : 2 ≤ z) (hN : N ≠ 0) (hzN : Nat.log 256 N = z) :
    Nat.log z N * Nat.log 2 z ≤ 16 * z := by
  have h1 : 2 ^ Nat.log 2 z ≤ z := Nat.pow_log_le_self 2 (by omega)
  have h2 : z ^ Nat.log z N ≤ N := Nat.pow_log_le_self z hN
  have h3 : N < 256 ^ (z + 1) := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 256) N
    rwa [hzN] at h
  have h4 : (2 ^ Nat.log 2 z) ^ Nat.log z N ≤ z ^ Nat.log z N := Nat.pow_le_pow_left h1 _
  have h5 : 2 ^ (Nat.log 2 z * Nat.log z N) < 2 ^ (8 * (z + 1)) := by
    calc 2 ^ (Nat.log 2 z * Nat.log z N) = (2 ^ Nat.log 2 z) ^ Nat.log z N := pow_mul 2 _ _
      _ ≤ z ^ Nat.log z N := h4
      _ ≤ N := h2
      _ < 256 ^ (z + 1) := h3
      _ = 2 ^ (8 * (z + 1)) := by
          rw [pow_mul]
          norm_num
  have h6 : Nat.log 2 z * Nat.log z N < 8 * (z + 1) :=
    (Nat.pow_lt_pow_iff_right (by norm_num)).mp h5
  have h7 : Nat.log z N * Nat.log 2 z = Nat.log 2 z * Nat.log z N := Nat.mul_comm _ _
  omega

/-- The upper bound for `ε ≤ 1`. -/
theorem upper_small (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ N0 : ℕ, ∀ N ≥ N0, ∀ A, Adm N A → (A.card : ℝ) ≤ (3 * √2 / 4 + ε) * √(N:ℝ) := by
  obtain ⟨T, hT⟩ := exists_nat_ge (8 / ε)
  obtain ⟨n, hn⟩ := exists_nat_ge (16 / ε)
  rw [div_le_iff₀ hε] at hT hn
  have hTε : 8 ≤ ε * T := by linarith
  have hnε : 16 ≤ ε * n := by linarith
  have hT8 : (1:ℝ) ≤ T := by
    have h := mul_le_mul_of_nonneg_right hε1 (Nat.cast_nonneg (α := ℝ) T)
    linarith
  have hn16 : (1:ℝ) ≤ n := by
    have h := mul_le_mul_of_nonneg_right hε1 (Nat.cast_nonneg (α := ℝ) n)
    linarith
  have hT0 : 0 < T := by exact_mod_cast (by linarith : (0:ℝ) < T)
  have hn0 : 0 < n := by exact_mod_cast (by linarith : (0:ℝ) < n)
  obtain ⟨M1, hM1⟩ := exists_nat_ge
    (256 * ((2 * (T:ℝ) + 1) * (2 * T + 1) * (2 * T + 1)) / ε)
  obtain ⟨M2, hM2⟩ := exists_nat_ge
    (8 * (4 * (n:ℝ) + 2 + n * (2 * T + 1) * ((2 * T).factorial : ℝ) +
      n * (2 * T + 1) * (2 * T + 1)) / ε)
  rw [div_le_iff₀ hε] at hM1 hM2
  refine ⟨256 ^ (2 ^ M1 + M2 + 2), fun N hN A hA => ?_⟩
  have hN0 : N ≠ 0 := by
    have hpos : 0 < 256 ^ (2 ^ M1 + M2 + 2) := pow_pos (by norm_num) _
    omega
  have hzge : 2 ^ M1 + M2 + 2 ≤ Nat.log 256 N := Nat.le_log_of_pow_le (by norm_num) hN
  have hpow : 256 ^ Nat.log 256 N ≤ N := Nat.pow_log_le_self 256 hN0
  obtain ⟨z, hzdef⟩ : ∃ z, Nat.log 256 N = z := ⟨_, rfl⟩
  rw [hzdef] at hzge hpow
  have hpM : 0 < 2 ^ M1 := pow_pos (by norm_num) M1
  have hz2 : 2 ≤ z := by omega
  have hM1z : 2 ^ M1 ≤ z := by omega
  have hM2z : M2 ≤ z := by omega
  have hlam : M1 ≤ Nat.log 2 z := Nat.le_log_of_pow_le (by norm_num) hM1z
  have hLlam := log_bound hz2 hN0 hzdef
  have hLdef : ∀ D, D ≤ N → (D.primeFactors.filter (fun p => z < p)).card ≤ Nat.log z N :=
    fun D hD => large_primeFactors_card hz2 hD
  obtain ⟨L, hL⟩ : ∃ L, Nat.log z N = L := ⟨_, rfl⟩
  obtain ⟨lam, hlamdef⟩ : ∃ lam, Nat.log 2 z = lam := ⟨_, rfl⟩
  rw [hL] at hLdef hLlam
  rw [hlamdef] at hlam hLlam
  have hzF : z < 4 ^ z := Nat.lt_pow_self (by norm_num)
  have hFF : 4 ^ z * 4 ^ z * (4 ^ z * 4 ^ z) ≤ N := by
    have e : 4 ^ z * 4 ^ z * (4 ^ z * 4 ^ z) = 256 ^ z := by
      rw [show (256:ℕ) = 4 * 4 * (4 * 4) by norm_num, mul_pow, mul_pow]
    rw [e]
    exact hpow
  have hQle : primorial z * (2 * T).factorial ≤ 4 ^ z * (2 * T).factorial :=
    Nat.mul_le_mul_right _ (primorial_le_four_pow z)
  obtain ⟨F, hFdef⟩ : ∃ F, 4 ^ z = F := ⟨_, rfl⟩
  rw [hFdef] at hzF hFF hQle
  have hFs : F * F ≤ Nat.sqrt N := Nat.le_sqrt.mpr hFF
  have hs1 : N < (Nat.sqrt N + 1) * (Nat.sqrt N + 1) := Nat.lt_succ_sqrt N
  have hsR : ((Nat.sqrt N : ℕ) : ℝ) ≤ √(N:ℝ) := Real.nat_sqrt_le_real_sqrt
  obtain ⟨s, hsdef⟩ : ∃ s, Nat.sqrt N = s := ⟨_, rfl⟩
  rw [hsdef] at hFs hs1 hsR
  have hw1 : s < n * (s / n + 1) := Nat.lt_mul_div_succ s hn0
  have hw2 : n * (s / n + 1) ≤ s + n := by
    have h := Nat.mul_div_le s n
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hw0 : 0 < s / n + 1 := Nat.succ_pos _
  obtain ⟨w, hwdef⟩ : ∃ w, s / n + 1 = w := ⟨_, rfl⟩
  rw [hwdef] at hw1 hw2 hw0
  have hw1' : s + 1 ≤ n * w := Nat.succ_le_of_lt hw1
  have hNw : N ≤ (n * w) * (n * w) := by
    have h : (s + 1) * (s + 1) ≤ (n * w) * (n * w) := Nat.mul_le_mul hw1' hw1'
    omega
  have hQdvd : ∀ d, 0 < d → d < 2 * T + 1 → ∀ p : ℕ, p.Prime → p ≤ z →
      p * d ∣ primorial z * (2 * T).factorial := by
    intro d hd0 hd p hp hpz
    exact Nat.mul_dvd_mul ((Nat.Prime.dvd_primorial_iff hp).mpr hpz)
      (Nat.dvd_factorial hd0 (by omega))
  have hQpos : 0 < primorial z * (2 * T).factorial :=
    Nat.mul_pos (primorial_pos z) (Nat.factorial_pos _)
  obtain ⟨Q, hQdef⟩ : ∃ Q, primorial z * (2 * T).factorial = Q := ⟨_, rfl⟩
  rw [hQdef] at hQdvd hQpos hQle
  have hfix := fixed_bound hA hn0 hw0 hT0 hNw hQdvd hz2 hQpos hLdef
  have htailN : N / (n * T * w) * T ≤ s := by
    have e : n * T * w = n * w * T := by ring
    have h1 : N / (n * w) < s + 1 := Nat.div_lt_of_lt_mul (by
      calc N < (s + 1) * (s + 1) := hs1
        _ ≤ (n * w) * (s + 1) := Nat.mul_le_mul_right _ hw1')
    rw [e, ← Nat.div_div_eq_div_mul]
    have h2 := Nat.div_mul_le_self (N / (n * w)) T
    omega
  have h0 : (A.card : ℝ) ≤ (n:ℝ) * w + n * ((2 * (T:ℝ) + 1) * ((Q:ℝ) + (2 * T + 1)) +
      (2 * T + 1) * ((2 * T + 1) * (2 * T + 1) * ((L:ℝ) * (((w / z : ℕ) : ℝ) + 1)))) +
      2 * w + n * E0 * (((w:ℝ) + 1) / 2) + ((N / (n * T * w) : ℕ) : ℝ) := by
    have h := hfix
    push_cast at h
    linarith
  have hnwR : (n:ℝ) * w ≤ √(N:ℝ) + n := by
    have h : ((n * w : ℕ) : ℝ) ≤ ((s + n : ℕ) : ℝ) := by exact_mod_cast hw2
    push_cast at h
    linarith
  have hwzR : ((w / z : ℕ) : ℝ) * z ≤ w := by exact_mod_cast Nat.div_mul_le_self w z
  have hz1R : (1:ℝ) ≤ z := by exact_mod_cast (by omega : 1 ≤ z)
  have hzFR : (z:ℝ) ≤ F := by exact_mod_cast hzF.le
  have hFFR : (F:ℝ) * F ≤ √(N:ℝ) := by
    have h : ((F * F : ℕ) : ℝ) ≤ (s:ℝ) := by exact_mod_cast hFs
    push_cast at h
    linarith
  have hQR : (Q:ℝ) ≤ ((2 * T).factorial : ℝ) * F := by
    have h : (Q:ℝ) ≤ ((F * (2 * T).factorial : ℕ) : ℝ) := by exact_mod_cast hQle
    push_cast at h
    linarith
  have hLlamR : (L:ℝ) * lam ≤ 16 * z := by exact_mod_cast hLlam
  have hlamR : 256 * ((2 * (T:ℝ) + 1) * (2 * T + 1) * (2 * T + 1)) ≤ ε * lam := by
    have h1 : (M1:ℝ) ≤ lam := by exact_mod_cast hlam
    have h2 := mul_le_mul_of_nonneg_left h1 hε.le
    linarith
  have htailR : ((N / (n * T * w) : ℕ) : ℝ) * (T:ℝ) ≤ √(N:ℝ) := by
    have h : ((N / (n * T * w) : ℕ) : ℝ) * (T:ℝ) ≤ (s:ℝ) := by exact_mod_cast htailN
    linarith
  have hCR : 8 * (4 * (n:ℝ) + 2 + n * (2 * T + 1) * ((2 * T).factorial : ℝ) +
      n * (2 * T + 1) * (2 * T + 1)) ≤ ε * F := by
    have h1 : (M2:ℝ) ≤ F := by exact_mod_cast le_trans hM2z hzF.le
    have h2 := mul_le_mul_of_nonneg_left h1 hε.le
    linarith
  exact asym_core h0 hε hε1 (Real.sqrt_nonneg _) hn16 hT8 (Nat.cast_nonneg w) hnwR
    (Nat.cast_nonneg _) hwzR hz1R hzFR hFFR (Nat.cast_nonneg _) hQR (Nat.cast_nonneg L)
    hLlamR hlamR (Nat.cast_nonneg _) htailR hnε hTε hCR

/-- The upper bound: for every `ε > 0` and all large `N`, `|A| ≤ (3√2/4 + ε) √N`. -/
theorem upper_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N ≥ N0, ∀ A, Adm N A → (A.card : ℝ) ≤ (3 * √2 / 4 + ε) * √(N:ℝ) := by
  obtain ⟨N0, h⟩ := upper_small (min ε 1) (lt_min hε one_pos) (min_le_right _ _)
  refine ⟨N0, fun N hN A hA => le_trans (h N hN A hA) ?_⟩
  exact mul_le_mul_of_nonneg_right (by linarith [min_le_left ε 1]) (Real.sqrt_nonneg _)

end E441C

theorem OMA.solution : type_of% @Erdos441.erdos_441.variants.chen := by
  exact E441C.final E441C.lower_construction E441C.upper_bound
