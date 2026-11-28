import FormalConjectures.ErdosProblems.«441»

-- Problem: Erdős Problem 441 — chen dai upper bound
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/441.lean:130 (declaration Erdos441.erdos_441.variants.chen_dai_upper_bound)
-- Credit: @fecheteluca (the owner of the agent is credited as the solver)

/-!
# The upper bound of Dai and Chen: `g(N) ≤ √(9N/8) + O(√(N / log N) · log log N)`

`g N` is the largest size of a set `A ⊆ [1, N]` all of whose pairwise least common multiples are
at most `N` (an admissible set).  This file proves
`g N - √(9N/8) = O(√(N / log N) · log log N)` by an elementary argument; the constant is `88`
and the bound holds for all `N ≥ 2 ^ 2 ^ 34`.

* From below (§1): all integers up to `√(N/2)` together with the even integers up to `√(2N)`
  form an admissible set of size at least `√(9N/8) - 2`.
* Windows (§2): fix a window length `w` and let `Ψ(τ)` be the largest number of elements of `A`
  in a window `(u, u + w]` with `u ≥ τ w`.  Then `Ψ` is antitone,
  `|A| ≤ ∑_{τ < m} Ψ(τ) + N / (m w)`, and `Ψ(τ) ≤ (w + 1) / 2` once `τ w ≥ √N`.
* The pattern lemma (§5): if the positions `X_c`, `c < k = 2T + 1`, satisfy
  `(c - c') N ≤ X_c X_c'` for `c' < c`, then the `k` windows `(X_c, X_c + w]` contain together at
  most `w + k (H R + k) + k³ L (w / z + 1)` elements of `A`.  Two elements `x`, `y` of `A` at the
  same offset in the windows `c` and `c'` have `x y ≤ gcd(x, y) N`, so their gcd exceeds
  `d = c - c'`.  Move the windows to positions `Y_c ≡ c` modulo `H = (4T)# (2T)!` such that
  moreover no prime in `(4T, z]` divides a difference `Y_c - Y_c'`.  The gcd divides
  `x - y = d (H' t + 1)`, where `H' = H / d` is divisible by every prime `≤ 4T`; as it exceeds
  `d`, one of its prime factors is neither `≤ 4T` nor in `(4T, z]`.  So a prime `p > z` divides
  both `x` and `Y_c - Y_c' ≤ N`: there are at most `L = log N / log z` such primes, and each of
  them allows at most `w / z + 1` offsets.
* The positions `Y_c` are found one after the other by Brun's pure sieve (§3, §4): given at most
  `t` forbidden residues modulo every prime in `(M, z]`, where `2 t ≤ M`, some
  `m < R = 2 (z + 1)^(2t) (1 + t z)^J + 1` with `J = 4 t (log₂ (z + 1) + 1) + 2` avoids all of
  them.  The sieve is proved by induction over the list of primes, with the Bonferroni
  inequalities in the form of Buchstab's identity.
* Thresholds (§6) and Abel summation (§7): for the rows `1 ≤ j ≤ n` the thresholds
  `θ(j, c) = ⌈c n² / j⌉` (`0 < c ≤ T`) and `max(⌈|c| n² / j⌉, (|c| + 1) j)` (`-T ≤ c ≤ 0`) give
  admissible positions of windows.  A counting inequality, `#{(j, c) : θ(j, c) ≤ τ} ≥ τ` for
  `τ < n` and `≥ τ - n (3√2/2 - 2) - 1` for `n ≤ τ < n T`, turns the `n` row bounds into
  `|A| ≤ n w + n err + 2 w + n (3√2/2 - 2) (w + 1) / 2 + N / (n T w)` whenever `N ≤ (n w)²` (§8),
  where `err` is the error term of the pattern lemma.
* Parameters (§9): with `l = ⌊log₂ N⌋` and `a = ⌊log₂ l⌋` take `n = T = ⌊⌊√l⌋ / a⌋`, `z = l⁴`
  and `w = ⌊⌊√N⌋ / T⌋ + 1`.  Then `T k T (H R + k) ≤ 2 ^ (l / 2) ≤ √N`, every error term is at
  most a constant times `√N / T`, and `1 / T ≤ 8 log log N / √(log N)`.
-/

namespace E441D

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

/-! ## 3. A sieve -/

/-- Number of `m < L` in the class `r` modulo `Q` avoiding, for every entry `(p, Ω)` of the list,
the residues in `Ω` modulo `p`. -/
def cnt (l : List (ℕ × Finset ℕ)) (Q r L : ℕ) : ℕ :=
  ((Finset.range L).filter (fun m => m ≡ r [MOD Q] ∧ ∀ q ∈ l, m % q.1 ∉ q.2)).card

lemma cnt_nil_bounds {Q : ℕ} (hQ : 0 < Q) (r L : ℕ) :
    (L:ℝ) / Q - 1 ≤ (cnt [] Q r L : ℝ) ∧ (cnt [] Q r L : ℝ) ≤ (L:ℝ) / Q + 1 := by
  have h1 : cnt [] Q r L = L / Q + if r % Q < L % Q then 1 else 0 := by
    unfold cnt
    rw [← Nat.count_modEq_card L hQ r, Nat.count_eq_card_filter_range]
    congr 1
    apply Finset.filter_congr
    intro m _
    simp
  have hQ' : (0:ℝ) < Q := by exact_mod_cast hQ
  have h2 : ((L / Q : ℕ) : ℝ) ≤ (L:ℝ) / Q := Nat.cast_div_le
  have h3 : (L:ℝ) / Q < ((L / Q : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hQ']
    have h5 := Nat.lt_mul_div_succ L hQ
    have h4 : (L:ℝ) < (Q:ℝ) * (((L / Q : ℕ) : ℝ) + 1) := by exact_mod_cast h5
    linarith
  rw [h1]
  split_ifs
  · push_cast
    constructor <;> linarith
  · push_cast
    constructor <;> linarith

/-- Removing one entry `(p, Ω)`: the integers hitting `Ω` modulo `p` split into `|Ω|` classes
modulo `Q p` (Chinese remainder theorem). -/
lemma cnt_cons {p : ℕ} {Ω : Finset ℕ} (l : List (ℕ × Finset ℕ)) {Q : ℕ} (r L : ℕ)
    (hΩ : Ω ⊆ Finset.range p) (hcop : Nat.Coprime Q p) :
    ∃ ρ : ℕ → ℕ, cnt ((p, Ω) :: l) Q r L + ∑ ω ∈ Ω, cnt l (Q * p) (ρ ω) L = cnt l Q r L := by
  refine ⟨fun ω => (Nat.chineseRemainder hcop r ω : ℕ), ?_⟩
  have hρ : ∀ ω, (Nat.chineseRemainder hcop r ω : ℕ) ≡ r [MOD Q] ∧
      (Nat.chineseRemainder hcop r ω : ℕ) ≡ ω [MOD p] :=
    fun ω => (Nat.chineseRemainder hcop r ω).2
  have h1 := Finset.card_filter_add_card_filter_not
    (s := (Finset.range L).filter (fun m => m ≡ r [MOD Q] ∧ ∀ q ∈ l, m % q.1 ∉ q.2))
    (fun m => m % p ∉ Ω)
  have h2 : ((Finset.range L).filter (fun m => m ≡ r [MOD Q] ∧ ∀ q ∈ l, m % q.1 ∉ q.2)).filter
      (fun m => m % p ∉ Ω) =
      (Finset.range L).filter (fun m => m ≡ r [MOD Q] ∧ ∀ q ∈ (p, Ω) :: l, m % q.1 ∉ q.2) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, List.forall_mem_cons]
    tauto
  have h3 : (((Finset.range L).filter (fun m => m ≡ r [MOD Q] ∧ ∀ q ∈ l, m % q.1 ∉ q.2)).filter
      (fun m => ¬ m % p ∉ Ω)).card =
      ∑ ω ∈ Ω, cnt l (Q * p) ((Nat.chineseRemainder hcop r ω : ℕ)) L := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun m => m % p) (t := Ω)]
    · apply Finset.sum_congr rfl
      intro ω hω
      unfold cnt
      congr 1
      ext m
      have hω' : ω < p := Finset.mem_range.mp (hΩ hω)
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨⟨⟨hm, hr, hl⟩, _⟩, hmp⟩
        refine ⟨hm, ?_, hl⟩
        rw [← Nat.modEq_and_modEq_iff_modEq_mul hcop]
        refine ⟨hr.trans (hρ ω).1.symm, ?_⟩
        have h4 : m ≡ ω [MOD p] := by
          rw [Nat.ModEq, hmp, Nat.mod_eq_of_lt hω']
        exact h4.trans (hρ ω).2.symm
      · rintro ⟨hm, hmod, hl⟩
        rw [← Nat.modEq_and_modEq_iff_modEq_mul hcop] at hmod
        have h5 : m % p = ω := by
          have h6 := hmod.2.trans (hρ ω).2
          rw [Nat.ModEq, Nat.mod_eq_of_lt hω'] at h6
          exact h6
        refine ⟨⟨⟨hm, hmod.1.trans (hρ ω).1, hl⟩, ?_⟩, h5⟩
        rw [h5]
        exact not_not.mpr hω
    · intro m hm
      rw [Finset.mem_coe, Finset.mem_filter] at hm
      exact not_not.mp hm.2
  rw [h2, h3] at h1
  exact h1

/-- The density `|Ω| / p` of an entry. -/
noncomputable def xq (q : ℕ × Finset ℕ) : ℝ := (q.2.card : ℝ) / q.1

/-- The sieve product `∏ (1 - |Ω| / p)`. -/
noncomputable def Wp : List (ℕ × Finset ℕ) → ℝ
  | [] => 1
  | q :: l => (1 - xq q) * Wp l

/-- The majorant `∏ (1 + 2 |Ω| / p)`. -/
noncomputable def Pu : List (ℕ × Finset ℕ) → ℝ
  | [] => 1
  | q :: l => (1 + 2 * xq q) * Pu l

/-- The total number of forbidden residues. -/
def sm : List (ℕ × Finset ℕ) → ℕ
  | [] => 0
  | q :: l => q.2.card + sm l

lemma xq_nonneg (q : ℕ × Finset ℕ) : 0 ≤ xq q := by
  unfold xq
  positivity

lemma xq_le_one {q : ℕ × Finset ℕ} (h : q.2 ⊆ Finset.range q.1) : xq q ≤ 1 := by
  unfold xq
  have h1 : q.2.card ≤ q.1 := by simpa using Finset.card_le_card h
  rcases Nat.eq_zero_or_pos q.1 with h0 | h0
  · rw [h0]
    simp
  · rw [div_le_one (by exact_mod_cast h0)]
    exact_mod_cast h1

lemma Wp_bounds : ∀ l : List (ℕ × Finset ℕ), (∀ q ∈ l, q.2 ⊆ Finset.range q.1) →
    0 ≤ Wp l ∧ Wp l ≤ 1 := by
  intro l
  induction l with
  | nil =>
    intro _
    simp [Wp]
  | cons q l ih =>
    intro h
    have h1 := ih (fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))
    have h2 := xq_nonneg q
    have h3 := xq_le_one (h q List.mem_cons_self)
    simp only [Wp]
    constructor
    · exact mul_nonneg (by linarith) h1.1
    · nlinarith [h1.1, h1.2]

lemma one_le_Pu : ∀ l : List (ℕ × Finset ℕ), 1 ≤ Pu l := by
  intro l
  induction l with
  | nil => simp [Pu]
  | cons q l ih =>
    have h2 := xq_nonneg q
    simp only [Pu]
    nlinarith

/-- Brun's pure sieve in recursive form: truncating the inclusion–exclusion after `j` steps gives
an upper bound for odd `j` and a lower bound for even `j`. -/
theorem sieve_main (L : ℕ) : ∀ (l : List (ℕ × Finset ℕ)),
    (∀ q ∈ l, 0 < q.1 ∧ q.2 ⊆ Finset.range q.1) →
    l.Pairwise (fun a b => Nat.Coprime a.1 b.1) →
    ∀ (j Q r : ℕ), 0 < Q → (∀ q ∈ l, Nat.Coprime Q q.1) →
      (Odd j → (cnt l Q r L : ℝ) ≤
        (L:ℝ) / Q * (Wp l + Pu l / 2 ^ j) + (1 + (sm l : ℝ)) ^ j) ∧
      (Even j → (L:ℝ) / Q * (Wp l - Pu l / 2 ^ j) - (1 + (sm l : ℝ)) ^ j ≤
        (cnt l Q r L : ℝ)) := by
  intro l
  induction l with
  | nil =>
    intro _ _ j Q r hQ _
    have hb := cnt_nil_bounds hQ r L
    have hLQ : (0:ℝ) ≤ (L:ℝ) / Q := by positivity
    have h1 : (0:ℝ) ≤ 1 / 2 ^ j := by positivity
    have h2 := mul_nonneg hLQ h1
    simp only [Wp, Pu, sm, Nat.cast_zero, add_zero, one_pow]
    constructor
    · intro _
      have e : (L:ℝ) / Q * (1 + 1 / 2 ^ j) = (L:ℝ) / Q + (L:ℝ) / Q * (1 / 2 ^ j) := by ring
      linarith [hb.2]
    · intro _
      have e : (L:ℝ) / Q * (1 - 1 / 2 ^ j) = (L:ℝ) / Q - (L:ℝ) / Q * (1 / 2 ^ j) := by ring
      linarith [hb.1]
  | cons q l ih =>
    intro hv hpw j Q r hQ hcop
    obtain ⟨p, Ω⟩ := q
    have hv' : ∀ q ∈ l, 0 < q.1 ∧ q.2 ⊆ Finset.range q.1 :=
      fun q hq => hv q (List.mem_cons_of_mem _ hq)
    have hp0 : 0 < p := (hv (p, Ω) List.mem_cons_self).1
    have hΩ : Ω ⊆ Finset.range p := (hv (p, Ω) List.mem_cons_self).2
    rw [List.pairwise_cons] at hpw
    have hcp : Nat.Coprime Q p := hcop (p, Ω) List.mem_cons_self
    have hcop' : ∀ q ∈ l, Nat.Coprime Q q.1 := fun q hq => hcop q (List.mem_cons_of_mem _ hq)
    have hcop2 : ∀ q ∈ l, Nat.Coprime (Q * p) q.1 :=
      fun q hq => Nat.Coprime.mul_left (hcop' q hq) (hpw.1 q hq)
    obtain ⟨ρ, hρ⟩ := cnt_cons l r L hΩ hcp
    have hcast : (cnt ((p, Ω) :: l) Q r L : ℝ) =
        (cnt l Q r L : ℝ) - ∑ ω ∈ Ω, (cnt l (Q * p) (ρ ω) L : ℝ) := by
      have h0 : ((cnt ((p, Ω) :: l) Q r L + ∑ ω ∈ Ω, cnt l (Q * p) (ρ ω) L : ℕ) : ℝ) =
          (cnt l Q r L : ℝ) := by rw [hρ]
      push_cast at h0
      linarith
    have hx0 : 0 ≤ (Ω.card : ℝ) / p := xq_nonneg (p, Ω)
    have hx1 : (Ω.card : ℝ) / p ≤ 1 := xq_le_one (q := (p, Ω)) hΩ
    have hW := Wp_bounds l (fun q hq => (hv' q hq).2)
    have hP := one_le_Pu l
    have hA : (0:ℝ) ≤ (L:ℝ) / Q := by positivity
    have hQp : (L:ℝ) / ((Q * p : ℕ) : ℝ) = (L:ℝ) / Q / p := by
      push_cast
      rw [div_div]
    have hp' : (p:ℝ) ≠ 0 := by exact_mod_cast hp0.ne'
    have hs0 : (0:ℝ) ≤ 1 + (sm l : ℝ) := by positivity
    have hsm : (sm ((p, Ω) :: l) : ℝ) = (Ω.card : ℝ) + (sm l : ℝ) := by
      simp only [sm]
      push_cast
      ring
    have hWp : Wp ((p, Ω) :: l) = (1 - (Ω.card : ℝ) / p) * Wp l := rfl
    have hPu : Pu ((p, Ω) :: l) = (1 + 2 * ((Ω.card : ℝ) / p)) * Pu l := rfl
    rw [hWp, hPu, hsm]
    obtain ⟨A, hAdef⟩ : ∃ A : ℝ, (L:ℝ) / Q = A := ⟨_, rfl⟩
    rw [hAdef] at hA hQp ⊢
    rcases j with _ | j
    · constructor
      · intro h
        exact absurd h (by simp)
      · intro _
        rw [pow_zero, pow_zero, div_one]
        have h1 : (1 - (Ω.card : ℝ) / p) * Wp l ≤ 1 := by nlinarith [hW.1, hW.2]
        have h2 : 1 ≤ (1 + 2 * ((Ω.card : ℝ) / p)) * Pu l := by nlinarith
        have h3 : A * ((1 - (Ω.card : ℝ) / p) * Wp l - (1 + 2 * ((Ω.card : ℝ) / p)) * Pu l) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hA (by linarith)
        have h4 : (0:ℝ) ≤ (cnt ((p, Ω) :: l) Q r L : ℝ) := Nat.cast_nonneg _
        linarith
    · have ih1 := ih hv' hpw.2 (j + 1) Q r hQ hcop'
      have ih2 := fun ω => ih hv' hpw.2 j (Q * p) (ρ ω) (Nat.mul_pos hQ hp0) hcop2
      rw [hAdef] at ih1
      have hE : (1 + (sm l : ℝ)) ^ (j + 1) + (Ω.card : ℝ) * (1 + (sm l : ℝ)) ^ j ≤
          (1 + ((Ω.card : ℝ) + (sm l : ℝ))) ^ (j + 1) := by
        have h1 : (1 + (sm l : ℝ)) ^ j ≤ (1 + ((Ω.card : ℝ) + (sm l : ℝ))) ^ j :=
          pow_le_pow_left₀ hs0 (by linarith [Nat.cast_nonneg (α := ℝ) Ω.card]) j
        have h2 : (0:ℝ) ≤ 1 + ((Ω.card : ℝ) + (sm l : ℝ)) := by positivity
        calc (1 + (sm l : ℝ)) ^ (j + 1) + (Ω.card : ℝ) * (1 + (sm l : ℝ)) ^ j
            = (1 + ((Ω.card : ℝ) + (sm l : ℝ))) * (1 + (sm l : ℝ)) ^ j := by ring
          _ ≤ (1 + ((Ω.card : ℝ) + (sm l : ℝ))) * (1 + ((Ω.card : ℝ) + (sm l : ℝ))) ^ j :=
              mul_le_mul_of_nonneg_left h1 h2
          _ = (1 + ((Ω.card : ℝ) + (sm l : ℝ))) ^ (j + 1) := by ring
      have hpow : ((2:ℝ) ^ j) ≠ 0 := by positivity
      have hid1 : A * (Wp l + Pu l / 2 ^ (j + 1)) -
          (Ω.card : ℝ) * (A / p * (Wp l - Pu l / 2 ^ j)) =
          A * ((1 - (Ω.card : ℝ) / p) * Wp l +
            (1 + 2 * ((Ω.card : ℝ) / p)) * Pu l / 2 ^ (j + 1)) := by
        field_simp
        ring
      have hid2 : A * (Wp l - Pu l / 2 ^ (j + 1)) -
          (Ω.card : ℝ) * (A / p * (Wp l + Pu l / 2 ^ j)) =
          A * ((1 - (Ω.card : ℝ) / p) * Wp l -
            (1 + 2 * ((Ω.card : ℝ) / p)) * Pu l / 2 ^ (j + 1)) := by
        field_simp
        ring
      constructor
      · intro hodd
        have hev : Even j := by
          rcases Nat.even_or_odd j with h | h
          · exact h
          · exact absurd hodd (by
              rw [Nat.not_odd_iff_even]
              exact h.add_one)
        have hU := ih1.1 hodd
        have hS : (Ω.card : ℝ) * (A / p * (Wp l - Pu l / 2 ^ j) - (1 + (sm l : ℝ)) ^ j) ≤
            ∑ ω ∈ Ω, (cnt l (Q * p) (ρ ω) L : ℝ) := by
          rw [← nsmul_eq_mul, ← Finset.sum_const]
          apply Finset.sum_le_sum
          intro ω _
          have h7 := (ih2 ω).2 hev
          rwa [hQp] at h7
        rw [hcast]
        have h8 : (Ω.card : ℝ) * (A / p * (Wp l - Pu l / 2 ^ j) - (1 + (sm l : ℝ)) ^ j) =
            (Ω.card : ℝ) * (A / p * (Wp l - Pu l / 2 ^ j)) -
              (Ω.card : ℝ) * (1 + (sm l : ℝ)) ^ j := by ring
        linarith
      · intro heven
        have hod : Odd j := by
          rcases Nat.even_or_odd j with h | h
          · exact absurd heven (by
              rw [Nat.not_even_iff_odd]
              exact h.add_one)
          · exact h
        have hU := ih1.2 heven
        have hS : ∑ ω ∈ Ω, (cnt l (Q * p) (ρ ω) L : ℝ) ≤
            (Ω.card : ℝ) * (A / p * (Wp l + Pu l / 2 ^ j) + (1 + (sm l : ℝ)) ^ j) := by
          rw [← nsmul_eq_mul, ← Finset.sum_const]
          apply Finset.sum_le_sum
          intro ω _
          have h7 := (ih2 ω).1 hod
          rwa [hQp] at h7
        rw [hcast]
        have h8 : (Ω.card : ℝ) * (A / p * (Wp l + Pu l / 2 ^ j) + (1 + (sm l : ℝ)) ^ j) =
            (Ω.card : ℝ) * (A / p * (Wp l + Pu l / 2 ^ j)) +
              (Ω.card : ℝ) * (1 + (sm l : ℝ)) ^ j := by ring
        linarith

/-- The primes in `(M, M + n]` with their forbidden residue sets. -/
def sl (Ω : ℕ → Finset ℕ) (M : ℕ) : ℕ → List (ℕ × Finset ℕ)
  | 0 => []
  | n + 1 => if (M + n + 1).Prime then (M + n + 1, Ω (M + n + 1)) :: sl Ω M n else sl Ω M n

lemma sl_succ (Ω : ℕ → Finset ℕ) (M n : ℕ) : sl Ω M (n + 1) =
    if (M + n + 1).Prime then (M + n + 1, Ω (M + n + 1)) :: sl Ω M n else sl Ω M n := rfl

lemma mem_sl {Ω : ℕ → Finset ℕ} {M : ℕ} : ∀ (n : ℕ) (q : ℕ × Finset ℕ), q ∈ sl Ω M n →
    q.1.Prime ∧ M < q.1 ∧ q.1 ≤ M + n ∧ q.2 = Ω q.1 := by
  intro n
  induction n with
  | zero =>
    intro q hq
    simp [sl] at hq
  | succ n ih =>
    intro q hq
    rw [sl_succ] at hq
    split_ifs at hq with hp
    · rcases List.mem_cons.mp hq with h | h
      · rw [h]
        refine ⟨hp, ?_, ?_, rfl⟩
        · show M < M + n + 1
          omega
        · show M + n + 1 ≤ M + (n + 1)
          omega
      · obtain ⟨h1, h2, h3, h4⟩ := ih q h
        exact ⟨h1, h2, by omega, h4⟩
    · obtain ⟨h1, h2, h3, h4⟩ := ih q hq
      exact ⟨h1, h2, by omega, h4⟩

lemma sl_mem {Ω : ℕ → Finset ℕ} {M : ℕ} : ∀ (n p : ℕ), p.Prime → M < p → p ≤ M + n →
    (p, Ω p) ∈ sl Ω M n := by
  intro n
  induction n with
  | zero =>
    intro p _ h1 h2
    omega
  | succ n ih =>
    intro p hp h1 h2
    rw [sl_succ]
    rcases Nat.lt_or_ge p (M + n + 1) with h | h
    · have h3 := ih p hp h1 (by omega)
      split_ifs
      · exact List.mem_cons_of_mem _ h3
      · exact h3
    · have e : p = M + n + 1 := by omega
      rw [← e, if_pos hp]
      exact List.mem_cons_self

lemma sl_pairwise (Ω : ℕ → Finset ℕ) (M : ℕ) : ∀ n : ℕ,
    (sl Ω M n).Pairwise (fun a b => Nat.Coprime a.1 b.1) := by
  intro n
  induction n with
  | zero => simp [sl]
  | succ n ih =>
    rw [sl_succ]
    split_ifs with hp
    · rw [List.pairwise_cons]
      refine ⟨fun q hq => ?_, ih⟩
      obtain ⟨h1, h2, h3, _⟩ := mem_sl n q hq
      show Nat.Coprime (M + n + 1) q.1
      rw [Nat.coprime_primes hp h1]
      omega
    · exact ih

lemma sl_valid {Ω : ℕ → Finset ℕ} {M t : ℕ}
    (hΩ : ∀ p, p.Prime → M < p → Ω p ⊆ Finset.range p ∧ (Ω p).card ≤ t) (n : ℕ) :
    ∀ q ∈ sl Ω M n, 0 < q.1 ∧ q.2 ⊆ Finset.range q.1 := by
  intro q hq
  obtain ⟨h1, h2, _, h4⟩ := mem_sl n q hq
  refine ⟨h1.pos, ?_⟩
  rw [h4]
  exact (hΩ q.1 h1 h2).1

lemma K0 {x b : ℝ} (hxb : x ≤ b) (hb0 : 0 ≤ b) (hb : b ≤ 1 / 2) :
    1 ≤ (1 - x) * (1 + 2 * b) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hxb) (by linarith : (0:ℝ) ≤ 1 + 2 * b),
    mul_nonneg hb0 (sub_nonneg.mpr hb)]

lemma Kb {m : ℕ} (hm : 0 < m) (t : ℕ) :
    (m:ℝ) ^ (2 * t) * (1 + 2 * ((t:ℝ) / m)) ≤ ((m:ℝ) + 1) ^ (2 * t) := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hb := one_add_mul_le_pow (a := 1 / (m:ℝ)) (by
    have : (0:ℝ) ≤ 1 / (m:ℝ) := by positivity
    linarith) (2 * t)
  have e : ((m:ℝ) + 1) ^ (2 * t) = (m:ℝ) ^ (2 * t) * (1 + 1 / (m:ℝ)) ^ (2 * t) := by
    rw [← mul_pow]
    congr 1
    field_simp
  have e2 : (1:ℝ) + ((2 * t : ℕ) : ℝ) * (1 / (m:ℝ)) = 1 + 2 * ((t:ℝ) / m) := by
    push_cast
    ring
  rw [e2] at hb
  rw [e]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

lemma K1 {m t ω : ℕ} (hm : 0 < m) (hω : ω ≤ t) (ht : 2 * t ≤ m) :
    (m:ℝ) ^ (2 * t) ≤ (1 - (ω:ℝ) / m) * ((m:ℝ) + 1) ^ (2 * t) := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hx : (ω:ℝ) / m ≤ (t:ℝ) / m :=
    div_le_div_of_nonneg_right (by exact_mod_cast hω) hm'.le
  have hb2 : (t:ℝ) / m ≤ 1 / 2 := by
    rw [div_le_iff₀ hm']
    have h : ((2 * t : ℕ) : ℝ) ≤ (m:ℝ) := by exact_mod_cast ht
    push_cast at h
    linarith
  have ht0 : (0:ℝ) ≤ (t:ℝ) / m := by positivity
  have hmp : (0:ℝ) ≤ (m:ℝ) ^ (2 * t) := by positivity
  have h1 := K0 hx ht0 hb2
  have h2 := Kb hm t
  have h3 : (0:ℝ) ≤ 1 - (ω:ℝ) / m := by linarith
  calc (m:ℝ) ^ (2 * t) = (m:ℝ) ^ (2 * t) * 1 := by ring
    _ ≤ (m:ℝ) ^ (2 * t) * ((1 - (ω:ℝ) / m) * (1 + 2 * ((t:ℝ) / m))) :=
        mul_le_mul_of_nonneg_left h1 hmp
    _ = (1 - (ω:ℝ) / m) * ((m:ℝ) ^ (2 * t) * (1 + 2 * ((t:ℝ) / m))) := by ring
    _ ≤ (1 - (ω:ℝ) / m) * ((m:ℝ) + 1) ^ (2 * t) := mul_le_mul_of_nonneg_left h2 h3

lemma K2 {m t ω : ℕ} (hm : 0 < m) (hω : ω ≤ t) :
    (1 + 2 * ((ω:ℝ) / m)) * (m:ℝ) ^ (2 * t) ≤ ((m:ℝ) + 1) ^ (2 * t) := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hx : (ω:ℝ) / m ≤ (t:ℝ) / m :=
    div_le_div_of_nonneg_right (by exact_mod_cast hω) hm'.le
  have hmp : (0:ℝ) ≤ (m:ℝ) ^ (2 * t) := by positivity
  have h2 := Kb hm t
  calc (1 + 2 * ((ω:ℝ) / m)) * (m:ℝ) ^ (2 * t)
      ≤ (1 + 2 * ((t:ℝ) / m)) * (m:ℝ) ^ (2 * t) :=
        mul_le_mul_of_nonneg_right (by linarith) hmp
    _ = (m:ℝ) ^ (2 * t) * (1 + 2 * ((t:ℝ) / m)) := by ring
    _ ≤ ((m:ℝ) + 1) ^ (2 * t) := h2

lemma sl_Wp {Ω : ℕ → Finset ℕ} {M t : ℕ}
    (hΩ : ∀ p, p.Prime → M < p → Ω p ⊆ Finset.range p ∧ (Ω p).card ≤ t) (hM : 2 * t ≤ M) :
    ∀ n : ℕ, ((M + 1 : ℕ) : ℝ) ^ (2 * t) ≤
      Wp (sl Ω M n) * ((M + n + 1 : ℕ) : ℝ) ^ (2 * t) := by
  intro n
  induction n with
  | zero => simp [sl, Wp]
  | succ n ih =>
    have hW := (Wp_bounds (sl Ω M n) (fun q hq => (sl_valid hΩ n q hq).2)).1
    rw [sl_succ]
    split_ifs with hp
    · have hk := K1 (m := M + n + 1) (t := t) (ω := (Ω (M + n + 1)).card) (by omega)
        (hΩ _ hp (by omega)).2 (by omega)
      have e : ((M + (n + 1) + 1 : ℕ) : ℝ) = ((M + n + 1 : ℕ) : ℝ) + 1 := by
        push_cast
        ring
      have hW' : Wp ((M + n + 1, Ω (M + n + 1)) :: sl Ω M n) =
          (1 - ((Ω (M + n + 1)).card : ℝ) / ((M + n + 1 : ℕ) : ℝ)) * Wp (sl Ω M n) := rfl
      rw [hW', e]
      calc ((M + 1 : ℕ) : ℝ) ^ (2 * t) ≤ Wp (sl Ω M n) * ((M + n + 1 : ℕ) : ℝ) ^ (2 * t) := ih
        _ ≤ Wp (sl Ω M n) * ((1 - ((Ω (M + n + 1)).card : ℝ) / ((M + n + 1 : ℕ) : ℝ)) *
              (((M + n + 1 : ℕ) : ℝ) + 1) ^ (2 * t)) := mul_le_mul_of_nonneg_left hk hW
        _ = _ := by ring
    · have hmono : ((M + n + 1 : ℕ) : ℝ) ^ (2 * t) ≤ ((M + (n + 1) + 1 : ℕ) : ℝ) ^ (2 * t) := by
        apply pow_le_pow_left₀ (Nat.cast_nonneg _)
        exact_mod_cast (by omega : M + n + 1 ≤ M + (n + 1) + 1)
      exact ih.trans (mul_le_mul_of_nonneg_left hmono hW)

lemma sl_Pu {Ω : ℕ → Finset ℕ} {M t : ℕ}
    (hΩ : ∀ p, p.Prime → M < p → Ω p ⊆ Finset.range p ∧ (Ω p).card ≤ t) :
    ∀ n : ℕ, Pu (sl Ω M n) * ((M + 1 : ℕ) : ℝ) ^ (2 * t) ≤
      ((M + n + 1 : ℕ) : ℝ) ^ (2 * t) := by
  intro n
  induction n with
  | zero => simp [sl, Pu]
  | succ n ih =>
    have hmono : ((M + n + 1 : ℕ) : ℝ) ^ (2 * t) ≤ ((M + (n + 1) + 1 : ℕ) : ℝ) ^ (2 * t) := by
      apply pow_le_pow_left₀ (Nat.cast_nonneg _)
      exact_mod_cast (by omega : M + n + 1 ≤ M + (n + 1) + 1)
    rw [sl_succ]
    split_ifs with hp
    · have hk := K2 (m := M + n + 1) (t := t) (ω := (Ω (M + n + 1)).card) (by omega)
        (hΩ _ hp (by omega)).2
      have e : ((M + (n + 1) + 1 : ℕ) : ℝ) = ((M + n + 1 : ℕ) : ℝ) + 1 := by
        push_cast
        ring
      have hP' : Pu ((M + n + 1, Ω (M + n + 1)) :: sl Ω M n) =
          (1 + 2 * (((Ω (M + n + 1)).card : ℝ) / ((M + n + 1 : ℕ) : ℝ))) * Pu (sl Ω M n) := rfl
      have hx0 : (0:ℝ) ≤ 1 + 2 * (((Ω (M + n + 1)).card : ℝ) / ((M + n + 1 : ℕ) : ℝ)) := by
        positivity
      rw [hP', e]
      calc (1 + 2 * (((Ω (M + n + 1)).card : ℝ) / ((M + n + 1 : ℕ) : ℝ))) * Pu (sl Ω M n) *
            ((M + 1 : ℕ) : ℝ) ^ (2 * t)
          = (1 + 2 * (((Ω (M + n + 1)).card : ℝ) / ((M + n + 1 : ℕ) : ℝ))) *
            (Pu (sl Ω M n) * ((M + 1 : ℕ) : ℝ) ^ (2 * t)) := by ring
        _ ≤ (1 + 2 * (((Ω (M + n + 1)).card : ℝ) / ((M + n + 1 : ℕ) : ℝ))) *
            ((M + n + 1 : ℕ) : ℝ) ^ (2 * t) := mul_le_mul_of_nonneg_left ih hx0
        _ ≤ (((M + n + 1 : ℕ) : ℝ) + 1) ^ (2 * t) := hk
    · exact ih.trans hmono

lemma sl_sm {Ω : ℕ → Finset ℕ} {M t : ℕ}
    (hΩ : ∀ p, p.Prime → M < p → Ω p ⊆ Finset.range p ∧ (Ω p).card ≤ t) :
    ∀ n : ℕ, sm (sl Ω M n) ≤ t * n := by
  intro n
  induction n with
  | zero => simp [sl, sm]
  | succ n ih =>
    have e : t * (n + 1) = t * n + t := Nat.mul_add_one t n
    rw [sl_succ]
    split_ifs with hp
    · have h1 := (hΩ _ hp (by omega)).2
      have hs : sm ((M + n + 1, Ω (M + n + 1)) :: sl Ω M n) =
          (Ω (M + n + 1)).card + sm (sl Ω M n) := rfl
      rw [hs]
      omega
    · omega

/-- Truncation level of the sieve. -/
def sieveJ (t z : ℕ) : ℕ := 4 * t * (Nat.log 2 (z + 1) + 1) + 2

/-- Length of an interval in which the sieve is guaranteed to leave a survivor. -/
def sieveR (t z : ℕ) : ℕ := 2 * (z + 1) ^ (2 * t) * (1 + t * z) ^ sieveJ t z + 1

/-- If at most `t` residues are forbidden modulo every prime `p ∈ (M, M + n]` and `2 t ≤ M`, then
some `m < sieveR t (M + n)` avoids all the forbidden residues. -/
theorem sieve_exists {M n t : ℕ} (Ω : ℕ → Finset ℕ)
    (hΩ : ∀ p, p.Prime → M < p → Ω p ⊆ Finset.range p ∧ (Ω p).card ≤ t) (hM : 2 * t ≤ M) :
    ∃ m, m < sieveR t (M + n) ∧ ∀ p, p.Prime → M < p → p ≤ M + n → m % p ∉ Ω p := by
  obtain ⟨R, hR⟩ : ∃ R, sieveR t (M + n) = R := ⟨_, rfl⟩
  obtain ⟨j, hj⟩ : ∃ j, sieveJ t (M + n) = j := ⟨_, rfl⟩
  have hjev : Even j := by
    rw [← hj]
    unfold sieveJ
    exact ⟨2 * t * (Nat.log 2 (M + n + 1) + 1) + 1, by ring⟩
  have hmain := (sieve_main R (sl Ω M n) (sl_valid hΩ n) (sl_pairwise Ω M n) j 1 0 Nat.one_pos
    (fun q _ => Nat.coprime_one_left _)).2 hjev
  have hW := sl_Wp hΩ hM n
  have hP := sl_Pu hΩ n
  have hS := sl_sm hΩ n
  have hRr : (R:ℝ) = 2 * ((M + n + 1 : ℕ) : ℝ) ^ (2 * t) *
      ((1 + t * (M + n) : ℕ) : ℝ) ^ j + 1 := by
    rw [← hR, ← hj]
    unfold sieveR
    norm_cast
  have h3 : 4 * (((M + n + 1 : ℕ) : ℝ) ^ (2 * t)) ^ 2 ≤ (2:ℝ) ^ j := by
    have hlog : M + n + 1 < 2 ^ (Nat.log 2 (M + n + 1) + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num) _
    have h4 : ((M + n + 1 : ℕ) : ℝ) ≤ (2:ℝ) ^ (Nat.log 2 (M + n + 1) + 1) := by
      exact_mod_cast hlog.le
    have h5 := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) (M + n + 1)) h4 (4 * t)
    rw [← hj]
    unfold sieveJ
    calc 4 * (((M + n + 1 : ℕ) : ℝ) ^ (2 * t)) ^ 2 = 4 * ((M + n + 1 : ℕ) : ℝ) ^ (4 * t) := by
          ring
      _ ≤ 4 * ((2:ℝ) ^ (Nat.log 2 (M + n + 1) + 1)) ^ (4 * t) := by linarith
      _ = (2:ℝ) ^ (4 * t * (Nat.log 2 (M + n + 1) + 1) + 2) := by
          rw [← pow_mul]
          ring
  have hsmE : (1 + (sm (sl Ω M n) : ℝ)) ^ j ≤ ((1 + t * (M + n) : ℕ) : ℝ) ^ j := by
    apply pow_le_pow_left₀ (by positivity)
    have h6 : sm (sl Ω M n) ≤ t * (M + n) :=
      hS.trans (Nat.mul_le_mul_left t (Nat.le_add_left n M))
    have h7 : ((1 + sm (sl Ω M n) : ℕ) : ℝ) ≤ ((1 + t * (M + n) : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_le_add_left h6 1
    push_cast at h7 ⊢
    linarith
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, ((M + n + 1 : ℕ) : ℝ) ^ (2 * t) = P := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, ((M + 1 : ℕ) : ℝ) ^ (2 * t) = B := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℝ, ((1 + t * (M + n) : ℕ) : ℝ) ^ j = E := ⟨_, rfl⟩
  rw [hPdef, hBdef] at hW hP
  rw [hPdef] at h3
  rw [hPdef, hE] at hRr
  rw [hE] at hsmE
  have hB1 : 1 ≤ B := by
    rw [← hBdef]
    apply one_le_pow₀
    exact_mod_cast (by omega : 1 ≤ M + 1)
  have hP0 : 0 < P := by
    rw [← hPdef]
    positivity
  have hPl := one_le_Pu (sl Ω M n)
  have h1 : 1 ≤ Wp (sl Ω M n) * P := hB1.trans hW
  have h2 : Pu (sl Ω M n) ≤ P := by nlinarith
  have h2j : (0:ℝ) < (2:ℝ) ^ j := by positivity
  have h5 : Pu (sl Ω M n) / (2:ℝ) ^ j ≤ 1 / (4 * P) := by
    rw [div_le_div_iff₀ h2j (by positivity)]
    have h6 : Pu (sl Ω M n) * (4 * P) ≤ P * (4 * P) :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    have h7 : P * (4 * P) = 4 * P ^ 2 := by ring
    linarith
  have h8 : 1 / (2 * P) ≤ Wp (sl Ω M n) - Pu (sl Ω M n) / (2:ℝ) ^ j := by
    have h9 : 1 / P ≤ Wp (sl Ω M n) := by
      rw [div_le_iff₀ hP0]
      exact h1
    have h10 : 1 / (2 * P) = 1 / P - 1 / (2 * P) := by
      field_simp
      ring
    have h11 : 1 / (4 * P) ≤ 1 / (2 * P) := by
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    linarith
  have hcnt : (0:ℝ) < (cnt (sl Ω M n) 1 0 R : ℝ) := by
    have h13 : (R:ℝ) / ((1:ℕ):ℝ) = R := by simp
    rw [h13] at hmain
    have hR0 : (0:ℝ) ≤ (R:ℝ) := Nat.cast_nonneg _
    have h14 : (R:ℝ) * (1 / (2 * P)) ≤
        (R:ℝ) * (Wp (sl Ω M n) - Pu (sl Ω M n) / (2:ℝ) ^ j) :=
      mul_le_mul_of_nonneg_left h8 hR0
    have h15 : (R:ℝ) * (1 / (2 * P)) = E + 1 / (2 * P) := by
      rw [hRr]
      field_simp
    have h16 : (0:ℝ) < 1 / (2 * P) := by positivity
    linarith
  have hpos : 0 < cnt (sl Ω M n) 1 0 R := by exact_mod_cast hcnt
  unfold cnt at hpos
  obtain ⟨m, hm⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter, Finset.mem_range] at hm
  refine ⟨m, ?_, fun p hp h1 h2 => hm.2.2 (p, Ω p) (sl_mem n p hp h1 h2)⟩
  rw [hR]
  exact hm.1

/-! ## 4. Choosing the positions of the windows -/

/-- Residues `r` modulo `p` for which `x0 + H r` collides with one of `Y 0, …, Y (k - 1)`. -/
def selΩ (H k x0 : ℕ) (Y : ℕ → ℕ) (p : ℕ) : Finset ℕ :=
  (Finset.range k).biUnion
    (fun i => (Finset.range p).filter (fun r => (x0 + H * r) % p = Y i % p))

lemma selΩ_prop {H k x0 M : ℕ} {Y : ℕ → ℕ} (hcop : ∀ p : ℕ, p.Prime → M < p → ¬ p ∣ H)
    {p : ℕ} (hp : p.Prime) (hMp : M < p) :
    selΩ H k x0 Y p ⊆ Finset.range p ∧ (selΩ H k x0 Y p).card ≤ k := by
  constructor
  · unfold selΩ
    rw [Finset.biUnion_subset]
    intro i _
    exact Finset.filter_subset _ _
  · have hone : ∀ i ∈ Finset.range k, ((Finset.range p).filter
        (fun r => (x0 + H * r) % p = Y i % p)).card ≤ 1 := by
      intro i _
      rw [Finset.card_le_one]
      intro a ha b hb
      rw [Finset.mem_filter, Finset.mem_range] at ha hb
      have h1 : x0 + H * a ≡ x0 + H * b [MOD p] := ha.2.trans hb.2.symm
      have h2 : H * a ≡ H * b [MOD p] := Nat.ModEq.add_left_cancel' x0 h1
      have h3 : Nat.gcd p H = 1 := (Nat.Prime.coprime_iff_not_dvd hp).mpr (hcop p hp hMp)
      have h4 : a ≡ b [MOD p] := Nat.ModEq.cancel_left_of_coprime h3 h2
      rw [Nat.ModEq, Nat.mod_eq_of_lt ha.1, Nat.mod_eq_of_lt hb.1] at h4
      exact h4
    calc (selΩ H k x0 Y p).card
        ≤ ∑ i ∈ Finset.range k, ((Finset.range p).filter
            (fun r => (x0 + H * r) % p = Y i % p)).card := Finset.card_biUnion_le
      _ ≤ ∑ i ∈ Finset.range k, 1 := Finset.sum_le_sum hone
      _ = k := by simp

/-- Positions `Y c ≥ X c` close to `X c`, with `Y c ≡ c` modulo `H`, no two of which are congruent
modulo a prime in `(M, z]`. -/
lemma select {M z H t : ℕ} (hH0 : 0 < H) (h2t : 2 * t ≤ M) (hMz : M ≤ z)
    (hcop : ∀ p : ℕ, p.Prime → M < p → ¬ p ∣ H) (X : ℕ → ℕ) :
    ∀ k, k ≤ t + 1 → ∃ Y q : ℕ → ℕ,
      (∀ c, c < k → Y c = H * q c + c ∧ X c ≤ Y c ∧ Y c ≤ X c + H * sieveR t z + c) ∧
      ∀ c, c < k → ∀ c', c' < c → ∀ p : ℕ, p.Prime → M < p → p ≤ z →
        Y c % p ≠ Y c' % p := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨fun _ => 0, fun _ => 0, fun c hc => absurd hc (Nat.not_lt_zero c),
      fun c hc => absurd hc (Nat.not_lt_zero c)⟩
  | succ k ih =>
    intro hk
    obtain ⟨Y, q, hY1, hY2⟩ := ih (by omega)
    obtain ⟨x0, hx0⟩ : ∃ x0, H * (X k / H + 1) + k = x0 := ⟨_, rfl⟩
    obtain ⟨m, hm1, hm2⟩ := sieve_exists (n := z - M) (selΩ H k x0 Y)
      (fun p hp hMp => ⟨(selΩ_prop hcop hp hMp).1,
        (selΩ_prop hcop hp hMp).2.trans (by omega)⟩) h2t
    rw [Nat.add_sub_cancel' hMz] at hm1 hm2
    obtain ⟨Y', hY'⟩ : ∃ Y' : ℕ → ℕ, Y' = fun c => if c = k then x0 + H * m else Y c :=
      ⟨_, rfl⟩
    obtain ⟨q', hq'⟩ : ∃ q' : ℕ → ℕ, q' = fun c => if c = k then X k / H + 1 + m else q c :=
      ⟨_, rfl⟩
    have hYk : Y' k = x0 + H * m := by simp [hY']
    have hYne : ∀ c, c ≠ k → Y' c = Y c := fun c hc => by simp [hY', hc]
    have hqk : q' k = X k / H + 1 + m := by simp [hq']
    have hqne : ∀ c, c ≠ k → q' c = q c := fun c hc => by simp [hq', hc]
    refine ⟨Y', q', ?_, ?_⟩
    · intro c hc
      by_cases hck : c = k
      · rw [hck, hYk, hqk]
        have h1 := Nat.lt_mul_div_succ (X k) hH0
        have h2 := Nat.mul_div_le (X k) H
        have h3 : H * (X k / H + 1 + m) = H * (X k / H + 1) + H * m := by ring
        have h4 : H * (X k / H + 1) = H * (X k / H) + H := by ring
        have h5 : H * m + H ≤ H * sieveR t z := by
          have h6 := Nat.mul_le_mul_left H (Nat.succ_le_of_lt hm1)
          rw [Nat.mul_succ] at h6
          exact h6
        refine ⟨?_, ?_, ?_⟩
        · omega
        · omega
        · omega
      · rw [hYne c hck, hqne c hck]
        exact hY1 c (by omega)
    · intro c hc c' hc' p hp hMp hpz
      have hc'k : c' ≠ k := by omega
      rw [hYne c' hc'k]
      by_cases hck : c = k
      · rw [hck, hYk]
        intro heq
        apply hm2 p hp hMp hpz
        unfold selΩ
        rw [Finset.mem_biUnion]
        have h1 : x0 + H * (m % p) ≡ x0 + H * m [MOD p] :=
          Nat.ModEq.add_left x0 (Nat.ModEq.mul_left H (Nat.mod_modEq m p))
        exact ⟨c', Finset.mem_range.mpr (by omega), Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (Nat.mod_lt _ hp.pos), h1.trans heq⟩⟩
      · rw [hYne c hck]
        exact hY2 c (by omega) c' hc' p hp hMp hpz

/-! ## 5. The pattern lemma -/

/-- If `x - y = H t + d` where `H` is divisible by `p d` for all primes `p ≤ M`, no prime in
`(M, z]` divides both `x` and `y`, and `gcd x y > d`, then `x` and `y` have a common prime factor
exceeding `z`. -/
lemma pair_prime {M z H d x y : ℕ} (hd : 0 < d) (hH : ∀ p : ℕ, p.Prime → p ≤ M → p * d ∣ H)
    (hM : 2 ≤ M) (hs : ∀ p : ℕ, p.Prime → M < p → p ≤ z → ¬ (p ∣ x ∧ p ∣ y))
    (t : ℤ) (hxy : (x:ℤ) - y = H * t + d) (hg : d < Nat.gcd x y) :
    ∃ p : ℕ, p.Prime ∧ z < p ∧ p ∣ x ∧ p ∣ y := by
  by_contra hcon
  obtain ⟨H', hH'⟩ : d ∣ H := Dvd.dvd.trans (Dvd.intro_left 2 rfl) (hH 2 Nat.prime_two hM)
  have hcop : Nat.Coprime (Nat.gcd x y) (((H':ℤ) * t + 1).natAbs) := by
    rw [Nat.Coprime, Nat.eq_one_iff_not_exists_prime_dvd]
    intro p hp hpd
    have hpG : p ∣ Nat.gcd x y := hpd.trans (Nat.gcd_dvd_left _ _)
    have hpx : p ∣ x := hpG.trans (Nat.gcd_dvd_left x y)
    have hpy : p ∣ y := hpG.trans (Nat.gcd_dvd_right x y)
    have hpM : p ≤ M := by
      by_contra h
      rw [not_le] at h
      by_cases hpz : p ≤ z
      · exact hs p hp h hpz ⟨hpx, hpy⟩
      · exact hcon ⟨p, hp, not_le.mp hpz, hpx, hpy⟩
    have h1 : p * d ∣ H' * d := by
      have h0 := hH p hp hpM
      rwa [hH', Nat.mul_comm d H'] at h0
    have h2 : p ∣ H' := Nat.dvd_of_mul_dvd_mul_right hd h1
    have h3 : (p:ℤ) ∣ (H':ℤ) * t + 1 := Int.natCast_dvd.mpr (hpd.trans (Nat.gcd_dvd_right _ _))
    have h4 : (p:ℤ) ∣ (H':ℤ) * t := Dvd.dvd.mul_right (Int.natCast_dvd_natCast.mpr h2) t
    have h5 : (p:ℤ) ∣ 1 := (dvd_add_right h4).mp h3
    have h6 : p ∣ 1 := by exact_mod_cast h5
    exact hp.one_lt.ne' (Nat.dvd_one.mp h6)
  have hG : ((Nat.gcd x y : ℕ) : ℤ) ∣ (x:ℤ) - y :=
    dvd_sub (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left x y))
      (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right x y))
  have e : (x:ℤ) - y = (d:ℤ) * ((H':ℤ) * t + 1) := by
    rw [hxy, hH']
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

/-- Positions in distinct residue classes modulo `H` are distinct. -/
lemma pos_ne {H k : ℕ} {Y q : ℕ → ℕ} (hkH : k ≤ H) (hY : ∀ c, c < k → Y c = H * q c + c)
    {c c' : ℕ} (hc : c < k) (hcc : c' < c) : Y c ≠ Y c' := by
  intro h
  have h1 := hY c hc
  have h2 := hY c' (by omega)
  have h3 : (H * q c + c) % H = (H * q c' + c') % H := by rw [← h1, ← h2, h]
  rw [Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)] at h3
  omega

lemma pattern_pair {N : ℕ} {A : Finset ℕ} (hA : Adm N A) {k M z H : ℕ} {X Y q : ℕ → ℕ}
    (hV : ∀ c, c < k → ∀ c', c' < c → (c - c') * N ≤ X c * X c')
    (hH : ∀ d, 0 < d → d < k → ∀ p : ℕ, p.Prime → p ≤ M → p * d ∣ H)
    (hM : 2 ≤ M)
    (hY : ∀ c, c < k → Y c = H * q c + c ∧ X c ≤ Y c)
    (hsv : ∀ c, c < k → ∀ c', c' < c → ∀ p : ℕ, p.Prime → M < p → p ≤ z →
      Y c % p ≠ Y c' % p)
    {a c c' : ℕ} (ha : 1 ≤ a) (hc : c < k) (hcc : c' < c)
    (hx : Y c + a ∈ A) (hy : Y c' + a ∈ A) :
    ∃ p : ℕ, p.Prime ∧ z < p ∧ p ∣ Y c + a ∧ p ∣ Y c' + a := by
  have hc' : c' < k := by omega
  have hXx := (hY c hc).2
  have hXy := (hY c' hc').2
  have hd : 0 < c - c' := by omega
  have hdk : c - c' < k := by omega
  have hg : c - c' < Nat.gcd (Y c + a) (Y c' + a) := by
    by_contra h
    rw [not_lt] at h
    have hl := hA.2 _ hx _ hy
    have h1 : (Y c + a) * (Y c' + a) ≤ X c * X c' :=
      calc (Y c + a) * (Y c' + a)
          = Nat.gcd (Y c + a) (Y c' + a) * Nat.lcm (Y c + a) (Y c' + a) :=
            (Nat.gcd_mul_lcm _ _).symm
        _ ≤ (c - c') * N := Nat.mul_le_mul h hl
        _ ≤ X c * X c' := hV c hc c' hcc
    have h2 : X c * X c' < (Y c + a) * (Y c' + a) :=
      Nat.mul_lt_mul'' (by omega) (by omega)
    omega
  have hxy : ((Y c + a : ℕ) : ℤ) - ((Y c' + a : ℕ) : ℤ) =
      (H : ℤ) * (((q c : ℕ) : ℤ) - ((q c' : ℕ) : ℤ)) + ((c - c' : ℕ) : ℤ) := by
    rw [(hY c hc).1, (hY c' hc').1, Nat.cast_sub hcc.le]
    push_cast
    ring
  refine pair_prime hd (hH (c - c') hd hdk) hM ?_ _ hxy hg
  intro p hp hMp hpz hdiv
  apply hsv c hc c' hcc p hp hMp hpz
  have h3 : Y c + a ≡ Y c' + a [MOD p] := by
    rw [Nat.ModEq, Nat.mod_eq_zero_of_dvd hdiv.1, Nat.mod_eq_zero_of_dvd hdiv.2]
  exact Nat.ModEq.add_right_cancel' a h3

/-- The exceptional offsets for the ordered pair of codes `q`. -/
def badSet (N w z : ℕ) (Y : ℕ → ℕ) (q : ℕ × ℕ) : Finset ℕ :=
  ((min (Y q.1) N - Y q.2).primeFactors.filter (fun p => z < p)).biUnion
    (fun p => (Finset.Icc 1 w).filter (fun a => p ∣ Y q.2 + a))

lemma badSet_card {N w z L : ℕ} (Y : ℕ → ℕ) (hz : 2 ≤ z)
    (hL : ∀ D, D ≤ N → (D.primeFactors.filter (fun p => z < p)).card ≤ L) (q : ℕ × ℕ) :
    (badSet N w z Y q).card ≤ L * (w / z + 1) := by
  unfold badSet
  refine le_trans Finset.card_biUnion_le ?_
  calc _ ≤ ∑ _p ∈ (min (Y q.1) N - Y q.2).primeFactors.filter
            (fun p => z < p), (w / z + 1) := by
        apply Finset.sum_le_sum
        intro p hp
        rw [Finset.mem_filter] at hp
        exact le_trans (card_dvd_window _ w p)
          (Nat.succ_le_succ (Nat.div_le_div_left hp.2.le (by omega)))
    _ = ((min (Y q.1) N - Y q.2).primeFactors.filter
            (fun p => z < p)).card * (w / z + 1) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ L * (w / z + 1) :=
        Nat.mul_le_mul_right _ (hL _ (le_trans (Nat.sub_le _ _) (Nat.min_le_right _ _)))

lemma mem_badSet {N w z : ℕ} {Y : ℕ → ℕ} {q : ℕ × ℕ} {a p : ℕ} (ha : a ∈ Finset.Icc 1 w)
    (hp : p.Prime) (hzp : z < p) (h1 : Y q.2 < Y q.1) (h2 : Y q.1 + a ≤ N)
    (hd1 : p ∣ Y q.1 + a) (hd2 : p ∣ Y q.2 + a) : a ∈ badSet N w z Y q := by
  unfold badSet
  have e : min (Y q.1) N = Y q.1 := Nat.min_eq_left (by omega)
  have e2 : Y q.1 - Y q.2 = Y q.1 + a - (Y q.2 + a) := by omega
  refine Finset.mem_biUnion.mpr ⟨p, Finset.mem_filter.mpr
    ⟨Nat.mem_primeFactors.mpr ⟨hp, ?_, ?_⟩, hzp⟩, Finset.mem_filter.mpr ⟨ha, hd2⟩⟩
  · rw [e, e2]
    exact Nat.dvd_sub hd1 hd2
  · rw [e]
    omega

lemma pattern_bad {N : ℕ} {A : Finset ℕ} (hA : Adm N A) {w k M z H L : ℕ} {X Y q : ℕ → ℕ}
    (hV : ∀ c, c < k → ∀ c', c' < c → (c - c') * N ≤ X c * X c')
    (hH : ∀ d, 0 < d → d < k → ∀ p : ℕ, p.Prime → p ≤ M → p * d ∣ H)
    (hM : 2 ≤ M) (hz : 2 ≤ z) (hH0 : 0 < H)
    (hY : ∀ c, c < k → Y c = H * q c + c ∧ X c ≤ Y c)
    (hsv : ∀ c, c < k → ∀ c', c' < c → ∀ p : ℕ, p.Prime → M < p → p ≤ z →
      Y c % p ≠ Y c' % p)
    (hL : ∀ D, D ≤ N → (D.primeFactors.filter (fun p => z < p)).card ≤ L) :
    ((Finset.Icc 1 w).filter (fun a =>
      1 < ((Finset.range k).filter (fun c => Y c + a ∈ A)).card)).card
      ≤ k * k * (L * (w / z + 1)) := by
  have key : ∀ a ∈ Finset.Icc 1 w, ∀ c, c < k → ∀ c', c' < c → Y c + a ∈ A →
      Y c' + a ∈ A →
      a ∈ (Finset.range k ×ˢ Finset.range k).biUnion (badSet N w z Y) := by
    intro a ha c hc c' hcc hx hy
    obtain ⟨p, hp, hzp, hpx, hpy⟩ :=
      pattern_pair hA hV hH hM hY hsv (Finset.mem_Icc.mp ha).1 hc hcc hx hy
    have hkH : k ≤ H := by
      have h := Nat.le_of_dvd hH0 (hH (k - 1) (by omega) (by omega) 2 Nat.prime_two hM)
      omega
    have hne := pos_ne hkH (fun c hc => (hY c hc).1) hc hcc
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
      1 < ((Finset.range k).filter (fun c => Y c + a ∈ A)).card) ⊆
      (Finset.range k ×ˢ Finset.range k).biUnion (badSet N w z Y) := by
    intro a ha
    rw [Finset.mem_filter, Finset.one_lt_card] at ha
    obtain ⟨ha1, c, hc, c', hc', hne⟩ := ha
    rw [Finset.mem_filter, Finset.mem_range] at hc hc'
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact key a ha1 c' hc'.1 c h hc'.2 hc.2
    · exact key a ha1 c hc.1 c' h hc.2 hc'.2
  calc _ ≤ ((Finset.range k ×ˢ Finset.range k).biUnion (badSet N w z Y)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ q ∈ Finset.range k ×ˢ Finset.range k, (badSet N w z Y q).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _q ∈ Finset.range k ×ˢ Finset.range k, L * (w / z + 1) :=
        Finset.sum_le_sum (fun q _ => badSet_card Y hz hL q)
    _ = k * k * (L * (w / z + 1)) := by
        rw [Finset.sum_const, Finset.card_product, Finset.card_range, smul_eq_mul]

/-- The pattern lemma: window counts at positions satisfying the product condition (V) add up to
at most one full window, up to lower-order terms.  Here `Y c` are the sieved positions. -/
theorem pattern_lemma {N : ℕ} {A : Finset ℕ} (hA : Adm N A) {w k M z H L S : ℕ}
    {X Y q : ℕ → ℕ}
    (hV : ∀ c, c < k → ∀ c', c' < c → (c - c') * N ≤ X c * X c')
    (hH : ∀ d, 0 < d → d < k → ∀ p : ℕ, p.Prime → p ≤ M → p * d ∣ H)
    (hM : 2 ≤ M) (hz : 2 ≤ z) (hH0 : 0 < H)
    (hY : ∀ c, c < k → Y c = H * q c + c ∧ X c ≤ Y c ∧ Y c ≤ X c + S)
    (hsv : ∀ c, c < k → ∀ c', c' < c → ∀ p : ℕ, p.Prime → M < p → p ≤ z →
      Y c % p ≠ Y c' % p)
    (hL : ∀ D, D ≤ N → (D.primeFactors.filter (fun p => z < p)).card ≤ L) :
    ∑ c ∈ Finset.range k, W A w (X c) ≤
      w + k * S + k * (k * k * (L * (w / z + 1))) := by
  have h1 : ∑ c ∈ Finset.range k, W A w (X c) ≤
      ∑ c ∈ Finset.range k, (W A w (Y c) + S) := by
    apply Finset.sum_le_sum
    intro c hc
    rw [Finset.mem_range] at hc
    have h5 := W_shift A w (hY c hc).2.1
    have h6 := (hY c hc).2.2
    omega
  have h2 : ∑ c ∈ Finset.range k, W A w (Y c) =
      ∑ a ∈ Finset.Icc 1 w, ((Finset.range k).filter (fun c => Y c + a ∈ A)).card := by
    unfold W
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have h3 : ∀ a ∈ Finset.Icc 1 w,
      ((Finset.range k).filter (fun c => Y c + a ∈ A)).card ≤ 1 + k *
        (if 1 < ((Finset.range k).filter (fun c => Y c + a ∈ A)).card then 1 else 0) := by
    intro a _
    have hk : ((Finset.range k).filter (fun c => Y c + a ∈ A)).card ≤ k := by
      calc _ ≤ (Finset.range k).card := Finset.card_filter_le _ _
        _ = k := Finset.card_range k
    split_ifs with h
    · omega
    · omega
  have h4 := pattern_bad (w := w) hA hV hH hM hz hH0
    (fun c hc => ⟨(hY c hc).1, (hY c hc).2.1⟩) hsv hL
  rw [Finset.card_filter] at h4
  calc ∑ c ∈ Finset.range k, W A w (X c)
      ≤ ∑ c ∈ Finset.range k, (W A w (Y c) + S) := h1
    _ = ∑ a ∈ Finset.Icc 1 w, ((Finset.range k).filter (fun c => Y c + a ∈ A)).card
          + k * S := by
        rw [Finset.sum_add_distrib, h2, Finset.sum_const, Finset.card_range, smul_eq_mul]
    _ ≤ ∑ a ∈ Finset.Icc 1 w, (1 + k *
          (if 1 < ((Finset.range k).filter (fun c => Y c + a ∈ A)).card then 1 else 0))
          + k * S := Nat.add_le_add_right (Finset.sum_le_sum h3) _
    _ = w + k * ∑ a ∈ Finset.Icc 1 w,
          (if 1 < ((Finset.range k).filter (fun c => Y c + a ∈ A)).card then 1 else 0)
          + k * S := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, smul_eq_mul,
          Nat.card_Icc, Nat.add_sub_cancel, Nat.mul_one]
    _ ≤ w + k * (k * k * (L * (w / z + 1))) + k * S :=
        Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left k h4) w) _
    _ = w + k * S + k * (k * k * (L * (w / z + 1))) := by ring

/-- The pattern lemma with the positions supplied by the sieve. -/
theorem pattern_sieve {N : ℕ} {A : Finset ℕ} (hA : Adm N A) {w T M z H L : ℕ} {X : ℕ → ℕ}
    (hV : ∀ c, c < 2 * T + 1 → ∀ c', c' < c → (c - c') * N ≤ X c * X c')
    (hH : ∀ d, 0 < d → d < 2 * T + 1 → ∀ p : ℕ, p.Prime → p ≤ M → p * d ∣ H)
    (hcop : ∀ p : ℕ, p.Prime → M < p → ¬ p ∣ H)
    (hM : 2 ≤ M) (h4T : 4 * T ≤ M) (hMz : M ≤ z) (hH0 : 0 < H)
    (hL : ∀ D, D ≤ N → (D.primeFactors.filter (fun p => z < p)).card ≤ L) :
    ∑ c ∈ Finset.range (2 * T + 1), W A w (X c) ≤
      w + ((2 * T + 1) * (H * sieveR (2 * T) z + (2 * T + 1)) +
        (2 * T + 1) * ((2 * T + 1) * (2 * T + 1) * (L * (w / z + 1)))) := by
  obtain ⟨Y, q, hY1, hY2⟩ :=
    select (t := 2 * T) hH0 (by omega) hMz hcop X (2 * T + 1) (le_refl _)
  have h := pattern_lemma (w := w) (S := H * sieveR (2 * T) z + (2 * T + 1)) hA hV hH hM
    (by omega) hH0 (fun c hc => ⟨(hY1 c hc).1, (hY1 c hc).2.1, by
      have h7 := (hY1 c hc).2.2
      omega⟩) hY2 hL
  omega

/-! ## 6. Thresholds -/

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

/-- A bound for the window counts along a row of positions passes to the envelope along one
pattern of thresholds. -/
lemma pattern_Psi {N : ℕ} {A : Finset ℕ} {n w T err j : ℕ}
    (hNw : N ≤ (n * w) * (n * w)) (hj1 : 1 ≤ j) (hjn : j ≤ n)
    (hrow : ∀ X : ℕ → ℕ,
      (∀ c, c < 2 * T + 1 → ∀ c', c' < c → (c - c') * N ≤ X c * X c') →
      ∑ c ∈ Finset.range (2 * T + 1), W A w (X c) ≤ w + err) :
    ∑ c ∈ Finset.range (2 * T + 1), Psi A N w (th n T j c) ≤ w + err := by
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
    _ ≤ w + err := hrow X hV

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

/-! ## 7. Abel summation -/

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

/-! ## 8. The bound for fixed parameters -/

theorem fixed_bound {N : ℕ} {A : Finset ℕ} (hA : Adm N A) {n w T err : ℕ}
    (hn : 0 < n) (hw : 0 < w) (hT : 0 < T) (hNw : N ≤ (n * w) * (n * w))
    (hrow : ∀ X : ℕ → ℕ,
      (∀ c, c < 2 * T + 1 → ∀ c', c' < c → (c - c') * N ≤ X c * X c') →
      ∑ c ∈ Finset.range (2 * T + 1), W A w (X c) ≤ w + err) :
    (A.card : ℝ) ≤ (n:ℝ) * w + n * (err : ℝ) + 2 * w + n * E0 * (((w:ℝ) + 1) / 2) +
      ((N / (n * T * w) : ℕ) : ℝ) := by
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
      n * (w + err) := by
    have e : ∑ i ∈ Finset.Icc 1 n ×ˢ Finset.range (2 * T + 1), Psi A N w (th n T i.1 i.2) =
        ∑ j ∈ Finset.Icc 1 n, ∑ c ∈ Finset.range (2 * T + 1), Psi A N w (th n T j c) :=
      Finset.sum_product _ _ _
    have hc : (Finset.Icc 1 n).card = n := by simp
    rw [e]
    calc ∑ j ∈ Finset.Icc 1 n, ∑ c ∈ Finset.range (2 * T + 1), Psi A N w (th n T j c)
        ≤ ∑ j ∈ Finset.Icc 1 n, (w + err) := by
          refine Finset.sum_le_sum (fun j hj => ?_)
          rw [Finset.mem_Icc] at hj
          exact pattern_Psi hNw hj.1 hj.2 hrow
      _ = n * (w + err) := by rw [Finset.sum_const, hc, smul_eq_mul]
  have h0 := Psi_le_w A N w 0
  have hhalf := Psi_half hA hNw (le_refl n)
  have hsplitR : (A.card : ℝ) ≤ ∑ τ ∈ Finset.range (n * T), (Psi A N w τ : ℝ) +
      ((N / (n * T * w) : ℕ) : ℝ) := by exact_mod_cast hsplit
  have hfamR : ∑ i ∈ Finset.Icc 1 n ×ˢ Finset.range (2 * T + 1),
        (Psi A N w (th n T i.1 i.2) : ℝ) ≤ (n:ℝ) * ((w:ℝ) + (err : ℝ)) := by
    exact_mod_cast hfam
  have h0R : (Psi A N w 0 : ℝ) ≤ w := by exact_mod_cast h0
  have hhalfR : (Psi A N w n : ℝ) ≤ ((w:ℝ) + 1) / 2 := by
    have : (2:ℝ) * (Psi A N w n : ℝ) ≤ (w:ℝ) + 1 := by exact_mod_cast hhalf
    linarith
  have hmulE : (n * E0) * (Psi A N w n : ℝ) ≤ (n * E0) * (((w:ℝ) + 1) / 2) :=
    mul_le_mul_of_nonneg_left hhalfR (mul_nonneg (Nat.cast_nonneg n) hE0)
  linarith


/-! ## 9. Asymptotics

Parameters for `N` large: `l = ⌊log₂ N⌋`, `a = ⌊log₂ l⌋`, `r = ⌊√l⌋`, `T = ⌊r / a⌋` (also the number
of rows), `2 T + 1` windows in a row, sieving level `z = l ^ 4`, modulus `H = (4T)# · (2T)!`.
Every error term is at most `√N / T`, and `1 / T ≤ 8 log log N / √(log N)`. -/

lemma two_pow_bound (b : ℕ) (hb : 17 ≤ b) : 2048 * (2 * b + 1) ≤ 2 ^ b := by
  induction b, hb using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ 2 n]
    omega

/-- For large `l`, the square root of `l` is much larger than its binary logarithm. -/
lemma sqrt_large {a l : ℕ} (ha : 34 ≤ a) (hl : 2 ^ a ≤ l) : 2048 * a ≤ Nat.sqrt l := by
  have h1 := two_pow_bound (a / 2) (by omega)
  have h2 : 2 ^ (a / 2) ≤ Nat.sqrt l := by
    rw [Nat.le_sqrt, ← pow_add]
    exact le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hl
  have h3 : 2048 * a ≤ 2048 * (2 * (a / 2) + 1) := Nat.mul_le_mul_left _ (by omega)
  exact le_trans h3 (le_trans h1 h2)

lemma z_bound {a l : ℕ} (hl : l < 2 ^ (a + 1)) : l ^ 4 + 1 ≤ 2 ^ (4 * a + 4) := by
  have h : l ^ 4 < (2 ^ (a + 1)) ^ 4 := Nat.pow_lt_pow_left hl (by norm_num)
  have e : (2 ^ (a + 1)) ^ 4 = 2 ^ (4 * a + 4) := by
    rw [← pow_mul]
    congr 1
    omega
  exact le_of_le_of_eq (Nat.succ_le_of_lt h) e

lemma two_mul_succ_le {x y X Y : ℕ} (hx : x ≤ X) (hy : y ≤ Y) (hX : 1 ≤ X) (hY : 1 ≤ Y) :
    2 * x * y + 1 ≤ 4 * (X * Y) := by
  have h1 : x * y ≤ X * Y := Nat.mul_le_mul hx hy
  have h2 : 1 ≤ X * Y := Nat.mul_pos hX hY
  have e : 2 * x * y = 2 * (x * y) := Nat.mul_assoc 2 x y
  omega

lemma pow_four_mul (X Y : ℕ) : (2:ℕ) ^ (2 + X + Y) = 4 * (2 ^ X * 2 ^ Y) := by
  rw [pow_add, pow_add]
  ring

lemma pow_add_le (p q : ℕ) : 2 ^ p + 2 ^ q ≤ 2 ^ (p + q + 1) := by
  have h1 : 2 ^ p ≤ 2 ^ (p + q) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ q ≤ 2 ^ (p + q) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e : 2 ^ (p + q + 1) = 2 ^ (p + q) * 2 := pow_succ 2 (p + q)
  omega

/-- The length of the sieve range, the modulus and the number of windows, all together, are at
most a power of two with a small exponent. -/
lemma size_chain {a T l : ℕ} (hT : 1 ≤ T) (hl : l < 2 ^ (a + 1)) (hTl : T ≤ l) :
    T * (2 * T + 1) * T *
        (primorial (4 * T) * (2 * T).factorial * sieveR (2 * T) (l ^ 4) + (2 * T + 1)) ≤
      2 ^ (160 * (T * a * a) + 410 * (T * a) + 268 * T + 14 * a + 21) := by
  have hz := z_bound hl
  obtain ⟨z, hzdef⟩ : ∃ z, l ^ 4 = z := ⟨_, rfl⟩
  rw [hzdef] at hz ⊢
  have hp1 : 2 ^ (a + 2) = 2 ^ (a + 1) * 2 := pow_succ 2 (a + 1)
  have hT1 : T ≤ 2 ^ (a + 1) := by omega
  have hT2 : 2 * T ≤ 2 ^ (a + 2) := by omega
  have hk : 2 * T + 1 ≤ 2 ^ (a + 2) := by omega
  have hlog : Nat.log 2 (z + 1) ≤ 4 * a + 4 := by
    have h : z + 1 < 2 ^ (4 * a + 5) :=
      lt_of_le_of_lt hz (Nat.pow_lt_pow_right (by norm_num) (by omega))
    have h' := Nat.log_lt_of_lt_pow (by omega) h
    omega
  obtain ⟨J0, hJ0⟩ : ∃ J0, 4 * (2 * T) * (4 * a + 5) + 2 = J0 := ⟨_, rfl⟩
  have hJ : sieveJ (2 * T) z ≤ J0 := by
    unfold sieveJ
    rw [← hJ0]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) 2
  have hB : 1 + 2 * T * z ≤ 2 ^ (5 * a + 6) := by
    calc 1 + 2 * T * z ≤ 2 * T * (z + 1) := by
          rw [Nat.mul_add, Nat.mul_one]
          omega
      _ ≤ 2 ^ (a + 2) * 2 ^ (4 * a + 4) := Nat.mul_le_mul hT2 hz
      _ = 2 ^ (5 * a + 6) := by
          rw [← pow_add]
          congr 1
          omega
  have hR : sieveR (2 * T) z ≤ 2 ^ (2 + (4 * a + 4) * (2 * (2 * T)) + (5 * a + 6) * J0) := by
    have h1 : (z + 1) ^ (2 * (2 * T)) ≤ 2 ^ ((4 * a + 4) * (2 * (2 * T))) := by
      rw [pow_mul 2 (4 * a + 4) (2 * (2 * T))]
      exact Nat.pow_le_pow_left hz _
    have h2 : (1 + 2 * T * z) ^ sieveJ (2 * T) z ≤ 2 ^ ((5 * a + 6) * J0) := by
      rw [pow_mul 2 (5 * a + 6) J0]
      exact le_trans (Nat.pow_le_pow_left hB _)
        (Nat.pow_le_pow_right (Nat.two_pow_pos _) hJ)
    rw [pow_four_mul]
    unfold sieveR
    exact two_mul_succ_le h1 h2 Nat.one_le_two_pow Nat.one_le_two_pow
  have hH : primorial (4 * T) * (2 * T).factorial ≤
      2 ^ (2 * (4 * T) + (a + 2) * (2 * T)) := by
    have h1 : primorial (4 * T) ≤ 2 ^ (2 * (4 * T)) := by
      have e : (4:ℕ) ^ (4 * T) = 2 ^ (2 * (4 * T)) := by
        rw [pow_mul 2 2 (4 * T)]
        norm_num
      exact le_of_le_of_eq (primorial_le_four_pow (4 * T)) e
    have h2 : (2 * T).factorial ≤ 2 ^ ((a + 2) * (2 * T)) := by
      rw [pow_mul 2 (a + 2) (2 * T)]
      exact le_trans (Nat.factorial_le_pow (2 * T)) (Nat.pow_le_pow_left hT2 _)
    rw [pow_add 2 (2 * (4 * T)) ((a + 2) * (2 * T))]
    exact Nat.mul_le_mul h1 h2
  have hS : primorial (4 * T) * (2 * T).factorial * sieveR (2 * T) z + (2 * T + 1) ≤
      2 ^ (2 * (4 * T) + (a + 2) * (2 * T) +
        (2 + (4 * a + 4) * (2 * (2 * T)) + (5 * a + 6) * J0) + (a + 2) + 1) :=
    le_trans (Nat.add_le_add (le_of_le_of_eq (Nat.mul_le_mul hH hR) (pow_add 2 _ _).symm) hk)
      (pow_add_le _ _)
  have hTkT : T * (2 * T + 1) * T ≤ 2 ^ (a + 1 + (a + 2) + (a + 1)) := by
    rw [pow_add 2 (a + 1 + (a + 2)) (a + 1), pow_add 2 (a + 1) (a + 2)]
    exact Nat.mul_le_mul (Nat.mul_le_mul hT1 hk) hT1
  have e : a + 1 + (a + 2) + (a + 1) + (2 * (4 * T) + (a + 2) * (2 * T) +
      (2 + (4 * a + 4) * (2 * (2 * T)) + (5 * a + 6) * J0) + (a + 2) + 1) =
      160 * (T * a * a) + 410 * (T * a) + 268 * T + 14 * a + 21 := by
    rw [← hJ0]
    ring
  calc T * (2 * T + 1) * T *
        (primorial (4 * T) * (2 * T).factorial * sieveR (2 * T) z + (2 * T + 1))
      ≤ 2 ^ (a + 1 + (a + 2) + (a + 1)) * 2 ^ (2 * (4 * T) + (a + 2) * (2 * T) +
        (2 + (4 * a + 4) * (2 * (2 * T)) + (5 * a + 6) * J0) + (a + 2) + 1) :=
        Nat.mul_le_mul hTkT hS
    _ = 2 ^ (160 * (T * a * a) + 410 * (T * a) + 268 * T + 14 * a + 21) := by
        rw [← pow_add, e]

/-- The second error term: few bad offsets per pair of windows. -/
lemma small_terms {T L l : ℕ} (hT : 1 ≤ T) (hTT : T * T ≤ l) (h27 : 27 * T ≤ l) (hL : L ≤ l) :
    T * ((2 * T + 1) * (2 * T + 1) * (2 * T + 1)) * L * T ≤ l ^ 4 := by
  have hk : 2 * T + 1 ≤ 3 * T := by omega
  calc T * ((2 * T + 1) * (2 * T + 1) * (2 * T + 1)) * L * T
      ≤ T * ((3 * T) * (3 * T) * (3 * T)) * l * T :=
        Nat.mul_le_mul_right T (Nat.mul_le_mul (Nat.mul_le_mul_left T
          (Nat.mul_le_mul (Nat.mul_le_mul hk hk) hk)) hL)
    _ = 27 * T * (T * T) * (T * T) * l := by ring
    _ ≤ l * l * l * l :=
        Nat.mul_le_mul_right l (Nat.mul_le_mul (Nat.mul_le_mul h27 hTT) hTT)
    _ = l ^ 4 := by ring

/-- The real-number bookkeeping: all error terms of the fixed-parameter bound are `O(R / T)`. -/
lemma asym_core {card T w s k S L wz z tail R : ℝ}
    (h0 : card ≤ T * w + T * (k * S + k * (k * k * (L * (wz + 1)))) + 2 * w +
      T * E0 * ((w + 1) / 2) + tail)
    (hT : 1 ≤ T) (hw0 : 0 ≤ w) (hnw : T * w ≤ s + T)
    (hU : T * k * T * S ≤ s) (hP : T * (k * k * k) * L * T ≤ z) (hzs : z ≤ s)
    (hwz0 : 0 ≤ wz) (hwz : wz * z ≤ w) (htail : tail * T ≤ s) (hTT : T * T ≤ s)
    (hsR : s ≤ R) :
    card * T ≤ 3 * √2 / 4 * (R * T) + 11 * R := by
  have hT0 : 0 < T := by linarith
  have hD : T * w + T * E0 * ((w + 1) / 2) =
      3 * √2 / 4 * (T * w) + (3 * √2 / 4 - 1) * T := by
    unfold E0
    ring
  have hm1 : 3 * √2 / 4 * (T * w) ≤ 3 * √2 / 4 * (s + T) :=
    mul_le_mul_of_nonneg_left hnw (by positivity)
  have hm2 : √2 * T ≤ 1.4143 * T := mul_le_mul_of_nonneg_right sqrt2_ub hT0.le
  have hlin : card ≤ 3 * √2 / 4 * s + 1.2 * T + T * (k * S) + T * (k * k * k) * L * wz +
      T * (k * k * k) * L + 2 * w + tail := by
    have e : T * (k * S + k * (k * k * (L * (wz + 1)))) =
        T * (k * S) + T * (k * k * k) * L * wz + T * (k * k * k) * L := by ring
    linarith
  have h1 := mul_le_mul_of_nonneg_right hlin hT0.le
  have hp1 : T * (k * k * k) * L * T * wz ≤ z * wz := mul_le_mul_of_nonneg_right hP hwz0
  have hw1 : w ≤ T * w := le_mul_of_one_le_left hw0 hT
  have hT2 : T ≤ T * T := le_mul_of_one_le_left hT0.le hT
  have hs1 : s * T ≤ R * T := mul_le_mul_of_nonneg_right hsR hT0.le
  have hs2 : 3 * √2 / 4 * (s * T) ≤ 3 * √2 / 4 * (R * T) :=
    mul_le_mul_of_nonneg_left hs1 (by positivity)
  linarith

/-- From `R / T` to `R / √(log N) · log log N`. -/
lemma asym_final {card T R lam G : ℝ} (h : card * T ≤ 3 * √2 / 4 * (R * T) + 11 * R)
    (hT : 0 < T) (hR : 0 ≤ R) (hlam0 : 0 < lam) (hlam : lam ≤ 8 * (T * G)) :
    card ≤ 3 * √2 / 4 * R + 88 * (R / lam * G) := by
  have hX : 0 ≤ R / lam := div_nonneg hR hlam0.le
  have e : R / lam * lam = R := div_mul_cancel₀ R hlam0.ne'
  have h1 : R / lam * lam ≤ R / lam * (8 * (T * G)) := mul_le_mul_of_nonneg_left hlam hX
  have h2 : card * T ≤ (3 * √2 / 4 * R + 88 * (R / lam * G)) * T := by
    have e2 : (3 * √2 / 4 * R + 88 * (R / lam * G)) * T =
        3 * √2 / 4 * (R * T) + 11 * (R / lam * (8 * (T * G))) := by ring
    rw [e2]
    linarith
  exact le_of_mul_le_mul_right h2 hT

lemma log_le_nat {N l : ℕ} (hl : 3 ≤ l) (hN0 : N ≠ 0) (hN : N < 2 ^ (l + 1)) :
    Real.log (N:ℝ) ≤ (l:ℝ) := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
  have hN2 : (N:ℝ) < (2:ℝ) ^ (l + 1) := by exact_mod_cast hN
  have h1 : Real.log (N:ℝ) < Real.log ((2:ℝ) ^ (l + 1)) := Real.log_lt_log hNpos hN2
  rw [Real.log_pow] at h1
  have h2 := Real.log_two_lt_d9
  have h3 : ((l + 1 : ℕ) : ℝ) * Real.log 2 ≤ ((l + 1 : ℕ) : ℝ) * 0.7 :=
    mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
  have hl3 : (3:ℝ) ≤ l := by exact_mod_cast hl
  push_cast at h1 h3
  linarith

lemma loglog_lb {N l a : ℕ} (ha : 4 ≤ a) (hl : 2 ^ a ≤ l) (hN : 2 ^ l ≤ N) :
    (a:ℝ) ≤ 2 * Real.log (Real.log N) := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  have h2 := Real.log_two_gt_d9
  have hN1 : (2:ℝ) ^ l ≤ N := by exact_mod_cast hN
  have h1 : Real.log ((2:ℝ) ^ l) ≤ Real.log N := Real.log_le_log (by positivity) hN1
  rw [Real.log_pow] at h1
  have hl1 : (2:ℝ) ^ (b + 1) ≤ l := by exact_mod_cast hl
  rw [pow_succ] at hl1
  have hb0 : (0:ℝ) < 2 ^ b := by positivity
  have h3 : (l:ℝ) * (1 / 2) ≤ (l:ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg l)
  have h4 : (2:ℝ) ^ b ≤ Real.log N := by linarith
  have h5 : Real.log ((2:ℝ) ^ b) ≤ Real.log (Real.log N) := Real.log_le_log hb0 h4
  rw [Real.log_pow] at h5
  have h6 : (b:ℝ) * 0.69 ≤ (b:ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg b)
  have hb3 : (3:ℝ) ≤ b := by exact_mod_cast (by omega : 3 ≤ b)
  push_cast
  linarith

/-- The upper bound of Dai and Chen, with explicit parameters. -/
theorem upper {N : ℕ} (hN : 34 ≤ Nat.log 2 (Nat.log 2 N)) {A : Finset ℕ} (hA : Adm N A) :
    (A.card : ℝ) ≤ √(9 / 8 * (N:ℝ)) +
      88 * (√((N:ℝ) / Real.log N) * Real.log (Real.log N)) := by
  obtain ⟨l, hl⟩ : ∃ l, Nat.log 2 N = l := ⟨_, rfl⟩
  rw [hl] at hN
  obtain ⟨a, ha⟩ : ∃ a, Nat.log 2 l = a := ⟨_, rfl⟩
  rw [ha] at hN
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [Nat.log_zero_right] at ha
    omega
  have hN0 : N ≠ 0 := by
    rintro rfl
    rw [Nat.log_zero_right] at hl
    omega
  have hl1 : 2 ^ a ≤ l := by
    rw [← ha]
    exact Nat.pow_log_le_self 2 hl0
  have hl2 : l < 2 ^ (a + 1) := by
    rw [← ha]
    exact Nat.lt_pow_succ_log_self (by norm_num) l
  have hN1 : 2 ^ l ≤ N := by
    rw [← hl]
    exact Nat.pow_log_le_self 2 hN0
  have hN2 : N < 2 ^ (l + 1) := by
    rw [← hl]
    exact Nat.lt_pow_succ_log_self (by norm_num) N
  have ha0 : 0 < a := by omega
  -- the parameters `r` and `T`
  have hra := sqrt_large hN hl1
  have hrr : Nat.sqrt l * Nat.sqrt l ≤ l := Nat.sqrt_le l
  have hr1 : l < (Nat.sqrt l + 1) * (Nat.sqrt l + 1) := Nat.lt_succ_sqrt l
  have hTa : Nat.sqrt l / a * a ≤ Nat.sqrt l := Nat.div_mul_le_self _ _
  have hT0 : 0 < Nat.sqrt l / a := Nat.div_pos (by omega) ha0
  have hr2 : Nat.sqrt l < a * (Nat.sqrt l / a + 1) := Nat.lt_mul_div_succ _ ha0
  obtain ⟨r, hrdef⟩ : ∃ r, Nat.sqrt l = r := ⟨_, rfl⟩
  rw [hrdef] at hra hrr hr1 hTa hT0 hr2
  obtain ⟨T, hTdef⟩ : ∃ T, r / a = T := ⟨_, rfl⟩
  rw [hTdef] at hTa hT0 hr2
  have hTr : T ≤ r := le_trans (Nat.le_mul_of_pos_right T ha0) hTa
  have hrl : r ≤ l := le_trans (Nat.le_mul_self r) hrr
  have hTl : T ≤ l := le_trans hTr hrl
  have hTT : T * T ≤ l := le_trans (Nat.mul_le_mul hTr hTr) hrr
  have h27 : 27 * T ≤ l := by
    have h : 27 * T ≤ T * a := by
      rw [Nat.mul_comm T a]
      exact Nat.mul_le_mul_right T (by omega)
    omega
  have hbig : 2048 * (T * a * a) ≤ l := by
    have h := Nat.mul_le_mul hTa hra
    have e : T * a * (2048 * a) = 2048 * (T * a * a) := by ring
    rw [e] at h
    exact le_trans h hrr
  have he : 2 * (160 * (T * a * a) + 410 * (T * a) + 268 * T + 14 * a + 21) ≤ l := by
    have q1 : T * a ≤ T * a * a := Nat.le_mul_of_pos_right _ ha0
    have q2 : T ≤ T * a := Nat.le_mul_of_pos_right _ ha0
    have q3 : a ≤ T * a := Nat.le_mul_of_pos_left _ hT0
    omega
  -- the square root of `N`
  have hs1 : N < (Nat.sqrt N + 1) * (Nat.sqrt N + 1) := Nat.lt_succ_sqrt N
  have hsR : ((Nat.sqrt N : ℕ) : ℝ) ≤ √(N:ℝ) := Real.nat_sqrt_le_real_sqrt
  have hpow : 2 ^ (160 * (T * a * a) + 410 * (T * a) + 268 * T + 14 * a + 21) ≤
      Nat.sqrt N := by
    rw [Nat.le_sqrt, ← pow_add]
    exact le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hN1
  have hzs : l ^ 4 ≤ Nat.sqrt N := by
    have h := z_bound hl2
    have h' : 2 ^ (4 * a + 4) ≤
        2 ^ (160 * (T * a * a) + 410 * (T * a) + 268 * T + 14 * a + 21) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hSs := le_trans (size_chain hT0 hl2 hTl) hpow
  have hlz : l ≤ l ^ 4 := Nat.le_self_pow (by norm_num) l
  -- the sieving level
  obtain ⟨z, hzdef⟩ : ∃ z, l ^ 4 = z := ⟨_, rfl⟩
  rw [hzdef] at hzs hSs hlz
  have hMz : 4 * T ≤ z := by omega
  have hz2 : 2 ≤ z := by omega
  have hLl : Nat.log z N ≤ l := by
    rw [← hl]
    exact Nat.log_anti_left (by norm_num) hz2
  have hLdef : ∀ D, D ≤ N → (D.primeFactors.filter (fun p => z < p)).card ≤ Nat.log z N :=
    fun D hD => large_primeFactors_card hz2 hD
  obtain ⟨L, hLd⟩ : ∃ L, Nat.log z N = L := ⟨_, rfl⟩
  rw [hLd] at hLdef hLl
  have hPz := small_terms hT0 hTT h27 hLl
  rw [hzdef] at hPz
  -- the modulus
  have hHdvd : ∀ d, 0 < d → d < 2 * T + 1 → ∀ p : ℕ, p.Prime → p ≤ 4 * T →
      p * d ∣ primorial (4 * T) * (2 * T).factorial := by
    intro d hd0 hd p hp hpM
    exact Nat.mul_dvd_mul ((Nat.Prime.dvd_primorial_iff hp).mpr hpM)
      (Nat.dvd_factorial hd0 (by omega))
  have hcop : ∀ p : ℕ, p.Prime → 4 * T < p →
      ¬ p ∣ primorial (4 * T) * (2 * T).factorial := by
    intro p hp hpM hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
    · have h' := (Nat.Prime.dvd_primorial_iff hp).mp h
      omega
    · have h' := (Nat.Prime.dvd_factorial hp).mp h
      omega
  have hH0 : 0 < primorial (4 * T) * (2 * T).factorial :=
    Nat.mul_pos (primorial_pos _) (Nat.factorial_pos _)
  obtain ⟨H, hHdef⟩ : ∃ H, primorial (4 * T) * (2 * T).factorial = H := ⟨_, rfl⟩
  rw [hHdef] at hHdvd hcop hH0 hSs
  obtain ⟨R, hRd⟩ : ∃ R, sieveR (2 * T) z = R := ⟨_, rfl⟩
  rw [hRd] at hSs
  obtain ⟨s, hsdef⟩ : ∃ s, Nat.sqrt N = s := ⟨_, rfl⟩
  rw [hsdef] at hs1 hsR hzs hSs
  have hTTs : T * T ≤ s := by
    have h1 : T * T ≤ T * (2 * T + 1) * T :=
      Nat.mul_le_mul_right T (Nat.le_mul_of_pos_right T (by omega))
    have h2 : T * (2 * T + 1) * T ≤ T * (2 * T + 1) * T * (H * R + (2 * T + 1)) :=
      Nat.le_mul_of_pos_right _ (by omega)
    exact le_trans h1 (le_trans h2 hSs)
  -- the windows
  have hw1 : s < T * (s / T + 1) := Nat.lt_mul_div_succ s hT0
  have hw2 : T * (s / T + 1) ≤ s + T := by
    have h := Nat.mul_div_le s T
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hw0 : 0 < s / T + 1 := Nat.succ_pos _
  obtain ⟨w, hwdef⟩ : ∃ w, s / T + 1 = w := ⟨_, rfl⟩
  rw [hwdef] at hw1 hw2 hw0
  have hw1' : s + 1 ≤ T * w := Nat.succ_le_of_lt hw1
  have hNw : N ≤ (T * w) * (T * w) := by
    have h : (s + 1) * (s + 1) ≤ (T * w) * (T * w) := Nat.mul_le_mul hw1' hw1'
    omega
  have hrow : ∀ X : ℕ → ℕ,
      (∀ c, c < 2 * T + 1 → ∀ c', c' < c → (c - c') * N ≤ X c * X c') →
      ∑ c ∈ Finset.range (2 * T + 1), W A w (X c) ≤
        w + ((2 * T + 1) * (H * R + (2 * T + 1)) +
          (2 * T + 1) * ((2 * T + 1) * (2 * T + 1) * (L * (w / z + 1)))) := by
    intro X hV
    have h := pattern_sieve (w := w) hA hV hHdvd hcop (by omega : 2 ≤ 4 * T) (le_refl _) hMz hH0
      hLdef
    rw [hRd] at h
    exact h
  have hfix := fixed_bound hA hT0 hw0 hT0 hNw hrow
  have htailN : N / (T * T * w) * T ≤ s := by
    have e : T * T * w = T * w * T := by ring
    have h1 : N / (T * w) < s + 1 := Nat.div_lt_of_lt_mul (by
      calc N < (s + 1) * (s + 1) := hs1
        _ ≤ (T * w) * (s + 1) := Nat.mul_le_mul_right _ hw1')
    rw [e, ← Nat.div_div_eq_div_mul]
    have h2 := Nat.div_mul_le_self (N / (T * w)) T
    omega
  -- to the reals
  have h0 : (A.card : ℝ) ≤ (T:ℝ) * w + (T:ℝ) * ((2 * (T:ℝ) + 1) * ((H:ℝ) * R + (2 * T + 1)) +
      (2 * (T:ℝ) + 1) * ((2 * (T:ℝ) + 1) * (2 * T + 1) * ((L:ℝ) * (((w / z : ℕ) : ℝ) + 1)))) +
      2 * w + T * E0 * (((w:ℝ) + 1) / 2) + ((N / (T * T * w) : ℕ) : ℝ) := by
    have h := hfix
    push_cast at h
    linarith
  have hnwR : (T:ℝ) * w ≤ (s:ℝ) + T := by exact_mod_cast hw2
  have hUR : (T:ℝ) * (2 * (T:ℝ) + 1) * T * ((H:ℝ) * R + (2 * T + 1)) ≤ (s:ℝ) := by
    exact_mod_cast hSs
  have hPR : (T:ℝ) * ((2 * (T:ℝ) + 1) * (2 * T + 1) * (2 * T + 1)) * L * T ≤ (z:ℝ) := by
    exact_mod_cast hPz
  have hzsR : (z:ℝ) ≤ (s:ℝ) := by exact_mod_cast hzs
  have hwzR : ((w / z : ℕ) : ℝ) * z ≤ w := by exact_mod_cast Nat.div_mul_le_self w z
  have htailR : ((N / (T * T * w) : ℕ) : ℝ) * (T:ℝ) ≤ (s:ℝ) := by exact_mod_cast htailN
  have hTTR : (T:ℝ) * T ≤ (s:ℝ) := by exact_mod_cast hTTs
  have hT1R : (1:ℝ) ≤ T := by exact_mod_cast hT0
  have hcore := asym_core h0 hT1R (Nat.cast_nonneg w) hnwR hUR hPR hzsR (Nat.cast_nonneg _)
    hwzR htailR hTTR hsR
  -- from `1 / T` to `log log N / √(log N)`
  have hlogle : Real.log (N:ℝ) ≤ (l:ℝ) := log_le_nat (by omega) hN0 hN2
  have haG : (a:ℝ) ≤ 2 * Real.log (Real.log N) := loglog_lb (by omega) hl1 hN1
  have hN1' : 1 < N := by
    have h : 2 ^ 1 ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hlogpos : 0 < Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast hN1')
  have hlam0 : 0 < √(Real.log (N:ℝ)) := Real.sqrt_pos.mpr hlogpos
  have hl4 : l ≤ 2 * r * (2 * r) := by
    have h : (r + 1) * (r + 1) ≤ 2 * r * (2 * r) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hlam1 : √(Real.log (N:ℝ)) ≤ 2 * (r:ℝ) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have h : (l:ℝ) ≤ 2 * (r:ℝ) * (2 * r) := by exact_mod_cast hl4
    rw [sq]
    linarith
  have hr2aT : r ≤ 2 * (a * T) := by
    have h := hr2
    rw [Nat.mul_add, Nat.mul_one] at h
    have h' : a ≤ a * T := Nat.le_mul_of_pos_right a hT0
    omega
  have hrR : (r:ℝ) ≤ 2 * ((a:ℝ) * T) := by exact_mod_cast hr2aT
  have hTR0 : (0:ℝ) < T := by linarith
  have haT : (a:ℝ) * T ≤ 2 * Real.log (Real.log N) * T :=
    mul_le_mul_of_nonneg_right haG hTR0.le
  have hlam : √(Real.log (N:ℝ)) ≤ 8 * ((T:ℝ) * Real.log (Real.log N)) := by linarith
  have hfin := asym_final hcore hTR0 (Real.sqrt_nonneg _) hlam0 hlam
  rw [sqrt98, Real.sqrt_div (Nat.cast_nonneg N)]
  exact hfin

/-- From the two bounds to the `O`-statement. -/
theorem final {K : ℕ} (hK : 4 ≤ K)
    (UB : ∀ N : ℕ, K ≤ Nat.log 2 (Nat.log 2 N) → ∀ A, Adm N A →
      (A.card : ℝ) ≤ √(9 / 8 * (N:ℝ)) +
        88 * (√((N:ℝ) / Real.log N) * Real.log (Real.log N))) :
    (fun N : ℕ ↦ (Erdos441.g N : ℝ) - √(9 / 8 * N)) =O[Filter.atTop]
      fun N : ℕ ↦ √(N / Real.log N) * Real.log (Real.log N) := by
  refine Asymptotics.IsBigO.of_bound 88
    (Filter.eventually_atTop.mpr ⟨2 ^ 2 ^ K, fun N hN => ?_⟩)
  have hl : 2 ^ K ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) hN
  have ha : K ≤ Nat.log 2 (Nat.log 2 N) := Nat.le_log_of_pow_le (by norm_num) hl
  have hN0 : N ≠ 0 := by
    have h : 0 < 2 ^ 2 ^ K := Nat.two_pow_pos _
    omega
  have hN1 : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 hN0
  have hG : (K:ℝ) ≤ 2 * Real.log (Real.log N) := loglog_lb hK hl hN1
  have hK4 : (4:ℝ) ≤ K := by exact_mod_cast hK
  have hN2 : 1 < N := by
    have h1 : 1 ≤ 2 ^ K := Nat.one_le_two_pow
    have h2 : 2 ^ 1 ≤ 2 ^ Nat.log 2 N := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hlogpos : 0 < Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast hN2)
  have hlogle : Real.log (N:ℝ) ≤ N := Real.log_le_self (Nat.cast_nonneg N)
  have hX : 1 ≤ √((N:ℝ) / Real.log N) := by
    rw [Real.sqrt_div (Nat.cast_nonneg N), one_le_div (Real.sqrt_pos.mpr hlogpos)]
    exact Real.sqrt_le_sqrt hlogle
  have hrhs : 1 ≤ √((N:ℝ) / Real.log N) * Real.log (Real.log N) := by
    have h := mul_le_mul_of_nonneg_right hX (by linarith : (0:ℝ) ≤ Real.log (Real.log N))
    linarith
  obtain ⟨A, hA, hAc⟩ := g_attained N
  obtain ⟨B, hB, hBc⟩ := lower_construction N
  have hBg : (B.card : ℝ) ≤ Erdos441.g N := by exact_mod_cast g_ge hB
  have hup := UB N ha A hA
  rw [hAc] at hup
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg
    (by linarith : (0:ℝ) ≤ √((N:ℝ) / Real.log N) * Real.log (Real.log N)), abs_le]
  constructor
  · linarith
  · linarith

end E441D

theorem OMA.solution : type_of% @Erdos441.erdos_441.variants.chen_dai_upper_bound := by
  exact E441D.final (K := 34) (by norm_num) (fun N hN A hA => E441D.upper hN hA)
