import OMAReductions.R_Erdos247_erdos_247_R1
import Mathlib

-- Step Erdos247.erdos_247.R1.H2: hypothesis H2 of reduction Erdos247.erdos_247.R1
-- Credit: @rickmanelius

/-! The digit-count bound for algebraic sums of distinct powers of `1/2`, by the carry method
of Bailey, Borwein, Crandall and Pomerance (On the binary expansions of algebraic numbers,
J. Théor. Nombres Bordeaux 16 (2004)). The method follows the merged proof of
`erdos_247.variants.strong_condition` (pull request 2993); the text below is written anew and
proves the counting form with an explicit polynomial bound.

Let `x = 1 + ∑ 2^(-n_k)` be a root of an integer polynomial `P` of degree `D` with positive
leading coefficient, and `x_k` its truncation after `k` digits. Then `P (x_k)` is a signed sum of
dyadic terms indexed by degree-`d` tuples of digits, and `|P (x_k)| ≪ 2^(-n_k)`. This gives the
Liouville gap bound `n_(k+1) ≤ D n_k + L`. If some `n_k` were larger than a constant times
`(k+1)^(3D)`, pigeonhole would give a long gap among the weights of the lower-degree terms, a
digit `n_j` in a controlled window, and a gap among all weights just below the top-degree term
built from them. Only top-degree terms (all of the same sign) can sit in that window, and the
carry lemma `carry_contra` rules this out. So `n_k < A (k+1)^(3D)`, and at least
`N^(1/(3D)) / (2A)` exponents are at most `N` for large `N`. -/

open Filter Finset Polynomial

namespace OMA.PE247H2

noncomputable section

/-- Dyadic weights `(1/2)^m`. -/
def dy (m : ℕ) : ℝ := (1 / 2 : ℝ) ^ m

theorem dy_pos (m : ℕ) : 0 < dy m := by unfold dy; positivity

theorem dy_add (a b : ℕ) : dy (a + b) = dy a * dy b := by unfold dy; rw [pow_add]

theorem dy_le {a b : ℕ} (h : a ≤ b) : dy b ≤ dy a := by
  unfold dy; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) h

theorem dy_zero : dy 0 = 1 := by simp [dy]

theorem two_pow_mul_dy (m : ℕ) : (2 : ℝ) ^ m * dy m = 1 := by
  unfold dy; rw [← mul_pow]; norm_num

theorem dy_mul_pow {a b : ℕ} (h : a ≤ b) : dy b * 2 ^ (b - a) = dy a := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, dy_add, mul_assoc, mul_comm (dy c), two_pow_mul_dy, mul_one]

theorem quarter_bound (B : ℕ) : (B : ℝ) * dy (B + 2) ≤ 1 / 4 := by
  have h1 : (B : ℝ) ≤ 2 ^ B := by exact_mod_cast (Nat.lt_two_pow_self).le
  have h2 : dy (B + 2) = dy B * (1 / 4) := by rw [dy_add]; norm_num [dy]
  have h3 := two_pow_mul_dy B
  have h4 : (B : ℝ) * dy B ≤ 1 := by
    calc (B : ℝ) * dy B ≤ 2 ^ B * dy B := mul_le_mul_of_nonneg_right h1 (dy_pos B).le
      _ = 1 := h3
  rw [h2]
  nlinarith [dy_pos B]

/-- A finite sum of integer multiples of `dy w` with `w ≤ R` is an integer multiple of `dy R`. -/
theorem sum_dy_eq_int {ι : Type*} (s : Finset ι) (c : ι → ℤ) (w : ι → ℕ) (R : ℕ)
    (hw : ∀ i ∈ s, w i ≤ R) :
    ∑ i ∈ s, (c i : ℝ) * dy (w i) = dy R * ((∑ i ∈ s, c i * 2 ^ (R - w i) : ℤ) : ℝ) := by
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [← dy_mul_pow (hw i hi)]
  ring

/-- Terms of weight at least `m` sum to at most the coefficient mass times `dy m`. -/
theorem abs_sum_dy_le {ι : Type*} (s : Finset ι) (c : ι → ℤ) (w : ι → ℕ) (m : ℕ)
    (hw : ∀ i ∈ s, m ≤ w i) :
    |∑ i ∈ s, (c i : ℝ) * dy (w i)| ≤ (∑ i ∈ s, |(c i : ℝ)|) * dy m := by
  rw [Finset.sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i hi => ?_))
  rw [abs_mul, abs_of_pos (dy_pos _)]
  exact mul_le_mul_of_nonneg_left (dy_le (hw i hi)) (abs_nonneg _)

/-- The carry contradiction: a small signed dyadic sum cannot have a gap above a cut `R`
followed by a positive term whose neighbourhood carries only nonnegative coefficients. -/
theorem carry_contra {ι : Type*} [Fintype ι] (c : ι → ℤ) (w : ι → ℕ) (B N R : ℕ) (i₀ : ι)
    (hB : ∑ i, |(c i : ℝ)| ≤ B)
    (hV : |∑ i, (c i : ℝ) * dy (w i)| ≤ B * dy N)
    (hgap : ∀ i, R < w i → R + B + 2 < w i)
    (hR : R < w i₀) (hN : w i₀ + B + 2 ≤ N) (hpos : 0 < c i₀)
    (hsign : ∀ i, R < w i → w i ≤ w i₀ + B + 2 → 0 ≤ c i) : False := by
  classical
  set v : ι → ℝ := fun i => (c i : ℝ) * dy (w i) with hv
  set T := univ.filter (fun i => ¬ w i ≤ R) with hT
  set Mid := T.filter (fun i => w i ≤ w i₀ + B + 2) with hMid
  set Hi := T.filter (fun i => ¬ w i ≤ w i₀ + B + 2) with hHi
  have hsplit : ∑ i, v i = ∑ i ∈ univ.filter (fun i => w i ≤ R), v i + ∑ i ∈ T, v i :=
    (sum_filter_add_sum_filter_not _ _ _).symm
  have hT2 : ∑ i ∈ T, v i = ∑ i ∈ Mid, v i + ∑ i ∈ Hi, v i :=
    (sum_filter_add_sum_filter_not _ _ _).symm
  obtain ⟨z, hz⟩ : ∃ z : ℤ, ∑ i ∈ univ.filter (fun i => w i ≤ R), v i = dy R * z :=
    ⟨_, sum_dy_eq_int _ c w R (fun i hi => (mem_filter.mp hi).2)⟩
  have hsumB : ∀ s : Finset ι, ∑ i ∈ s, |(c i : ℝ)| ≤ B := fun s =>
    (sum_le_sum_of_subset_of_nonneg (subset_univ s) (fun _ _ _ => abs_nonneg _)).trans hB
  have hq : ∀ m : ℕ, (B : ℝ) * dy (m + B + 2) ≤ dy m / 4 := by
    intro m
    rw [add_assoc, dy_add]
    nlinarith [quarter_bound B, dy_pos m]
  have hTsmall : |∑ i ∈ T, v i| ≤ dy R / 4 := by
    have hw : ∀ i ∈ T, R + B + 2 ≤ w i := fun i hi =>
      (hgap i (lt_of_not_ge (mem_filter.mp hi).2)).le
    calc |∑ i ∈ T, v i| ≤ (∑ i ∈ T, |(c i : ℝ)|) * dy (R + B + 2) := abs_sum_dy_le T c w _ hw
      _ ≤ B * dy (R + B + 2) := mul_le_mul_of_nonneg_right (hsumB T) (dy_pos _).le
      _ ≤ dy R / 4 := hq R
  have hHsmall : |∑ i ∈ Hi, v i| ≤ dy (w i₀) / 4 := by
    have hw : ∀ i ∈ Hi, w i₀ + B + 2 ≤ w i := fun i hi =>
      (lt_of_not_ge (mem_filter.mp hi).2).le
    calc |∑ i ∈ Hi, v i| ≤ (∑ i ∈ Hi, |(c i : ℝ)|) * dy (w i₀ + B + 2) :=
          abs_sum_dy_le Hi c w _ hw
      _ ≤ B * dy (w i₀ + B + 2) := mul_le_mul_of_nonneg_right (hsumB Hi) (dy_pos _).le
      _ ≤ dy (w i₀) / 4 := hq (w i₀)
  have hMidge : dy (w i₀) ≤ ∑ i ∈ Mid, v i := by
    have hi₀ : i₀ ∈ Mid := by
      rw [hMid, hT, mem_filter, mem_filter]
      exact ⟨⟨mem_univ _, not_le.mpr hR⟩, by omega⟩
    have hc1 : (1 : ℝ) ≤ c i₀ := by exact_mod_cast hpos
    have hnn : ∀ i ∈ Mid, 0 ≤ v i := by
      intro i hi
      rw [hMid, hT, mem_filter, mem_filter] at hi
      have hc : (0 : ℝ) ≤ c i := by
        exact_mod_cast hsign i (lt_of_not_ge hi.1.2) hi.2
      exact mul_nonneg hc (dy_pos _).le
    calc dy (w i₀) ≤ v i₀ := by
          simp only [hv]
          nlinarith [dy_pos (w i₀)]
      _ ≤ ∑ i ∈ Mid, v i := single_le_sum hnn hi₀
  have hVsmall : |∑ i, v i| ≤ dy (w i₀) / 4 := by
    calc |∑ i, v i| ≤ B * dy N := hV
      _ ≤ B * dy (w i₀ + B + 2) := mul_le_mul_of_nonneg_left (dy_le hN) (Nat.cast_nonneg _)
      _ ≤ dy (w i₀) / 4 := hq (w i₀)
  have hdyR : dy (w i₀) ≤ dy R := dy_le hR.le
  have hz0 : z = 0 := by
    have h1 : |dy R * (z : ℝ)| ≤ dy R / 2 := by
      rw [← hz]
      have heq : ∑ i ∈ univ.filter (fun i => w i ≤ R), v i = ∑ i, v i - ∑ i ∈ T, v i := by
        rw [hsplit]; ring
      rw [heq]
      calc |∑ i, v i - ∑ i ∈ T, v i| ≤ |∑ i, v i| + |∑ i ∈ T, v i| := abs_sub _ _
        _ ≤ dy (w i₀) / 4 + dy R / 4 := add_le_add hVsmall hTsmall
        _ ≤ dy R / 2 := by linarith
    rw [abs_mul, abs_of_pos (dy_pos R)] at h1
    have hRpos := dy_pos R
    have h2 : |(z : ℝ)| < 1 := by
      by_contra hcon
      push Not at hcon
      nlinarith
    have h3 : |z| < 1 := by exact_mod_cast h2
    exact Int.abs_lt_one_iff.mp h3
  have hfin : ∑ i, v i = ∑ i ∈ Mid, v i + ∑ i ∈ Hi, v i := by
    rw [hsplit, hz, hz0, ← hT2]
    simp
  have e1 := (abs_le.mp hHsmall).1
  have e2 := (abs_le.mp hVsmall).2
  linarith [dy_pos (w i₀)]

/-- Pigeonhole for gaps: some start in a window of length `len` has no element of `S` in the
next `G` places. -/
theorem exists_gap (S : Finset ℕ) (a len G : ℕ) (h : S.card * G < len) :
    ∃ R ∈ Ico a (a + len), ∀ s ∈ S, ¬ (R < s ∧ s ≤ R + G) := by
  have hcard : (S.biUnion (fun s => Ico (s - G) s)).card < (Ico a (a + len)).card := by
    rw [Nat.card_Ico, Nat.add_sub_cancel_left]
    calc (S.biUnion (fun s => Ico (s - G) s)).card
        ≤ ∑ s ∈ S, (Ico (s - G) s).card := card_biUnion_le
      _ ≤ ∑ _s ∈ S, G := sum_le_sum (fun s _ => by rw [Nat.card_Ico]; omega)
      _ = S.card * G := by rw [sum_const, smul_eq_mul]
      _ < len := h
  obtain ⟨R, hR, hRn⟩ := exists_mem_notMem_of_card_lt_card hcard
  refine ⟨R, hR, fun s hs hRs => hRn ?_⟩
  rw [mem_biUnion]
  exact ⟨s, hs, by rw [mem_Ico]; omega⟩

/-- Digit weights: `none` stands for the leading `1`, `some j` for the digit at `n j`. -/
def dig (n : ℕ → ℕ) {k : ℕ} : Option (Fin k) → ℕ
  | none => 0
  | some j => n j

theorem dig_some (n : ℕ → ℕ) {k : ℕ} (j : Fin k) : dig n (some j) = n j := rfl

/-- The terms of `P (xs n k)`: a degree `d` and a tuple of `d` digits. -/
abbrev Idx (D k : ℕ) := Σ d : Fin (D + 1), (Fin d → Option (Fin k))

/-- The weight of a term: the sum of its digit positions. -/
def wt (n : ℕ → ℕ) {D k : ℕ} (u : Idx D k) : ℕ := ∑ i, dig n (u.2 i)

/-- The truncation `1 + 2^(-n_0) + ... + 2^(-n_(k-1))`. -/
def xs (n : ℕ → ℕ) (k : ℕ) : ℝ := 1 + ∑ i ∈ range k, dy (n i)

theorem xs_eq (n : ℕ → ℕ) (k : ℕ) : xs n k = ∑ o : Option (Fin k), dy (dig n o) := by
  rw [Fintype.sum_option]
  simp only [dig, dy_zero, xs]
  rw [Fin.sum_univ_eq_sum_range (fun i => dy (n i)) k]

theorem aeval_xs (P : ℤ[X]) (n : ℕ → ℕ) (k D : ℕ) (hD : P.natDegree ≤ D) :
    aeval (xs n k) P = ∑ u : Idx D k, (P.coeff u.1 : ℝ) * dy (wt n u) := by
  rw [aeval_eq_sum_range' (Nat.lt_succ_of_le hD), ← Fin.sum_univ_eq_sum_range, Fintype.sum_sigma]
  refine Fintype.sum_congr _ _ (fun d => ?_)
  rw [xs_eq, Fintype.sum_pow, zsmul_eq_mul, Finset.mul_sum]
  refine Fintype.sum_congr _ _ (fun t => ?_)
  simp only [wt, dy]
  rw [Finset.prod_pow_eq_pow_sum]

theorem summable_dyn {n : ℕ → ℕ} (hn : StrictMono n) : Summable (fun i => dy (n i)) :=
  Summable.of_nonneg_of_le (fun _ => (dy_pos _).le) (fun i => dy_le (hn.id_le i))
    summable_geometric_two

theorem tsum_dy : ∑' i, dy i = 2 := tsum_geometric_two

theorem xs_bounds {n : ℕ → ℕ} (hn : StrictMono n) (k : ℕ) :
    xs n k ∈ Set.Icc (0 : ℝ) 3 ∧ 1 + ∑' i, dy (n i) ∈ Set.Icc (0 : ℝ) 3 ∧
      |xs n k - (1 + ∑' i, dy (n i))| ≤ 2 * dy (n k) := by
  have hs := summable_dyn hn
  have hsplit := hs.sum_add_tsum_nat_add k
  have hs' : Summable (fun i => dy (n (i + k))) := (summable_nat_add_iff k).mpr hs
  have htail0 : 0 ≤ ∑' i, dy (n (i + k)) := tsum_nonneg (fun _ => (dy_pos _).le)
  have hstep : ∀ i, n k + i ≤ n (i + k) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have := hn (show i + k < i + 1 + k by omega)
      omega
  have htail : ∑' i, dy (n (i + k)) ≤ 2 * dy (n k) := by
    calc ∑' i, dy (n (i + k)) ≤ ∑' i, dy (n k) * dy i :=
          hs'.tsum_le_tsum (fun i => (dy_le (hstep i)).trans_eq (dy_add _ _))
            (summable_geometric_two.mul_left _)
      _ = 2 * dy (n k) := by rw [tsum_mul_left, tsum_dy]; ring
  have hpart : 0 ≤ ∑ i ∈ range k, dy (n i) := sum_nonneg (fun _ _ => (dy_pos _).le)
  have htot : ∑' i, dy (n i) ≤ 2 := by
    rw [← tsum_dy]
    exact hs.tsum_le_tsum (fun i => dy_le (hn.id_le i)) summable_geometric_two
  have hdk : dy (n k) ≤ 1 := by
    have := dy_le (Nat.zero_le (n k)); rwa [dy_zero] at this
  unfold xs
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ?_⟩
  rw [abs_le]
  constructor <;> linarith

/-- The truncations approach the root with error `O(2^(-n_k))`. -/
theorem poly_error (P : ℤ[X]) {n : ℕ → ℕ} (hn : StrictMono n)
    (hP : aeval (1 + ∑' i, dy (n i)) P = (0 : ℝ)) :
    ∃ L : ℕ, ∀ k, |aeval (xs n k) P| ≤ L * dy (n k) := by
  set K : ℝ := ∑ d ∈ range (P.natDegree + 1), |(P.coeff d : ℝ)| * (d * 3 ^ d) with hK
  have hK0 : 0 ≤ K := sum_nonneg (fun d _ => by positivity)
  obtain ⟨L, hL⟩ := exists_nat_gt (2 * K)
  refine ⟨L, fun k => ?_⟩
  obtain ⟨⟨h1a, h1b⟩, ⟨h2a, h2b⟩, h3⟩ := xs_bounds hn k
  set a := xs n k
  set b := 1 + ∑' i, dy (n i)
  have hdiff : aeval a P = ∑ d ∈ range (P.natDegree + 1), (P.coeff d : ℝ) * (a ^ d - b ^ d) := by
    rw [aeval_eq_sum_range, ← sub_zero (∑ _ ∈ _, _), ← hP, aeval_eq_sum_range, ← sum_sub_distrib]
    refine sum_congr rfl (fun d _ => ?_)
    rw [zsmul_eq_mul, zsmul_eq_mul]; ring
  have hterm : ∀ d ∈ range (P.natDegree + 1),
      |(P.coeff d : ℝ) * (a ^ d - b ^ d)| ≤ |(P.coeff d : ℝ)| * (d * 3 ^ d) * |a - b| := by
    intro d _
    rw [abs_mul]
    have hmax : max |a| |b| ≤ 3 := by
      rw [abs_of_nonneg h1a, abs_of_nonneg h2a]; exact max_le h1b h2b
    have hp := abs_pow_sub_pow_le a b d
    have h3d : max |a| |b| ^ (d - 1) ≤ 3 ^ d := by
      calc max |a| |b| ^ (d - 1) ≤ 3 ^ (d - 1) :=
            pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg a)) hmax _
        _ ≤ 3 ^ d := pow_le_pow_right₀ (by norm_num) (Nat.sub_le d 1)
    calc |(P.coeff d : ℝ)| * |a ^ d - b ^ d|
        ≤ |(P.coeff d : ℝ)| * (|a - b| * d * 3 ^ d) := by
          gcongr
          calc |a ^ d - b ^ d| ≤ |a - b| * d * max |a| |b| ^ (d - 1) := hp
            _ ≤ |a - b| * d * 3 ^ d := by gcongr
      _ = |(P.coeff d : ℝ)| * (d * 3 ^ d) * |a - b| := by ring
  calc |aeval a P| ≤ ∑ d ∈ range (P.natDegree + 1), |(P.coeff d : ℝ) * (a ^ d - b ^ d)| := by
        rw [hdiff]; exact abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ range (P.natDegree + 1), |(P.coeff d : ℝ)| * (d * 3 ^ d) * |a - b| :=
        sum_le_sum hterm
    _ = K * |a - b| := by rw [hK, sum_mul]
    _ ≤ K * (2 * dy (n k)) := mul_le_mul_of_nonneg_left h3 hK0
    _ = (2 * K) * dy (n k) := by ring
    _ ≤ L * dy (n k) := mul_le_mul_of_nonneg_right hL.le (dy_pos _).le

theorem xs_strictMono (n : ℕ → ℕ) : StrictMono (xs n) := by
  refine strictMono_nat_of_lt_succ (fun k => ?_)
  simp only [xs, sum_range_succ]
  linarith [dy_pos (n k)]

theorem eventually_ne_zero (P : ℤ[X]) (hP : P ≠ 0) (n : ℕ → ℕ) :
    ∀ᶠ k in atTop, aeval (xs n k) P ≠ (0 : ℝ) := by
  have hQ : P.map (algebraMap ℤ ℝ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap ℤ ℝ).injective_int).mpr hP
  have hfin : {k | aeval (xs n k) P = (0 : ℝ)}.Finite := by
    have := (Polynomial.finite_setOfPred_isRoot hQ).preimage (xs_strictMono n).injective.injOn
    refine this.subset (fun k hk => ?_)
    simp only [Set.mem_ofPred_eq] at hk
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, IsRoot, eval_map, ← aeval_def]
    exact hk
  have := hfin.eventually_cofinite_notMem
  rw [Nat.cofinite_eq_atTop] at this
  exact this

/-- Liouville's gap bound: the next digit after `n k` is at most `D n_k + L`. -/
theorem liouville (P : ℤ[X]) (hP : P ≠ 0) {n : ℕ → ℕ} (hn : StrictMono n) (L : ℕ)
    (hL : ∀ k, |aeval (xs n k) P| ≤ L * dy (n k)) :
    ∃ k₀, ∀ k ≥ k₀, n (k + 1) ≤ P.natDegree * n k + L := by
  obtain ⟨k₁, hk₁⟩ := eventually_atTop.mp (eventually_ne_zero P hP n)
  refine ⟨k₁, fun k hk => ?_⟩
  have hw : ∀ u : Idx P.natDegree (k + 1), wt n u ≤ P.natDegree * n k := by
    intro u
    have hdig : ∀ o : Option (Fin (k + 1)), dig n o ≤ n k := by
      intro o
      cases o with
      | none => simp [dig]
      | some j => exact hn.monotone (Nat.lt_succ_iff.mp j.isLt)
    calc wt n u = ∑ i, dig n (u.2 i) := rfl
      _ ≤ ∑ _i : Fin u.1, n k := sum_le_sum (fun _ _ => hdig _)
      _ = u.1 * n k := by simp
      _ ≤ P.natDegree * n k := Nat.mul_le_mul_right _ (Nat.lt_succ_iff.mp u.1.isLt)
  obtain ⟨z, hz⟩ : ∃ z : ℤ, aeval (xs n (k + 1)) P = dy (P.natDegree * n k) * z := by
    rw [aeval_xs P n (k + 1) P.natDegree le_rfl]
    exact ⟨_, sum_dy_eq_int univ _ _ (P.natDegree * n k) (fun u _ => hw u)⟩
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hk₁ (k + 1) (by omega) (by simpa using hz)
  have h1 : dy (P.natDegree * n k) ≤ |aeval (xs n (k + 1)) P| := by
    rw [hz, abs_mul, abs_of_pos (dy_pos _)]
    have : (1 : ℝ) ≤ |(z : ℝ)| := by exact_mod_cast Int.one_le_abs hz0
    nlinarith [dy_pos (P.natDegree * n k)]
  have h2 := hL (k + 1)
  by_contra hcon
  push Not at hcon
  have h3 : dy (n (k + 1)) ≤ dy (P.natDegree * n k) * dy (L + 1) := by
    rw [← dy_add]; exact dy_le (by omega)
  have h4 : (L : ℝ) * dy (L + 1) < 1 := by
    have h5 : (L : ℝ) < 2 ^ (L + 1) := by
      exact_mod_cast (Nat.lt_two_pow_self).trans (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self L))
    have h6 := two_pow_mul_dy (L + 1)
    nlinarith [dy_pos (L + 1)]
  have h7 : (L : ℝ) * dy (n (k + 1)) ≤ dy (P.natDegree * n k) * ((L : ℝ) * dy (L + 1)) := by
    calc (L : ℝ) * dy (n (k + 1)) ≤ L * (dy (P.natDegree * n k) * dy (L + 1)) :=
          mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _)
      _ = dy (P.natDegree * n k) * ((L : ℝ) * dy (L + 1)) := by ring
  have h8 : dy (P.natDegree * n k) * ((L : ℝ) * dy (L + 1)) < dy (P.natDegree * n k) :=
    mul_lt_of_lt_one_right (dy_pos _) h4
  linarith

/-- Every long enough initial stretch is followed by a digit within a factor `D`. -/
theorem nearby {n : ℕ → ℕ} (hn : StrictMono n) {D L k₀ : ℕ}
    (hb : ∀ k ≥ k₀, n (k + 1) ≤ D * n k + L) (x : ℕ) (hx : n k₀ ≤ x) :
    ∃ i, x < n i ∧ n i ≤ D * x + L := by
  classical
  have hex : ∃ i, x < n i := ⟨x + 1, Nat.lt_of_lt_of_le (Nat.lt_succ_self x) (hn.id_le (x + 1))⟩
  have hxi : x < n (Nat.find hex) := Nat.find_spec hex
  have hpos : k₀ < Nat.find hex := by
    by_contra h
    push Not at h
    exact absurd (lt_of_lt_of_le hxi (le_trans (hn.monotone h) hx)) (lt_irrefl _)
  have hprev : n (Nat.find hex - 1) ≤ x := by
    have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    omega
  have hstep := hb (Nat.find hex - 1) (by omega)
  rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at hstep
  exact ⟨Nat.find hex, hxi, hstep.trans (Nat.add_le_add_right (Nat.mul_le_mul_left D hprev) L)⟩

theorem card_idx (D k : ℕ) : Fintype.card (Idx D k) ≤ (D + 1) * (k + 1) ^ D := by
  rw [Fintype.card_sigma]
  calc ∑ d : Fin (D + 1), Fintype.card (Fin d → Option (Fin k))
      ≤ ∑ _d : Fin (D + 1), (k + 1) ^ D := by
        refine sum_le_sum (fun d _ => ?_)
        rw [Fintype.card_fun, Fintype.card_option, Fintype.card_fin, Fintype.card_fin]
        exact Nat.pow_le_pow_right (by omega) (Nat.lt_succ_iff.mp d.isLt)
    _ = (D + 1) * (k + 1) ^ D := by simp

/-- Shorter digit tuples can be padded with `none` without changing the weight. -/
theorem pad (n : ℕ → ℕ) {k d : ℕ} (t : Fin d → Option (Fin k)) :
    ∀ e, d ≤ e → ∃ t' : Fin e → Option (Fin k), ∑ i, dig n (t' i) = ∑ i, dig n (t i) := by
  intro e
  induction e with
  | zero =>
    intro h
    obtain rfl : d = 0 := by omega
    exact ⟨t, rfl⟩
  | succ e ih =>
    intro h
    rcases Nat.lt_or_ge d (e + 1) with hlt | hge
    · obtain ⟨t', ht'⟩ := ih (by omega)
      refine ⟨Fin.snoc t' none, ?_⟩
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, dig, add_zero]
      exact ht'
    · obtain rfl : d = e + 1 := by omega
      exact ⟨t, rfl⟩

/-- The carry step: the digit positions grow at most polynomially. -/
theorem stage {n : ℕ → ℕ} (hn : StrictMono n) (P : ℤ[X]) (D' : ℕ)
    (hD' : P.natDegree = D' + 1) (hlead : 0 < P.leadingCoeff) (L k₀ : ℕ)
    (hL : ∀ k, |aeval (xs n k) P| ≤ L * dy (n k))
    (hb : ∀ k ≥ k₀, n (k + 1) ≤ (D' + 1) * n k + L) (k : ℕ) :
    let U := ∑ d ∈ range (D' + 2), (P.coeff d).natAbs
    let C := (D' + 2) * (U + 1) + L
    let B := C * (k + 1) ^ (D' + 1)
    let H := (B + 2) ^ 2 + n k₀ + 1
    let M := (D' + 1) * H + L + B + 2
    n k < B * M + 1 + M := by
  intro U C B H M
  classical
  by_contra hcon
  push Not at hcon
  set S := (k + 1) ^ (D' + 1) with hS
  have hS1 : 1 ≤ S := Nat.one_le_pow _ _ (by omega)
  have hCD : D' + 2 ≤ C := by
    have : D' + 2 ≤ (D' + 2) * (U + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hcard : Fintype.card (Idx (D' + 1) k) ≤ B := by
    calc Fintype.card (Idx (D' + 1) k) ≤ (D' + 1 + 1) * (k + 1) ^ (D' + 1) := card_idx _ _
      _ ≤ C * S := Nat.mul_le_mul_right _ (by omega)
  have hLB : L ≤ B := by
    have : L ≤ C := by omega
    calc L ≤ C := this
      _ = C * 1 := (mul_one C).symm
      _ ≤ C * S := Nat.mul_le_mul_left _ hS1
  have hcoef : ∀ u : Idx (D' + 1) k, (P.coeff u.1).natAbs ≤ U := by
    intro u
    exact single_le_sum (f := fun d => (P.coeff d).natAbs) (fun _ _ => Nat.zero_le _)
      (mem_range.mpr u.1.isLt)
  have hmass : ∑ u : Idx (D' + 1) k, |((P.coeff u.1 : ℤ) : ℝ)| ≤ B := by
    have h1 : ∑ u : Idx (D' + 1) k, |((P.coeff u.1 : ℤ) : ℝ)| ≤
        ∑ _u : Idx (D' + 1) k, (U : ℝ) := by
      refine sum_le_sum (fun u _ => ?_)
      rw [← Int.cast_abs, Int.abs_eq_natAbs]
      exact_mod_cast hcoef u
    have h2 : (Fintype.card (Idx (D' + 1) k) : ℝ) * U ≤ B := by
      have : Fintype.card (Idx (D' + 1) k) * U ≤ B := by
        calc Fintype.card (Idx (D' + 1) k) * U ≤ ((D' + 2) * S) * U :=
              Nat.mul_le_mul_right _ (card_idx _ _)
          _ ≤ C * S := by
              have : (D' + 2) * U ≤ C := by
                have : (D' + 2) * U ≤ (D' + 2) * (U + 1) := Nat.mul_le_mul_left _ (by omega)
                omega
              calc (D' + 2) * S * U = ((D' + 2) * U) * S := by ring
                _ ≤ C * S := Nat.mul_le_mul_right _ this
      exact_mod_cast this
    calc _ ≤ ∑ _u : Idx (D' + 1) k, (U : ℝ) := h1
      _ = (Fintype.card (Idx (D' + 1) k) : ℝ) * U := by rw [sum_const, card_univ, nsmul_eq_mul]
      _ ≤ B := h2
  -- weights of the lower-degree terms
  set low : Finset ℕ := (univ : Finset (Fin D' → Option (Fin k))).image
    (fun t => ∑ i, dig n (t i)) with hlow
  have hlowcard : low.card ≤ B := by
    calc low.card ≤ (univ : Finset (Fin D' → Option (Fin k))).card := card_image_le
      _ = (k + 1) ^ D' := by simp
      _ ≤ S := Nat.pow_le_pow_right (by omega) (by omega)
      _ = 1 * S := (one_mul S).symm
      _ ≤ C * S := Nat.mul_le_mul_right _ (by omega)
  have h0low : 0 ∈ low := mem_image.mpr ⟨fun _ => none, mem_univ _, by simp [dig]⟩
  -- a long gap in the lower-degree weights
  obtain ⟨r₀, hr₀, hgap1⟩ := exists_gap low 0 (B * M + 1) M
    (by have := Nat.mul_le_mul_right M hlowcard; omega)
  have hr₀W : r₀ < B * M + 1 := by simpa using (mem_Ico.mp hr₀).2
  have hne : (low.filter (fun s => s ≤ r₀)).Nonempty := ⟨0, mem_filter.mpr ⟨h0low, Nat.zero_le _⟩⟩
  set a := (low.filter (fun s => s ≤ r₀)).max' hne with ha
  have ha_mem : a ∈ low ∧ a ≤ r₀ := mem_filter.mp (max'_mem _ _)
  have ha_above : ∀ s ∈ low, a < s → r₀ + M < s := by
    intro s hs has
    by_cases hsr : s ≤ r₀
    · have : s ≤ a := le_max' _ _ (mem_filter.mpr ⟨hs, hsr⟩)
      omega
    · have := hgap1 s hs
      omega
  -- a digit in a controlled window
  obtain ⟨j, hj1, hj2⟩ := nearby hn hb H (by omega)
  have hjk : j < k := by
    have : n j < n k := by omega
    exact hn.lt_iff_lt.mp this
  -- a gap in all weights just above `a`
  set allw : Finset ℕ := (univ : Finset (Idx (D' + 1) k)).image (wt n) with hallw
  have hallcard : allw.card ≤ B := card_image_le.trans (by rw [card_univ]; exact hcard)
  obtain ⟨R, hR, hgap2⟩ := exists_gap allw a (n j) (B + 2) (by
    have h1 := Nat.mul_le_mul_right (B + 2) hallcard
    have h2 : B * (B + 2) < (B + 2) ^ 2 := by nlinarith
    omega)
  obtain ⟨hRa, hRj⟩ := mem_Ico.mp hR
  -- the special top-degree term
  obtain ⟨ta, -, hta⟩ := mem_image.mp ha_mem.1
  let i₀ : Idx (D' + 1) k := ⟨Fin.last (D' + 1), Fin.cons (some ⟨j, hjk⟩) ta⟩
  have hwi₀ : wt n i₀ = n j + a := by
    change ∑ i : Fin (D' + 1), dig n ((Fin.cons (some ⟨j, hjk⟩) ta : Fin (D' + 1) → _) i) = _
    rw [Fin.sum_univ_succ, Fin.cons_zero]
    simp only [Fin.cons_succ]
    rw [hta, dig_some]
  have hci₀ : 0 < P.coeff i₀.1 := by
    change 0 < P.coeff (D' + 1)
    rw [← hD']
    exact hlead
  refine carry_contra (fun u : Idx (D' + 1) k => P.coeff u.1) (wt n) B (n k) R i₀
    hmass ?_ ?_ ?_ ?_ hci₀ ?_
  · rw [← aeval_xs P n k (D' + 1) hD'.le]
    calc |aeval (xs n k) P| ≤ L * dy (n k) := hL k
      _ ≤ B * dy (n k) := mul_le_mul_of_nonneg_right (by exact_mod_cast hLB) (dy_pos _).le
  · intro u hu
    have := hgap2 (wt n u) (mem_image.mpr ⟨u, mem_univ _, rfl⟩)
    omega
  · rw [hwi₀]; omega
  · rw [hwi₀]; omega
  · intro u hu1 hu2
    by_cases htop : (u.1 : ℕ) = D' + 1
    · have : P.coeff u.1 = P.leadingCoeff := by
        rw [htop, leadingCoeff, hD']
      rw [this]
      exact hlead.le
    · exfalso
      obtain ⟨t', ht'⟩ := pad n u.2 D' (by have := u.1.isLt; omega)
      have hmem : wt n u ∈ low := mem_image.mpr ⟨t', mem_univ _, ht'⟩
      have := ha_above (wt n u) hmem (by omega)
      rw [hwi₀] at hu2
      omega

/-- The cutoff of `stage` is at most a constant times `S^3`. -/
theorem poly_cutoff (C D L Q S : ℕ) (hS : 1 ≤ S) :
    (C * S) * (D * ((C * S + 2) ^ 2 + Q + 1) + L + C * S + 2) + 1 +
      (D * ((C * S + 2) ^ 2 + Q + 1) + L + C * S + 2) ≤
    ((C + 1) * (D * ((C + 2) ^ 2 + Q + 1) + L + C + 2) + 1) * S ^ 3 := by
  have hS2 : 1 ≤ S ^ 2 := Nat.one_le_pow _ _ hS
  have hS3 : 1 ≤ S ^ 3 := Nat.one_le_pow _ _ hS
  have hSS : S ≤ S ^ 2 := by nlinarith
  have h1 : C * S + 2 ≤ (C + 2) * S := by nlinarith
  have h2 : (C * S + 2) ^ 2 ≤ (C + 2) ^ 2 * S ^ 2 := by
    calc (C * S + 2) ^ 2 ≤ ((C + 2) * S) ^ 2 := Nat.pow_le_pow_left h1 2
      _ = (C + 2) ^ 2 * S ^ 2 := by ring
  have h3 : (C * S + 2) ^ 2 + Q + 1 ≤ ((C + 2) ^ 2 + Q + 1) * S ^ 2 := by nlinarith
  have h4 : D * ((C * S + 2) ^ 2 + Q + 1) ≤ D * (((C + 2) ^ 2 + Q + 1) * S ^ 2) :=
    Nat.mul_le_mul_left _ h3
  have h5 : L ≤ L * S ^ 2 := Nat.le_mul_of_pos_right _ (by omega)
  have h6 : C * S + 2 ≤ (C + 2) * S ^ 2 := le_trans h1 (Nat.mul_le_mul_left _ hSS)
  have hM : D * ((C * S + 2) ^ 2 + Q + 1) + L + C * S + 2 ≤
      (D * ((C + 2) ^ 2 + Q + 1) + L + C + 2) * S ^ 2 := by nlinarith
  have h7 : C * S + 1 ≤ (C + 1) * S := by nlinarith
  calc (C * S) * (D * ((C * S + 2) ^ 2 + Q + 1) + L + C * S + 2) + 1 +
        (D * ((C * S + 2) ^ 2 + Q + 1) + L + C * S + 2)
      = (C * S + 1) * (D * ((C * S + 2) ^ 2 + Q + 1) + L + C * S + 2) + 1 := by ring
    _ ≤ ((C + 1) * S) * ((D * ((C + 2) ^ 2 + Q + 1) + L + C + 2) * S ^ 2) + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul h7 hM) 1
    _ = (C + 1) * (D * ((C + 2) ^ 2 + Q + 1) + L + C + 2) * S ^ 3 + 1 := by ring
    _ ≤ ((C + 1) * (D * ((C + 2) ^ 2 + Q + 1) + L + C + 2) + 1) * S ^ 3 := by nlinarith

/-- An algebraic real number is a root of an integer polynomial of positive degree with
positive leading coefficient. -/
theorem pos_poly (x : ℝ) (hx : IsAlgebraic ℤ x) :
    ∃ P : ℤ[X], P ≠ 0 ∧ 0 < P.natDegree ∧ 0 < P.leadingCoeff ∧ aeval x P = 0 := by
  obtain ⟨P, hP, hroot⟩ := hx
  have hdeg : 0 < P.natDegree := by
    rcases Nat.eq_zero_or_pos P.natDegree with h | h
    · exfalso
      have hc := eq_C_of_natDegree_eq_zero h
      have h0 : P.coeff 0 = 0 := by
        rw [hc] at hroot
        simpa using hroot
      exact hP (by rw [hc, h0, C_0])
    · exact h
  rcases lt_or_gt_of_ne (leadingCoeff_ne_zero.mpr hP) with hneg | hposc
  · refine ⟨-P, neg_ne_zero.mpr hP, by rwa [natDegree_neg], ?_, by simp [hroot]⟩
    rw [leadingCoeff_neg]
    omega
  · exact ⟨P, hP, hdeg, hposc, hroot⟩

/-- Polynomial growth of the digit positions gives the counting bound. -/
theorem count_of_growth {n : ℕ → ℕ} (A T : ℕ) (hA : 1 ≤ A) (hT : 0 < T)
    (hid : ∀ k, k ≤ n k) (hg : ∀ k, n k < A * (k + 1) ^ T) :
    ∀ᶠ N : ℕ in atTop, (1 / (2 * A : ℝ)) * (N : ℝ) ^ ((1 : ℝ) / T) ≤
      ((range (N + 1)).filter (fun k => n k ≤ N)).card := by
  rw [eventually_atTop]
  refine ⟨(2 * A) ^ T, fun N hN => ?_⟩
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  have hA1 : (1 : ℝ) ≤ A := by exact_mod_cast hA
  set y : ℝ := (N : ℝ) ^ ((1 : ℝ) / T) with hy
  have hy0 : 0 ≤ y := by positivity
  have hyT : y ^ T = N := by
    rw [hy, one_div]
    exact Real.rpow_inv_natCast_pow (Nat.cast_nonneg N) (by omega)
  have hNbig : ((2 * A : ℕ) : ℝ) ^ T ≤ N := by exact_mod_cast hN
  have hy2 : 2 * A ≤ y := by
    by_contra hlt
    push Not at hlt
    have : y ^ T < (2 * A : ℝ) ^ T := pow_lt_pow_left₀ hlt hy0 (by omega)
    push_cast at hNbig
    linarith
  set m := ⌊y / A⌋₊ with hm
  have hm1 : (m : ℝ) ≤ y / A := Nat.floor_le (by positivity)
  have hm2 : y / A < m + 1 := Nat.lt_floor_add_one _
  have hsub : range m ⊆ (range (N + 1)).filter (fun k => n k ≤ N) := by
    intro k hk
    rw [mem_range] at hk
    have hk1 : ((k + 1 : ℕ) : ℝ) ≤ y / A := by
      have : ((k + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hk
      linarith
    have hAk : (A : ℝ) * (k + 1 : ℕ) ≤ y := by
      rw [le_div_iff₀ hA0] at hk1
      linarith
    have hpow : ((A : ℝ) * (k + 1 : ℕ)) ^ T ≤ N := by
      rw [← hyT]
      exact pow_le_pow_left₀ (by positivity) hAk T
    have hAT : (A : ℝ) ≤ (A : ℝ) ^ T := by
      calc (A : ℝ) = A ^ 1 := (pow_one _).symm
        _ ≤ A ^ T := pow_le_pow_right₀ hA1 hT
    have hnk : ((n k : ℕ) : ℝ) < N := by
      have h1 : ((n k : ℕ) : ℝ) < A * ((k + 1 : ℕ) : ℝ) ^ T := by exact_mod_cast hg k
      have h2 : (A : ℝ) * ((k + 1 : ℕ) : ℝ) ^ T ≤ ((A : ℝ) * (k + 1 : ℕ)) ^ T := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right hAT (by positivity)
      linarith
    have hnkN : n k < N := by exact_mod_cast hnk
    have hkN : k < N + 1 := by have := hid k; omega
    exact mem_filter.mpr ⟨mem_range.mpr hkN, hnkN.le⟩
  have hcard : (m : ℝ) ≤ ((range (N + 1)).filter (fun k => n k ≤ N)).card := by
    have := card_le_card hsub
    rw [card_range] at this
    exact_mod_cast this
  have hmy : y / (2 * A) ≤ m := by
    have : y / A - 1 ≤ m := by linarith
    have h2 : y / (2 * A) ≤ y / A - 1 := by
      rw [div_le_iff₀ (by positivity)]
      have : y / A * (2 * A) = 2 * y := by field_simp
      nlinarith
    linarith
  calc (1 / (2 * A : ℝ)) * y = y / (2 * A) := by ring
    _ ≤ m := hmy
    _ ≤ _ := hcard

theorem sol : OMA.R_Erdos247_erdos_247_R1.H2 := by
  unfold OMA.R_Erdos247_erdos_247_R1.H2
  intro n hn halg
  have hq : (∑' k, (1 : ℝ) / 2 ^ n k) = ∑' k, dy (n k) := by
    congr 1
    funext k
    rw [dy, one_div_pow]
  rw [hq] at halg
  have hx : IsAlgebraic ℚ (1 + ∑' k, dy (n k)) := isAlgebraic_one.add halg
  obtain ⟨P, hP, hD, hlead, hroot⟩ :=
    pos_poly _ ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr hx)
  obtain ⟨L, hL⟩ := poly_error P hn hroot
  obtain ⟨k₀, hk₀⟩ := liouville P hP hn L hL
  obtain ⟨D', hD'⟩ : ∃ D', P.natDegree = D' + 1 := ⟨P.natDegree - 1, by omega⟩
  rw [hD'] at hk₀
  set C := (D' + 2) * ((∑ d ∈ range (D' + 2), (P.coeff d).natAbs) + 1) + L with hC
  set A := (C + 1) * ((D' + 1) * ((C + 2) ^ 2 + n k₀ + 1) + L + C + 2) + 1 with hA
  have hgrowth : ∀ k, n k < A * (k + 1) ^ (3 * (D' + 1)) := by
    intro k
    have h1 := stage hn P D' hD' hlead L k₀ hL hk₀ k
    have h2 := poly_cutoff C (D' + 1) L (n k₀) ((k + 1) ^ (D' + 1))
      (Nat.one_le_pow _ _ (by omega))
    calc n k < _ := h1
      _ ≤ A * ((k + 1) ^ (D' + 1)) ^ 3 := h2
      _ = A * (k + 1) ^ (3 * (D' + 1)) := by rw [← pow_mul, mul_comm (D' + 1) 3]
  refine ⟨3 * (D' + 1), by omega, 1 / (2 * A : ℝ), by positivity, ?_⟩
  exact_mod_cast count_of_growth A (3 * (D' + 1)) (by omega) (by omega)
    (fun k => hn.id_le k) hgrowth

end

end OMA.PE247H2

theorem OMA.solution : OMA.R_Erdos247_erdos_247_R1.H2 := OMA.PE247H2.sol
