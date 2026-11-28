import FormalConjectures.ErdosProblems.«910»

/-!
# Erdős Problem 910 (Rudin's Connected Subset of the Plane under CH)

This file formalizes Mary Ellen Rudin's theorem (*A connected subset of the plane*,
Fund. Math. 46 (1958), 15–24): assuming the Continuum Hypothesis (`ℵ₁ = 𝔠`), there exists a
nontrivial connected subset `M` of the Euclidean plane `ℝ²` such that for every nontrivial
connected subset `N ⊆ M`, the complement `M \ N` is countable.

## Proof architecture

1. **Ambient indecomposable continuum (`BH`)**: We work with the Knaster bucket-handle continuum
   realized explicitly as the inverse limit of the tent map `tent t = 1 - |2 * t - 1|` on `[0, 1]`,
   embedded explicitly into `ℝ²` via a piecewise-linear (`ℓ¹`-diamond) bucket-handle embedding
   `embedBH : BH → ℝ²`.
2. **Composants and sections**: Every proper subcontinuum of `BH` lies in a single arc fiber
   `chart m η '' [0, 1]`, giving a clean algebraic characterization of composants and a
   countable basis of sections `Section` (`(k, a, b)` with rational endpoints avoiding `1/2`),
   together with binary-word strips, blocks, cylinder splitting `splitCyl`, and the separating-set
   section family `G(S)`.
3. **Rudin's Lemmas 1–4**: Adapted verbatim to `BH` and `Section`.
4. **Transfinite recursion under CH**: Using `ℵ₁ = 𝔠` to enumerate all countable single-point-per-
   composant sets `ℬ` and canonical separating sets `𝒮` along `ω₁`, we construct `M = ⋃ A_α ⊆ BH`
   meeting every separating set and having at most one point per composant, and prove `(M \ N).Countable`
   for every nontrivial connected `N ⊆ M`. Transferring along `embedBH` yields the planar witness.

-- Credit: @gdyan2022
-/

open scoped Cardinal Topology Classical
open Set Filter

namespace Erdos910RudinCH

noncomputable section

/- Section 1: Tent map, branch maps, and the bucket-handle continuum `BH` -/

/-- The standard tent map on `[0, 1]`. -/
def tent (t : ℝ) : ℝ := 1 - |2 * t - 1|

lemma continuous_tent : Continuous tent := by
  unfold tent
  fun_prop

lemma tent_eq_two_mul {t : ℝ} (ht : t ≤ 1 / 2) : tent t = 2 * t := by
  unfold tent
  rw [abs_of_nonpos (by linarith)]
  ring

lemma tent_eq_two_sub {t : ℝ} (ht : 1 / 2 ≤ t) : tent t = 2 - 2 * t := by
  unfold tent
  rw [abs_of_nonneg (by linarith)]
  ring

lemma tent_zero : tent 0 = 0 := by simp [tent]
lemma tent_one : tent 1 = 0 := by norm_num [tent]
lemma tent_half : tent (1 / 2) = 1 := by norm_num [tent]

lemma tent_mem_Icc {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : tent t ∈ Icc (0 : ℝ) 1 := by
  rcases le_total t (1 / 2) with h | h
  · rw [tent_eq_two_mul h]; constructor <;> linarith [ht.1, ht.2]
  · rw [tent_eq_two_sub h]; constructor <;> linarith [ht.1, ht.2]

lemma tent_iterate_mem_Icc (n : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    tent^[n] t ∈ Icc (0 : ℝ) 1 := by
  induction n generalizing t with
  | zero => exact ht
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact ih (tent_mem_Icc ht)

lemma tent_lipschitz (x y : ℝ) : |tent x - tent y| ≤ 2 * |x - y| := by
  unfold tent
  have h1 : |1 - |2 * x - 1| - (1 - |2 * y - 1|)| = |(|2 * y - 1| - |2 * x - 1|)| := by
    congr 1; ring
  rw [h1]
  calc
    |(|2 * y - 1| - |2 * x - 1|)| ≤ |(2 * y - 1) - (2 * x - 1)| := abs_abs_sub_abs_le _ _
    _ = |2 * (y - x)| := by ring_nf
    _ = 2 * |y - x| := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ = 2 * |x - y| := by rw [abs_sub_comm]

lemma tent_iterate_lipschitz (n : ℕ) (x y : ℝ) :
    |tent^[n] x - tent^[n] y| ≤ (2 : ℝ) ^ n * |x - y| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    calc
      |tent (tent^[n] x) - tent (tent^[n] y)| ≤ 2 * |tent^[n] x - tent^[n] y| :=
        tent_lipschitz _ _
      _ ≤ 2 * ((2 : ℝ) ^ n * |x - y|) := by gcongr
      _ = (2 : ℝ) ^ (n + 1) * |x - y| := by ring

/-- One-step inverse branch of the tent map. -/
def branchBit (b : Bool) (t : ℝ) : ℝ :=
  if b then 1 - t / 2 else t / 2

lemma continuous_branchBit (b : Bool) : Continuous (branchBit b) := by
  cases b <;> unfold branchBit <;> simp <;> fun_prop

lemma branchBit_mem_Icc (b : Bool) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    branchBit b t ∈ Icc (0 : ℝ) 1 := by
  cases b <;> simp only [branchBit, Bool.false_eq_true, ↓reduceIte, mem_Icc] at * <;>
    constructor <;> linarith [ht.1, ht.2]

lemma branchBit_false_mem_Ioo {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    branchBit false t ∈ Ioo (0 : ℝ) (1 / 2) := by
  simp only [branchBit, Bool.false_eq_true, ↓reduceIte, mem_Ioo]
  constructor <;> linarith [ht.1, ht.2]

lemma branchBit_true_mem_Ioo {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    branchBit true t ∈ Ioo (1 / 2 : ℝ) 1 := by
  simp only [branchBit, ↓reduceIte, mem_Ioo]
  constructor <;> linarith [ht.1, ht.2]

lemma tent_branchBit (b : Bool) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    tent (branchBit b t) = t := by
  cases b
  · simp only [branchBit, Bool.false_eq_true, ↓reduceIte]
    rw [tent_eq_two_mul (by linarith [ht.2])]; ring
  · simp only [branchBit, ↓reduceIte]
    rw [tent_eq_two_sub (by linarith [ht.2])]; ring

lemma branchBit_tent {s : ℝ} :
    branchBit (decide (1 / 2 < s)) (tent s) = s := by
  by_cases h : 1 / 2 < s
  · simp only [h, decide_true, branchBit, ↓reduceIte]
    rw [tent_eq_two_sub (le_of_lt h)]; ring
  · simp only [h, decide_false, branchBit, Bool.false_eq_true, ↓reduceIte]
    rw [tent_eq_two_mul (not_lt.mp h)]; ring

/-- Iterated inverse branch of the tent map along a finite word of bits. -/
def branchWord : List Bool → ℝ → ℝ
  | [], t => t
  | b :: w, t => branchWord w (branchBit b t)

/-- Parity of the number of `true` bits in a word (determines orientation reversal). -/
def branchParity : List Bool → Bool
  | [] => false
  | b :: w => xor b (branchParity w)

/-- Orientation sign `+1` or `-1` of `branchWord w`. -/
def branchSign (w : List Bool) : ℝ :=
  if branchParity w then -1 else 1

lemma branchSign_cons (b : Bool) (w : List Bool) :
    branchSign (b :: w) = (if b then -1 else 1) * branchSign w := by
  cases b <;> cases h : branchParity w <;> simp [branchSign, branchParity, h]

lemma branchWord_affine (w : List Bool) (t : ℝ) :
    branchWord w t = branchWord w 0 + branchSign w * t / (2 : ℝ) ^ w.length := by
  induction w generalizing t with
  | nil => simp [branchWord, branchSign, branchParity]
  | cons b w ih =>
    simp only [branchWord, List.length_cons]
    rw [ih (branchBit b t), ih (branchBit b 0), branchSign_cons]
    cases b <;> simp [branchBit] <;> ring

lemma branchWord_append (w₁ w₂ : List Bool) (t : ℝ) :
    branchWord (w₁ ++ w₂) t = branchWord w₂ (branchWord w₁ t) := by
  induction w₁ generalizing t with
  | nil => rfl
  | cons b w₁ ih => simp [branchWord, ih]

lemma branchWord_mem_Icc (w : List Bool) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    branchWord w t ∈ Icc (0 : ℝ) 1 := by
  induction w generalizing t with
  | nil => exact ht
  | cons b w ih => exact ih (branchBit_mem_Icc b ht)

lemma tent_iterate_branchWord (w : List Bool) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    tent^[w.length] (branchWord w t) = t := by
  induction w generalizing t with
  | nil => rfl
  | cons b w ih =>
    simp only [List.length_cons, branchWord]
    rw [Function.iterate_succ_apply', ih (branchBit_mem_Icc b ht), tent_branchBit b ht]

/-- The Knaster bucket-handle continuum as the inverse limit of `tent` on `[0, 1]`. -/
def BHSet : Set (ℕ → ℝ) :=
  {x | (∀ n, x n ∈ Icc (0 : ℝ) 1) ∧ ∀ n, tent (x (n + 1)) = x n}

abbrev BH := {x : ℕ → ℝ // x ∈ BHSet}

lemma bh_mem_Icc (x : BH) (n : ℕ) : x.1 n ∈ Icc (0 : ℝ) 1 := x.2.1 n

lemma bh_tent (x : BH) (n : ℕ) : tent (x.1 (n + 1)) = x.1 n := x.2.2 n

lemma bh_tent_iterate (x : BH) (n m : ℕ) : tent^[m] (x.1 (n + m)) = x.1 n := by
  induction m generalizing n with
  | zero => simp
  | succ m ih =>
    rw [show n + (m + 1) = (n + 1) + m by omega, Function.iterate_succ_apply', ih (n + 1),
      bh_tent x n]

lemma bh_tent_iterate_of_le (x : BH) {n k : ℕ} (h : n ≤ k) :
    tent^[k - n] (x.1 k) = x.1 n := by
  have h1 := bh_tent_iterate x n (k - n)
  rwa [Nat.add_sub_cancel' h] at h1

/-- The exceptional endpoint `0 = (0, 0, 0, ...)` of `BH`. -/
def bhZero : BH :=
  ⟨fun _ => 0, ⟨fun _ => ⟨le_rfl, zero_le_one⟩, fun _ => tent_zero⟩⟩

lemma isClosed_BHSet : IsClosed BHSet := by
  have h1 : IsClosed {x : ℕ → ℝ | ∀ n, x n ∈ Icc (0 : ℝ) 1} := by
    rw [show {x : ℕ → ℝ | ∀ n, x n ∈ Icc (0 : ℝ) 1} = ⋂ n, (fun x : ℕ → ℝ => x n) ⁻¹' Icc 0 1 by
      ext x; simp]
    exact isClosed_iInter fun n => isClosed_Icc.preimage (continuous_apply n)
  have h2 : IsClosed {x : ℕ → ℝ | ∀ n, tent (x (n + 1)) = x n} := by
    rw [show {x : ℕ → ℝ | ∀ n, tent (x (n + 1)) = x n} =
        ⋂ n, {x : ℕ → ℝ | tent (x (n + 1)) = x n} by ext x; simp]
    exact isClosed_iInter fun n =>
      isClosed_eq (continuous_tent.comp (continuous_apply (n + 1))) (continuous_apply n)
  exact h1.inter h2

instance : CompactSpace BH := by
  rw [← isCompact_univ_iff]
  have hsub : BHSet ⊆ Set.univ.pi (fun _ : ℕ => Icc (0 : ℝ) 1) := fun x hx n _ => hx.1 n
  have hcomp : IsCompact BHSet :=
    (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset isClosed_BHSet hsub
  simpa using (Topology.IsInducing.subtypeVal.isCompact_iff (s := univ)).mpr (by simpa using hcomp)

lemma continuous_bhCoord (n : ℕ) : Continuous (fun x : BH => x.1 n) :=
  (continuous_apply n).comp continuous_subtype_val

/-- Coordinate chart `chart k ε t`: the point of `BH` with `x_k = t` and upper bits `ε`. -/
def chartAux (ε : ℕ → Bool) (t : ℝ) : ℕ → ℝ
  | 0 => t
  | j + 1 => branchBit (ε j) (chartAux ε t j)

lemma chartAux_mem_Icc (ε : ℕ → Bool) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (j : ℕ) :
    chartAux ε t j ∈ Icc (0 : ℝ) 1 := by
  induction j with
  | zero => exact ht
  | succ j ih => exact branchBit_mem_Icc (ε j) ih

lemma continuous_chartAux (j : ℕ) :
    Continuous (fun p : (ℕ → Bool) × ℝ => chartAux p.1 p.2 j) := by
  induction j with
  | zero => exact continuous_snd
  | succ j ih =>
    rw [continuous_iff_continuousAt]
    intro ⟨ε, t⟩
    have hcond : Continuous (fun p : (ℕ → Bool) × ℝ => p.1 j) :=
      (continuous_apply j).comp continuous_fst
    have hopen : {p : (ℕ → Bool) × ℝ | p.1 j = ε j} ∈ 𝓝 (ε, t) := by
      have ho : IsOpen ((fun p : (ℕ → Bool) × ℝ => p.1 j) ⁻¹' {ε j}) :=
        (isOpen_discrete _).preimage hcond
      exact ho.mem_nhds rfl
    have hcon : ContinuousAt (fun p : (ℕ → Bool) × ℝ => branchBit (ε j) (chartAux p.1 p.2 j)) (ε, t) :=
      ((continuous_branchBit (ε j)).comp ih).continuousAt
    refine hcon.congr (Filter.eventually_of_mem hopen ?_)
    intro p hp
    have hpe : p.1 j = ε j := hp
    simp only [chartAux, hpe]

def chartVal (k : ℕ) (ε : ℕ → Bool) (t : ℝ) (n : ℕ) : ℝ :=
  if n ≤ k then tent^[k - n] t else chartAux ε t (n - k)

lemma chartVal_mem_BHSet (k : ℕ) (ε : ℕ → Bool) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    chartVal k ε t ∈ BHSet := by
  refine ⟨fun n => ?_, fun n => ?_⟩
  · unfold chartVal
    split_ifs
    · exact tent_iterate_mem_Icc _ ht
    · exact chartAux_mem_Icc ε ht _
  · unfold chartVal
    by_cases h1 : n + 1 ≤ k
    · have h0 : n ≤ k := by omega
      simp only [h1, h0, ↓reduceIte]
      have heq : k - n = (k - (n + 1)) + 1 := by omega
      rw [heq, Function.iterate_succ_apply']
    · by_cases h0 : n ≤ k
      · have hnk : n = k := by omega
        subst hnk
        simp only [h1, le_refl, ↓reduceIte, Nat.add_sub_cancel_left, Nat.sub_self,
          Function.iterate_zero, id_eq, chartAux]
        exact tent_branchBit (ε 0) ht
      · simp only [h1, h0, ↓reduceIte]
        have heq : n + 1 - k = (n - k) + 1 := by omega
        rw [heq, chartAux]
        exact tent_branchBit (ε (n - k)) (chartAux_mem_Icc ε ht (n - k))

/-- Chart map from `(ℕ → Bool) × [0, 1]` to `BH`. -/
def chart (k : ℕ) (ε : ℕ → Bool) (t : Icc (0 : ℝ) 1) : BH :=
  ⟨chartVal k ε t.1, chartVal_mem_BHSet k ε t.2⟩

lemma continuous_chart (k : ℕ) : Continuous (fun p : (ℕ → Bool) × Icc (0 : ℝ) 1 => chart k p.1 p.2) := by
  apply Continuous.subtype_mk
  rw [continuous_pi_iff]
  intro n
  unfold chartVal
  by_cases h : n ≤ k
  · simp only [h, ↓reduceIte]
    have hc : Continuous (tent^[k - n]) := continuous_tent.iterate (k - n)
    exact hc.comp (continuous_subtype_val.comp continuous_snd)
  · simp only [h, ↓reduceIte]
    exact (continuous_chartAux (n - k)).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

lemma chart_coord_self (k : ℕ) (ε : ℕ → Bool) (t : Icc (0 : ℝ) 1) :
    (chart k ε t).1 k = t.1 := by
  simp [chart, chartVal]

lemma chart_coord_add (k : ℕ) (ε : ℕ → Bool) (t : Icc (0 : ℝ) 1) (j : ℕ) :
    (chart k ε t).1 (k + j) = chartAux ε t.1 j := by
  cases j with
  | zero => simp [chart, chartVal, chartAux]
  | succ j =>
    have h : ¬ (k + (j + 1) ≤ k) := by omega
    simp [chart, chartVal, h]

/-- Prepend a finite word `w` to an infinite bit sequence `η`. -/
def prependWord (w : List Bool) (η : ℕ → Bool) (n : ℕ) : Bool :=
  if h : n < w.length then w[n] else η (n - w.length)

lemma prependWord_nil (η : ℕ → Bool) : prependWord [] η = η := by
  funext n; simp [prependWord]

lemma prependWord_cons_zero (b : Bool) (w : List Bool) (η : ℕ → Bool) :
    prependWord (b :: w) η 0 = b := by
  simp [prependWord]

lemma prependWord_cons_succ (b : Bool) (w : List Bool) (η : ℕ → Bool) (m : ℕ) :
    prependWord (b :: w) η (m + 1) = prependWord w η m := by
  simp only [prependWord, List.length_cons, Nat.add_lt_add_iff_right]
  split_ifs with h
  · rfl
  · congr 1; omega

lemma chartAux_prependWord (w : List Bool) (η : ℕ → Bool) (t : ℝ) (j : ℕ) :
    chartAux (prependWord w η) t (w.length + j) = chartAux η (branchWord w t) j := by
  induction w generalizing t with
  | nil => simp [prependWord_nil, branchWord]
  | cons b w ih =>
    have hstep : ∀ m, chartAux (prependWord (b :: w) η) t (m + 1) =
        chartAux (prependWord w η) (branchBit b t) m := by
      intro m
      induction m with
      | zero => simp [chartAux, prependWord_cons_zero]
      | succ m ihm =>
        conv_lhs => rw [chartAux]
        rw [ihm, prependWord_cons_succ]
        rfl
    simp only [List.length_cons, branchWord]
    rw [show w.length + 1 + j = (w.length + j) + 1 by omega, hstep, ih]

lemma chart_shift_word (k : ℕ) (w : List Bool) (η : ℕ → Bool) (t : Icc (0 : ℝ) 1) :
    chart (k + w.length) η ⟨branchWord w t.1, branchWord_mem_Icc w t.2⟩ =
      chart k (prependWord w η) t := by
  apply Subtype.ext
  funext n
  by_cases h : n ≤ k + w.length
  · have lhs_eq : (chart (k + w.length) η ⟨branchWord w t.1, branchWord_mem_Icc w t.2⟩).1 n =
        tent^[k + w.length - n] (branchWord w t.1) := by
      simp [chart, chartVal, h]
    have rhs_eq : (chart k (prependWord w η) t).1 n =
        tent^[k + w.length - n] ((chart k (prependWord w η) t).1 (k + w.length)) :=
      (bh_tent_iterate_of_le (chart k (prependWord w η) t) h).symm
    rw [lhs_eq, rhs_eq, chart_coord_add, show w.length = w.length + 0 by omega,
      chartAux_prependWord, chartAux]
  · have h1 : ¬ n ≤ k := by omega
    simp only [chart, chartVal, h, h1, ↓reduceIte]
    have hsub : n - k = w.length + (n - (k + w.length)) := by omega
    rw [hsub, chartAux_prependWord]

/-- Bit sequence of a point `x ∈ BH` starting at level `k`. -/
def bitsAt (k : ℕ) (x : BH) (j : ℕ) : Bool :=
  decide (1 / 2 < x.1 (k + j + 1))

lemma chart_bitsAt (k : ℕ) (x : BH) :
    chart k (bitsAt k x) ⟨x.1 k, bh_mem_Icc x k⟩ = x := by
  apply Subtype.ext
  funext n
  by_cases h : n ≤ k
  · simp only [chart, chartVal, h, ↓reduceIte]
    exact bh_tent_iterate_of_le x h
  · have haux : ∀ j, chartAux (bitsAt k x) (x.1 k) j = x.1 (k + j) := by
      intro j
      induction j with
      | zero => simp [chartAux]
      | succ j ih =>
        rw [chartAux, ih, bitsAt, show k + j + 1 = k + (j + 1) by omega]
        rw [← bh_tent x (k + (j + 1)), show k + (j + 1) = k + j + 1 by omega]
        simpa [bh_tent] using branchBit_tent (s := x.1 (k + j + 1))
    simp only [chart, chartVal, h, ↓reduceIte]
    rw [haux (n - k), show k + (n - k) = n by omega]

lemma chartAux_mem_Ioo (ε : ℕ → Bool) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (j : ℕ) :
    chartAux ε t j ∈ Ioo (0 : ℝ) 1 := by
  induction j with
  | zero => exact ht
  | succ j ih =>
    rw [chartAux]
    cases ε j
    · have h := branchBit_false_mem_Ioo ih
      exact ⟨h.1, by linarith [h.2]⟩
    · have h := branchBit_true_mem_Ioo ih
      exact ⟨by linarith [h.1], h.2⟩

lemma bitsAt_chart (k : ℕ) (ε : ℕ → Bool) {t : Icc (0 : ℝ) 1} (ht : t.1 ∈ Ioo (0 : ℝ) 1) :
    bitsAt k (chart k ε t) = ε := by
  funext j
  unfold bitsAt
  rw [show k + j + 1 = k + (j + 1) by omega, chart_coord_add, chartAux]
  have hmem := chartAux_mem_Ioo ε ht j
  cases hε : ε j
  · have hlt := (branchBit_false_mem_Ioo hmem).2
    rw [decide_eq_false_iff_not]; linarith
  · have hgt := (branchBit_true_mem_Ioo hmem).1
    rw [decide_eq_true_eq]; exact hgt

lemma chart_injective_on_Ioo (k : ℕ) {ε₁ ε₂ : ℕ → Bool} {t₁ t₂ : Icc (0 : ℝ) 1}
    (ht₁ : t₁.1 ∈ Ioo (0 : ℝ) 1) (h : chart k ε₁ t₁ = chart k ε₂ t₂) :
    ε₁ = ε₂ ∧ t₁ = t₂ := by
  have ht : t₁ = t₂ := by
    apply Subtype.ext
    have hc := congrArg (fun x : BH => x.1 k) h
    simpa [chart_coord_self] using hc
  subst ht
  have hε : ε₁ = ε₂ := by
    have hb := congrArg (bitsAt k) h
    rwa [bitsAt_chart k ε₁ ht₁, bitsAt_chart k ε₂ ht₁] at hb
  exact ⟨hε, rfl⟩

/-- `BH` is connected, because the path-connected composant of `bhZero` is dense in `BH`. -/
lemma isConnected_univ_BH : IsConnected (univ : Set BH) := by
  let F : ℕ → Set BH := fun m => range (fun t : Icc (0 : ℝ) 1 => chart m (fun _ => false) t)
  let S : Set BH := ⋃ m : ℕ, F m
  have hzero_mem : ∀ m : ℕ, bhZero ∈ F m := by
    intro m
    refine ⟨⟨0, le_rfl, zero_le_one⟩, ?_⟩
    apply Subtype.ext; funext n
    simp only [chart, chartVal, bhZero]
    split_ifs
    · have h0 : ∀ r, tent^[r] 0 = 0 := by
        intro r; induction r with | zero => rfl | succ r ih => rw [Function.iterate_succ_apply', ih, tent_zero]
      exact h0 _
    · have h0 : ∀ r, chartAux (fun _ => false) 0 r = 0 := by
        intro r; induction r with | zero => rfl | succ r ih => simp [chartAux, branchBit, ih]
      exact h0 _
  have hconnS : IsConnected S := by
    refine ⟨⟨bhZero, mem_iUnion.mpr ⟨0, hzero_mem 0⟩⟩, ?_⟩
    rw [show S = ⋃₀ range F by simp [S]]
    refine isPreconnected_sUnion bhZero (range F) ?_ ?_
    · rintro _ ⟨m, rfl⟩; exact hzero_mem m
    · rintro _ ⟨m, rfl⟩
      have hc : Continuous (fun t : Icc (0 : ℝ) 1 => chart m (fun _ => false) t) :=
        (continuous_chart m).comp (continuous_const.prodMk continuous_id)
      simpa [F, image_univ] using (isPreconnected_univ (α := Icc (0 : ℝ) 1)).image _ hc.continuousOn
  have hdenseS : Dense S := by
    intro x
    rw [mem_closure_iff_nhds]
    intro U hU
    rw [nhds_induced] at hU
    rcases hU with ⟨V, hV, hVU⟩
    rw [nhds_pi, Filter.mem_pi'] at hV
    rcases hV with ⟨I, t, ht, hIt⟩
    let m := I.sup id
    let y : BH := chart m (fun _ => false) ⟨x.1 m, bh_mem_Icc x m⟩
    refine ⟨y, ?_, mem_iUnion.mpr ⟨m, ⟨_, rfl⟩⟩⟩
    apply hVU
    apply hIt
    intro n hn
    have hnm : n ≤ m := Finset.le_sup (f := id) hn
    have hval : y.1 n = x.1 n := by
      simp only [y, chart, chartVal, hnm, ↓reduceIte]
      exact bh_tent_iterate_of_le x hnm
    rw [hval]
    exact mem_of_mem_nhds (ht n)
  rw [← hdenseS.closure_eq]
  exact hconnS.closure

instance : ConnectedSpace BH := connectedSpace_iff_univ.mpr isConnected_univ_BH

/- Section 2: Explicit planar `ℓ¹`-diamond bucket-handle embedding `embedBH : BH → ℝ²` -/

/-- Cumulative XOR (Gray code) of an infinite bit sequence. -/
def cumXor (ε : ℕ → Bool) : ℕ → Bool
  | 0 => ε 0
  | j + 1 => xor (cumXor ε j) (ε (j + 1))

lemma cumXor_injective : Function.Injective cumXor := by
  intro ε₁ ε₂ h
  funext j
  cases j with
  | zero => exact congrFun h 0
  | succ j =>
    have h1 : cumXor ε₁ j = cumXor ε₂ j := congrFun h j
    have h2 : xor (cumXor ε₁ j) (ε₁ (j + 1)) = xor (cumXor ε₂ j) (ε₂ (j + 1)) := congrFun h (j + 1)
    rw [h1] at h2
    cases h0 : cumXor ε₂ j <;> cases h1' : ε₁ (j + 1) <;> cases h2' : ε₂ (j + 1) <;> simp_all

lemma cumXor_zero_prefix (ε : ℕ → Bool) {k : ℕ} (h : ∀ j < k, ε j = false) :
    ∀ j < k, cumXor ε j = false := by
  intro j hj
  induction j with
  | zero => simpa [cumXor] using h 0 hj
  | succ j ih =>
    simp [cumXor, ih (by omega), h (j + 1) hj]

lemma cumXor_first_true (ε : ℕ → Bool) {k : ℕ} (h0 : ∀ j < k, ε j = false) (hk : ε k = true) :
    cumXor ε k = true := by
  cases k with
  | zero => simpa [cumXor] using hk
  | succ k => simp [cumXor, cumXor_zero_prefix ε h0 k (by omega), hk]

/-- Standard middle-thirds Cantor coordinate in `[0, 1]`. -/
def cantorTerm (δ : ℕ → Bool) (j : ℕ) : ℝ :=
  (if δ j then (2 : ℝ) else 0) / (3 : ℝ) ^ (j + 1)

lemma summable_two_div_three_pow : Summable (fun j : ℕ => (2 : ℝ) / (3 : ℝ) ^ (j + 1)) := by
  have h1 : (fun j : ℕ => (2 : ℝ) / (3 : ℝ) ^ (j + 1)) =
      fun j : ℕ => (2 / 3 : ℝ) * ((1 / 3 : ℝ) ^ j) := by
    funext j; rw [pow_succ, one_div_pow]; ring
  rw [h1]
  exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _

lemma summable_cantorTerm (δ : ℕ → Bool) : Summable (cantorTerm δ) := by
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) summable_two_div_three_pow
  · unfold cantorTerm; split_ifs <;> positivity
  · unfold cantorTerm; split_ifs
    · exact le_rfl
    · rw [zero_div]; positivity

def cantorVal (δ : ℕ → Bool) : ℝ := ∑' j : ℕ, cantorTerm δ j

lemma tsum_two_div_three_pow : ∑' j : ℕ, (2 : ℝ) / (3 : ℝ) ^ (j + 1) = 1 := by
  have h1 : (fun j : ℕ => (2 : ℝ) / (3 : ℝ) ^ (j + 1)) =
      fun j : ℕ => (2 / 3 : ℝ) * ((1 / 3 : ℝ) ^ j) := by
    funext j; rw [pow_succ, one_div_pow]; ring
  rw [h1, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

lemma cantorVal_nonneg (δ : ℕ → Bool) : 0 ≤ cantorVal δ :=
  tsum_nonneg fun j => by unfold cantorTerm; split_ifs <;> positivity

lemma cantorVal_le_one (δ : ℕ → Bool) : cantorVal δ ≤ 1 := by
  rw [← tsum_two_div_three_pow]
  refine (summable_cantorTerm δ).tsum_le_tsum (fun j => ?_) summable_two_div_three_pow
  unfold cantorTerm; split_ifs
  · exact le_rfl
  · rw [zero_div]; positivity

lemma cantorVal_split (δ : ℕ → Bool) (m : ℕ) :
    cantorVal δ = (∑ j ∈ Finset.range m, cantorTerm δ j) +
      cantorVal (fun j => δ (m + j)) / (3 : ℝ) ^ m := by
  unfold cantorVal
  rw [← (summable_cantorTerm δ).sum_add_tsum_nat_add m]
  congr 1
  rw [← tsum_div_const]
  congr 1; funext j
  unfold cantorTerm
  rw [show j + m = m + j by omega, show m + j + 1 = (j + 1) + m by omega, pow_add]
  ring

lemma cantorVal_compl (δ : ℕ → Bool) :
    cantorVal (fun j => !δ j) = 1 - cantorVal δ := by
  have hsum : cantorVal (fun j => !δ j) + cantorVal δ = 1 := by
    unfold cantorVal
    rw [← (summable_cantorTerm _).tsum_add (summable_cantorTerm _), ← tsum_two_div_three_pow]
    congr 1; funext j
    unfold cantorTerm
    cases h : δ j <;> simp [h]
  linarith

lemma cantorVal_eq_zero_iff (δ : ℕ → Bool) :
    cantorVal δ = 0 ↔ ∀ j, δ j = false := by
  constructor
  · intro h j
    by_contra hne
    have htrue : δ j = true := by cases hdj : δ j <;> simp_all
    have hpos : 0 < cantorTerm δ j := by simp [cantorTerm, htrue]
    have hle : cantorTerm δ j ≤ cantorVal δ :=
      (summable_cantorTerm δ).le_tsum j (fun i _ => by unfold cantorTerm; split_ifs <;> positivity)
    linarith
  · intro h
    unfold cantorVal
    convert tsum_zero with j
    simp [cantorTerm, h j]

lemma cantorVal_dist_le {δ₁ δ₂ : ℕ → Bool} {m : ℕ} (h : ∀ j < m, δ₁ j = δ₂ j) :
    |cantorVal δ₁ - cantorVal δ₂| ≤ 1 / (3 : ℝ) ^ m := by
  rw [cantorVal_split δ₁ m, cantorVal_split δ₂ m]
  have hsum : ∑ j ∈ Finset.range m, cantorTerm δ₁ j = ∑ j ∈ Finset.range m, cantorTerm δ₂ j := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [cantorTerm, h j (Finset.mem_range.mp hj)]
  rw [hsum, add_sub_add_left_eq_sub, ← sub_div, abs_div,
    abs_of_pos (show (0 : ℝ) < (3 : ℝ) ^ m by positivity)]
  have h1 := cantorVal_nonneg (fun j => δ₁ (m + j))
  have h2 := cantorVal_le_one (fun j => δ₁ (m + j))
  have h3 := cantorVal_nonneg (fun j => δ₂ (m + j))
  have h4 := cantorVal_le_one (fun j => δ₂ (m + j))
  gcongr
  rw [abs_le]; constructor <;> linarith

lemma cantorVal_injective : Function.Injective cantorVal := by
  intro δ₁ δ₂ heq
  by_contra hne
  have hex : ∃ j, δ₁ j ≠ δ₂ j := by
    by_contra hall; push Not at hall; exact hne (funext hall)
  let m := Nat.find hex
  have hm : δ₁ m ≠ δ₂ m := Nat.find_spec hex
  have hlt : ∀ j < m, δ₁ j = δ₂ j := fun j hj => by
    by_contra hne'; exact Nat.find_min hex hj hne'
  have hsplit := heq
  rw [cantorVal_split δ₁ (m + 1), cantorVal_split δ₂ (m + 1),
    Finset.sum_range_succ, Finset.sum_range_succ] at hsplit
  have hsum : ∑ j ∈ Finset.range m, cantorTerm δ₁ j = ∑ j ∈ Finset.range m, cantorTerm δ₂ j :=
    Finset.sum_congr rfl fun j hj => by simp [cantorTerm, hlt j (Finset.mem_range.mp hj)]
  have hdiff : cantorTerm δ₁ m - cantorTerm δ₂ m =
      (cantorVal (fun j => δ₂ (m + 1 + j)) - cantorVal (fun j => δ₁ (m + 1 + j))) /
        (3 : ℝ) ^ (m + 1) := by
    rw [sub_div]; linarith
  have habs_rhs : |(cantorVal (fun j => δ₂ (m + 1 + j)) - cantorVal (fun j => δ₁ (m + 1 + j))) /
      (3 : ℝ) ^ (m + 1)| ≤ 1 / (3 : ℝ) ^ (m + 1) := by
    rw [abs_div, abs_of_pos (show (0 : ℝ) < (3 : ℝ) ^ (m + 1) by positivity)]
    have h1 := cantorVal_nonneg (fun j => δ₁ (m + 1 + j))
    have h2 := cantorVal_le_one (fun j => δ₁ (m + 1 + j))
    have h3 := cantorVal_nonneg (fun j => δ₂ (m + 1 + j))
    have h4 := cantorVal_le_one (fun j => δ₂ (m + 1 + j))
    gcongr; rw [abs_le]; constructor <;> linarith
  have habs_lhs : |cantorTerm δ₁ m - cantorTerm δ₂ m| = 2 / (3 : ℝ) ^ (m + 1) := by
    unfold cantorTerm
    cases h1 : δ₁ m <;> cases h2 : δ₂ m
    · exact absurd (h1.trans h2.symm) hm
    · simp only [Bool.false_eq_true, ↓reduceIte, zero_div, zero_sub, abs_neg,
        abs_of_pos (show (0 : ℝ) < 2 / (3 : ℝ) ^ (m + 1) by positivity)]
    · simp only [Bool.false_eq_true, ↓reduceIte, zero_div, sub_zero,
        abs_of_pos (show (0 : ℝ) < 2 / (3 : ℝ) ^ (m + 1) by positivity)]
    · exact absurd (h1.trans h2.symm) hm
  rw [hdiff] at habs_lhs
  have hpos : (0 : ℝ) < 1 / (3 : ℝ) ^ (m + 1) := by positivity
  have h2eq : 2 / (3 : ℝ) ^ (m + 1) = 2 * (1 / (3 : ℝ) ^ (m + 1)) := by ring
  linarith

lemma cantorVal_bounds_of_first_true {δ : ℕ → Bool} {j0 : ℕ}
    (h0 : ∀ j < j0, δ j = false) (h1 : δ j0 = true) :
    2 / (3 : ℝ) ^ (j0 + 1) ≤ cantorVal δ ∧ cantorVal δ ≤ 1 / (3 : ℝ) ^ j0 := by
  rw [cantorVal_split δ (j0 + 1), Finset.sum_range_succ]
  have hz : ∑ j ∈ Finset.range j0, cantorTerm δ j = 0 :=
    Finset.sum_eq_zero fun j hj => by simp [cantorTerm, h0 j (Finset.mem_range.mp hj)]
  rw [hz, zero_add]
  have ht : cantorTerm δ j0 = 2 / (3 : ℝ) ^ (j0 + 1) := by simp [cantorTerm, h1]
  rw [ht]
  have hn := cantorVal_nonneg (fun j => δ (j0 + 1 + j))
  have hl := cantorVal_le_one (fun j => δ (j0 + 1 + j))
  have hpow : (3 : ℝ) ^ (j0 + 1) = 3 * (3 : ℝ) ^ j0 := by rw [pow_succ]; ring
  constructor
  · have : 0 ≤ cantorVal (fun j => δ (j0 + 1 + j)) / (3 : ℝ) ^ (j0 + 1) := by positivity
    linarith
  · have hdiv : cantorVal (fun j => δ (j0 + 1 + j)) / (3 : ℝ) ^ (j0 + 1) ≤
        1 / (3 : ℝ) ^ (j0 + 1) := by gcongr
    have hsum : 2 / (3 : ℝ) ^ (j0 + 1) + 1 / (3 : ℝ) ^ (j0 + 1) = 1 / (3 : ℝ) ^ j0 := by
      rw [hpow]; field_simp; ring
    linarith

lemma cantorVal_dist_mid_bounds {δ : ℕ → Bool} {j0 : ℕ}
    (h0 : ∀ j < j0, δ j = false) (h1 : δ j0 = true) :
    1 / (6 * (3 : ℝ) ^ (j0 + 1)) ≤ |cantorVal δ - 5 / (2 * (3 : ℝ) ^ (j0 + 1))| ∧
      |cantorVal δ - 5 / (2 * (3 : ℝ) ^ (j0 + 1))| ≤ 1 / (2 * (3 : ℝ) ^ (j0 + 1)) := by
  rw [cantorVal_split δ (j0 + 2), Finset.sum_range_succ, Finset.sum_range_succ]
  have hz : ∑ j ∈ Finset.range j0, cantorTerm δ j = 0 :=
    Finset.sum_eq_zero fun j hj => by simp [cantorTerm, h0 j (Finset.mem_range.mp hj)]
  rw [hz, zero_add]
  have ht0 : cantorTerm δ j0 = 2 / (3 : ℝ) ^ (j0 + 1) := by simp [cantorTerm, h1]
  rw [ht0]
  set r := cantorVal (fun j => δ (j0 + 2 + j))
  have hr0 : 0 ≤ r := cantorVal_nonneg _
  have hr1 : r ≤ 1 := cantorVal_le_one _
  have hpow : (3 : ℝ) ^ (j0 + 2) = 3 * (3 : ℝ) ^ (j0 + 1) := by rw [pow_succ]; ring
  have hp3 : (0 : ℝ) < (3 : ℝ) ^ (j0 + 1) := by positivity
  have hp6 : (0 : ℝ) < 6 * (3 : ℝ) ^ (j0 + 1) := by positivity
  cases h2 : δ (j0 + 1)
  · have ht1 : cantorTerm δ (j0 + 1) = 0 := by simp [cantorTerm, h2]
    rw [ht1, add_zero, hpow]
    have hdiff : 2 / (3 : ℝ) ^ (j0 + 1) + r / (3 * (3 : ℝ) ^ (j0 + 1)) -
        5 / (2 * (3 : ℝ) ^ (j0 + 1)) = -(3 - 2 * r) / (6 * (3 : ℝ) ^ (j0 + 1)) := by
      field_simp; ring
    rw [hdiff, abs_div, abs_neg, abs_of_pos (show 0 < 3 - 2 * r by linarith), abs_of_pos hp6]
    constructor
    · rw [div_le_div_iff_of_pos_right hp6]; linarith
    · rw [div_le_div_iff₀ hp6 (by positivity)]; nlinarith
  · have ht1 : cantorTerm δ (j0 + 1) = 2 / (3 : ℝ) ^ (j0 + 2) := by simp [cantorTerm, h2]
    rw [ht1, hpow]
    have hdiff : 2 / (3 : ℝ) ^ (j0 + 1) + 2 / (3 * (3 : ℝ) ^ (j0 + 1)) +
        r / (3 * (3 : ℝ) ^ (j0 + 1)) - 5 / (2 * (3 : ℝ) ^ (j0 + 1)) =
        (1 + 2 * r) / (6 * (3 : ℝ) ^ (j0 + 1)) := by
      field_simp; ring
    rw [hdiff, abs_div, abs_of_pos (show 0 < 1 + 2 * r by linarith), abs_of_pos hp6]
    constructor
    · rw [div_le_div_iff_of_pos_right hp6]; linarith
    · rw [div_le_div_iff₀ hp6 (by positivity)]; nlinarith

lemma cantorVal_dist_half_bounds (δ : ℕ → Bool) :
    1 / 6 ≤ |cantorVal δ - 1 / 2| ∧ |cantorVal δ - 1 / 2| ≤ 1 / 2 := by
  rw [cantorVal_split δ 1, Finset.sum_range_one]
  set r := cantorVal (fun j => δ (1 + j))
  have hr0 : 0 ≤ r := cantorVal_nonneg _
  have hr1 : r ≤ 1 := cantorVal_le_one _
  cases h0 : δ 0
  · simp only [cantorTerm, h0, Bool.false_eq_true, ↓reduceIte, zero_div, zero_add, pow_one]
    rw [abs_of_neg (by linarith)]
    constructor <;> linarith
  · simp only [cantorTerm, h0, ↓reduceIte, pow_one]
    rw [abs_of_pos (by linarith)]
    constructor <;> linarith

/-- Explicit `ℓ¹`-diamond bucket-handle embedding `BH → ℝ × ℝ`. -/
def embedBH2 (x : BH) : ℝ × ℝ :=
  let ε := bitsAt 0 x
  let c := cantorVal (cumXor ε)
  if h : ∃ j, ε j = true then
    let k := Nat.find h + 1
    let tk : ℝ := 1 / (2 : ℝ) ^ (k + 1)
    let mk : ℝ := 5 / (2 * (3 : ℝ) ^ k)
    if tk ≤ x.1 0 then
      let s := (x.1 0 - tk) / (1 - tk)
      ((1 - s) * c + s / 2, s * |c - 1 / 2|)
    else
      let s := 1 - x.1 0 / tk
      ((1 - s) * c + s * mk, -(s * |c - mk|))
  else
    (x.1 0 / 2, x.1 0 / 2)

/-- Explicit planar embedding `BH → EuclideanSpace ℝ (Fin 2)`. -/
def embedBH (x : BH) : EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![ (embedBH2 x).1, (embedBH2 x).2 ]

lemma bh_no_half_of_x0_mem_Ioo (x : BH) (hx0 : x.1 0 ∈ Ioo (0 : ℝ) 1) (n : ℕ) :
    x.1 (n + 1) ∈ Ioo (0 : ℝ) 1 ∧ x.1 (n + 1) ≠ 1 / 2 := by
  induction n with
  | zero =>
    have ht := bh_tent x 0
    have hmem := bh_mem_Icc x 1
    have hne0 : x.1 1 ≠ 0 := fun h => by rw [h, tent_zero] at ht; linarith [hx0.1]
    have hne1 : x.1 1 ≠ 1 := fun h => by rw [h, tent_one] at ht; linarith [hx0.1]
    have hneh : x.1 1 ≠ 1 / 2 := fun h => by rw [h, tent_half] at ht; linarith [hx0.2]
    exact ⟨⟨lt_of_le_of_ne hmem.1 (Ne.symm hne0), lt_of_le_of_ne hmem.2 hne1⟩, hneh⟩
  | succ n ih =>
    have ht := bh_tent x (n + 1)
    have hmem := bh_mem_Icc x (n + 2)
    have hne0 : x.1 (n + 2) ≠ 0 := fun h => by rw [h, tent_zero] at ht; linarith [ih.1.1]
    have hne1 : x.1 (n + 2) ≠ 1 := fun h => by rw [h, tent_one] at ht; linarith [ih.1.1]
    have hneh : x.1 (n + 2) ≠ 1 / 2 := fun h => by rw [h, tent_half] at ht; linarith [ih.1.2]
    exact ⟨⟨lt_of_le_of_ne hmem.1 (Ne.symm hne0), lt_of_le_of_ne hmem.2 hne1⟩, hneh⟩

lemma bh_after_one (x : BH) {k : ℕ} (hk : x.1 k = 1) :
    x.1 (k + 1) = 1 / 2 ∧ ∀ j, x.1 (k + j + 2) ∈ Ioo (0 : ℝ) 1 ∧ x.1 (k + j + 2) ≠ 1 / 2 := by
  have h1 : x.1 (k + 1) = 1 / 2 := by
    have ht := bh_tent x k
    rw [hk] at ht
    unfold tent at ht
    have habs : |2 * x.1 (k + 1) - 1| = 0 := by linarith
    rw [abs_eq_zero] at habs
    linarith
  refine ⟨h1, fun j => ?_⟩
  induction j with
  | zero =>
    have ht := bh_tent x (k + 1)
    rw [h1] at ht
    have hmem := bh_mem_Icc x (k + 2)
    have hne0 : x.1 (k + 2) ≠ 0 := fun h => by rw [h, tent_zero] at ht; norm_num at ht
    have hne1 : x.1 (k + 2) ≠ 1 := fun h => by rw [h, tent_one] at ht; norm_num at ht
    have hneh : x.1 (k + 2) ≠ 1 / 2 := fun h => by rw [h, tent_half] at ht; norm_num at ht
    exact ⟨⟨lt_of_le_of_ne hmem.1 (Ne.symm hne0), lt_of_le_of_ne hmem.2 hne1⟩, hneh⟩
  | succ j ih =>
    have ht := bh_tent x (k + j + 2)
    have hmem := bh_mem_Icc x (k + (j + 1) + 2)
    rw [show k + (j + 1) + 2 = k + j + 2 + 1 by omega] at hmem ⊢
    have hne0 : x.1 (k + j + 2 + 1) ≠ 0 := fun h => by rw [h, tent_zero] at ht; linarith [ih.1.1]
    have hne1 : x.1 (k + j + 2 + 1) ≠ 1 := fun h => by rw [h, tent_one] at ht; linarith [ih.1.1]
    have hneh : x.1 (k + j + 2 + 1) ≠ 1 / 2 := fun h => by rw [h, tent_half] at ht; linarith [ih.1.2]
    exact ⟨⟨lt_of_le_of_ne hmem.1 (Ne.symm hne0), lt_of_le_of_ne hmem.2 hne1⟩, hneh⟩

lemma bitsAt_zero_eventually_eq {x : BH} {j : ℕ} (hne : x.1 (j + 1) ≠ 1 / 2) :
    ∀ᶠ y : BH in 𝓝 x, bitsAt 0 y j = bitsAt 0 x j := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hopen : IsOpen {y : BH | y.1 (j + 1) < 1 / 2} :=
      isOpen_lt (continuous_bhCoord (j + 1)) continuous_const
    filter_upwards [hopen.mem_nhds hlt] with y hy
    simp only [bitsAt, Nat.zero_add]
    rw [decide_eq_false (by linarith), decide_eq_false (by linarith)]
  · have hopen : IsOpen {y : BH | 1 / 2 < y.1 (j + 1)} :=
      isOpen_lt continuous_const (continuous_bhCoord (j + 1))
    filter_upwards [hopen.mem_nhds hgt] with y hy
    simp only [bitsAt, Nat.zero_add]
    rw [decide_eq_true (by linarith), decide_eq_true (by linarith)]

lemma cantorVal_cumXor_half_formula (w : BH) :
    |cantorVal (cumXor (bitsAt 0 w)) - 1 / 2| =
      1 / 2 - cantorVal (cumXor (fun i => bitsAt 0 w (i + 1))) / 3 := by
  have hcum : ∀ j, cumXor (bitsAt 0 w) (j + 1) =
      xor (bitsAt 0 w 0) (cumXor (fun i => bitsAt 0 w (i + 1)) j) := by
    intro j
    induction j with
    | zero => simp [cumXor]
    | succ j ih =>
      conv_lhs => rw [cumXor]
      rw [ih, cumXor]
      cases bitsAt 0 w 0 <;> cases cumXor (fun i => bitsAt 0 w (i + 1)) j <;>
        cases bitsAt 0 w (j + 2) <;> rfl
  rw [cantorVal_split (cumXor (bitsAt 0 w)) 1, Finset.sum_range_one]
  have htail : (fun j => cumXor (bitsAt 0 w) (1 + j)) =
      if bitsAt 0 w 0 then fun j => !(cumXor (fun i => bitsAt 0 w (i + 1)) j)
      else cumXor (fun i => bitsAt 0 w (i + 1)) := by
    funext j
    rw [Nat.add_comm, hcum j]
    cases bitsAt 0 w 0 <;> simp
  rw [htail]
  have hc0 := cantorVal_nonneg (cumXor (fun i => bitsAt 0 w (i + 1)))
  have hc1 := cantorVal_le_one (cumXor (fun i => bitsAt 0 w (i + 1)))
  cases hw0 : bitsAt 0 w 0
  · simp only [cantorTerm, cumXor, hw0, Bool.false_eq_true, ↓reduceIte, zero_div, zero_add, pow_one]
    rw [abs_of_neg (by linarith)]; ring
  · simp only [cantorTerm, cumXor, hw0, ↓reduceIte, pow_one]
    rw [cantorVal_compl, abs_of_pos (by linarith)]; ring

lemma embedBH2_upper_bound_near_one (z : BH) (hz0 : 1 / 2 < z.1 0) :
    |(embedBH2 z).1 - 1 / 2| ≤ 1 - z.1 0 ∧
      |(embedBH2 z).2 - (|cantorVal (cumXor (bitsAt 0 z)) - 1 / 2|)| ≤ 1 - z.1 0 := by
  have hzle := (bh_mem_Icc z 0).2
  by_cases h1 : ∃ j, bitsAt 0 z j = true
  · set k := Nat.find h1 + 1
    set tk : ℝ := 1 / (2 : ℝ) ^ (k + 1)
    have htk_le : tk ≤ 1 / 4 := by
      have h4 : (4 : ℝ) ≤ (2 : ℝ) ^ (k + 1) :=
        calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
          _ ≤ (2 : ℝ) ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have h2 : tk ≤ z.1 0 := by linarith
    have hemb : embedBH2 z =
        let s := (z.1 0 - tk) / (1 - tk)
        ((1 - s) * cantorVal (cumXor (bitsAt 0 z)) + s / 2,
          s * |cantorVal (cumXor (bitsAt 0 z)) - 1 / 2|) := by
      dsimp only [embedBH2]; rw [dif_pos h1, if_pos h2]
    rw [hemb]
    set s := (z.1 0 - tk) / (1 - tk)
    have h1s : 1 - s = (1 - z.1 0) / (1 - tk) := by
      have : (1 : ℝ) - tk ≠ 0 := by linarith
      dsimp only [s]; field_simp; ring
    have h1s_nonneg : 0 ≤ 1 - s := by rw [h1s]; exact div_nonneg (by linarith) (by linarith)
    have h1s_le : 1 - s ≤ 2 * (1 - z.1 0) := by
      rw [h1s, div_le_iff₀ (by linarith)]; nlinarith
    have hc := cantorVal_dist_half_bounds (cumXor (bitsAt 0 z))
    constructor
    · have : (1 - s) * cantorVal (cumXor (bitsAt 0 z)) + s / 2 - 1 / 2 =
          (1 - s) * (cantorVal (cumXor (bitsAt 0 z)) - 1 / 2) := by ring
      dsimp only
      rw [this, abs_mul, abs_of_nonneg h1s_nonneg]
      nlinarith [hc.2]
    · have : s * |cantorVal (cumXor (bitsAt 0 z)) - 1 / 2| -
          |cantorVal (cumXor (bitsAt 0 z)) - 1 / 2| =
          -(1 - s) * |cantorVal (cumXor (bitsAt 0 z)) - 1 / 2| := by ring
      dsimp only
      rw [this, abs_mul, abs_neg, abs_of_nonneg h1s_nonneg, abs_abs]
      nlinarith [hc.2]
  · have hemb : embedBH2 z = (z.1 0 / 2, z.1 0 / 2) := by
      dsimp only [embedBH2]; rw [dif_neg h1]
    rw [hemb]
    push Not at h1
    have hcz : cantorVal (cumXor (bitsAt 0 z)) = 0 := by
      rw [cantorVal_eq_zero_iff]
      intro j
      exact cumXor_zero_prefix (bitsAt 0 z) (fun i _ => by cases h : bitsAt 0 z i <;> simp_all) j
        (Nat.lt_succ_self j)
    rw [hcz]
    have hrew : z.1 0 / 2 - 1 / 2 = -(1 - z.1 0) / 2 := by ring
    dsimp only
    constructor
    · rw [hrew, abs_div, abs_neg, abs_of_nonneg (by linarith), abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    · norm_num
      rw [hrew, abs_div, abs_neg, abs_of_nonneg (by linarith), abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith

lemma continuousAt_embedBH2_of_x0_eq_one {x : BH} (hx1 : x.1 0 = 1) :
    ContinuousAt embedBH2 x := by
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro δ hδ
  have hafter := bh_after_one x hx1
  obtain ⟨M, hM⟩ : ∃ M : ℕ, 1 / (3 : ℝ) ^ (M + 1) < δ / 4 := by
    obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < δ / 4 by positivity)
      (show (1 / 3 : ℝ) < 1 by norm_num)
    refine ⟨M, ?_⟩
    calc 1 / (3 : ℝ) ^ (M + 1) ≤ 1 / (3 : ℝ) ^ M := by gcongr; norm_num; omega
      _ < δ / 4 := by simpa [one_div_pow, one_div] using hM
  have hbits : ∀ᶠ y : BH in 𝓝 x, ∀ j < M, bitsAt 0 y (j + 1) = bitsAt 0 x (j + 1) := by
    have hfin : ∀ j ∈ Finset.range M, ∀ᶠ y : BH in 𝓝 x, bitsAt 0 y (j + 1) = bitsAt 0 x (j + 1) :=
      fun j _ => bitsAt_zero_eventually_eq (by simpa [Nat.add_assoc] using (hafter.2 j).2)
    filter_upwards [(Filter.eventually_all_finset _).mpr hfin] with y hy j hj
    exact hy j (Finset.mem_range.mpr hj)
  have hclose0 : ∀ᶠ y : BH in 𝓝 x, 1 - min (1 / 4) (δ / 8) < y.1 0 := by
    apply (isOpen_lt continuous_const (continuous_bhCoord 0)).mem_nhds
    show 1 - min (1 / 4 : ℝ) (δ / 8) < x.1 0
    have : 0 < min (1 / 4 : ℝ) (δ / 8) := lt_min (by norm_num) (by positivity)
    linarith
  filter_upwards [hbits, hclose0] with y hybits hy0
  have hux := embedBH2_upper_bound_near_one x (by linarith)
  have huy := embedBH2_upper_bound_near_one y (by linarith [min_le_left (1 / 4 : ℝ) (δ / 8)])
  have h1y : 1 - y.1 0 < δ / 8 := by linarith [min_le_right (1 / 4 : ℝ) (δ / 8)]
  have h1x : 1 - x.1 0 = 0 := by linarith
  have hd1 : |(embedBH2 y).1 - (embedBH2 x).1| < δ := by
    have htri := abs_sub_le (embedBH2 y).1 (1 / 2) (embedBH2 x).1
    rw [abs_sub_comm (1 / 2)] at htri
    linarith [huy.1, hux.1]
  have hagree : ∀ j < M,
      cumXor (fun i => bitsAt 0 y (i + 1)) j = cumXor (fun i => bitsAt 0 x (i + 1)) j := by
    intro j hj
    induction j with
    | zero => simpa [cumXor] using hybits 0 hj
    | succ j ih => simp [cumXor, ih (by omega), hybits (j + 1) hj]
  have habs : |(|cantorVal (cumXor (bitsAt 0 y)) - 1 / 2| -
      |cantorVal (cumXor (bitsAt 0 x)) - 1 / 2|)| ≤ 1 / (3 : ℝ) ^ (M + 1) := by
    rw [cantorVal_cumXor_half_formula y, cantorVal_cumXor_half_formula x]
    rw [show 1 / 2 - cantorVal (cumXor (fun i => bitsAt 0 y (i + 1))) / 3 -
        (1 / 2 - cantorVal (cumXor (fun i => bitsAt 0 x (i + 1))) / 3) =
        -(cantorVal (cumXor (fun i => bitsAt 0 y (i + 1))) -
          cantorVal (cumXor (fun i => bitsAt 0 x (i + 1)))) / 3 by ring]
    rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    calc
      |cantorVal (cumXor (fun i => bitsAt 0 y (i + 1))) -
          cantorVal (cumXor (fun i => bitsAt 0 x (i + 1)))| / 3
        ≤ (1 / (3 : ℝ) ^ M) / 3 := by gcongr; exact cantorVal_dist_le hagree
      _ = 1 / (3 : ℝ) ^ (M + 1) := by rw [pow_succ]; ring
  have hd2 : |(embedBH2 y).2 - (embedBH2 x).2| < δ := by
    have htri1 := abs_sub_le (embedBH2 y).2 |cantorVal (cumXor (bitsAt 0 y)) - 1 / 2| (embedBH2 x).2
    have htri2 := abs_sub_le |cantorVal (cumXor (bitsAt 0 y)) - 1 / 2|
      |cantorVal (cumXor (bitsAt 0 x)) - 1 / 2| (embedBH2 x).2
    rw [abs_sub_comm |cantorVal (cumXor (bitsAt 0 x)) - 1 / 2|] at htri2
    linarith [huy.2, hux.2, habs]
  exact max_lt hd1 hd2

lemma continuousAt_embedBH2_bhZero : ContinuousAt embedBH2 bhZero := by
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro δ hδ
  have hembed0 : embedBH2 bhZero = (0, 0) := by
    have hno : ¬ ∃ j, bitsAt 0 bhZero j = true := by
      rintro ⟨j, hj⟩; simp [bitsAt, bhZero] at hj; norm_num at hj
    dsimp only [embedBH2]; rw [dif_neg hno]; simp [bhZero]
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 4 / (3 : ℝ) ^ N < δ / 2 := by
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < δ / 8 by positivity)
      (show (1 / 3 : ℝ) < 1 by norm_num)
    refine ⟨N, ?_⟩
    rw [one_div_pow] at hN
    have h4eq : 4 / (3 : ℝ) ^ N = 4 * (1 / (3 : ℝ) ^ N) := by ring
    linarith
  have h0 : ∀ᶠ y : BH in 𝓝 bhZero, y.1 0 < δ / 4 :=
    (isOpen_lt (continuous_bhCoord 0) continuous_const).mem_nhds (by simp [bhZero]; positivity)
  have hfin : ∀ j ∈ Finset.range N, ∀ᶠ y : BH in 𝓝 bhZero, y.1 (j + 1) < 1 / 2 := fun j _ =>
    (isOpen_lt (continuous_bhCoord (j + 1)) continuous_const).mem_nhds (by simp [bhZero])
  filter_upwards [h0, (Filter.eventually_all_finset _).mpr hfin] with y hy0 hyj
  rw [hembed0]
  have hbits0 : ∀ j < N, bitsAt 0 y j = false := fun j hj => by
    simp only [bitsAt, Nat.zero_add]
    rw [decide_eq_false_iff_not]; linarith [hyj j (Finset.mem_range.mpr hj)]
  have hc_le : cantorVal (cumXor (bitsAt 0 y)) ≤ 1 / (3 : ℝ) ^ N := by
    have h0c := cumXor_zero_prefix _ hbits0
    have hcz : cantorVal (fun _ => false) = 0 := (cantorVal_eq_zero_iff _).mpr fun _ => rfl
    have hd := cantorVal_dist_le (δ₁ := cumXor (bitsAt 0 y)) (δ₂ := fun _ => false) h0c
    rwa [hcz, sub_zero, abs_of_nonneg (cantorVal_nonneg _)] at hd
  have hy0_nn : 0 ≤ y.1 0 := (bh_mem_Icc y 0).1
  have hc_nn : 0 ≤ cantorVal (cumXor (bitsAt 0 y)) := cantorVal_nonneg _
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ N := by positivity
  by_cases h1 : ∃ j, bitsAt 0 y j = true
  · set j0 := Nat.find h1
    set k := j0 + 1
    set tk : ℝ := 1 / (2 : ℝ) ^ (k + 1)
    set mk : ℝ := 5 / (2 * (3 : ℝ) ^ k)
    by_cases h2 : tk ≤ y.1 0
    · have hemb : embedBH2 y =
          let s := (y.1 0 - tk) / (1 - tk)
          ((1 - s) * cantorVal (cumXor (bitsAt 0 y)) + s / 2,
            s * |cantorVal (cumXor (bitsAt 0 y)) - 1 / 2|) := by
        dsimp only [embedBH2]; rw [dif_pos h1, if_pos h2]
      rw [hemb]
      have htk_le : tk ≤ 1 / 4 := by
        have h4 : (4 : ℝ) ≤ (2 : ℝ) ^ (k + 1) :=
          calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
            _ ≤ (2 : ℝ) ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      set s := (y.1 0 - tk) / (1 - tk)
      have hs_nn : 0 ≤ s := div_nonneg (by linarith) (by linarith)
      have hs_le : s ≤ 2 * y.1 0 := by rw [div_le_iff₀ (by linarith)]; nlinarith [show (0 : ℝ) ≤ tk by positivity]
      have hs_le1 : s ≤ 1 := (div_le_one (by linarith)).mpr (by linarith [(bh_mem_Icc y 0).2])
      have hd1 : |(1 - s) * cantorVal (cumXor (bitsAt 0 y)) + s / 2 - 0| < δ := by
        rw [sub_zero, abs_of_nonneg (by nlinarith)]
        have : 1 / (3 : ℝ) ^ N ≤ 4 / (3 : ℝ) ^ N := by gcongr; norm_num
        nlinarith
      have hd2 : |s * |cantorVal (cumXor (bitsAt 0 y)) - 1 / 2| - 0| < δ := by
        rw [sub_zero, abs_of_nonneg (by positivity)]
        nlinarith [(cantorVal_dist_half_bounds (cumXor (bitsAt 0 y))).2]
      exact max_lt hd1 hd2
    · have hemb : embedBH2 y =
          let s := 1 - y.1 0 / tk
          ((1 - s) * cantorVal (cumXor (bitsAt 0 y)) + s * mk,
            -(s * |cantorVal (cumXor (bitsAt 0 y)) - mk|)) := by
        dsimp only [embedBH2]; rw [dif_pos h1, if_neg h2]
      rw [hemb]
      have hj0_ge : N ≤ j0 := by
        by_contra hlt; push Not at hlt
        exact Bool.false_ne_true ((hbits0 j0 hlt).symm.trans (Nat.find_spec h1))
      set s := 1 - y.1 0 / tk
      have hs_nn : 0 ≤ s := by
        have : y.1 0 / tk ≤ 1 := (div_le_one (by positivity)).mpr (le_of_lt (not_le.mp h2))
        linarith
      have hs_le1 : s ≤ 1 := by
        have : 0 ≤ y.1 0 / tk := div_nonneg hy0_nn (by positivity)
        linarith
      have h3k : (3 : ℝ) ^ N ≤ (3 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
      have hmk_le : mk ≤ 3 / (3 : ℝ) ^ N := by
        calc mk = 5 / (2 * (3 : ℝ) ^ k) := rfl
          _ ≤ 5 / (2 * (3 : ℝ) ^ N) := by gcongr
          _ ≤ 3 / (3 : ℝ) ^ N := by rw [div_le_div_iff₀ (by positivity) h3pos]; nlinarith
      have hd1 : |(1 - s) * cantorVal (cumXor (bitsAt 0 y)) + s * mk - 0| < δ := by
        rw [sub_zero, abs_of_nonneg (by positivity)]
        have : 1 / (3 : ℝ) ^ N + 3 / (3 : ℝ) ^ N = 4 / (3 : ℝ) ^ N := by ring
        nlinarith [show (0 : ℝ) ≤ mk by positivity]
      have hd2 : |-(s * |cantorVal (cumXor (bitsAt 0 y)) - mk|) - 0| < δ := by
        rw [sub_zero, abs_neg, abs_of_nonneg (by positivity)]
        have hcm : |cantorVal (cumXor (bitsAt 0 y)) - mk| ≤ 4 / (3 : ℝ) ^ N := by
          have h34 : 3 / (3 : ℝ) ^ N ≤ 4 / (3 : ℝ) ^ N := by gcongr; norm_num
          have h14 : 1 / (3 : ℝ) ^ N ≤ 4 / (3 : ℝ) ^ N := by gcongr; norm_num
          rw [abs_le]; constructor <;> linarith [show (0 : ℝ) ≤ mk by positivity]
        nlinarith
      exact max_lt hd1 hd2
  · have hemb : embedBH2 y = (y.1 0 / 2, y.1 0 / 2) := by
      dsimp only [embedBH2]; rw [dif_neg h1]
    rw [hemb]
    have hd1 : |y.1 0 / 2 - 0| < δ := by rw [sub_zero, abs_of_nonneg (by linarith)]; linarith
    exact max_lt hd1 hd1

lemma cantorVal_cumXor_mid_formula (k : ℕ) (hk : 0 < k) (w : BH)
    (hw0 : ∀ j < k - 1, bitsAt 0 w j = false) (hw1 : bitsAt 0 w (k - 1) = true) :
    |cantorVal (cumXor (bitsAt 0 w)) - 5 / (2 * (3 : ℝ) ^ k)| =
      1 / (2 * (3 : ℝ) ^ k) -
        cantorVal (cumXor (fun j => bitsAt 0 w (k + 1 + j))) / (3 : ℝ) ^ (k + 1) := by
  have hcum_lt := cumXor_zero_prefix _ hw0
  have hcum_k1 := cumXor_first_true _ hw0 hw1
  have hcum_k : cumXor (bitsAt 0 w) k = !(bitsAt 0 w k) := by
    have hk_eq : k = (k - 1) + 1 := by omega
    conv_lhs => rw [hk_eq]
    simp [cumXor, hcum_k1, ← hk_eq]
  have hcum_tail : ∀ j, cumXor (bitsAt 0 w) (k + 1 + j) =
      xor (!(bitsAt 0 w k)) (cumXor (fun i => bitsAt 0 w (k + 1 + i)) j) := by
    intro j
    induction j with
    | zero => rw [show k + 1 + 0 = k + 1 by omega]; simp only [cumXor, hcum_k]
    | succ j ih =>
      rw [show k + 1 + (j + 1) = (k + 1 + j) + 1 by omega]
      simp only [cumXor, ih]
      cases bitsAt 0 w k <;> cases cumXor (fun i => bitsAt 0 w (k + 1 + i)) j <;>
        cases bitsAt 0 w (k + 1 + (j + 1)) <;> rfl
  rw [cantorVal_split (cumXor (bitsAt 0 w)) (k + 1), Finset.sum_range_succ,
    show k = (k - 1) + 1 by omega, Finset.sum_range_succ]
  have hsum0 : ∑ j ∈ Finset.range (k - 1), cantorTerm (cumXor (bitsAt 0 w)) j = 0 :=
    Finset.sum_eq_zero fun j hj => by simp [cantorTerm, hcum_lt j (Finset.mem_range.mp hj)]
  rw [hsum0, zero_add]
  have ht1 : cantorTerm (cumXor (bitsAt 0 w)) (k - 1) = 2 / (3 : ℝ) ^ k := by
    simp [cantorTerm, hcum_k1, show k - 1 + 1 = k by omega]
  rw [ht1]
  have htail_fn : (fun j => cumXor (bitsAt 0 w) (k - 1 + 1 + 1 + j)) =
      if bitsAt 0 w k then cumXor (fun i => bitsAt 0 w (k + 1 + i))
      else fun j => !(cumXor (fun i => bitsAt 0 w (k + 1 + i)) j) := by
    funext j
    rw [show k - 1 + 1 + 1 + j = k + 1 + j by omega, hcum_tail j]
    cases bitsAt 0 w k <;> simp
  rw [htail_fn]
  have hpow1 : (3 : ℝ) ^ (k - 1 + 1 + 1) = 3 * (3 : ℝ) ^ k := by
    rw [show k - 1 + 1 + 1 = k + 1 by omega, pow_succ]; ring
  have hpow2 : (3 : ℝ) ^ (k + 1) = 3 * (3 : ℝ) ^ k := by rw [pow_succ]; ring
  set r := cantorVal (cumXor (fun i => bitsAt 0 w (k + 1 + i)))
  have hr0 : 0 ≤ r := cantorVal_nonneg _
  have hr1 : r ≤ 1 := cantorVal_le_one _
  have h3p : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  have h6p : (0 : ℝ) < 6 * (3 : ℝ) ^ k := by positivity
  cases hwk : bitsAt 0 w k
  · have ht2 : cantorTerm (cumXor (bitsAt 0 w)) k = 2 / (3 * (3 : ℝ) ^ k) := by
      simp [cantorTerm, hcum_k, hwk, hpow2]
    simp only [Bool.false_eq_true, ↓reduceIte, cantorVal_compl, show k - 1 + 1 = k by omega,
      hpow2, ht2]
    have hdiff : 2 / (3 : ℝ) ^ k + 2 / (3 * (3 : ℝ) ^ k) + (1 - r) / (3 * (3 : ℝ) ^ k) -
        5 / (2 * (3 : ℝ) ^ k) = (3 - 2 * r) / (6 * (3 : ℝ) ^ k) := by field_simp; ring
    rw [show 2 / (3 : ℝ) ^ k + 2 / (3 * (3 : ℝ) ^ k) + (1 - r) / (3 * (3 : ℝ) ^ k) -
        5 / (2 * (3 : ℝ) ^ k) = (3 - 2 * r) / (6 * (3 : ℝ) ^ k) from hdiff,
      abs_div, abs_of_pos (show 0 < 3 - 2 * r by linarith), abs_of_pos h6p]
    field_simp; ring
  · have ht2 : cantorTerm (cumXor (bitsAt 0 w)) k = 0 := by
      simp [cantorTerm, hcum_k, hwk]
    simp only [↓reduceIte, show k - 1 + 1 = k by omega, hpow2, ht2, add_zero]
    have hdiff : 2 / (3 : ℝ) ^ k + r / (3 * (3 : ℝ) ^ k) - 5 / (2 * (3 : ℝ) ^ k) =
        -(3 - 2 * r) / (6 * (3 : ℝ) ^ k) := by field_simp; ring
    rw [show 2 / (3 : ℝ) ^ k + r / (3 * (3 : ℝ) ^ k) - 5 / (2 * (3 : ℝ) ^ k) =
        -(3 - 2 * r) / (6 * (3 : ℝ) ^ k) from hdiff,
      abs_div, abs_neg, abs_of_pos (show 0 < 3 - 2 * r by linarith), abs_of_pos h6p]
    field_simp; ring

lemma continuousAt_embedBH2_of_x0_eq_zero_ne {x : BH} (hx0 : x.1 0 = 0) (hne : x ≠ bhZero) :
    ContinuousAt embedBH2 x := by
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro δ hδ
  have hall0 : ∃ n, x.1 n ≠ 0 := by
    by_contra h; push Not at h; exact hne (Subtype.ext (funext h))
  let k := Nat.find hall0
  have hk_ne : x.1 k ≠ 0 := Nat.find_spec hall0
  have hk_pos : 0 < k := Nat.pos_of_ne_zero fun h0 => hk_ne (by rwa [h0])
  have hk_lt : ∀ m < k, x.1 m = 0 := fun m hm => by
    by_contra h; exact Nat.find_min hall0 hm h
  have hxk1 : x.1 k = 1 := by
    have ht := bh_tent x (k - 1)
    rw [show k - 1 + 1 = k by omega, hk_lt (k - 1) (by omega)] at ht
    rcases le_total (x.1 k) (1 / 2) with h | h
    · rw [tent_eq_two_mul h] at ht; exfalso; exact hk_ne (by linarith)
    · rw [tent_eq_two_sub h] at ht; linarith
  have hafter := bh_after_one x hxk1
  obtain ⟨M, hM⟩ : ∃ M : ℕ, 1 / (3 : ℝ) ^ (k + M) < δ / 4 := by
    obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < δ / 4 by positivity)
      (show (1 / 3 : ℝ) < 1 by norm_num)
    refine ⟨M, ?_⟩
    calc 1 / (3 : ℝ) ^ (k + M) ≤ 1 / (3 : ℝ) ^ M := by gcongr; norm_num; omega
      _ < δ / 4 := by simpa [one_div_pow, one_div] using hM
  set tk : ℝ := 1 / (2 : ℝ) ^ (k + 1)
  set mk : ℝ := 5 / (2 * (3 : ℝ) ^ k)
  have htk_pos : 0 < tk := by positivity
  have hlt_bits : ∀ j ∈ Finset.range (k - 1), ∀ᶠ y : BH in 𝓝 x, bitsAt 0 y j = false := by
    intro j hj
    have hne' : x.1 (j + 1) ≠ 1 / 2 := by rw [hk_lt (j + 1) (by simp at hj; omega)]; norm_num
    filter_upwards [bitsAt_zero_eventually_eq hne'] with y hy
    rw [hy]; simp only [bitsAt, Nat.zero_add]
    rw [decide_eq_false_iff_not, hk_lt (j + 1) (by simp at hj; omega)]; norm_num
  have hkt : ∀ᶠ y : BH in 𝓝 x, bitsAt 0 y (k - 1) = true := by
    have hne' : x.1 (k - 1 + 1) ≠ 1 / 2 := by rw [show k - 1 + 1 = k by omega, hxk1]; norm_num
    filter_upwards [bitsAt_zero_eventually_eq hne'] with y hy
    rw [hy]; simp only [bitsAt, Nat.zero_add]
    rw [decide_eq_true_eq, show k - 1 + 1 = k by omega, hxk1]; norm_num
  have htail : ∀ j ∈ Finset.range M,
      ∀ᶠ y : BH in 𝓝 x, bitsAt 0 y (k + 1 + j) = bitsAt 0 x (k + 1 + j) := fun j _ =>
    bitsAt_zero_eventually_eq (by rw [show k + 1 + j + 1 = k + j + 2 by omega]; exact (hafter.2 j).2)
  have h0 : ∀ᶠ y : BH in 𝓝 x, y.1 0 < min tk (tk * δ / 4) := by
    apply (isOpen_lt (continuous_bhCoord 0) continuous_const).mem_nhds
    show x.1 0 < min tk (tk * δ / 4)
    rw [hx0]; exact lt_min htk_pos (by positivity)
  have hlower_form : ∀ w : BH,
      (∀ j < k - 1, bitsAt 0 w j = false) → bitsAt 0 w (k - 1) = true → w.1 0 < tk →
      embedBH2 w =
        ((w.1 0 / tk) * cantorVal (cumXor (bitsAt 0 w)) + (1 - w.1 0 / tk) * mk,
          -((1 - w.1 0 / tk) * |cantorVal (cumXor (bitsAt 0 w)) - mk|)) := by
    intro w hw0 hw1 hwlt
    have hex : ∃ j, bitsAt 0 w j = true := ⟨k - 1, hw1⟩
    have hfind : Nat.find hex = k - 1 := by
      apply le_antisymm (Nat.find_min' hex hw1)
      by_contra hlt; push Not at hlt
      exact Bool.false_ne_true ((hw0 _ hlt).symm.trans (Nat.find_spec hex))
    dsimp only [embedBH2]
    rw [dif_pos hex]
    simp only [hfind, show k - 1 + 1 = k by omega]
    rw [if_neg (not_le.mpr hwlt)]
    exact Prod.ext (by ring) rfl
  have hx0_lt : ∀ j < k - 1, bitsAt 0 x j = false := fun j hj => by
    simp only [bitsAt, Nat.zero_add]; rw [decide_eq_false_iff_not, hk_lt (j + 1) (by omega)]; norm_num
  have hx0_t : bitsAt 0 x (k - 1) = true := by
    simp only [bitsAt, Nat.zero_add]; rw [decide_eq_true_eq, show k - 1 + 1 = k by omega, hxk1]; norm_num
  have hnhds : ∀ᶠ y : BH in 𝓝 x, dist (embedBH2 y) (embedBH2 x) < δ := by
    filter_upwards [(Filter.eventually_all_finset _).mpr hlt_bits, hkt,
      (Filter.eventually_all_finset _).mpr htail, h0] with y hy0' hy1 hytail' hylt
    have hy0 : ∀ j < k - 1, bitsAt 0 y j = false := fun j hj => hy0' j (Finset.mem_range.mpr hj)
    have hytail : ∀ j < M, bitsAt 0 y (k + 1 + j) = bitsAt 0 x (k + 1 + j) :=
      fun j hj => hytail' j (Finset.mem_range.mpr hj)
    have hylt_tk : y.1 0 < tk := lt_of_lt_of_le hylt (min_le_left _ _)
    have hylt_d : y.1 0 < tk * δ / 4 := lt_of_lt_of_le hylt (min_le_right _ _)
    rw [hlower_form y hy0 hy1 hylt_tk, hlower_form x hx0_lt hx0_t (by rw [hx0]; exact htk_pos)]
    simp only [hx0, zero_div, zero_mul, sub_zero, zero_add, one_mul]
    have hcm_bound : |cantorVal (cumXor (bitsAt 0 y)) - mk| ≤ 1 := by
      have h1 := cantorVal_nonneg (cumXor (bitsAt 0 y))
      have h2 := cantorVal_le_one (cumXor (bitsAt 0 y))
      have h3 : (0 : ℝ) ≤ mk := by positivity
      have h4 : mk ≤ 5 / 6 := by
        unfold mk
        have h3k : (3 : ℝ) ≤ (3 : ℝ) ^ k :=
          calc (3 : ℝ) = (3 : ℝ) ^ 1 := by norm_num
            _ ≤ (3 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      rw [abs_le]; constructor <;> linarith
    have hy0_nn : 0 ≤ y.1 0 := (bh_mem_Icc y 0).1
    have hdiv_lt : y.1 0 / tk < δ / 4 := (div_lt_iff₀ htk_pos).mpr (by linarith)
    have hmul_le : (y.1 0 / tk) * |cantorVal (cumXor (bitsAt 0 y)) - mk| ≤ y.1 0 / tk :=
      mul_le_of_le_one_right (div_nonneg hy0_nn (le_of_lt htk_pos)) hcm_bound
    have hd1 : |(y.1 0 / tk) * cantorVal (cumXor (bitsAt 0 y)) + (1 - y.1 0 / tk) * mk - mk| < δ := by
      rw [show (y.1 0 / tk) * cantorVal (cumXor (bitsAt 0 y)) + (1 - y.1 0 / tk) * mk - mk =
        (y.1 0 / tk) * (cantorVal (cumXor (bitsAt 0 y)) - mk) by ring,
        abs_mul, abs_of_nonneg (div_nonneg hy0_nn (le_of_lt htk_pos))]
      linarith
    have hagree : ∀ j < M,
        cumXor (fun i => bitsAt 0 y (k + 1 + i)) j = cumXor (fun i => bitsAt 0 x (k + 1 + i)) j := by
      intro j hj
      induction j with
      | zero => simpa [cumXor] using hytail 0 hj
      | succ j ih => simp [cumXor, ih (by omega), hytail (j + 1) hj]
    have hrad_diff : |(|cantorVal (cumXor (bitsAt 0 y)) - mk| -
        |cantorVal (cumXor (bitsAt 0 x)) - mk|)| ≤ 1 / (3 : ℝ) ^ (k + M) := by
      rw [cantorVal_cumXor_mid_formula k hk_pos y hy0 hy1,
        cantorVal_cumXor_mid_formula k hk_pos x hx0_lt hx0_t]
      rw [show 1 / (2 * (3 : ℝ) ^ k) -
          cantorVal (cumXor (fun j => bitsAt 0 y (k + 1 + j))) / (3 : ℝ) ^ (k + 1) -
          (1 / (2 * (3 : ℝ) ^ k) -
          cantorVal (cumXor (fun j => bitsAt 0 x (k + 1 + j))) / (3 : ℝ) ^ (k + 1)) =
          -(cantorVal (cumXor (fun j => bitsAt 0 y (k + 1 + j))) -
            cantorVal (cumXor (fun j => bitsAt 0 x (k + 1 + j)))) / (3 : ℝ) ^ (k + 1) by ring]
      rw [abs_div, abs_neg, abs_of_pos (show (0 : ℝ) < (3 : ℝ) ^ (k + 1) by positivity)]
      calc
        |cantorVal (cumXor (fun j => bitsAt 0 y (k + 1 + j))) -
            cantorVal (cumXor (fun j => bitsAt 0 x (k + 1 + j)))| / (3 : ℝ) ^ (k + 1)
          ≤ (1 / (3 : ℝ) ^ M) / (3 : ℝ) ^ (k + 1) := by gcongr; exact cantorVal_dist_le hagree
        _ ≤ 1 / (3 : ℝ) ^ (k + M) := by
          rw [div_div, ← pow_add]
          exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
    have hd2 : |-((1 - y.1 0 / tk) * |cantorVal (cumXor (bitsAt 0 y)) - mk|) -
        (-(|cantorVal (cumXor (bitsAt 0 x)) - mk|))| < δ := by
      have hrew : -((1 - y.1 0 / tk) * |cantorVal (cumXor (bitsAt 0 y)) - mk|) -
          (-(|cantorVal (cumXor (bitsAt 0 x)) - mk|)) =
          (y.1 0 / tk) * |cantorVal (cumXor (bitsAt 0 y)) - mk| -
          (|cantorVal (cumXor (bitsAt 0 y)) - mk| - |cantorVal (cumXor (bitsAt 0 x)) - mk|) := by
        ring
      rw [hrew]
      calc |(y.1 0 / tk) * |cantorVal (cumXor (bitsAt 0 y)) - mk| -
            (|cantorVal (cumXor (bitsAt 0 y)) - mk| - |cantorVal (cumXor (bitsAt 0 x)) - mk|)|
        ≤ |(y.1 0 / tk) * (|cantorVal (cumXor (bitsAt 0 y)) - mk|)| +
          |(|cantorVal (cumXor (bitsAt 0 y)) - mk| - |cantorVal (cumXor (bitsAt 0 x)) - mk|)| :=
            abs_sub _ _
        _ = (y.1 0 / tk) * |cantorVal (cumXor (bitsAt 0 y)) - mk| +
            |(|cantorVal (cumXor (bitsAt 0 y)) - mk| - |cantorVal (cumXor (bitsAt 0 x)) - mk|)| := by
            rw [abs_mul, abs_of_nonneg (div_nonneg hy0_nn (le_of_lt htk_pos)), abs_abs]
        _ < δ := by linarith
    exact max_lt hd1 hd2
  exact hnhds

lemma continuousAt_embedBH2_of_x0_mem_Ioo {x : BH} (hx0 : x.1 0 ∈ Ioo (0 : ℝ) 1) :
    ContinuousAt embedBH2 x := by
  have hnohalf := bh_no_half_of_x0_mem_Ioo x hx0
  by_cases hex : ∃ j, bitsAt 0 x j = true
  · let j0 := Nat.find hex
    have hj0_t : bitsAt 0 x j0 = true := Nat.find_spec hex
    have hj0_f : ∀ j < j0, bitsAt 0 x j = false := fun j hj => by
      by_contra h; exact Nat.find_min hex hj (by cases hj' : bitsAt 0 x j <;> simp_all)
    set k := j0 + 1
    set tk : ℝ := 1 / (2 : ℝ) ^ (k + 1)
    set mk : ℝ := 5 / (2 * (3 : ℝ) ^ k)
    have htk_pos : 0 < tk := by positivity
    let F : ℝ × ℝ → ℝ × ℝ := fun p =>
      if tk ≤ p.2 then
        let s := (p.2 - tk) / (1 - tk)
        ((1 - s) * p.1 + s / 2, s * |p.1 - 1 / 2|)
      else
        let s := 1 - p.2 / tk
        ((1 - s) * p.1 + s * mk, -(s * |p.1 - mk|))
    have hF_cont : Continuous F := by
      apply Continuous.if_le _ _ continuous_const continuous_snd
      · intro p hp
        have hpt : p.2 = tk := hp.symm
        simp [hpt, show tk ≠ 0 from ne_of_gt htk_pos]
      · refine Continuous.prodMk ?_ ?_ <;> fun_prop
      · refine Continuous.prodMk ?_ ?_ <;> fun_prop
    have hc_cont : ContinuousAt (fun y : BH => cantorVal (cumXor (bitsAt 0 y))) x := by
      rw [ContinuousAt, Metric.tendsto_nhds]
      intro ε hε
      obtain ⟨M, hM⟩ : ∃ M : ℕ, 1 / (3 : ℝ) ^ M < ε := by
        obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hε (show (1 / 3 : ℝ) < 1 by norm_num)
        exact ⟨M, by simpa [one_div_pow, one_div] using hM⟩
      have hfin : ∀ j ∈ Finset.range M, ∀ᶠ y : BH in 𝓝 x, bitsAt 0 y j = bitsAt 0 x j :=
        fun j _ => bitsAt_zero_eventually_eq (hnohalf j).2
      filter_upwards [(Filter.eventually_all_finset _).mpr hfin] with y hy
      have hagree : ∀ j < M, cumXor (bitsAt 0 y) j = cumXor (bitsAt 0 x) j := by
        intro j hj
        induction j with
        | zero => simpa [cumXor] using hy 0 (Finset.mem_range.mpr hj)
        | succ j ih => simp [cumXor, ih (by omega), hy (j + 1) (Finset.mem_range.mpr hj)]
      exact lt_of_le_of_lt (cantorVal_dist_le hagree) hM
    have hcomp : ContinuousAt (fun y : BH => F (cantorVal (cumXor (bitsAt 0 y)), y.1 0)) x :=
      hF_cont.continuousAt.comp (hc_cont.prodMk (continuous_bhCoord 0).continuousAt)
    have heq_ev : (fun y : BH => embedBH2 y) =ᶠ[𝓝 x]
        (fun y : BH => F (cantorVal (cumXor (bitsAt 0 y)), y.1 0)) := by
      have hfin : ∀ j ∈ Finset.range (j0 + 1), ∀ᶠ y : BH in 𝓝 x, bitsAt 0 y j = bitsAt 0 x j :=
        fun j _ => bitsAt_zero_eventually_eq (hnohalf j).2
      filter_upwards [(Filter.eventually_all_finset _).mpr hfin] with y hy
      have hex_y : ∃ j, bitsAt 0 y j = true :=
        ⟨j0, by rw [hy j0 (Finset.mem_range.mpr (Nat.lt_succ_self j0)), hj0_t]⟩
      have hfind_y : Nat.find hex_y = j0 := by
        apply le_antisymm (Nat.find_min' hex_y
          (by rw [hy j0 (Finset.mem_range.mpr (Nat.lt_succ_self j0)), hj0_t]))
        by_contra hlt; push Not at hlt
        have hspec := Nat.find_spec hex_y
        rw [hy _ (Finset.mem_range.mpr (by omega)), hj0_f _ hlt] at hspec
        exact Bool.false_ne_true hspec
      dsimp only [embedBH2, F, k, tk, mk]
      rw [dif_pos hex_y]
      simp only [hfind_y]
    exact hcomp.congr heq_ev.symm
  · rw [ContinuousAt, Metric.tendsto_nhds]
    intro δ hδ
    push Not at hex
    have hex_f : ∀ j, bitsAt 0 x j = false := fun j => by cases h : bitsAt 0 x j <;> simp_all
    have hx_emb : embedBH2 x = (x.1 0 / 2, x.1 0 / 2) := by
      have hno : ¬ ∃ j, bitsAt 0 x j = true := by push Not; exact hex
      simp [embedBH2, hno]
    obtain ⟨N, hN1, hN2, hN3⟩ :
        ∃ N : ℕ, 1 / (2 : ℝ) ^ (N + 1) < x.1 0 / 2 ∧
          1 / (2 : ℝ) ^ (N + 1) < δ / 8 ∧ 1 / (3 : ℝ) ^ N < δ / 4 := by
      obtain ⟨N₁, h1⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < min (x.1 0 / 2) (δ / 8) by
        exact lt_min (by linarith [hx0.1]) (by positivity)) (show (1 / 2 : ℝ) < 1 by norm_num)
      obtain ⟨N₂, h2⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < δ / 4 by positivity)
        (show (1 / 3 : ℝ) < 1 by norm_num)
      refine ⟨max N₁ N₂, ?_, ?_, ?_⟩
      · have hle : 1 / (2 : ℝ) ^ (max N₁ N₂ + 1) ≤ (1 / 2 : ℝ) ^ N₁ := by
          rw [one_div_pow]; gcongr; norm_num; omega
        exact lt_of_le_of_lt hle (lt_of_lt_of_le h1 (min_le_left _ _))
      · have hle : 1 / (2 : ℝ) ^ (max N₁ N₂ + 1) ≤ (1 / 2 : ℝ) ^ N₁ := by
          rw [one_div_pow]; gcongr; norm_num; omega
        exact lt_of_le_of_lt hle (lt_of_lt_of_le h1 (min_le_right _ _))
      · have hle : 1 / (3 : ℝ) ^ (max N₁ N₂) ≤ (1 / 3 : ℝ) ^ N₂ := by
          rw [one_div_pow]; gcongr; norm_num; omega
        exact lt_of_le_of_lt hle h2
    have hfin : ∀ j ∈ Finset.range N, ∀ᶠ y : BH in 𝓝 x, bitsAt 0 y j = false := fun j _ => by
      filter_upwards [bitsAt_zero_eventually_eq (hnohalf j).2] with y hy
      rw [hy, hex_f j]
    have hclose0 : ∀ᶠ y : BH in 𝓝 x, |y.1 0 - x.1 0| < min (x.1 0 / 2) (δ / 4) := by
      have hc0 : ContinuousAt (fun y : BH => y.1 0) x := (continuous_bhCoord 0).continuousAt
      have ht := (Metric.tendsto_nhds.mp hc0)
        (min (x.1 0 / 2) (δ / 4)) (lt_min (by linarith [hx0.1]) (by positivity))
      simpa [Real.dist_eq] using ht
    filter_upwards [(Filter.eventually_all_finset _).mpr hfin, hclose0] with y hybits hy0
    rw [hx_emb]
    have hy_diff1 : |y.1 0 - x.1 0| < x.1 0 / 2 := lt_of_lt_of_le hy0 (min_le_left _ _)
    have hy_diff2 : |y.1 0 - x.1 0| < δ / 4 := lt_of_lt_of_le hy0 (min_le_right _ _)
    have hy_gt : x.1 0 / 2 < y.1 0 := by linarith [(abs_lt.mp hy_diff1).1]
    have hbits0 : ∀ j < N, bitsAt 0 y j = false := fun j hj => hybits j (Finset.mem_range.mpr hj)
    have hc_le : cantorVal (cumXor (bitsAt 0 y)) ≤ 1 / (3 : ℝ) ^ N := by
      have h0c := cumXor_zero_prefix _ hbits0
      have hcz : cantorVal (fun _ => false) = 0 := (cantorVal_eq_zero_iff _).mpr fun _ => rfl
      have hd := cantorVal_dist_le (δ₁ := cumXor (bitsAt 0 y)) (δ₂ := fun _ => false) h0c
      rwa [hcz, sub_zero, abs_of_nonneg (cantorVal_nonneg _)] at hd
    have hc_nn : 0 ≤ cantorVal (cumXor (bitsAt 0 y)) := cantorVal_nonneg _
    by_cases h1 : ∃ j, bitsAt 0 y j = true
    · set k := Nat.find h1 + 1
      have hk_ge : N + 1 ≤ k := by
        by_contra hlt; push Not at hlt
        exact Bool.false_ne_true ((hbits0 (Nat.find h1) (by omega)).symm.trans (Nat.find_spec h1))
      set tk : ℝ := 1 / (2 : ℝ) ^ (k + 1)
      have htk_nn : 0 ≤ tk := by positivity
      have htk_le : tk ≤ 1 / (2 : ℝ) ^ (N + 1) :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
      have h2 : tk ≤ y.1 0 := by linarith
      have hemb : embedBH2 y =
          let s := (y.1 0 - tk) / (1 - tk)
          ((1 - s) * cantorVal (cumXor (bitsAt 0 y)) + s / 2,
            s * |cantorVal (cumXor (bitsAt 0 y)) - 1 / 2|) := by
        dsimp only [embedBH2]; rw [dif_pos h1, if_pos h2]
      rw [hemb]
      have htk_half : tk ≤ 1 / 4 := by
        have h4 : (4 : ℝ) ≤ (2 : ℝ) ^ (k + 1) :=
          calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
            _ ≤ (2 : ℝ) ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      set s := (y.1 0 - tk) / (1 - tk)
      have hs_nn : 0 ≤ s := div_nonneg (by linarith) (by linarith)
      have hs_le1 : s ≤ 1 := (div_le_one (by linarith)).mpr (by linarith [(bh_mem_Icc y 0).2])
      have hs_diff : |s - y.1 0| ≤ 2 * tk := by
        have : s - y.1 0 = -(tk * (1 - y.1 0)) / (1 - tk) := by
          have : (1 : ℝ) - tk ≠ 0 := by linarith
          dsimp only [s]; field_simp; ring
        rw [this, abs_div, abs_neg, abs_of_nonneg (by nlinarith [(bh_mem_Icc y 0).2]),
          abs_of_pos (show 0 < 1 - tk by linarith), div_le_iff₀ (by linarith)]
        nlinarith [(bh_mem_Icc y 0).1, (bh_mem_Icc y 0).2]
      have hhalf_eq : |cantorVal (cumXor (bitsAt 0 y)) - 1 / 2| =
          1 / 2 - cantorVal (cumXor (bitsAt 0 y)) := by
        have hNpos : 1 ≤ N := by
          by_contra h0; push Not at h0
          have : N = 0 := by omega
          subst this; norm_num at hN1; linarith [hx0.2]
        have h3 : 1 / (3 : ℝ) ^ N ≤ 1 / 3 :=
          one_div_le_one_div_of_le (by norm_num)
            (calc (3 : ℝ) = 3 ^ 1 := by norm_num
              _ ≤ (3 : ℝ) ^ N := pow_le_pow_right₀ (by norm_num) hNpos)
        rw [abs_of_neg (by linarith)]; ring
      have hd1 : |(1 - s) * cantorVal (cumXor (bitsAt 0 y)) + s / 2 - x.1 0 / 2| < δ := by
        have hrew : (1 - s) * cantorVal (cumXor (bitsAt 0 y)) + s / 2 - x.1 0 / 2 =
            (1 - s) * cantorVal (cumXor (bitsAt 0 y)) + (s - y.1 0) / 2 + (y.1 0 - x.1 0) / 2 := by ring
        rw [hrew]
        calc |(1 - s) * cantorVal (cumXor (bitsAt 0 y)) + (s - y.1 0) / 2 + (y.1 0 - x.1 0) / 2|
          ≤ |(1 - s) * cantorVal (cumXor (bitsAt 0 y))| + |(s - y.1 0) / 2| + |(y.1 0 - x.1 0) / 2| :=
            le_trans (abs_add_le _ _) (add_le_add (abs_add_le _ _) le_rfl)
          _ ≤ 1 / (3 : ℝ) ^ N + tk + |y.1 0 - x.1 0| / 2 := by
            rw [abs_of_nonneg (by nlinarith), abs_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
            nlinarith
          _ < δ := by linarith
      have hd2 : |s * |cantorVal (cumXor (bitsAt 0 y)) - 1 / 2| - x.1 0 / 2| < δ := by
        rw [hhalf_eq]
        have hrew : s * (1 / 2 - cantorVal (cumXor (bitsAt 0 y))) - x.1 0 / 2 =
            -(s * cantorVal (cumXor (bitsAt 0 y))) + (s - y.1 0) / 2 + (y.1 0 - x.1 0) / 2 := by ring
        rw [hrew]
        calc |-(s * cantorVal (cumXor (bitsAt 0 y))) + (s - y.1 0) / 2 + (y.1 0 - x.1 0) / 2|
          ≤ |-(s * cantorVal (cumXor (bitsAt 0 y)))| + |(s - y.1 0) / 2| + |(y.1 0 - x.1 0) / 2| :=
            le_trans (abs_add_le _ _) (add_le_add (abs_add_le _ _) le_rfl)
          _ ≤ 1 / (3 : ℝ) ^ N + tk + |y.1 0 - x.1 0| / 2 := by
            rw [abs_neg, abs_of_nonneg (by nlinarith), abs_div, abs_div,
              abs_of_pos (by norm_num : (0 : ℝ) < 2)]
            nlinarith
          _ < δ := by linarith
      exact max_lt hd1 hd2
    · have hemb : embedBH2 y = (y.1 0 / 2, y.1 0 / 2) := by
        dsimp only [embedBH2]; rw [dif_neg h1]
      rw [hemb]
      have hd : |y.1 0 / 2 - x.1 0 / 2| < δ := by
        rw [← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
      exact max_lt hd hd

lemma continuous_embedBH2 : Continuous embedBH2 := by
  rw [continuous_iff_continuousAt]
  intro x
  have hx0_mem := bh_mem_Icc x 0
  by_cases hx1 : x.1 0 = 1
  · exact continuousAt_embedBH2_of_x0_eq_one hx1
  · by_cases hx0 : x.1 0 = 0
    · by_cases hzero : x = bhZero
      · subst hzero; exact continuousAt_embedBH2_bhZero
      · exact continuousAt_embedBH2_of_x0_eq_zero_ne hx0 hzero
    · exact continuousAt_embedBH2_of_x0_mem_Ioo
        ⟨lt_of_le_of_ne hx0_mem.1 (Ne.symm hx0), lt_of_le_of_ne hx0_mem.2 hx1⟩

lemma embedBH2_upper_char (z : BH) (hzpos : 0 < (embedBH2 z).2) :
    let c := cantorVal (cumXor (bitsAt 0 z))
    let R := |c - 1 / 2|
    |(embedBH2 z).1 - 1 / 2| + (embedBH2 z).2 = R ∧
    0 < R ∧
    ((embedBH2 z).1 = 1 / 2 → z.1 0 = 1) ∧
    ((embedBH2 z).1 ≠ 1 / 2 →
      ((embedBH2 z).1 < 1 / 2 ↔ c < 1 / 2) ∧
      (embedBH2 z).2 / R =
        if h : ∃ j, bitsAt 0 z j = true then
          let k := Nat.find h + 1
          let tk : ℝ := 1 / (2 : ℝ) ^ (k + 1)
          (z.1 0 - tk) / (1 - tk)
        else z.1 0) := by
  by_cases h1z : ∃ j, bitsAt 0 z j = true
  · set k := Nat.find h1z + 1
    set tk : ℝ := 1 / (2 : ℝ) ^ (k + 1)
    set mk : ℝ := 5 / (2 * (3 : ℝ) ^ k)
    by_cases h2z : tk ≤ z.1 0
    · have hemb : embedBH2 z =
          let s := (z.1 0 - tk) / (1 - tk)
          ((1 - s) * cantorVal (cumXor (bitsAt 0 z)) + s / 2,
            s * |cantorVal (cumXor (bitsAt 0 z)) - 1 / 2|) := by
        dsimp only [embedBH2]; rw [dif_pos h1z, if_pos h2z]
      rw [hemb] at hzpos ⊢
      have htk_lt1 : tk < 1 := (div_lt_one (by positivity)).mpr (one_lt_pow₀ (by norm_num) (by omega))
      set s := (z.1 0 - tk) / (1 - tk)
      have hs_le1 : s ≤ 1 := (div_le_one (by linarith)).mpr (by linarith [(bh_mem_Icc z 0).2])
      set c := cantorVal (cumXor (bitsAt 0 z))
      have hRpos : 0 < |c - 1 / 2| := lt_of_lt_of_le (by norm_num) (cantorVal_dist_half_bounds _).1
      dsimp only
      refine ⟨?_, hRpos, ?_, ?_⟩
      · have : (1 - s) * c + s / 2 - 1 / 2 = (1 - s) * (c - 1 / 2) := by ring
        rw [this, abs_mul, abs_of_nonneg (by linarith)]; ring
      · intro hhalf
        have : (1 - s) * (c - 1 / 2) = 0 := by linarith
        have h1s0 : 1 - s = 0 := (mul_eq_zero.mp this).resolve_right (abs_pos.mp hRpos)
        have hs1 : s = 1 := by linarith
        have := (div_eq_one_iff_eq (show (1 : ℝ) - tk ≠ 0 by linarith)).mp hs1
        linarith
      · intro hne
        have h1s_pos : 0 < 1 - s := by
          refine lt_of_le_of_ne (by linarith) fun h0 => hne ?_
          have : s = 1 := by linarith
          rw [this]; ring
        refine ⟨?_, ?_⟩
        · have : (1 - s) * c + s / 2 - 1 / 2 = (1 - s) * (c - 1 / 2) := by ring
          constructor <;> intro hlt <;> nlinarith
        · rw [dif_pos h1z]
          exact mul_div_cancel_right₀ s (ne_of_gt hRpos)
    · exfalso
      have hemb : embedBH2 z =
          let s := 1 - z.1 0 / tk
          ((1 - s) * cantorVal (cumXor (bitsAt 0 z)) + s * mk,
            -(s * |cantorVal (cumXor (bitsAt 0 z)) - mk|)) := by
        dsimp only [embedBH2]; rw [dif_pos h1z, if_neg h2z]
      rw [hemb] at hzpos
      set s := 1 - z.1 0 / tk
      have hs_nn : 0 ≤ s := by
        have : z.1 0 / tk ≤ 1 := (div_le_one (by positivity)).mpr (le_of_lt (not_le.mp h2z))
        linarith
      have : 0 ≤ s * |cantorVal (cumXor (bitsAt 0 z)) - mk| := by positivity
      dsimp only at hzpos
      linarith
  · have hemb : embedBH2 z = (z.1 0 / 2, z.1 0 / 2) := by
      dsimp only [embedBH2]; rw [dif_neg h1z]
    rw [hemb] at hzpos ⊢
    have h1z' : ∀ j, bitsAt 0 z j = false := by
      intro j; by_contra h; exact h1z ⟨j, by cases hb : bitsAt 0 z j <;> simp_all⟩
    have hcz : cantorVal (cumXor (bitsAt 0 z)) = 0 :=
      (cantorVal_eq_zero_iff _).mpr fun j => cumXor_zero_prefix _ (fun i _ => h1z' i) j (Nat.lt_succ_self j)
    have hR : |cantorVal (cumXor (bitsAt 0 z)) - 1 / 2| = 1 / 2 := by rw [hcz]; norm_num
    have hz0_le := (bh_mem_Icc z 0).2
    dsimp only at hzpos ⊢
    refine ⟨?_, by rw [hR]; norm_num, ?_, ?_⟩
    · rw [hR, abs_of_nonpos (by linarith)]; ring
    · intro hhalf; linarith
    · intro hne
      refine ⟨?_, ?_⟩
      · rw [hcz]; constructor <;> intro _ <;> linarith [lt_of_le_of_ne (show z.1 0 / 2 ≤ 1 / 2 by linarith) hne]
      · rw [dif_neg h1z, hR]; ring

lemma embedBH2_lower_char (z : BH) (hzneg : (embedBH2 z).2 < 0) :
    ∃ h : ∃ j, bitsAt 0 z j = true,
      let k := Nat.find h + 1
      let tk : ℝ := 1 / (2 : ℝ) ^ (k + 1)
      let mk : ℝ := 5 / (2 * (3 : ℝ) ^ k)
      let c := cantorVal (cumXor (bitsAt 0 z))
      let r := |c - mk|
      z.1 0 < tk ∧
      (embedBH2 z).1 ∈ Icc (2 / (3 : ℝ) ^ k) (1 / (3 : ℝ) ^ (k - 1)) ∧
      |(embedBH2 z).1 - mk| - (embedBH2 z).2 = r ∧
      0 < r ∧
      ((embedBH2 z).1 = mk → z.1 0 = 0) ∧
      ((embedBH2 z).1 ≠ mk →
        ((embedBH2 z).1 < mk ↔ c < mk) ∧ -(embedBH2 z).2 / r = 1 - z.1 0 / tk) := by
  by_cases h1z : ∃ j, bitsAt 0 z j = true
  · set j0 := Nat.find h1z
    set k := j0 + 1
    set tk : ℝ := 1 / (2 : ℝ) ^ (k + 1)
    set mk : ℝ := 5 / (2 * (3 : ℝ) ^ k)
    by_cases h2z : tk ≤ z.1 0
    · exfalso
      have hemb : embedBH2 z =
          let s := (z.1 0 - tk) / (1 - tk)
          ((1 - s) * cantorVal (cumXor (bitsAt 0 z)) + s / 2,
            s * |cantorVal (cumXor (bitsAt 0 z)) - 1 / 2|) := by
        dsimp only [embedBH2]; rw [dif_pos h1z, if_pos h2z]
      rw [hemb] at hzneg
      have htk_lt1 : tk < 1 := (div_lt_one (by positivity)).mpr (one_lt_pow₀ (by norm_num) (by omega))
      have : 0 ≤ (z.1 0 - tk) / (1 - tk) * |cantorVal (cumXor (bitsAt 0 z)) - 1 / 2| :=
        mul_nonneg (div_nonneg (by linarith) (by linarith)) (abs_nonneg _)
      dsimp only at hzneg; linarith
    · have hemb : embedBH2 z =
          let s := 1 - z.1 0 / tk
          ((1 - s) * cantorVal (cumXor (bitsAt 0 z)) + s * mk,
            -(s * |cantorVal (cumXor (bitsAt 0 z)) - mk|)) := by
        dsimp only [embedBH2]; rw [dif_pos h1z, if_neg h2z]
      refine ⟨h1z, ?_⟩
      rw [hemb]
      set c := cantorVal (cumXor (bitsAt 0 z))
      set r := |c - mk|
      set s := 1 - z.1 0 / tk
      have hzlt : z.1 0 < tk := not_le.mp h2z
      have hs_pos : 0 < s := by
        have : z.1 0 / tk < 1 := (div_lt_one (by positivity)).mpr hzlt
        linarith
      have hs_le1 : s ≤ 1 := by
        have : 0 ≤ z.1 0 / tk := div_nonneg (bh_mem_Icc z 0).1 (by positivity)
        linarith
      have hj0_f : ∀ j < j0, bitsAt 0 z j = false := fun j hj => by
        by_contra h; exact Nat.find_min h1z hj (by cases hj' : bitsAt 0 z j <;> simp_all)
      have hj0_t : bitsAt 0 z j0 = true := Nat.find_spec h1z
      have hcum_f := cumXor_zero_prefix _ hj0_f
      have hcum_t := cumXor_first_true _ hj0_f hj0_t
      have hc_bds := cantorVal_bounds_of_first_true hcum_f hcum_t
      have hr_bds := cantorVal_dist_mid_bounds hcum_f hcum_t
      have hr_pos : 0 < r := lt_of_lt_of_le (by positivity) hr_bds.1
      have hmk_bds : 2 / (3 : ℝ) ^ k ≤ mk ∧ mk ≤ 1 / (3 : ℝ) ^ j0 := by
        unfold mk
        have hpow : (3 : ℝ) ^ k = 3 * (3 : ℝ) ^ j0 := by rw [pow_succ]; ring
        have h3p : (0 : ℝ) < (3 : ℝ) ^ j0 := by positivity
        constructor
        · rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
        · rw [hpow, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
      dsimp only
      refine ⟨hzlt, ?_, ?_, hr_pos, ?_, ?_⟩
      · simp only [Nat.add_sub_cancel]
        constructor <;> nlinarith [hc_bds.1, hc_bds.2, hmk_bds.1, hmk_bds.2]
      · have : (1 - s) * c + s * mk - mk = (1 - s) * (c - mk) := by ring
        rw [this, abs_mul, abs_of_nonneg (by linarith)]; ring
      · intro hmk_eq
        have : (1 - s) * (c - mk) = 0 := by linarith
        have h1s0 : 1 - s = 0 := (mul_eq_zero.mp this).resolve_right (abs_pos.mp hr_pos)
        have hdiv0 : z.1 0 / tk = 0 := by linarith
        exact (div_eq_zero_iff.mp hdiv0).resolve_right (by positivity)
      · intro hne
        have h1s_pos : 0 < 1 - s := by
          refine lt_of_le_of_ne (by linarith) fun h0 => hne ?_
          have : s = 1 := by linarith
          rw [this]; ring
        refine ⟨?_, ?_⟩
        · have : (1 - s) * c + s * mk - mk = (1 - s) * (c - mk) := by ring
          constructor <;> intro hlt <;> nlinarith
        · rw [neg_neg]; exact mul_div_cancel_right₀ s (ne_of_gt hr_pos)
  · exfalso
    have hemb : embedBH2 z = (z.1 0 / 2, z.1 0 / 2) := by
      dsimp only [embedBH2]; rw [dif_neg h1z]
    rw [hemb] at hzneg; dsimp only at hzneg; linarith [(bh_mem_Icc z 0).1]

lemma embedBH2_zero_char (z : BH) (hz0 : (embedBH2 z).2 = 0) :
    (embedBH2 z).1 = cantorVal (cumXor (bitsAt 0 z)) ∧
    z.1 0 = (if h : ∃ j, bitsAt 0 z j = true then 1 / (2 : ℝ) ^ (Nat.find h + 1 + 1) else 0) := by
  by_cases h1z : ∃ j, bitsAt 0 z j = true
  · set j0 := Nat.find h1z
    set k := j0 + 1
    set tk : ℝ := 1 / (2 : ℝ) ^ (k + 1)
    set mk : ℝ := 5 / (2 * (3 : ℝ) ^ k)
    by_cases h2z : tk ≤ z.1 0
    · have hemb : embedBH2 z =
          let s := (z.1 0 - tk) / (1 - tk)
          ((1 - s) * cantorVal (cumXor (bitsAt 0 z)) + s / 2,
            s * |cantorVal (cumXor (bitsAt 0 z)) - 1 / 2|) := by
        dsimp only [embedBH2]; rw [dif_pos h1z, if_pos h2z]
      rw [hemb] at hz0 ⊢
      dsimp only at hz0 ⊢
      have hRpos : 0 < |cantorVal (cumXor (bitsAt 0 z)) - 1 / 2| :=
        lt_of_lt_of_le (by norm_num) (cantorVal_dist_half_bounds _).1
      have hs0 : (z.1 0 - tk) / (1 - tk) = 0 := (mul_eq_zero.mp hz0).resolve_right (ne_of_gt hRpos)
      have htk_lt1 : tk < 1 := (div_lt_one (by positivity)).mpr (one_lt_pow₀ (by norm_num) (by omega))
      have hzt : z.1 0 = tk := by
        have := (div_eq_zero_iff.mp hs0).resolve_right (by linarith)
        linarith
      refine ⟨by simp [hs0], by rw [dif_pos h1z]; exact hzt⟩
    · exfalso
      have hemb : embedBH2 z =
          let s := 1 - z.1 0 / tk
          ((1 - s) * cantorVal (cumXor (bitsAt 0 z)) + s * mk,
            -(s * |cantorVal (cumXor (bitsAt 0 z)) - mk|)) := by
        dsimp only [embedBH2]; rw [dif_pos h1z, if_neg h2z]
      rw [hemb] at hz0; dsimp only at hz0
      have hj0_f : ∀ j < j0, bitsAt 0 z j = false := fun j hj => by
        by_contra h; exact Nat.find_min h1z hj (by cases hj' : bitsAt 0 z j <;> simp_all)
      have hr_pos : 0 < |cantorVal (cumXor (bitsAt 0 z)) - mk| :=
        lt_of_lt_of_le (by positivity) (cantorVal_dist_mid_bounds (cumXor_zero_prefix _ hj0_f)
          (cumXor_first_true _ hj0_f (Nat.find_spec h1z))).1
      have hs_pos : 0 < 1 - z.1 0 / tk := by
        have : z.1 0 / tk < 1 := (div_lt_one (by positivity)).mpr (not_le.mp h2z)
        linarith
      linarith [mul_pos hs_pos hr_pos]
  · have hemb : embedBH2 z = (z.1 0 / 2, z.1 0 / 2) := by
      dsimp only [embedBH2]; rw [dif_neg h1z]
    rw [hemb] at hz0 ⊢; dsimp only at hz0 ⊢
    have h1z' : ∀ j, bitsAt 0 z j = false := by
      intro j; by_contra h; exact h1z ⟨j, by cases hb : bitsAt 0 z j <;> simp_all⟩
    have hz00 : z.1 0 = 0 := by linarith
    have hcz : cantorVal (cumXor (bitsAt 0 z)) = 0 :=
      (cantorVal_eq_zero_iff _).mpr fun j => cumXor_zero_prefix _ (fun i _ => h1z' i) j (Nat.lt_succ_self j)
    exact ⟨by linarith, by rw [dif_neg h1z]; exact hz00⟩

lemma injective_embedBH2 : Function.Injective embedBH2 := by
  intro x y hxy
  have h1 : (embedBH2 x).1 = (embedBH2 y).1 := congrArg Prod.fst hxy
  have h2 : (embedBH2 x).2 = (embedBH2 y).2 := congrArg Prod.snd hxy
  rcases lt_trichotomy (embedBH2 x).2 0 with hneg | hzero | hpos
  · obtain ⟨hx_ex, hxlt, hx_int, hx_rad, hx_rpos, hx_at_m, hx_off_m⟩ := embedBH2_lower_char x hneg
    obtain ⟨hy_ex, hylt, hy_int, hy_rad, hy_rpos, hy_at_m, hy_off_m⟩ :=
      embedBH2_lower_char y (by rwa [← h2])
    set kx := Nat.find hx_ex + 1
    set ky := Nat.find hy_ex + 1
    have hk_eq : kx = ky := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have h3le : (3 : ℝ) ^ kx ≤ (3 : ℝ) ^ (ky - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        have h1' : 1 / (3 : ℝ) ^ (ky - 1) ≤ 1 / (3 : ℝ) ^ kx := by gcongr
        have h2' : 1 / (3 : ℝ) ^ kx < 2 / (3 : ℝ) ^ kx := by
          rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num
        linarith [hx_int.1, hy_int.2]
      · have h3le : (3 : ℝ) ^ ky ≤ (3 : ℝ) ^ (kx - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        have h1' : 1 / (3 : ℝ) ^ (kx - 1) ≤ 1 / (3 : ℝ) ^ ky := by gcongr
        have h2' : 1 / (3 : ℝ) ^ ky < 2 / (3 : ℝ) ^ ky := by
          rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num
        linarith [hy_int.1, hx_int.2]
    have hy_rad' : |(embedBH2 y).1 - 5 / (2 * (3 : ℝ) ^ kx)| - (embedBH2 y).2 =
        |cantorVal (cumXor (bitsAt 0 y)) - 5 / (2 * (3 : ℝ) ^ kx)| := by
      simpa [← hk_eq] using hy_rad
    have hrad_eq : |cantorVal (cumXor (bitsAt 0 x)) - 5 / (2 * (3 : ℝ) ^ kx)| =
        |cantorVal (cumXor (bitsAt 0 y)) - 5 / (2 * (3 : ℝ) ^ kx)| := by
      rw [← hx_rad, ← hy_rad', h1, h2]
    set mk : ℝ := 5 / (2 * (3 : ℝ) ^ kx)
    by_cases hmid : (embedBH2 x).1 = mk
    · have hx0 : x.1 0 = 0 := hx_at_m hmid
      have hy0 : y.1 0 = 0 := hy_at_m (by rw [← h1, ← hk_eq]; exact hmid)
      have hpref_zero : ∀ (z : BH) (hz0 : z.1 0 = 0) (hzex : ∃ j, bitsAt 0 z j = true),
          Nat.find hzex + 1 = kx → (∀ m < kx, z.1 m = 0) ∧ z.1 kx = 1 := by
        intro z hz0 hzex hfk
        have hltz : ∀ m < kx, z.1 m = 0 := by
          intro m hm
          induction m with
          | zero => exact hz0
          | succ m ih =>
            have ht := bh_tent z m
            rw [ih (by omega)] at ht
            have hbf : bitsAt 0 z m = false := by
              by_contra h
              have ht' : bitsAt 0 z m = true := by cases hm' : bitsAt 0 z m <;> simp_all
              have hle := Nat.find_min' hzex ht'
              omega
            simp only [bitsAt, Nat.zero_add, decide_eq_false_iff_not, not_lt] at hbf
            rw [tent_eq_two_mul hbf] at ht; linarith
        refine ⟨hltz, ?_⟩
        have ht := bh_tent z (kx - 1)
        rw [show kx - 1 + 1 = kx by omega, hltz (kx - 1) (by omega)] at ht
        have hbt : bitsAt 0 z (kx - 1) = true := by
          have := Nat.find_spec hzex; rwa [show Nat.find hzex = kx - 1 by omega] at this
        simp only [bitsAt, Nat.zero_add, show kx - 1 + 1 = kx by omega, decide_eq_true_eq] at hbt
        rw [tent_eq_two_sub (le_of_lt hbt)] at ht; linarith
      obtain ⟨_, hxk1⟩ := hpref_zero x hx0 hx_ex rfl
      obtain ⟨_, hyk1⟩ := hpref_zero y hy0 hy_ex hk_eq.symm
      have hx_aft := bh_after_one x hxk1
      have hy_aft := bh_after_one y hyk1
      have hgt_mk : ∀ (z : BH) (hzex : ∃ j, bitsAt 0 z j = true),
          Nat.find hzex + 1 = kx → z.1 (kx + 1) = 1 / 2 →
          mk < cantorVal (cumXor (bitsAt 0 z)) := by
        intro z hzex hfk hzh
        have hz0 : ∀ j < kx - 1, bitsAt 0 z j = false := fun j hj => by
          by_contra h; exact absurd (Nat.find_min' hzex (by cases hj' : bitsAt 0 z j <;> simp_all)) (by omega)
        have hz1 : bitsAt 0 z (kx - 1) = true := by
          have := Nat.find_spec hzex; rwa [show Nat.find hzex = kx - 1 by omega] at this
        have hzk : bitsAt 0 z kx = false := by
          unfold bitsAt; rw [decide_eq_false_iff_not]; simp [hzh]
        have hcf := cumXor_zero_prefix _ hz0
        have hct := cumXor_first_true _ hz0 hz1
        have hck : cumXor (bitsAt 0 z) kx = true := by
          have hke : kx = (kx - 1) + 1 := by omega
          conv_lhs => rw [hke]
          simp [cumXor, hct, ← hke, hzk]
        rw [cantorVal_split (cumXor (bitsAt 0 z)) (kx + 1), Finset.sum_range_succ,
          show kx = (kx - 1) + 1 by omega, Finset.sum_range_succ]
        have hzsum : ∑ j ∈ Finset.range (kx - 1), cantorTerm (cumXor (bitsAt 0 z)) j = 0 :=
          Finset.sum_eq_zero fun j hj => by simp [cantorTerm, hcf j (Finset.mem_range.mp hj)]
        rw [hzsum, zero_add]
        have ht1 : cantorTerm (cumXor (bitsAt 0 z)) (kx - 1) = 2 / (3 : ℝ) ^ kx := by
          simp [cantorTerm, hct, show kx - 1 + 1 = kx by omega]
        have ht2 : cantorTerm (cumXor (bitsAt 0 z)) (kx - 1 + 1) = 2 / (3 : ℝ) ^ (kx + 1) := by
          rw [show kx - 1 + 1 = kx by omega]; simp [cantorTerm, hck]
        rw [ht1, ht2]
        have hnn : 0 ≤ cantorVal (fun j => cumXor (bitsAt 0 z) (kx - 1 + 1 + 1 + j)) /
            (3 : ℝ) ^ (kx - 1 + 1 + 1) := div_nonneg (cantorVal_nonneg _) (by positivity)
        have hpow : (3 : ℝ) ^ (kx + 1) = 3 * (3 : ℝ) ^ kx := by rw [pow_succ]; ring
        have h3p : (0 : ℝ) < (3 : ℝ) ^ kx := by positivity
        have hlt_mk : mk < 2 / (3 : ℝ) ^ kx + 2 / (3 : ℝ) ^ (kx + 1) := by
          unfold mk; rw [hpow]; field_simp; nlinarith
        linarith
      have hxc_gt := hgt_mk x hx_ex rfl hx_aft.1
      have hyc_gt := hgt_mk y hy_ex hk_eq.symm hy_aft.1
      rw [abs_of_pos (by linarith), abs_of_pos (by linarith)] at hrad_eq
      have hbits_eq : bitsAt 0 x = bitsAt 0 y := cumXor_injective (cantorVal_injective (by linarith))
      rw [← chart_bitsAt (kx + 1) x, ← chart_bitsAt (kx + 1) y]
      have hbits_k1 : bitsAt (kx + 1) x = bitsAt (kx + 1) y := by
        funext j
        have h := congrFun hbits_eq (kx + 1 + j)
        simpa [bitsAt, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      simp [hbits_k1, hx_aft.1, hy_aft.1]
    · have hne_y : (embedBH2 y).1 ≠ 5 / (2 * (3 : ℝ) ^ ky) := by rw [← h1, ← hk_eq]; exact hmid
      have ⟨hx_sgn, hx_s⟩ := hx_off_m hmid
      have ⟨hy_sgn, hy_s⟩ := hy_off_m hne_y
      have hc_eq : cantorVal (cumXor (bitsAt 0 x)) = cantorVal (cumXor (bitsAt 0 y)) := by
        have hy_sgn' : (embedBH2 y).1 < mk ↔ cantorVal (cumXor (bitsAt 0 y)) < mk := by
          simpa [← hk_eq, mk] using hy_sgn
        by_cases hlt : (embedBH2 x).1 < mk
        · have hxc := hx_sgn.mp hlt
          have hyc := hy_sgn'.mp (by rwa [← h1])
          rw [abs_of_neg (by linarith), abs_of_neg (by linarith)] at hrad_eq; linarith
        · have hxge : mk ≤ cantorVal (cumXor (bitsAt 0 x)) := not_lt.mp fun h => hlt (hx_sgn.mpr h)
          have hyge : mk ≤ cantorVal (cumXor (bitsAt 0 y)) :=
            not_lt.mp fun h => hlt (by rw [h1]; exact hy_sgn'.mpr h)
          rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at hrad_eq; linarith
      have hbits_eq : bitsAt 0 x = bitsAt 0 y := cumXor_injective (cantorVal_injective hc_eq)
      have hx0_eq : x.1 0 = y.1 0 := by
        have hy_s' : -(embedBH2 y).2 / |cantorVal (cumXor (bitsAt 0 y)) - mk| =
            1 - y.1 0 / (1 / (2 : ℝ) ^ (kx + 1)) := by simpa [← hk_eq, mk] using hy_s
        have hs_eq : 1 - x.1 0 / (1 / (2 : ℝ) ^ (kx + 1)) = 1 - y.1 0 / (1 / (2 : ℝ) ^ (kx + 1)) := by
          rw [← hx_s, ← hy_s', h2, hrad_eq]
        have htk_ne : (1 : ℝ) / (2 : ℝ) ^ (kx + 1) ≠ 0 := by positivity
        exact (div_left_inj' htk_ne).mp (by linarith)
      rw [← chart_bitsAt 0 x, ← chart_bitsAt 0 y]
      simp [hbits_eq, hx0_eq]
  · obtain ⟨hxc, hxt⟩ := embedBH2_zero_char x hzero
    obtain ⟨hyc, hyt⟩ := embedBH2_zero_char y (by rw [← h2]; exact hzero)
    have hbits_eq : bitsAt 0 x = bitsAt 0 y := cumXor_injective (cantorVal_injective (by linarith))
    have hx0_eq : x.1 0 = y.1 0 := by rw [hxt, hyt]; simp [hbits_eq]
    by_cases hex : ∃ j, bitsAt 0 x j = true
    · rw [← chart_bitsAt 0 x, ← chart_bitsAt 0 y]; simp [hbits_eq, hx0_eq]
    · push Not at hex
      have hfx : ∀ n, x.1 n = 0 := by
        intro n; induction n with
        | zero => rw [hxt, dif_neg (by push Not; exact hex)]
        | succ n ih =>
          have ht := bh_tent x n; rw [ih] at ht
          have hle : x.1 (n + 1) ≤ 1 / 2 := by
            have := hex n; unfold bitsAt at this
            by_contra hgt; push Not at hgt; exact this (decide_eq_true (by simpa using hgt))
          rw [tent_eq_two_mul hle] at ht; linarith
      have hfy : ∀ n, y.1 n = 0 := by
        intro n; induction n with
        | zero => rw [hyt, dif_neg (by push Not; rwa [← hbits_eq])]
        | succ n ih =>
          have ht := bh_tent y n; rw [ih] at ht
          have hle : y.1 (n + 1) ≤ 1 / 2 := by
            have := hex n; rw [hbits_eq] at this; unfold bitsAt at this
            by_contra hgt; push Not at hgt; exact this (decide_eq_true (by simpa using hgt))
          rw [tent_eq_two_mul hle] at ht; linarith
      exact Subtype.ext (funext fun n => by rw [hfx n, hfy n])
  · obtain ⟨hx_rad, hx_rpos, hx_at_h, hx_off_h⟩ := embedBH2_upper_char x hpos
    obtain ⟨hy_rad, hy_rpos, hy_at_h, hy_off_h⟩ := embedBH2_upper_char y (by rwa [← h2])
    have hrad_eq : |cantorVal (cumXor (bitsAt 0 x)) - 1 / 2| =
        |cantorVal (cumXor (bitsAt 0 y)) - 1 / 2| := by
      rw [← hx_rad, ← hy_rad, h1, h2]
    by_cases hmid : (embedBH2 x).1 = 1 / 2
    · have hx1 : x.1 0 = 1 := hx_at_h hmid
      have hy1 : y.1 0 = 1 := hy_at_h (by rwa [← h1])
      have hx_aft := bh_after_one x hx1
      have hy_aft := bh_after_one y hy1
      have hx0f : bitsAt 0 x 0 = false := by unfold bitsAt; rw [decide_eq_false_iff_not]; simp [hx_aft.1]
      have hy0f : bitsAt 0 y 0 = false := by unfold bitsAt; rw [decide_eq_false_iff_not]; simp [hy_aft.1]
      have hlt_half : ∀ z : BH, bitsAt 0 z 0 = false → cantorVal (cumXor (bitsAt 0 z)) < 1 / 2 := by
        intro z hz0
        rw [cantorVal_split (cumXor (bitsAt 0 z)) 1, Finset.sum_range_one]
        simp only [cantorTerm, cumXor, hz0, Bool.false_eq_true, ↓reduceIte, zero_div, zero_add, pow_one]
        linarith [cantorVal_le_one (fun j => cumXor (bitsAt 0 z) (1 + j))]
      have hxc := hlt_half x hx0f
      have hyc := hlt_half y hy0f
      rw [abs_of_neg (by linarith), abs_of_neg (by linarith)] at hrad_eq
      have hbits_eq : bitsAt 0 x = bitsAt 0 y := cumXor_injective (cantorVal_injective (by linarith))
      rw [← chart_bitsAt 1 x, ← chart_bitsAt 1 y]
      have hbits1 : bitsAt 1 x = bitsAt 1 y := by
        funext j
        have h := congrFun hbits_eq (j + 1)
        simpa [bitsAt, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      simp [hbits1, hx_aft.1, hy_aft.1]
    · have ⟨hx_sgn, hx_s⟩ := hx_off_h hmid
      have ⟨hy_sgn, hy_s⟩ := hy_off_h (by rwa [← h1])
      have hc_eq : cantorVal (cumXor (bitsAt 0 x)) = cantorVal (cumXor (bitsAt 0 y)) := by
        by_cases hlt : (embedBH2 x).1 < 1 / 2
        · have hxc := hx_sgn.mp hlt
          have hyc := hy_sgn.mp (by rwa [← h1])
          rw [abs_of_neg (by linarith), abs_of_neg (by linarith)] at hrad_eq; linarith
        · have hxge : 1 / 2 ≤ cantorVal (cumXor (bitsAt 0 x)) := not_lt.mp fun h => hlt (hx_sgn.mpr h)
          have hyge : 1 / 2 ≤ cantorVal (cumXor (bitsAt 0 y)) :=
            not_lt.mp fun h => hlt (by rw [h1]; exact hy_sgn.mpr h)
          rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at hrad_eq; linarith
      have hbits_eq : bitsAt 0 x = bitsAt 0 y := cumXor_injective (cantorVal_injective hc_eq)
      have hx0_eq : x.1 0 = y.1 0 := by
        have hs_eq : (embedBH2 x).2 / |cantorVal (cumXor (bitsAt 0 x)) - 1 / 2| =
            (embedBH2 y).2 / |cantorVal (cumXor (bitsAt 0 y)) - 1 / 2| := by rw [h2, hc_eq]
        rw [hx_s, hy_s] at hs_eq
        by_cases hex : ∃ j, bitsAt 0 x j = true
        · have hey : ∃ j, bitsAt 0 y j = true := by rwa [← hbits_eq]
          rw [dif_pos hex, dif_pos hey] at hs_eq
          have hfeq : Nat.find hex = Nat.find hey := by simp [hbits_eq]
          rw [hfeq] at hs_eq
          set tk : ℝ := 1 / (2 : ℝ) ^ (Nat.find hey + 1 + 1)
          have htk_lt1 : tk < 1 := (div_lt_one (by positivity)).mpr (one_lt_pow₀ (by norm_num) (by omega))
          have hsub := (div_left_inj' (show (1 : ℝ) - tk ≠ 0 by linarith)).mp hs_eq
          linarith
        · have hny : ¬ ∃ j, bitsAt 0 y j = true := by rwa [← hbits_eq]
          rw [dif_neg hex, dif_neg hny] at hs_eq
          exact hs_eq
      rw [← chart_bitsAt 0 x, ← chart_bitsAt 0 y]
      simp [hbits_eq, hx0_eq]

lemma isEmbedding_embedBH : Topology.IsEmbedding embedBH := by
  have hcont : Continuous embedBH := by
    unfold embedBH
    refine (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp ?_
    rw [continuous_pi_iff]
    intro i
    fin_cases i
    · exact continuous_fst.comp continuous_embedBH2
    · exact continuous_snd.comp continuous_embedBH2
  have hinj : Function.Injective embedBH := by
    intro x y h
    have hpi := (EuclideanSpace.equiv (Fin 2) ℝ).symm.injective h
    have h0 : (embedBH2 x).1 = (embedBH2 y).1 := congrFun hpi 0
    have h1 : (embedBH2 x).2 = (embedBH2 y).2 := congrFun hpi 1
    exact injective_embedBH2 (Prod.ext h0 h1)
  exact (hcont.isClosedEmbedding hinj).isEmbedding

/- Section 3: Proper subcontinua and composants of `BH` -/

/-- A single arc fiber of `BH` at level `m` with bit sequence `η`. -/
def arcFiber (m : ℕ) (η : ℕ → Bool) : Set BH :=
  range (fun t : Icc (0 : ℝ) 1 => chart m η t)

lemma isCompact_arcFiber (m : ℕ) (η : ℕ → Bool) : IsCompact (arcFiber m η) := by
  have hc : Continuous (fun t : Icc (0 : ℝ) 1 => chart m η t) :=
    (continuous_chart m).comp (continuous_const.prodMk continuous_id)
  simpa [arcFiber, image_univ] using isCompact_univ.image hc

lemma isConnected_arcFiber (m : ℕ) (η : ℕ → Bool) : IsConnected (arcFiber m η) := by
  have hc : Continuous (fun t : Icc (0 : ℝ) 1 => chart m η t) :=
    (continuous_chart m).comp (continuous_const.prodMk continuous_id)
  refine ⟨⟨chart m η ⟨0, le_rfl, zero_le_one⟩, ⟨_, rfl⟩⟩, ?_⟩
  simpa [arcFiber, image_univ] using (isPreconnected_univ (α := Icc (0 : ℝ) 1)).image _ hc.continuousOn

lemma arcFiber_subset_shift (m d : ℕ) (η : ℕ → Bool) :
    arcFiber m η ⊆ arcFiber (m + d) (fun j => η (d + j)) := by
  rintro _ ⟨t, rfl⟩
  let w : List Bool := List.ofFn (fun i : Fin d => η i)
  have hwlen : w.length = d := List.length_ofFn
  have hprep : prependWord w (fun j => η (d + j)) = η := by
    funext n
    unfold prependWord
    by_cases hn : n < w.length
    · rw [dif_pos hn]; simp [w]
    · rw [dif_neg hn, hwlen]; dsimp only; congr 1; rw [hwlen] at hn; omega
  refine ⟨⟨branchWord w t.1, branchWord_mem_Icc w t.2⟩, ?_⟩
  have hsh := chart_shift_word m w (fun j => η (d + j)) t
  rw [hprep] at hsh
  have hlen_eq : m + w.length = m + d := by rw [hwlen]
  simpa [hlen_eq] using hsh

lemma proper_subcontinuum_subset_fiber {H : Set BH} (hclosed : IsClosed H) (hconn : IsConnected H)
    (hne : H ≠ univ) : ∃ (m : ℕ) (η : ℕ → Bool), H ⊆ arcFiber m η := by
  -- Step 1: Some coordinate projection of `H` is not all of `[0, 1]`.
  have hex_m : ∃ m : ℕ, (fun x : BH => x.1 m) '' H ≠ Icc (0 : ℝ) 1 := by
    by_contra hall; push Not at hall
    apply hne
    rw [eq_univ_iff_forall]
    intro x
    rw [← hclosed.closure_eq, mem_closure_iff_nhds]
    intro U hU
    rw [nhds_induced] at hU
    rcases hU with ⟨V, hV, hVU⟩
    rw [nhds_pi, Filter.mem_pi'] at hV
    rcases hV with ⟨I, t, ht, hIt⟩
    let m := I.sup id
    have hmem : x.1 m ∈ (fun z : BH => z.1 m) '' H := by
      rw [hall m]; exact bh_mem_Icc x m
    rcases hmem with ⟨h, hhH, hhm⟩
    refine ⟨h, hVU (hIt fun n hn => ?_), hhH⟩
    have hnm : n ≤ m := Finset.le_sup (f := id) hn
    have heq : h.1 n = x.1 n := by
      dsimp only at hhm
      rw [← bh_tent_iterate_of_le h hnm, hhm, bh_tent_iterate_of_le x hnm]
    rw [heq]
    exact mem_of_mem_nhds (ht n)
  rcases hex_m with ⟨m, hm⟩
  -- Helper: if 0 ∉ π_k '' H, then H ⊆ arcFiber (k + 1) η for some η.
  have hcase_no_zero : ∀ k : ℕ, (0 : ℝ) ∉ (fun x : BH => x.1 k) '' H →
      ∃ η : ℕ → Bool, H ⊆ arcFiber (k + 1) η := by
    intro k h0k
    have hno01 : ∀ j : ℕ, ∀ x ∈ H, x.1 (k + j + 1) ∈ Ioo (0 : ℝ) 1 := by
      intro j
      induction j with
      | zero =>
        intro x hx
        have ht := bh_tent x k
        have hmem := bh_mem_Icc x (k + 1)
        have hne0 : x.1 (k + 1) ≠ 0 := fun h => h0k ⟨x, hx, by dsimp only; rw [← ht, h, tent_zero]⟩
        have hne1 : x.1 (k + 1) ≠ 1 := fun h => h0k ⟨x, hx, by dsimp only; rw [← ht, h, tent_one]⟩
        exact ⟨lt_of_le_of_ne hmem.1 (Ne.symm hne0), lt_of_le_of_ne hmem.2 hne1⟩
      | succ j ih =>
        intro x hx
        have ht := bh_tent x (k + j + 1)
        have hmem := bh_mem_Icc x (k + (j + 1) + 1)
        have hprev := ih x hx
        rw [show k + (j + 1) + 1 = k + j + 1 + 1 by omega] at hmem ⊢
        have hne0 : x.1 (k + j + 1 + 1) ≠ 0 := fun h => by rw [h, tent_zero] at ht; linarith [hprev.1]
        have hne1 : x.1 (k + j + 1 + 1) ≠ 1 := fun h => by rw [h, tent_one] at ht; linarith [hprev.1]
        exact ⟨lt_of_le_of_ne hmem.1 (Ne.symm hne0), lt_of_le_of_ne hmem.2 hne1⟩
    rcases hconn.nonempty with ⟨x₀, hx₀⟩
    refine ⟨bitsAt (k + 1) x₀, fun x hx => ?_⟩
    have hbits : bitsAt (k + 1) x = bitsAt (k + 1) x₀ := by
      funext j
      have hconn_j : IsPreconnected ((fun z : BH => z.1 (k + 1 + j + 1)) '' H) :=
        hconn.isPreconnected.image _ (continuous_bhCoord _).continuousOn
      have hnohalf : (1 / 2 : ℝ) ∉ (fun z : BH => z.1 (k + 1 + j + 1)) '' H := by
        rintro ⟨z, hz, hzh⟩
        dsimp only at hzh
        have ht := bh_tent z (k + 1 + j)
        rw [hzh, tent_half] at ht
        have hprev := hno01 j z hz
        rw [show k + 1 + j = k + j + 1 by omega] at ht
        linarith [hprev.2]
      have hne_x : x.1 (k + 1 + j + 1) ≠ 1 / 2 := fun h => hnohalf ⟨x, hx, h⟩
      have hne_x0 : x₀.1 (k + 1 + j + 1) ≠ 1 / 2 := fun h => hnohalf ⟨x₀, hx₀, h⟩
      unfold bitsAt
      by_cases hlt : 1 / 2 < x₀.1 (k + 1 + j + 1)
      · have hltx : 1 / 2 < x.1 (k + 1 + j + 1) := by
          by_contra hle; push Not at hle
          have hmem : (1 / 2 : ℝ) ∈ Icc (x.1 (k + 1 + j + 1)) (x₀.1 (k + 1 + j + 1)) := ⟨hle, le_of_lt hlt⟩
          exact hnohalf (hconn_j.Icc_subset ⟨x, hx, rfl⟩ ⟨x₀, hx₀, rfl⟩ hmem)
        rw [decide_eq_true hltx, decide_eq_true hlt]
      · have hgtx : ¬ 1 / 2 < x.1 (k + 1 + j + 1) := by
          intro hgt
          have hmem : (1 / 2 : ℝ) ∈ Icc (x₀.1 (k + 1 + j + 1)) (x.1 (k + 1 + j + 1)) :=
            ⟨not_lt.mp hlt, le_of_lt hgt⟩
          exact hnohalf (hconn_j.Icc_subset ⟨x₀, hx₀, rfl⟩ ⟨x, hx, rfl⟩ hmem)
        rw [decide_eq_false hgtx, decide_eq_false hlt]
    exact ⟨⟨x.1 (k + 1), bh_mem_Icc x (k + 1)⟩, by dsimp only; rw [← hbits, chart_bitsAt]⟩
  -- Step 2: Either some level k ≥ m misses 0, or every level k ≥ m hits 0 and misses 1.
  by_cases hex0 : ∃ k ≥ m, (0 : ℝ) ∉ (fun x : BH => x.1 k) '' H
  · rcases hex0 with ⟨k, _, hk⟩
    obtain ⟨η, hη⟩ := hcase_no_zero k hk
    exact ⟨k + 1, η, hη⟩
  · push Not at hex0
    have hno1m : (1 : ℝ) ∉ (fun x : BH => x.1 m) '' H := by
      intro h1m
      apply hm
      apply Subset.antisymm
      · rintro _ ⟨x, _, rfl⟩; exact bh_mem_Icc x m
      · exact (hconn.isPreconnected.image _ (continuous_bhCoord m).continuousOn).Icc_subset
          (hex0 m le_rfl) h1m
    have hall_lt : ∀ j : ℕ, (1 : ℝ) ∉ (fun x : BH => x.1 (m + j)) '' H ∧
        ∀ x ∈ H, x.1 (m + j + 1) < 1 / 2 := by
      intro j
      induction j with
      | zero =>
        refine ⟨by simpa using hno1m, fun x hx => ?_⟩
        have hnohalf : (1 / 2 : ℝ) ∉ (fun z : BH => z.1 (m + 1)) '' H := by
          rintro ⟨z, hz, hzh⟩
          dsimp only at hzh
          exact hno1m ⟨z, hz, by dsimp only; rw [← bh_tent z m, hzh, tent_half]⟩
        rcases hex0 (m + 1) (by omega) with ⟨z0, hz0H, hz0⟩
        by_contra hge; push Not at hge
        have hconn1 := hconn.isPreconnected.image _ (continuous_bhCoord (m + 1)).continuousOn
        have hmem : (1 / 2 : ℝ) ∈ Icc (z0.1 (m + 1)) (x.1 (m + 1)) := ⟨by linarith, hge⟩
        exact hnohalf (hconn1.Icc_subset ⟨z0, hz0H, rfl⟩ ⟨x, hx, rfl⟩ hmem)
      | succ j ih =>
        have hno1 : (1 : ℝ) ∉ (fun x : BH => x.1 (m + (j + 1))) '' H := by
          rintro ⟨x, hx, hx1⟩
          have hlt := ih.2 x hx
          rw [show m + (j + 1) = m + j + 1 by omega] at hx1
          linarith
        refine ⟨hno1, fun x hx => ?_⟩
        have hnohalf : (1 / 2 : ℝ) ∉ (fun z : BH => z.1 (m + (j + 1) + 1)) '' H := by
          rintro ⟨z, hz, hzh⟩
          dsimp only at hzh
          exact hno1 ⟨z, hz, by dsimp only; rw [← bh_tent z (m + (j + 1)), hzh, tent_half]⟩
        rcases hex0 (m + (j + 1) + 1) (by omega) with ⟨z0, hz0H, hz0⟩
        by_contra hge; push Not at hge
        have hconn1 := hconn.isPreconnected.image _ (continuous_bhCoord (m + (j + 1) + 1)).continuousOn
        have hmem : (1 / 2 : ℝ) ∈ Icc (z0.1 (m + (j + 1) + 1)) (x.1 (m + (j + 1) + 1)) := ⟨by linarith, hge⟩
        exact hnohalf (hconn1.Icc_subset ⟨z0, hz0H, rfl⟩ ⟨x, hx, rfl⟩ hmem)
    refine ⟨m, fun _ => false, fun x hx => ?_⟩
    have hbits : bitsAt m x = fun _ => false := by
      funext j
      unfold bitsAt
      rw [decide_eq_false_iff_not]
      linarith [(hall_lt j).2 x hx]
    exact ⟨⟨x.1 m, bh_mem_Icc x m⟩, by dsimp only; rw [← hbits, chart_bitsAt]⟩

/-- Two points of `BH` lie in the same composant iff they share an arc fiber. -/
def SameComp (x y : BH) : Prop :=
  ∃ (m : ℕ) (η : ℕ → Bool), x ∈ arcFiber m η ∧ y ∈ arcFiber m η

/-- The composant of a point `x ∈ BH`. -/
def compSet (x : BH) : Set BH := {y | SameComp x y}

lemma sameComp_refl (x : BH) : SameComp x x :=
  ⟨0, bitsAt 0 x, ⟨⟨x.1 0, bh_mem_Icc x 0⟩, chart_bitsAt 0 x⟩,
    ⟨⟨x.1 0, bh_mem_Icc x 0⟩, chart_bitsAt 0 x⟩⟩

lemma sameComp_symm {x y : BH} (h : SameComp x y) : SameComp y x := by
  rcases h with ⟨m, η, hx, hy⟩; exact ⟨m, η, hy, hx⟩

lemma sameComp_trans {x y z : BH} (hxy : SameComp x y) (hyz : SameComp y z) : SameComp x z := by
  rcases hxy with ⟨m₁, η₁, hx, hy₁⟩
  rcases hyz with ⟨m₂, η₂, hy₂, hz⟩
  let M := max m₁ m₂
  let η₁' : ℕ → Bool := fun j => η₁ (M - m₁ + j)
  let η₂' : ℕ → Bool := fun j => η₂ (M - m₂ + j)
  have hsub1 : arcFiber m₁ η₁ ⊆ arcFiber M η₁' := by
    have h := arcFiber_subset_shift m₁ (M - m₁) η₁
    rwa [Nat.add_sub_cancel' (le_max_left m₁ m₂)] at h
  have hsub2 : arcFiber m₂ η₂ ⊆ arcFiber M η₂' := by
    have h := arcFiber_subset_shift m₂ (M - m₂) η₂
    rwa [Nat.add_sub_cancel' (le_max_right m₁ m₂)] at h
  let H := arcFiber M η₁' ∪ arcFiber M η₂'
  have hclosed : IsClosed H := (isCompact_arcFiber M η₁').isClosed.union (isCompact_arcFiber M η₂').isClosed
  have hconn : IsConnected H := by
    refine ⟨⟨y, Or.inl (hsub1 hy₁)⟩, ?_⟩
    exact (isConnected_arcFiber M η₁').isPreconnected.union' ⟨y, hsub1 hy₁, hsub2 hy₂⟩
      (isConnected_arcFiber M η₂').isPreconnected
  have hne : H ≠ univ := by
    let η₃ : ℕ → Bool := fun j => if j = 0 then !(η₁' 0) else !(η₂' 1)
    let p : BH := chart M η₃ ⟨1 / 2, by norm_num, by norm_num⟩
    intro heq
    have hp : p ∈ H := by rw [heq]; trivial
    rcases hp with ⟨t, ht⟩ | ⟨t, ht⟩
    · have h1 := (chart_injective_on_Ioo M (by norm_num : (1 / 2 : ℝ) ∈ Ioo 0 1) ht.symm).1
      have h0 := congrFun h1 0
      simp [η₃] at h0
    · have h1 := (chart_injective_on_Ioo M (by norm_num : (1 / 2 : ℝ) ∈ Ioo 0 1) ht.symm).1
      have h0 := congrFun h1 1
      simp [η₃] at h0
  obtain ⟨m, η, hm⟩ := proper_subcontinuum_subset_fiber hclosed hconn hne
  exact ⟨m, η, hm (Or.inl (hsub1 hx)), hm (Or.inr (hsub2 hz))⟩

lemma mem_compSet_self (x : BH) : x ∈ compSet x := sameComp_refl x

lemma compSet_eq_of_mem {x y : BH} (h : y ∈ compSet x) : compSet y = compSet x := by
  ext z; exact ⟨fun hz => sameComp_trans h hz, fun hz => sameComp_trans (sameComp_symm h) hz⟩

lemma compSet_fibers_countable (p : BH) (k : ℕ) {a b : ℝ} (ha : 0 < a) (hb : b < 1) :
    {ε : ℕ → Bool | ∃ t : Icc (0 : ℝ) 1, t.1 ∈ Icc a b ∧ chart k ε t ∈ compSet p}.Countable := by
  set E := {ε : ℕ → Bool | ∃ t : Icc (0 : ℝ) 1, t.1 ∈ Icc a b ∧ chart k ε t ∈ compSet p}
  by_cases hemp : E = ∅
  · rw [hemp]; exact countable_empty
  · obtain ⟨ε₀, t₀, ht₀, hmem₀⟩ := Set.nonempty_iff_ne_empty.mpr hemp
    have hcomp_eq : compSet p = compSet (chart k ε₀ t₀) := (compSet_eq_of_mem hmem₀).symm
    have hsub : E ⊆ ⋃ w : List Bool, {prependWord w (fun j => ε₀ (w.length + j))} := by
      rintro ε ⟨t, ht, hmem⟩
      rw [hcomp_eq] at hmem
      rcases hmem with ⟨m, η, h0, h1⟩
      let M := max m k
      let d := M - k
      have hMd : M = k + d := (Nat.add_sub_cancel' (le_max_right m k)).symm
      let η' : ℕ → Bool := fun j => η (M - m + j)
      have hsubM : arcFiber m η ⊆ arcFiber M η' := by
        have h := arcFiber_subset_shift m (M - m) η
        rwa [Nat.add_sub_cancel' (le_max_left m k)] at h
      rcases hsubM h0 with ⟨s₀, hs₀⟩
      rcases hsubM h1 with ⟨s₁, hs₁⟩
      have ht₀_ioo : t₀.1 ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_lt_of_le ha ht₀.1, lt_of_le_of_lt ht₀.2 hb⟩
      have ht_ioo : t.1 ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
      have hcoord_ioo : ∀ (ε' : ℕ → Bool) (t' : Icc (0 : ℝ) 1), t'.1 ∈ Ioo (0 : ℝ) 1 →
          (chart k ε' t').1 M ∈ Ioo (0 : ℝ) 1 := by
        intro ε' t' ht'
        rw [hMd, chart_coord_add]
        exact chartAux_mem_Ioo ε' ht' d
      have hs₀_ioo : s₀.1 ∈ Ioo (0 : ℝ) 1 := by
        have := congrArg (fun z : BH => z.1 M) hs₀
        rw [chart_coord_self] at this
        rw [this]; exact hcoord_ioo ε₀ t₀ ht₀_ioo
      have hs₁_ioo : s₁.1 ∈ Ioo (0 : ℝ) 1 := by
        have := congrArg (fun z : BH => z.1 M) hs₁
        rw [chart_coord_self] at this
        rw [this]; exact hcoord_ioo ε t ht_ioo
      have hbits_shift : ∀ (ε' : ℕ → Bool) (t' : Icc (0 : ℝ) 1), t'.1 ∈ Ioo (0 : ℝ) 1 →
          bitsAt M (chart k ε' t') = fun j => ε' (d + j) := by
        intro ε' t' ht'
        funext j
        have hb := congrFun (bitsAt_chart k ε' ht') (d + j)
        simpa [bitsAt, hMd, Nat.add_assoc] using hb
      have hη0 : (fun j => ε₀ (d + j)) = η' := by
        rw [← hbits_shift ε₀ t₀ ht₀_ioo, ← hs₀, bitsAt_chart M η' hs₀_ioo]
      have hη1 : (fun j => ε (d + j)) = η' := by
        rw [← hbits_shift ε t ht_ioo, ← hs₁, bitsAt_chart M η' hs₁_ioo]
      let w : List Bool := List.ofFn (fun i : Fin d => ε i)
      refine mem_iUnion.mpr ⟨w, mem_singleton_iff.mpr ?_⟩
      funext n
      unfold prependWord
      by_cases hn : n < w.length
      · rw [dif_pos hn]; simp [w]
      · rw [dif_neg hn, List.length_ofFn]
        have htail : ε (d + (n - d)) = ε₀ (d + (n - d)) := congrFun (hη1.trans hη0.symm) (n - d)
        have hnd : d + (n - d) = n := by rw [List.length_ofFn] at hn; omega
        dsimp only
        rw [hnd] at htail ⊢
        exact htail
    exact (countable_iUnion fun _ => countable_singleton _).mono hsub

/- Section 4: Sections, blocks, strips, cylinder splitting, and `G(S)` -/

/-- Exact rational one-step inverse branch of `tent`. -/
def branchBitQ (b : Bool) (q : ℚ) : ℚ := if b then 1 - q / 2 else q / 2

/-- Exact rational iterated inverse branch of `tent`. -/
def branchWordQ : List Bool → ℚ → ℚ
  | [], q => q
  | b :: w, q => branchWordQ w (branchBitQ b q)

lemma branchBitQ_cast (b : Bool) (q : ℚ) : (branchBitQ b q : ℝ) = branchBit b (q : ℝ) := by
  cases b <;> simp [branchBitQ, branchBit]

lemma branchWordQ_cast (w : List Bool) (q : ℚ) : (branchWordQ w q : ℝ) = branchWord w (q : ℝ) := by
  induction w generalizing q with
  | nil => rfl
  | cons b w ih => simp [branchWordQ, branchWord, ih, branchBitQ_cast]

lemma branchWordQ_append (w₁ w₂ : List Bool) (q : ℚ) :
    branchWordQ (w₁ ++ w₂) q = branchWordQ w₂ (branchWordQ w₁ q) := by
  induction w₁ generalizing q with
  | nil => rfl
  | cons b w₁ ih => simp [branchWordQ, ih]

lemma branchBitQ_false_bounds {q : ℚ} (h0 : 0 < q) (h1 : q < 1) :
    0 < branchBitQ false q ∧ branchBitQ false q < 1 / 2 := by
  simp only [branchBitQ, Bool.false_eq_true, ↓reduceIte]; constructor <;> linarith

lemma branchBitQ_true_bounds {q : ℚ} (h0 : 0 < q) (h1 : q < 1) :
    1 / 2 < branchBitQ true q ∧ branchBitQ true q < 1 := by
  simp only [branchBitQ, ↓reduceIte]; constructor <;> linarith

lemma branchWordQ_bounds (w : List Bool) {q : ℚ} (h0 : 0 < q) (h1 : q < 1) :
    0 < branchWordQ w q ∧ branchWordQ w q < 1 := by
  induction w generalizing q with
  | nil => exact ⟨h0, h1⟩
  | cons b w ih =>
    cases b
    · have hb := branchBitQ_false_bounds h0 h1
      exact ih hb.1 (by linarith [hb.2])
    · have hb := branchBitQ_true_bounds h0 h1
      exact ih (by linarith [hb.1]) hb.2

lemma branchWord_strictMono_or_anti (w : List Bool) {a b : ℝ} (hab : a < b) :
    (branchParity w = false → branchWord w a < branchWord w b) ∧
    (branchParity w = true → branchWord w b < branchWord w a) := by
  have ha := branchWord_affine w a
  have hb := branchWord_affine w b
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ w.length := by positivity
  constructor <;> intro hp
  · rw [ha, hb]; simp only [branchSign, hp, Bool.false_eq_true, ↓reduceIte, one_mul]
    linarith [div_lt_div_of_pos_right hab h2pos]
  · rw [ha, hb]; simp only [branchSign, hp, ↓reduceIte, neg_mul, one_mul, neg_div]
    have : a / (2 : ℝ) ^ w.length < b / (2 : ℝ) ^ w.length := div_lt_div_of_pos_right hab h2pos
    linarith

lemma branchWord_mem_Ioo_iff (w : List Bool) {a b t : ℝ} (hab : a < b) :
    branchWord w t ∈ Ioo (min (branchWord w a) (branchWord w b))
        (max (branchWord w a) (branchWord w b)) ↔ t ∈ Ioo a b := by
  have hma := branchWord_strictMono_or_anti w hab
  have ha := branchWord_affine w a
  have hb := branchWord_affine w b
  have ht := branchWord_affine w t
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ w.length := by positivity
  cases hp : branchParity w
  · have hlt := hma.1 hp
    rw [min_eq_left (le_of_lt hlt), max_eq_right (le_of_lt hlt)]
    simp only [mem_Ioo, ha, hb, ht, branchSign, hp, Bool.false_eq_true, ↓reduceIte, one_mul]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(div_lt_div_iff_of_pos_right h2pos).mp (by linarith),
        (div_lt_div_iff_of_pos_right h2pos).mp (by linarith)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith [div_lt_div_of_pos_right h1 h2pos],
        by linarith [div_lt_div_of_pos_right h2 h2pos]⟩
  · have hlt := hma.2 hp
    rw [min_eq_right (le_of_lt hlt), max_eq_left (le_of_lt hlt)]
    simp only [mem_Ioo, ha, hb, ht, branchSign, hp, ↓reduceIte, neg_mul, one_mul, neg_div]
    constructor
    · rintro ⟨h1, h2⟩
      have h1' : t / (2 : ℝ) ^ w.length < b / (2 : ℝ) ^ w.length := by linarith
      have h2' : a / (2 : ℝ) ^ w.length < t / (2 : ℝ) ^ w.length := by linarith
      exact ⟨(div_lt_div_iff_of_pos_right h2pos).mp h2',
        (div_lt_div_iff_of_pos_right h2pos).mp h1'⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith [div_lt_div_of_pos_right h2 h2pos],
        by linarith [div_lt_div_of_pos_right h1 h2pos]⟩

/-- A canonical section `U = (k, a, b)` of `BH` with rational endpoints strictly on one side of `1/2`. -/
structure BHSec where
  level : ℕ
  lo : ℚ
  hi : ℚ
  hlo : 0 < lo
  hlt : lo < hi
  hhi : hi < 1
  hside : hi < 1 / 2 ∨ 1 / 2 < lo

instance : Countable BHSec := by
  refine Function.Injective.countable (f := fun U : BHSec => (U.level, U.lo, U.hi)) ?_
  rintro ⟨k₁, a₁, b₁, _, _, _, _⟩ ⟨k₂, a₂, b₂, _, _, _, _⟩ h
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl⟩; rfl

namespace BHSec

lemma eq_of_fields {U V : BHSec} (h1 : U.level = V.level) (h2 : U.lo = V.lo)
    (h3 : U.hi = V.hi) : U = V := by
  cases U; cases V; simp only [BHSec.mk.injEq]; exact ⟨h1, h2, h3⟩

def carrier (U : BHSec) : Set BH := {x | (U.lo : ℝ) < x.1 U.level ∧ x.1 U.level < (U.hi : ℝ)}
def bar (U : BHSec) : Set BH := {x | (U.lo : ℝ) ≤ x.1 U.level ∧ x.1 U.level ≤ (U.hi : ℝ)}
def end0 (U : BHSec) : Set BH := {x | x.1 U.level = (U.lo : ℝ)}
def end1 (U : BHSec) : Set BH := {x | x.1 U.level = (U.hi : ℝ)}
def ends (U : BHSec) : Set BH := U.end0 ∪ U.end1

lemma lo_pos_real (U : BHSec) : (0 : ℝ) < U.lo := by exact_mod_cast U.hlo
lemma lo_lt_hi_real (U : BHSec) : (U.lo : ℝ) < U.hi := by exact_mod_cast U.hlt
lemma hi_lt_one_real (U : BHSec) : (U.hi : ℝ) < 1 := by exact_mod_cast U.hhi

lemma isOpen_carrier (U : BHSec) : IsOpen U.carrier :=
  (isOpen_lt continuous_const (continuous_bhCoord U.level)).inter
    (isOpen_lt (continuous_bhCoord U.level) continuous_const)

lemma isClosed_bar (U : BHSec) : IsClosed U.bar :=
  (isClosed_le continuous_const (continuous_bhCoord U.level)).inter
    (isClosed_le (continuous_bhCoord U.level) continuous_const)

lemma carrier_subset_bar (U : BHSec) : U.carrier ⊆ U.bar :=
  fun _ hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩

lemma bar_eq_carrier_union_ends (U : BHSec) : U.bar = U.carrier ∪ U.ends := by
  ext x
  simp only [bar, carrier, ends, end0, end1, mem_union, mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    rcases eq_or_lt_of_le h1 with h1' | h1'
    · exact Or.inr (Or.inl h1'.symm)
    · rcases eq_or_lt_of_le h2 with h2' | h2'
      · exact Or.inr (Or.inr h2')
      · exact Or.inl ⟨h1', h2'⟩
  · rintro (⟨h1, h2⟩ | h1 | h2)
    · exact ⟨le_of_lt h1, le_of_lt h2⟩
    · exact ⟨le_of_eq h1.symm, le_of_lt (by rw [h1]; exact U.lo_lt_hi_real)⟩
    · exact ⟨le_of_lt (by rw [h2]; exact U.lo_lt_hi_real), le_of_eq h2⟩

lemma disjoint_end0_end1 (U : BHSec) : Disjoint U.end0 U.end1 :=
  disjoint_left.mpr fun _ h0 h1 => ne_of_lt U.lo_lt_hi_real (h0.symm.trans h1)

lemma disjoint_carrier_ends (U : BHSec) : Disjoint U.carrier U.ends := by
  rw [disjoint_left]
  rintro x ⟨h1, h2⟩ (h0 | h3)
  · exact ne_of_gt h1 h0
  · exact ne_of_lt h2 h3

lemma closure_carrier (U : BHSec) : closure U.carrier = U.bar := by
  apply Subset.antisymm
  · exact closure_minimal U.carrier_subset_bar U.isClosed_bar
  · intro x hx
    rw [mem_closure_iff_nhds]
    intro O hO
    have hc : Continuous (fun t : Icc (0 : ℝ) 1 => chart U.level (bitsAt U.level x) t) :=
      (continuous_chart U.level).comp (continuous_const.prodMk continuous_id)
    let tx : Icc (0 : ℝ) 1 := ⟨x.1 U.level, bh_mem_Icc x U.level⟩
    have hpre : (fun t : Icc (0 : ℝ) 1 => chart U.level (bitsAt U.level x) t) ⁻¹' O ∈ 𝓝 tx :=
      hc.continuousAt.preimage_mem_nhds (by simpa [tx, chart_bitsAt] using hO)
    rw [Metric.mem_nhds_iff] at hpre
    rcases hpre with ⟨ε, hε, hball⟩
    let δ := min (ε / 2) (((U.hi : ℝ) - (U.lo : ℝ)) / 4)
    have hδ : 0 < δ := lt_min (by positivity) (by linarith [U.lo_lt_hi_real])
    have hδ_le_l : δ ≤ ε / 2 := min_le_left _ _
    have hδ_le_r : δ ≤ ((U.hi : ℝ) - (U.lo : ℝ)) / 4 := min_le_right _ _
    let s : ℝ := if x.1 U.level < ((U.lo : ℝ) + (U.hi : ℝ)) / 2 then x.1 U.level + δ else x.1 U.level - δ
    have hs_ioo : s ∈ Ioo (U.lo : ℝ) (U.hi : ℝ) := by
      dsimp only [s]
      split_ifs with hlt
      · exact ⟨by linarith [hx.1], by linarith⟩
      · exact ⟨by linarith, by linarith [hx.2]⟩
    have hs_icc : s ∈ Icc (0 : ℝ) 1 :=
      ⟨le_of_lt (lt_trans U.lo_pos_real hs_ioo.1), le_of_lt (lt_trans hs_ioo.2 U.hi_lt_one_real)⟩
    let ts : Icc (0 : ℝ) 1 := ⟨s, hs_icc⟩
    have hdist : dist ts tx < ε := by
      change |s - x.1 U.level| < ε
      dsimp only [s]
      split_ifs
      · rw [add_sub_cancel_left, abs_of_pos hδ]; linarith
      · rw [sub_sub_cancel_left, abs_neg, abs_of_pos hδ]; linarith
    refine ⟨chart U.level (bitsAt U.level x) ts, hball hdist, ?_⟩
    simp only [carrier, mem_ofPred_eq, chart_coord_self, ts]; exact hs_ioo

lemma bar_mem_Ioo (U : BHSec) {x : BH} (hx : x ∈ U.bar) : x.1 U.level ∈ Ioo (0 : ℝ) 1 :=
  ⟨lt_of_lt_of_le U.lo_pos_real hx.1, lt_of_le_of_lt hx.2 U.hi_lt_one_real⟩

lemma ne_bhZero_of_mem_bar (U : BHSec) {x : BH} (hx : x ∈ U.bar) : x ≠ bhZero := by
  intro h; subst h; have := (U.bar_mem_Ioo hx).1; simp [bhZero] at this

/-- The strip of `U` indexed by a finite binary word `w`. -/
def strip (U : BHSec) (w : List Bool) : BHSec :=
  { level := U.level + w.length
    lo := min (branchWordQ w U.lo) (branchWordQ w U.hi)
    hi := max (branchWordQ w U.lo) (branchWordQ w U.hi)
    hlo := lt_min (branchWordQ_bounds w U.hlo (lt_trans U.hlt U.hhi)).1
      (branchWordQ_bounds w (lt_trans U.hlo U.hlt) U.hhi).1
    hlt := by
      have hne : branchWordQ w U.lo ≠ branchWordQ w U.hi := by
        intro heq
        have hr : branchWord w (U.lo : ℝ) = branchWord w (U.hi : ℝ) := by
          rw [← branchWordQ_cast, ← branchWordQ_cast, heq]
        have hma := branchWord_strictMono_or_anti w U.lo_lt_hi_real
        cases hp : branchParity w
        · exact ne_of_lt (hma.1 hp) hr
        · exact ne_of_gt (hma.2 hp) hr
      exact min_lt_max.mpr hne
    hhi := max_lt (branchWordQ_bounds w U.hlo (lt_trans U.hlt U.hhi)).2
      (branchWordQ_bounds w (lt_trans U.hlo U.hlt) U.hhi).2
    hside := by
      cases hw : w.reverse with
      | nil =>
        have hw' : w = [] := List.reverse_eq_nil_iff.mp hw
        subst hw'
        simpa [branchWordQ, min_eq_left (le_of_lt U.hlt), max_eq_right (le_of_lt U.hlt)] using U.hside
      | cons b wr =>
        have hw' : w = wr.reverse ++ [b] := by
          have := congrArg List.reverse hw; simpa using this
        rw [hw', branchWordQ_append, branchWordQ_append]
        have hlo_b := branchWordQ_bounds wr.reverse U.hlo (lt_trans U.hlt U.hhi)
        have hhi_b := branchWordQ_bounds wr.reverse (lt_trans U.hlo U.hlt) U.hhi
        cases b
        · left; exact max_lt (branchBitQ_false_bounds hlo_b.1 hlo_b.2).2
            (branchBitQ_false_bounds hhi_b.1 hhi_b.2).2
        · right; exact lt_min (branchBitQ_true_bounds hlo_b.1 hlo_b.2).1
            (branchBitQ_true_bounds hhi_b.1 hhi_b.2).1 }

lemma strip_nil (U : BHSec) : U.strip [] = U := by
  cases U with
  | mk k a b hlo hlt hhi hside =>
    simp [strip, branchWordQ, min_eq_left (le_of_lt hlt), max_eq_right (le_of_lt hlt)]

lemma strip_append (U : BHSec) (w₁ w₂ : List Bool) :
    (U.strip w₁).strip w₂ = U.strip (w₁ ++ w₂) := by
  have h1 : (U.strip w₁).level + w₂.length = U.level + (w₁ ++ w₂).length := by
    simp [strip, Nat.add_assoc]
  have h2 : min (branchWordQ w₂ (U.strip w₁).lo) (branchWordQ w₂ (U.strip w₁).hi) =
      min (branchWordQ (w₁ ++ w₂) U.lo) (branchWordQ (w₁ ++ w₂) U.hi) := by
    simp only [strip, branchWordQ_append]
    rcases le_total (branchWordQ w₁ U.lo) (branchWordQ w₁ U.hi) with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h, min_comm]
  have h3 : max (branchWordQ w₂ (U.strip w₁).lo) (branchWordQ w₂ (U.strip w₁).hi) =
      max (branchWordQ (w₁ ++ w₂) U.lo) (branchWordQ (w₁ ++ w₂) U.hi) := by
    simp only [strip, branchWordQ_append]
    rcases le_total (branchWordQ w₁ U.lo) (branchWordQ w₁ U.hi) with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h, max_comm]
  exact BHSec.eq_of_fields h1 h2 h3

/-- Cylinder predicate: `ε` starts with finite word `w`. -/
def inCyl (w : List Bool) (ε : ℕ → Bool) : Prop :=
  ∀ i (hi : i < w.length), ε i = w[i]

lemma inCyl_nil (ε : ℕ → Bool) : inCyl [] ε := fun _ hi => absurd hi (Nat.not_lt_zero _)

lemma inCyl_prepend (w : List Bool) (η : ℕ → Bool) : inCyl w (prependWord w η) := by
  intro i hi; simp [prependWord, hi]

lemma inCyl_append (w₁ w₂ : List Bool) (ε : ℕ → Bool) :
    inCyl (w₁ ++ w₂) ε ↔ inCyl w₁ ε ∧ inCyl w₂ (fun j => ε (w₁.length + j)) := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun j hj => ?_⟩
    · have := h i (by simp; omega)
      simpa [List.getElem_append_left hi] using this
    · have := h (w₁.length + j) (by simp; omega)
      simpa [List.getElem_append_right (Nat.le_add_right w₁.length j)] using this
  · rintro ⟨h1, h2⟩ i hi
    by_cases hlt : i < w₁.length
    · rw [List.getElem_append_left hlt]; exact h1 i hlt
    · rw [List.getElem_append_right (not_lt.mp hlt)]
      have := h2 (i - w₁.length) (by simp at hi; omega)
      dsimp only at this
      rwa [Nat.add_sub_cancel' (not_lt.mp hlt)] at this

lemma mem_strip_carrier_iff (U : BHSec) (w : List Bool) (x : BH) :
    x ∈ (U.strip w).carrier ↔ x ∈ U.carrier ∧ inCyl w (bitsAt U.level x) := by
  constructor
  · intro hx
    have hlo_r : ((U.strip w).lo : ℝ) = min (branchWord w U.lo) (branchWord w U.hi) := by
      simp [strip, branchWordQ_cast]
    have hhi_r : ((U.strip w).hi : ℝ) = max (branchWord w U.lo) (branchWord w U.hi) := by
      simp [strip, branchWordQ_cast]
    have hxk : x.1 (U.level + w.length) ∈
        Ioo (min (branchWord w U.lo) (branchWord w U.hi))
          (max (branchWord w U.lo) (branchWord w U.hi)) := by
      rw [← hlo_r, ← hhi_r]; exact hx
    -- Show x.1 U.level ∈ Ioo U.lo U.hi and x.1 (U.level + w.length) = branchWord w (x.1 U.level)
    have hsurj : ∃ t ∈ Ioo (U.lo : ℝ) (U.hi : ℝ), branchWord w t = x.1 (U.level + w.length) := by
      have ha := branchWord_affine w U.lo
      have hb := branchWord_affine w U.hi
      have h2pos : (0 : ℝ) < (2 : ℝ) ^ w.length := by positivity
      let t := branchSign w * (2 : ℝ) ^ w.length * (x.1 (U.level + w.length) - branchWord w 0)
      have hs2 : branchSign w * branchSign w = 1 := by
        cases hp : branchParity w <;> simp [branchSign, hp]
      have hbw : branchWord w t = x.1 (U.level + w.length) := by
        rw [branchWord_affine w t]
        have hne : (2 : ℝ) ^ w.length ≠ 0 := ne_of_gt h2pos
        dsimp only [t]
        calc branchWord w 0 + branchSign w * (branchSign w * 2 ^ w.length *
              (x.1 (U.level + w.length) - branchWord w 0)) / 2 ^ w.length
          = branchWord w 0 + (branchSign w * branchSign w) *
              (x.1 (U.level + w.length) - branchWord w 0) * (2 ^ w.length / 2 ^ w.length) := by ring
          _ = x.1 (U.level + w.length) := by rw [hs2, div_self hne]; ring
      have ht_ioo : t ∈ Ioo (U.lo : ℝ) (U.hi : ℝ) :=
        (branchWord_mem_Ioo_iff w U.lo_lt_hi_real).mp (by rwa [hbw])
      exact ⟨t, ht_ioo, hbw⟩
    rcases hsurj with ⟨t, ht, hbw⟩
    have ht_icc : t ∈ Icc (0 : ℝ) 1 :=
      ⟨le_of_lt (lt_trans U.lo_pos_real ht.1), le_of_lt (lt_trans ht.2 U.hi_lt_one_real)⟩
    have ht_ioo : t ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_trans U.lo_pos_real ht.1, lt_trans ht.2 U.hi_lt_one_real⟩
    have hx_eq : x = chart U.level (prependWord w (bitsAt (U.level + w.length) x)) ⟨t, ht_icc⟩ := by
      rw [← chart_shift_word U.level w (bitsAt (U.level + w.length) x) ⟨t, ht_icc⟩]
      have hsub : (⟨branchWord w t, branchWord_mem_Icc w ht_icc⟩ : Icc (0 : ℝ) 1) =
          ⟨x.1 (U.level + w.length), bh_mem_Icc x (U.level + w.length)⟩ := Subtype.ext hbw
      rw [hsub, chart_bitsAt]
    rw [hx_eq]
    refine ⟨?_, ?_⟩
    · simp only [carrier, mem_ofPred_eq, chart_coord_self]; exact ht
    · rw [bitsAt_chart U.level _ ht_ioo]; exact inCyl_prepend w _
  · rintro ⟨hxU, hcyl⟩
    have ht_ioo : x.1 U.level ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_trans U.lo_pos_real hxU.1, lt_trans hxU.2 U.hi_lt_one_real⟩
    have hprep : bitsAt U.level x = prependWord w (bitsAt (U.level + w.length) x) := by
      funext n
      unfold prependWord
      by_cases hn : n < w.length
      · rw [dif_pos hn]; exact hcyl n hn
      · rw [dif_neg hn]
        simp only [bitsAt]
        apply congrArg (fun k => decide (1 / 2 < x.1 k)); omega
    have hch : x = chart (U.level + w.length) (bitsAt (U.level + w.length) x)
        ⟨branchWord w (x.1 U.level), branchWord_mem_Icc w (bh_mem_Icc x U.level)⟩ := by
      have h1 := chart_shift_word U.level w (bitsAt (U.level + w.length) x)
        ⟨x.1 U.level, bh_mem_Icc x U.level⟩
      rw [← hprep, chart_bitsAt] at h1
      exact h1.symm
    have hcoord : x.1 (U.level + w.length) = branchWord w (x.1 U.level) := by
      conv_lhs => rw [hch]; rw [chart_coord_self]
    have hlo_r : ((U.strip w).lo : ℝ) = min (branchWord w U.lo) (branchWord w U.hi) := by
      simp [strip, branchWordQ_cast]
    have hhi_r : ((U.strip w).hi : ℝ) = max (branchWord w U.lo) (branchWord w U.hi) := by
      simp [strip, branchWordQ_cast]
    change (U.strip w).lo < x.1 (U.level + w.length) ∧ x.1 (U.level + w.length) < (U.strip w).hi
    rw [hlo_r, hhi_r, hcoord]
    exact (branchWord_mem_Ioo_iff w U.lo_lt_hi_real).mpr hxU

lemma strip_carrier_subset (U : BHSec) (w : List Bool) : (U.strip w).carrier ⊆ U.carrier :=
  fun x hx => ((U.mem_strip_carrier_iff w x).mp hx).1

lemma mem_strip_bar_iff (U : BHSec) (w : List Bool) (x : BH) :
    x ∈ (U.strip w).bar ↔ x ∈ U.bar ∧ inCyl w (bitsAt U.level x) := by
  constructor
  · intro hx
    have hlo_r : ((U.strip w).lo : ℝ) = min (branchWord w U.lo) (branchWord w U.hi) := by
      simp [strip, branchWordQ_cast]
    have hhi_r : ((U.strip w).hi : ℝ) = max (branchWord w U.lo) (branchWord w U.hi) := by
      simp [strip, branchWordQ_cast]
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ w.length := by positivity
    let t := branchSign w * (2 : ℝ) ^ w.length * (x.1 (U.level + w.length) - branchWord w 0)
    have hs2 : branchSign w * branchSign w = 1 := by
      cases hp : branchParity w <;> simp [branchSign, hp]
    have hbw : branchWord w t = x.1 (U.level + w.length) := by
      rw [branchWord_affine w t]
      have hne : (2 : ℝ) ^ w.length ≠ 0 := ne_of_gt h2pos
      dsimp only [t]
      calc branchWord w 0 + branchSign w * (branchSign w * 2 ^ w.length *
            (x.1 (U.level + w.length) - branchWord w 0)) / 2 ^ w.length
        = branchWord w 0 + (branchSign w * branchSign w) *
            (x.1 (U.level + w.length) - branchWord w 0) * (2 ^ w.length / 2 ^ w.length) := by ring
        _ = x.1 (U.level + w.length) := by rw [hs2, div_self hne]; ring
    have ht_icc_ab : t ∈ Icc (U.lo : ℝ) (U.hi : ℝ) := by
      have hx' : branchWord w t ∈ Icc (min (branchWord w U.lo) (branchWord w U.hi))
          (max (branchWord w U.lo) (branchWord w U.hi)) := by
        rw [hbw, ← hlo_r, ← hhi_r]; exact hx
      have hma := branchWord_strictMono_or_anti w U.lo_lt_hi_real
      have ha := branchWord_affine w U.lo
      have hb := branchWord_affine w U.hi
      have ht' := branchWord_affine w t
      cases hp : branchParity w
      · rw [min_eq_left (le_of_lt (hma.1 hp)), max_eq_right (le_of_lt (hma.1 hp))] at hx'
        simp only [mem_Icc, ha, hb, ht', branchSign, hp, Bool.false_eq_true, ↓reduceIte, one_mul] at hx'
        exact ⟨(div_le_div_iff_of_pos_right h2pos).mp (by linarith),
          (div_le_div_iff_of_pos_right h2pos).mp (by linarith)⟩
      · rw [min_eq_right (le_of_lt (hma.2 hp)), max_eq_left (le_of_lt (hma.2 hp))] at hx'
        simp only [mem_Icc, ha, hb, ht', branchSign, hp, ↓reduceIte, neg_mul, one_mul, neg_div] at hx'
        exact ⟨(div_le_div_iff_of_pos_right h2pos).mp (by linarith),
          (div_le_div_iff_of_pos_right h2pos).mp (by linarith)⟩
    have ht_ioo : t ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_lt_of_le U.lo_pos_real ht_icc_ab.1, lt_of_le_of_lt ht_icc_ab.2 U.hi_lt_one_real⟩
    have ht_icc : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt ht_ioo.1, le_of_lt ht_ioo.2⟩
    have hx_eq : x = chart U.level (prependWord w (bitsAt (U.level + w.length) x)) ⟨t, ht_icc⟩ := by
      rw [← chart_shift_word U.level w (bitsAt (U.level + w.length) x) ⟨t, ht_icc⟩]
      have hsub : (⟨branchWord w t, branchWord_mem_Icc w ht_icc⟩ : Icc (0 : ℝ) 1) =
          ⟨x.1 (U.level + w.length), bh_mem_Icc x (U.level + w.length)⟩ := Subtype.ext hbw
      rw [hsub, chart_bitsAt]
    rw [hx_eq]
    refine ⟨?_, ?_⟩
    · simp only [bar, mem_ofPred_eq, chart_coord_self]; exact ht_icc_ab
    · rw [bitsAt_chart U.level _ ht_ioo]; exact inCyl_prepend w _
  · rintro ⟨hxU, hcyl⟩
    have hprep : bitsAt U.level x = prependWord w (bitsAt (U.level + w.length) x) := by
      funext n; unfold prependWord
      by_cases hn : n < w.length
      · rw [dif_pos hn]; exact hcyl n hn
      · rw [dif_neg hn]; simp only [bitsAt]; apply congrArg (fun k => decide (1 / 2 < x.1 k)); omega
    have hch : x = chart (U.level + w.length) (bitsAt (U.level + w.length) x)
        ⟨branchWord w (x.1 U.level), branchWord_mem_Icc w (bh_mem_Icc x U.level)⟩ := by
      have h1 := chart_shift_word U.level w (bitsAt (U.level + w.length) x)
        ⟨x.1 U.level, bh_mem_Icc x U.level⟩
      rw [← hprep, chart_bitsAt] at h1
      exact h1.symm
    have hcoord : x.1 (U.level + w.length) = branchWord w (x.1 U.level) := by
      conv_lhs => rw [hch]; rw [chart_coord_self]
    have hlo_r : ((U.strip w).lo : ℝ) = min (branchWord w U.lo) (branchWord w U.hi) := by
      simp [strip, branchWordQ_cast]
    have hhi_r : ((U.strip w).hi : ℝ) = max (branchWord w U.lo) (branchWord w U.hi) := by
      simp [strip, branchWordQ_cast]
    change (U.strip w).lo ≤ x.1 (U.level + w.length) ∧ x.1 (U.level + w.length) ≤ (U.strip w).hi
    rw [hlo_r, hhi_r, hcoord]
    have hma := branchWord_strictMono_or_anti w U.lo_lt_hi_real
    have ha := branchWord_affine w U.lo
    have hb := branchWord_affine w U.hi
    have ht' := branchWord_affine w (x.1 U.level)
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ w.length := by positivity
    cases hp : branchParity w
    · rw [min_eq_left (le_of_lt (hma.1 hp)), max_eq_right (le_of_lt (hma.1 hp))]
      simp only [ha, hb, ht', branchSign, hp, Bool.false_eq_true, ↓reduceIte, one_mul]
      exact ⟨by linarith [div_le_div_of_nonneg_right hxU.1 (le_of_lt h2pos)],
        by linarith [div_le_div_of_nonneg_right hxU.2 (le_of_lt h2pos)]⟩
    · rw [min_eq_right (le_of_lt (hma.2 hp)), max_eq_left (le_of_lt (hma.2 hp))]
      simp only [ha, hb, ht', branchSign, hp, ↓reduceIte, neg_mul, one_mul, neg_div]
      exact ⟨by linarith [div_le_div_of_nonneg_right hxU.2 (le_of_lt h2pos)],
        by linarith [div_le_div_of_nonneg_right hxU.1 (le_of_lt h2pos)]⟩

lemma strip_ends_subset (U : BHSec) (w : List Bool) :
    (branchParity w = false → (U.strip w).end0 ⊆ U.end0 ∧ (U.strip w).end1 ⊆ U.end1) ∧
    (branchParity w = true → (U.strip w).end0 ⊆ U.end1 ∧ (U.strip w).end1 ⊆ U.end0) := by
  have hma := branchWord_strictMono_or_anti w U.lo_lt_hi_real
  have hlo_r : ((U.strip w).lo : ℝ) = min (branchWord w U.lo) (branchWord w U.hi) := by
    simp [strip, branchWordQ_cast]
  have hhi_r : ((U.strip w).hi : ℝ) = max (branchWord w U.lo) (branchWord w U.hi) := by
    simp [strip, branchWordQ_cast]
  have htent : ∀ x : BH, x.1 U.level = tent^[w.length] (x.1 (U.level + w.length)) :=
    fun x => (bh_tent_iterate x U.level w.length).symm
  have hlo_icc : (U.lo : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt U.lo_pos_real, le_of_lt (lt_trans U.lo_lt_hi_real U.hi_lt_one_real)⟩
  have hhi_icc : (U.hi : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt (lt_trans U.lo_pos_real U.lo_lt_hi_real), le_of_lt U.hi_lt_one_real⟩
  constructor <;> intro hp
  · have hlt := hma.1 hp
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · change x.1 U.level = U.lo; rw [htent x]
      have hx' : x.1 (U.level + w.length) = branchWord w U.lo := by
        have hx0 : x.1 (U.level + w.length) = (U.strip w).lo := hx
        rw [hx0, hlo_r, min_eq_left (le_of_lt hlt)]
      rw [hx', tent_iterate_branchWord w hlo_icc]
    · change x.1 U.level = U.hi; rw [htent x]
      have hx' : x.1 (U.level + w.length) = branchWord w U.hi := by
        have hx0 : x.1 (U.level + w.length) = (U.strip w).hi := hx
        rw [hx0, hhi_r, max_eq_right (le_of_lt hlt)]
      rw [hx', tent_iterate_branchWord w hhi_icc]
  · have hlt := hma.2 hp
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · change x.1 U.level = U.hi; rw [htent x]
      have hx' : x.1 (U.level + w.length) = branchWord w U.hi := by
        have hx0 : x.1 (U.level + w.length) = (U.strip w).lo := hx
        rw [hx0, hlo_r, min_eq_right (le_of_lt hlt)]
      rw [hx', tent_iterate_branchWord w hhi_icc]
    · change x.1 U.level = U.lo; rw [htent x]
      have hx' : x.1 (U.level + w.length) = branchWord w U.lo := by
        have hx0 : x.1 (U.level + w.length) = (U.strip w).hi := hx
        rw [hx0, hhi_r, max_eq_left (le_of_lt hlt)]
      rw [hx', tent_iterate_branchWord w hlo_icc]

/-- `V` is a block of `U` (same level, sub-interval). -/
def IsBlock (V U : BHSec) : Prop :=
  V.level = U.level ∧ U.lo ≤ V.lo ∧ V.hi ≤ U.hi

lemma isBlock_refl (U : BHSec) : IsBlock U U := ⟨rfl, le_rfl, le_rfl⟩

lemma isBlock_trans {W V U : BHSec} (h1 : IsBlock W V) (h2 : IsBlock V U) : IsBlock W U :=
  ⟨h1.1.trans h2.1, le_trans h2.2.1 h1.2.1, le_trans h1.2.2 h2.2.2⟩

lemma isBlock_carrier_subset {V U : BHSec} (h : IsBlock V U) : V.carrier ⊆ U.carrier := by
  intro x hx
  have h1 : (U.lo : ℝ) ≤ V.lo := by exact_mod_cast h.2.1
  have h2 : (V.hi : ℝ) ≤ U.hi := by exact_mod_cast h.2.2
  rw [carrier, ← h.1]
  exact ⟨lt_of_le_of_lt h1 hx.1, lt_of_lt_of_le hx.2 h2⟩

lemma isBlock_bar_subset {V U : BHSec} (h : IsBlock V U) : V.bar ⊆ U.bar := by
  intro x hx
  have h1 : (U.lo : ℝ) ≤ V.lo := by exact_mod_cast h.2.1
  have h2 : (V.hi : ℝ) ≤ U.hi := by exact_mod_cast h.2.2
  rw [bar, ← h.1]
  exact ⟨le_trans h1 hx.1, le_trans hx.2 h2⟩

lemma isBlock_strip {V U : BHSec} (h : IsBlock V U) (w : List Bool) :
    IsBlock (V.strip w) (U.strip w) := by
  refine ⟨by simp [strip, h.1], ?_, ?_⟩
  · simp only [strip]
    have hma := branchWord_strictMono_or_anti w U.lo_lt_hi_real
    have h1 : (U.lo : ℝ) ≤ V.lo := by exact_mod_cast h.2.1
    have h2 : (V.hi : ℝ) ≤ U.hi := by exact_mod_cast h.2.2
    have hvlt := V.lo_lt_hi_real
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ w.length := by positivity
    cases hp : branchParity w
    · have hlo : branchWord w U.lo ≤ branchWord w V.lo := by
        rw [branchWord_affine w U.lo, branchWord_affine w V.lo]
        simp only [branchSign, hp, Bool.false_eq_true, ↓reduceIte, one_mul]
        linarith [div_le_div_of_nonneg_right h1 (le_of_lt h2pos)]
      have hhi : branchWord w V.lo ≤ branchWord w V.hi := le_of_lt ((branchWord_strictMono_or_anti w hvlt).1 hp)
      have hU : branchWord w U.lo ≤ branchWord w U.hi := le_of_lt (hma.1 hp)
      rw [← Rat.cast_le (K := ℝ), Rat.cast_min, Rat.cast_min,
        branchWordQ_cast, branchWordQ_cast, branchWordQ_cast, branchWordQ_cast,
        min_eq_left hU, min_eq_left hhi]
      exact hlo
    · have hlo : branchWord w U.hi ≤ branchWord w V.hi := by
        rw [branchWord_affine w U.hi, branchWord_affine w V.hi]
        simp only [branchSign, hp, ↓reduceIte, neg_mul, one_mul, neg_div]
        linarith [div_le_div_of_nonneg_right h2 (le_of_lt h2pos)]
      have hhi : branchWord w V.hi ≤ branchWord w V.lo := le_of_lt ((branchWord_strictMono_or_anti w hvlt).2 hp)
      have hU : branchWord w U.hi ≤ branchWord w U.lo := le_of_lt (hma.2 hp)
      rw [← Rat.cast_le (K := ℝ), Rat.cast_min, Rat.cast_min,
        branchWordQ_cast, branchWordQ_cast, branchWordQ_cast, branchWordQ_cast,
        min_eq_right hU, min_eq_right hhi]
      exact hlo
  · simp only [strip]
    have hma := branchWord_strictMono_or_anti w U.lo_lt_hi_real
    have h1 : (U.lo : ℝ) ≤ V.lo := by exact_mod_cast h.2.1
    have h2 : (V.hi : ℝ) ≤ U.hi := by exact_mod_cast h.2.2
    have hvlt := V.lo_lt_hi_real
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ w.length := by positivity
    cases hp : branchParity w
    · have hhi : branchWord w V.hi ≤ branchWord w U.hi := by
        rw [branchWord_affine w V.hi, branchWord_affine w U.hi]
        simp only [branchSign, hp, Bool.false_eq_true, ↓reduceIte, one_mul]
        linarith [div_le_div_of_nonneg_right h2 (le_of_lt h2pos)]
      have hV : branchWord w V.lo ≤ branchWord w V.hi := le_of_lt ((branchWord_strictMono_or_anti w hvlt).1 hp)
      have hU : branchWord w U.lo ≤ branchWord w U.hi := le_of_lt (hma.1 hp)
      rw [← Rat.cast_le (K := ℝ), Rat.cast_max, Rat.cast_max,
        branchWordQ_cast, branchWordQ_cast, branchWordQ_cast, branchWordQ_cast,
        max_eq_right hU, max_eq_right hV]
      exact hhi
    · have hhi : branchWord w V.lo ≤ branchWord w U.lo := by
        rw [branchWord_affine w V.lo, branchWord_affine w U.lo]
        simp only [branchSign, hp, ↓reduceIte, neg_mul, one_mul, neg_div]
        linarith [div_le_div_of_nonneg_right h1 (le_of_lt h2pos)]
      have hV : branchWord w V.hi ≤ branchWord w V.lo := le_of_lt ((branchWord_strictMono_or_anti w hvlt).2 hp)
      have hU : branchWord w U.hi ≤ branchWord w U.lo := le_of_lt (hma.2 hp)
      rw [← Rat.cast_le (K := ℝ), Rat.cast_max, Rat.cast_max,
        branchWordQ_cast, branchWordQ_cast, branchWordQ_cast, branchWordQ_cast,
        max_eq_left hU, max_eq_left hV]
      exact hhi

/-- Every subsection `W ⊆ U` has `U.level ≤ W.level` and is a block of a unique strip of `U`. -/
lemma subsec_eq_block_of_strip {W U : BHSec} (hsub : W.carrier ⊆ U.carrier) :
    U.level ≤ W.level ∧ ∃ w : List Bool, w.length = W.level - U.level ∧ IsBlock W (U.strip w) := by
  have hle : U.level ≤ W.level := by
    by_contra hlt; push Not at hlt
    let d := U.level - W.level
    have hd : 0 < d := by omega
    let t : ℝ := ((W.lo : ℝ) + (W.hi : ℝ)) / 2
    have ht_W : t ∈ Ioo (W.lo : ℝ) (W.hi : ℝ) := by
      dsimp only [t]; exact ⟨by linarith [W.lo_lt_hi_real], by linarith [W.lo_lt_hi_real]⟩
    have ht_ioo : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_trans W.lo_pos_real ht_W.1, lt_trans ht_W.2 W.hi_lt_one_real⟩
    have ht_icc : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt ht_ioo.1, le_of_lt ht_ioo.2⟩
    let w0 := List.replicate d false
    let w1 := List.replicate d true
    have hU_eq : W.level + d = U.level := by omega
    let x0 : BH := chart W.level (prependWord w0 (fun _ => false)) ⟨t, ht_icc⟩
    let x1 : BH := chart W.level (prependWord w1 (fun _ => false)) ⟨t, ht_icc⟩
    have hx0U : x0 ∈ U.carrier := hsub (by simp only [x0, carrier, mem_ofPred_eq, chart_coord_self]; exact ht_W)
    have hx1U : x1 ∈ U.carrier := hsub (by simp only [x1, carrier, mem_ofPred_eq, chart_coord_self]; exact ht_W)
    have hx0_lt : x0.1 U.level < 1 / 2 := by
      have h := chartAux_mem_Ioo (prependWord w0 (fun _ => false)) ht_ioo (d - 1)
      have hcoord : x0.1 U.level = branchBit false (chartAux (prependWord w0 (fun _ => false)) t (d - 1)) := by
        rw [← hU_eq, show W.level + d = W.level + ((d - 1) + 1) by omega, chart_coord_add, chartAux]
        congr 1; simp [prependWord, w0, show d - 1 < d by omega]
      rw [hcoord]; exact (branchBit_false_mem_Ioo h).2
    have hx1_gt : 1 / 2 < x1.1 U.level := by
      have h := chartAux_mem_Ioo (prependWord w1 (fun _ => false)) ht_ioo (d - 1)
      have hcoord : x1.1 U.level = branchBit true (chartAux (prependWord w1 (fun _ => false)) t (d - 1)) := by
        rw [← hU_eq, show W.level + d = W.level + ((d - 1) + 1) by omega, chart_coord_add, chartAux]
        congr 1; simp [prependWord, w1, show d - 1 < d by omega]
      rw [hcoord]; exact (branchBit_true_mem_Ioo h).1
    rcases U.hside with hside | hside
    · have hUhi : (U.hi : ℝ) < 1 / 2 := by simpa using (Rat.cast_lt (K := ℝ)).mpr hside
      linarith [hx1U.2]
    · have hUlo : (1 / 2 : ℝ) < U.lo := by simpa using (Rat.cast_lt (K := ℝ)).mpr hside
      linarith [hx0U.1]
  refine ⟨hle, ?_⟩
  let m := W.level - U.level
  let t0 : ℝ := ((W.lo : ℝ) + (W.hi : ℝ)) / 2
  have ht0_W : t0 ∈ Ioo (W.lo : ℝ) (W.hi : ℝ) := by
    dsimp only [t0]; exact ⟨by linarith [W.lo_lt_hi_real], by linarith [W.lo_lt_hi_real]⟩
  have ht0_icc : t0 ∈ Icc (0 : ℝ) 1 :=
    ⟨le_of_lt (lt_trans W.lo_pos_real ht0_W.1), le_of_lt (lt_trans ht0_W.2 W.hi_lt_one_real)⟩
  let x0 : BH := chart W.level (fun _ => false) ⟨t0, ht0_icc⟩
  let w : List Bool := List.ofFn (fun i : Fin m => bitsAt U.level x0 i)
  have hwlen : w.length = m := List.length_ofFn
  refine ⟨w, hwlen, ?_⟩
  -- Every point of W.carrier lies in (U.strip w).carrier!
  have hW_in_strip : W.carrier ⊆ (U.strip w).carrier := by
    intro x hx
    rw [U.mem_strip_carrier_iff w x]
    refine ⟨hsub hx, fun i hi => ?_⟩
    rw [hwlen] at hi
    simp only [w, List.getElem_ofFn]
    -- Compare bitsAt U.level x i and bitsAt U.level x0 i via connectedness of (W.lo, W.hi)
    have hnohalf : ∀ s ∈ Ioo (W.lo : ℝ) (W.hi : ℝ), tent^[m - (i + 1)] s ≠ 1 / 2 := by
      intro s hs hhalf
      have hs_icc : s ∈ Icc (0 : ℝ) 1 :=
        ⟨le_of_lt (lt_trans W.lo_pos_real hs.1), le_of_lt (lt_trans hs.2 W.hi_lt_one_real)⟩
      let y := chart W.level (fun _ => false) ⟨s, hs_icc⟩
      have hyU : y ∈ U.carrier := hsub (by simp only [y, carrier, mem_ofPred_eq, chart_coord_self]; exact hs)
      have hcoord : y.1 U.level = tent^[m] s := by
        rw [← bh_tent_iterate_of_le y hle, chart_coord_self]
      have h01 : tent^[m] s = 0 ∨ tent^[m] s = 1 := by
        have hm_eq : m = (m - (i + 1)) + 1 + (i) := by omega
        have hstep1 : tent^[(m - (i + 1)) + 1] s = 1 := by
          rw [Function.iterate_succ_apply', hhalf, tent_half]
        have h01_iter : ∀ r, tent^[r] 1 = 0 ∨ tent^[r] 1 = 1 := by
          intro r; cases r with
          | zero => right; rfl
          | succ r =>
            left
            rw [Function.iterate_succ_apply, tent_one]
            clear hstep1 hcoord hyU y hs_icc hs hhalf
            induction r with
            | zero => rfl
            | succ r ihr => rw [Function.iterate_succ_apply', ihr, tent_zero]
        have heq : tent^[m] s = tent^[i] (tent^[(m - (i + 1)) + 1] s) := by
          rw [← Function.iterate_add_apply, show i + (m - (i + 1) + 1) = m by omega]
        rw [heq, hstep1]; exact h01_iter i
      change (U.lo : ℝ) < y.1 U.level ∧ y.1 U.level < U.hi at hyU
      rw [hcoord] at hyU
      rcases h01 with h0 | h1
      · linarith [hyU.1, U.lo_pos_real]
      · linarith [hyU.2, U.hi_lt_one_real]
    have hval_x : x.1 (U.level + i + 1) = tent^[m - (i + 1)] (x.1 W.level) := by
      have hle' : U.level + i + 1 ≤ W.level := by omega
      have h := bh_tent_iterate_of_le x hle'
      rw [show W.level - (U.level + i + 1) = m - (i + 1) by omega] at h
      exact h.symm
    have hval_x0 : x0.1 (U.level + i + 1) = tent^[m - (i + 1)] t0 := by
      have hle' : U.level + i + 1 ≤ W.level := by omega
      have h := bh_tent_iterate_of_le x0 hle'
      rw [chart_coord_self, show W.level - (U.level + i + 1) = m - (i + 1) by omega] at h
      dsimp only at h
      exact h.symm
    have hconnI : IsPreconnected (tent^[m - (i + 1)] '' Ioo (W.lo : ℝ) (W.hi : ℝ)) :=
      isPreconnected_Ioo.image _ (continuous_tent.iterate _).continuousOn
    have hnohalf' : (1 / 2 : ℝ) ∉ tent^[m - (i + 1)] '' Ioo (W.lo : ℝ) (W.hi : ℝ) := by
      rintro ⟨s, hs, hsh⟩; exact hnohalf s hs hsh
    unfold bitsAt
    rw [hval_x, hval_x0]
    by_cases hgt : 1 / 2 < tent^[m - (i + 1)] t0
    · have hgtx : 1 / 2 < tent^[m - (i + 1)] (x.1 W.level) := by
        by_contra hle'; push Not at hle'
        exact hnohalf' (hconnI.Icc_subset ⟨x.1 W.level, hx, rfl⟩ ⟨t0, ht0_W, rfl⟩ ⟨hle', le_of_lt hgt⟩)
      rw [decide_eq_true hgtx, decide_eq_true hgt]
    · have hltx : ¬ 1 / 2 < tent^[m - (i + 1)] (x.1 W.level) := by
        intro hgtx
        exact hnohalf' (hconnI.Icc_subset ⟨t0, ht0_W, rfl⟩ ⟨x.1 W.level, hx, rfl⟩ ⟨not_lt.mp hgt, le_of_lt hgtx⟩)
      rw [decide_eq_false hltx, decide_eq_false hgt]
  refine ⟨by simp [strip, hwlen, m]; omega, ?_, ?_⟩
  · have hbar : W.bar ⊆ (U.strip w).bar := by
      rw [← W.closure_carrier, ← (U.strip w).closure_carrier]; exact closure_mono hW_in_strip
    have hmem : chart W.level (fun _ => false) ⟨W.lo, le_of_lt W.lo_pos_real,
        le_of_lt (lt_trans W.lo_lt_hi_real W.hi_lt_one_real)⟩ ∈ (U.strip w).bar :=
      hbar (by simp [bar, chart_coord_self, le_of_lt W.lo_lt_hi_real])
    have h1 := hmem.1
    rw [show (U.strip w).level = W.level by simp [strip, hwlen, m]; omega, chart_coord_self] at h1
    dsimp only at h1
    exact_mod_cast h1
  · have hbar : W.bar ⊆ (U.strip w).bar := by
      rw [← W.closure_carrier, ← (U.strip w).closure_carrier]; exact closure_mono hW_in_strip
    have hmem : chart W.level (fun _ => false) ⟨W.hi, le_of_lt (lt_trans W.lo_pos_real W.lo_lt_hi_real),
        le_of_lt W.hi_lt_one_real⟩ ∈ (U.strip w).bar :=
      hbar (by simp [bar, chart_coord_self, le_of_lt W.lo_lt_hi_real])
    have h2 := hmem.2
    rw [show (U.strip w).level = W.level by simp [strip, hwlen, m]; omega, chart_coord_self] at h2
    dsimp only at h2
    exact_mod_cast h2

/-- The unique cylinder word `w` of `W ⊆ U` inside `U`. -/
def subsecWord {W U : BHSec} (hsub : W.carrier ⊆ U.carrier) : List Bool :=
  (subsec_eq_block_of_strip hsub).2.choose

lemma subsecWord_spec {W U : BHSec} (hsub : W.carrier ⊆ U.carrier) :
    (subsecWord hsub).length = W.level - U.level ∧ IsBlock W (U.strip (subsecWord hsub)) :=
  (subsec_eq_block_of_strip hsub).2.choose_spec

lemma strip_carrier_disjoint_of_incomp (U : BHSec) {w₁ w₂ : List Bool}
    (h : ∀ ε : ℕ → Bool, ¬ (inCyl w₁ ε ∧ inCyl w₂ ε)) :
    Disjoint (U.strip w₁).bar (U.strip w₂).bar := by
  rw [disjoint_left]
  intro x h1 h2
  exact h (bitsAt U.level x) ⟨((U.mem_strip_bar_iff w₁ x).mp h1).2, ((U.mem_strip_bar_iff w₂ x).mp h2).2⟩

/-- Explicit finite partition of cylinder `w` against cylinder `v`: every returned word
    extends `w`, the cylinders pairwise disjointly partition `inCyl w`, and every returned
    cylinder is either contained in `inCyl v` or disjoint from `inCyl v`. -/
def splitCylSuffix (w : List Bool) : List Bool → List (List Bool)
  | [] => [w]
  | b :: rest => (w ++ [!b]) :: splitCylSuffix (w ++ [b]) rest

def splitCyl (w v : List Bool) : List (List Bool) :=
  if w.length < v.length ∧ w = v.take w.length then
    splitCylSuffix w (v.drop w.length)
  else [w]

lemma splitCylSuffix_mem_inCyl (w r : List Bool) (ε : ℕ → Bool) :
    inCyl w ε ↔ ∃ u ∈ splitCylSuffix w r, inCyl u ε := by
  induction r generalizing w with
  | nil => simp [splitCylSuffix]
  | cons b rest ih =>
    simp only [splitCylSuffix, List.mem_cons, exists_eq_or_imp, ← ih]
    constructor
    · intro hw
      cases hε : ε w.length
      · cases b
        · right
          rw [inCyl_append]
          exact ⟨hw, fun i hi => by
            have hi0 : i = 0 := by simp at hi; omega
            subst hi0; simpa using hε⟩
        · left
          rw [inCyl_append]
          exact ⟨hw, fun i hi => by
            have hi0 : i = 0 := by simp at hi; omega
            subst hi0; simpa using hε⟩
      · cases b
        · left
          rw [inCyl_append]
          exact ⟨hw, fun i hi => by
            have hi0 : i = 0 := by simp at hi; omega
            subst hi0; simpa using hε⟩
        · right
          rw [inCyl_append]
          exact ⟨hw, fun i hi => by
            have hi0 : i = 0 := by simp at hi; omega
            subst hi0; simpa using hε⟩
    · rintro (h | h) <;> exact ((inCyl_append _ _ _).mp h).1

lemma splitCylSuffix_disjoint (w r : List Bool) :
    (splitCylSuffix w r).Pairwise (fun u₁ u₂ => ∀ ε, ¬ (inCyl u₁ ε ∧ inCyl u₂ ε)) := by
  induction r generalizing w with
  | nil => simp [splitCylSuffix]
  | cons b rest ih =>
    simp only [splitCylSuffix, List.pairwise_cons]
    refine ⟨fun u hu ε ⟨h1, h2⟩ => ?_, ih (w ++ [b])⟩
    have h2' : inCyl (w ++ [b]) ε := (splitCylSuffix_mem_inCyl (w ++ [b]) rest ε).mpr ⟨u, hu, h2⟩
    have e1 := ((inCyl_append _ _ _).mp h1).2 0 (by simp)
    have e2 := ((inCyl_append _ _ _).mp h2').2 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at e1 e2
    rw [e1] at e2; cases b <;> simp at e2

lemma splitCylSuffix_decides (w r : List Bool) :
    ∀ u ∈ splitCylSuffix w r,
      (u = w ++ r) ∨ (∀ ε, ¬ (inCyl u ε ∧ inCyl (w ++ r) ε)) := by
  induction r generalizing w with
  | nil => intro u hu; simp [splitCylSuffix] at hu; left; simpa using hu
  | cons b rest ih =>
    intro u hu
    simp only [splitCylSuffix, List.mem_cons] at hu
    rcases hu with rfl | hu
    · right
      intro ε ⟨h1, h2⟩
      have e1 := ((inCyl_append _ _ _).mp h1).2 0 (by simp)
      have e2 := ((inCyl_append _ _ _).mp h2).2 0 (by simp)
      simp only [Nat.add_zero, List.getElem_cons_zero] at e1 e2
      rw [e1] at e2; cases b <;> simp at e2
    · rcases ih (w ++ [b]) u hu with rfl | hdisj
      · left; simp
      · right; simpa [List.append_assoc] using hdisj

lemma splitCylSuffix_extends (w r : List Bool) :
    ∀ u ∈ splitCylSuffix w r, ∃ s : List Bool, u = w ++ s := by
  induction r generalizing w with
  | nil => intro u hu; simp [splitCylSuffix] at hu; exact ⟨[], by simpa using hu⟩
  | cons b rest ih =>
    intro u hu
    simp only [splitCylSuffix, List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact ⟨[!b], rfl⟩
    · rcases ih (w ++ [b]) u hu with ⟨s, rfl⟩
      exact ⟨b :: s, by simp⟩

lemma splitCyl_spec (w v : List Bool) :
    (∀ ε, inCyl w ε ↔ ∃ u ∈ splitCyl w v, inCyl u ε) ∧
    (splitCyl w v).Pairwise (fun u₁ u₂ => ∀ ε, ¬ (inCyl u₁ ε ∧ inCyl u₂ ε)) ∧
    (∀ u ∈ splitCyl w v, ∃ s : List Bool, u = w ++ s) ∧
    (∀ u ∈ splitCyl w v, (∀ ε, inCyl u ε → inCyl v ε) ∨ (∀ ε, ¬ (inCyl u ε ∧ inCyl v ε))) := by
  unfold splitCyl
  split_ifs with h
  · rcases h with ⟨hlt, htake⟩
    have hwr : w ++ v.drop w.length = v := by
      conv_rhs => rw [← List.take_append_drop w.length v]
      rw [← htake]
    refine ⟨splitCylSuffix_mem_inCyl w (v.drop w.length),
      splitCylSuffix_disjoint w (v.drop w.length),
      splitCylSuffix_extends w (v.drop w.length), fun u hu => ?_⟩
    rcases splitCylSuffix_decides w (v.drop w.length) u hu with rfl | hdisj
    · left; rw [hwr]; exact fun _ h => h
    · right; rwa [hwr] at hdisj
  · refine ⟨by simp, by simp, fun u hu => ⟨[], by simp at hu; simp [hu]⟩, fun u hu => ?_⟩
    simp only [List.mem_singleton] at hu; subst u
    by_cases hle : v.length ≤ w.length
    · by_cases hpref : v = w.take v.length
      · left
        intro ε hε i hi
        have h1 := hε i (lt_of_lt_of_le hi hle)
        have h2 := congrArg (fun l => l[i]?) hpref
        rw [List.getElem?_eq_getElem hi, List.getElem?_take_of_lt hi,
          List.getElem?_eq_getElem (lt_of_lt_of_le hi hle)] at h2
        exact h1.trans (Option.some.inj h2).symm
      · right
        intro ε ⟨hw, hv⟩
        apply hpref
        apply List.ext_getElem (by simp [hle])
        intro i hi1 hi2
        have h1 := hv i hi1
        have h2 := hw i (lt_of_lt_of_le hi1 hle)
        simp [← h1, h2]
    · push Not at hle
      have hne : w ≠ v.take w.length := fun heq => h ⟨hle, heq⟩
      right
      intro ε ⟨hw, hv⟩
      apply hne
      apply List.ext_getElem (by simp [le_of_lt hle])
      intro i hi1 hi2
      have h1 := hw i hi1
      have h2 := hv i (lt_trans hi1 hle)
      simp [← h1, h2]

/-- Basis property of `BHSec` on `BH \ {bhZero}`. -/
lemma exists_sec_bar_subset_of_mem_open {p : BH} (hp : p ≠ bhZero) {O : Set BH}
    (hO : IsOpen O) (hpO : p ∈ O) (k₀ : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ U : BHSec, k₀ ≤ U.level ∧ (U.hi : ℝ) - (U.lo : ℝ) < ε ∧ p ∈ U.carrier ∧ U.bar ⊆ O := by
  have hex_pos : ∃ n₀, 0 < p.1 n₀ := by
    by_contra hall; push Not at hall
    apply hp; apply Subtype.ext; funext n
    exact le_antisymm (hall n) (bh_mem_Icc p n).1
  rcases hex_pos with ⟨n₀, hn₀⟩
  have hioo_ge : ∀ m ≥ n₀ + 1, p.1 m ∈ Ioo (0 : ℝ) 1 := by
    intro m hm
    obtain ⟨j, rfl⟩ : ∃ j, m = n₀ + 1 + j := ⟨m - (n₀ + 1), by omega⟩
    clear hm
    induction j with
    | zero =>
      have ht := bh_tent p n₀
      have hmem := bh_mem_Icc p (n₀ + 1)
      have hne0 : p.1 (n₀ + 1) ≠ 0 := fun h => by rw [h, tent_zero] at ht; linarith
      have hne1 : p.1 (n₀ + 1) ≠ 1 := fun h => by rw [h, tent_one] at ht; linarith
      exact ⟨lt_of_le_of_ne hmem.1 (Ne.symm hne0), lt_of_le_of_ne hmem.2 hne1⟩
    | succ j ih =>
      have ht := bh_tent p (n₀ + 1 + j)
      have hmem := bh_mem_Icc p (n₀ + 1 + (j + 1))
      rw [show n₀ + 1 + (j + 1) = n₀ + 1 + j + 1 by omega] at hmem ⊢
      have hne0 : p.1 (n₀ + 1 + j + 1) ≠ 0 := fun h => by rw [h, tent_zero] at ht; linarith [ih.1]
      have hne1 : p.1 (n₀ + 1 + j + 1) ≠ 1 := fun h => by rw [h, tent_one] at ht; linarith [ih.1]
      exact ⟨lt_of_le_of_ne hmem.1 (Ne.symm hne0), lt_of_le_of_ne hmem.2 hne1⟩
  have hne_half_ge : ∀ m ≥ n₀ + 2, p.1 m ≠ 1 / 2 := by
    intro m hm hhalf
    have ht := bh_tent p (m - 1)
    rw [show m - 1 + 1 = m by omega, hhalf, tent_half] at ht
    linarith [(hioo_ge (m - 1) (by omega)).2]
  have hnhds : O ∈ 𝓝 p := hO.mem_nhds hpO
  rw [nhds_induced] at hnhds
  rcases hnhds with ⟨V, hV, hVO⟩
  rw [nhds_pi, Filter.mem_pi'] at hV
  rcases hV with ⟨I, t, ht, hIt⟩
  have hball : ∀ n ∈ I, ∃ r : ℝ, 0 < r ∧ Metric.ball (p.1 n) r ⊆ t n :=
    fun n _ => Metric.mem_nhds_iff.mp (ht n)
  let rad : ℕ → ℝ := fun n => if h : n ∈ I then (hball n h).choose else 1
  have hrad_pos : ∀ n, 0 < rad n := by
    intro n; unfold rad; split_ifs with h
    · exact (hball n h).choose_spec.1
    · norm_num
  let I' := insert 0 I
  let rmin : ℝ := I'.inf' (Finset.insert_nonempty 0 I) rad
  have hrmin_pos : 0 < rmin := (Finset.lt_inf'_iff _).mpr fun n _ => hrad_pos n
  let k := max (max k₀ (n₀ + 2)) (I.sup id)
  have hk_ioo : p.1 k ∈ Ioo (0 : ℝ) 1 := hioo_ge k (by omega)
  have hk_nh : p.1 k ≠ 1 / 2 := hne_half_ge k (by omega)
  let gap : ℝ := min (min (ε / 2) (rmin / (2 : ℝ) ^ k))
    (min (min (p.1 k) (1 - p.1 k)) |p.1 k - 1 / 2|)
  have hgap_pos : 0 < gap := by
    apply lt_min
    · exact lt_min (by positivity) (by positivity)
    · exact lt_min (lt_min hk_ioo.1 (by linarith [hk_ioo.2])) (abs_pos.mpr (sub_ne_zero.mpr hk_nh))
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show p.1 k - gap / 2 < p.1 k by linarith)
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show p.1 k < p.1 k + gap / 2 by linarith)
  have hgap_le_e : gap ≤ ε / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hgap_le_r : gap ≤ rmin / (2 : ℝ) ^ k := le_trans (min_le_left _ _) (min_le_right _ _)
  have hgap_le_0 : gap ≤ p.1 k := le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hgap_le_1 : gap ≤ 1 - p.1 k := le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hgap_le_h : gap ≤ |p.1 k - 1 / 2| := le_trans (min_le_right _ _) (min_le_right _ _)
  have ha_pos : (0 : ℚ) < a := by exact_mod_cast (by linarith : (0 : ℝ) < a)
  have hab : a < b := by exact_mod_cast (lt_trans ha2 hb1)
  have hb_lt1 : b < 1 := by exact_mod_cast (by linarith : (b : ℝ) < 1)
  have hside : b < 1 / 2 ∨ 1 / 2 < a := by
    rcases lt_or_gt_of_ne hk_nh with hlt | hgt
    · left
      have : |p.1 k - 1 / 2| = 1 / 2 - p.1 k := by rw [abs_of_neg (by linarith)]; ring
      have hb_r : (b : ℝ) < ((1 / 2 : ℚ) : ℝ) := by norm_num; linarith
      exact Rat.cast_lt.mp hb_r
    · right
      have : |p.1 k - 1 / 2| = p.1 k - 1 / 2 := abs_of_pos (by linarith)
      have ha_r : ((1 / 2 : ℚ) : ℝ) < (a : ℝ) := by norm_num; linarith
      exact Rat.cast_lt.mp ha_r
  let U : BHSec := ⟨k, a, b, ha_pos, hab, hb_lt1, hside⟩
  refine ⟨U, le_trans (le_max_left _ _) (le_max_left _ _), by linarith, ⟨ha2, hb1⟩, fun y hy => ?_⟩
  apply hVO; apply hIt
  intro n hn
  have hnm : n ≤ k := le_trans (Finset.le_sup (f := id) hn) (le_max_right _ _)
  have hrad_le : rmin ≤ rad n := Finset.inf'_le (s := I') rad (Finset.mem_insert_of_mem hn)
  have hrad_eq : rad n = (hball n hn).choose := dif_pos hn
  apply (hball n hn).choose_spec.2
  rw [Metric.mem_ball, Real.dist_eq]
  have hdist : |y.1 n - p.1 n| < rmin := by
    rw [← bh_tent_iterate_of_le y hnm, ← bh_tent_iterate_of_le p hnm]
    have hlip := tent_iterate_lipschitz (k - n) (y.1 k) (p.1 k)
    have h2le : (2 : ℝ) ^ (k - n) ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) (Nat.sub_le k n)
    have hydiff : |y.1 k - p.1 k| < gap := by
      rw [abs_lt]; constructor <;> linarith [hy.1, hy.2, ha1, hb2]
    have hmul : (2 : ℝ) ^ k * gap ≤ rmin := (le_div_iff₀' (by positivity)).mp hgap_le_r
    have hstrict : (2 : ℝ) ^ (k - n) * |y.1 k - p.1 k| < (2 : ℝ) ^ k * gap := by
      calc (2 : ℝ) ^ (k - n) * |y.1 k - p.1 k| ≤ (2 : ℝ) ^ k * |y.1 k - p.1 k| :=
            mul_le_mul_of_nonneg_right h2le (abs_nonneg _)
        _ < (2 : ℝ) ^ k * gap := mul_lt_mul_of_pos_left hydiff (by positivity)
    linarith
  linarith

/-- Intersection of two sections decomposes into a finite list of common subsections. -/
lemma section_inter_decompose (W U : BHSec) :
    ∃ L : List BHSec,
      W.carrier ∩ U.carrier = ⋃ V ∈ L, V.carrier ∧
      ∀ V ∈ L, V.carrier ⊆ W.carrier ∧ V.carrier ⊆ U.carrier := by
  -- Helper: same-level intersection of two sections is empty or one section
  have hsame : ∀ (A B : BHSec), A.level = B.level →
      ∃ L : List BHSec, A.carrier ∩ B.carrier = ⋃ V ∈ L, V.carrier ∧
        ∀ V ∈ L, V.carrier ⊆ A.carrier ∧ V.carrier ⊆ B.carrier := by
    intro A B hlvl
    let lo' := max A.lo B.lo
    let hi' := min A.hi B.hi
    by_cases hlt : lo' < hi'
    · let V : BHSec :=
        { level := A.level
          lo := lo'
          hi := hi'
          hlo := lt_of_lt_of_le A.hlo (le_max_left _ _)
          hlt := hlt
          hhi := lt_of_le_of_lt (min_le_left _ _) A.hhi
          hside := A.hside.imp (fun h => lt_of_le_of_lt (min_le_left _ _) h)
            (fun h => lt_of_lt_of_le h (le_max_left _ _)) }
      refine ⟨[V], ?_, ?_⟩
      · ext x
        simp only [List.mem_singleton, iUnion_iUnion_eq_left, mem_inter_iff, carrier, mem_ofPred_eq,
          V, lo', hi', Rat.cast_max, Rat.cast_min, max_lt_iff, lt_min_iff, hlvl]
        tauto
      · intro V' hV'
        simp only [List.mem_singleton] at hV'; subst hV'
        refine ⟨fun x hx => ⟨lt_of_le_of_lt (by exact_mod_cast le_max_left A.lo B.lo) hx.1,
            lt_of_lt_of_le hx.2 (by exact_mod_cast min_le_left A.hi B.hi)⟩,
          fun x hx => ?_⟩
        rw [carrier, ← hlvl]
        exact ⟨lt_of_le_of_lt (by exact_mod_cast le_max_right A.lo B.lo) hx.1,
          lt_of_lt_of_le hx.2 (by exact_mod_cast min_le_right A.hi B.hi)⟩
    · refine ⟨[], ?_, by simp⟩
      ext x
      simp only [List.not_mem_nil, iUnion_false, iUnion_empty, mem_inter_iff, carrier, mem_ofPred_eq,
        mem_empty_iff_false, iff_false]
      rintro ⟨hxA, hxB⟩
      rw [← hlvl] at hxB
      have hmax : (lo' : ℝ) < x.1 A.level := by
        simp only [lo', Rat.cast_max, max_lt_iff]; exact ⟨hxA.1, hxB.1⟩
      have hmin : x.1 A.level < (hi' : ℝ) := by
        simp only [hi', Rat.cast_min, lt_min_iff]; exact ⟨hxA.2, hxB.2⟩
      exact hlt (by exact_mod_cast lt_trans hmax hmin)
  -- Helper: list of all binary words of length m
  let allWords : ℕ → List (List Bool) := fun m =>
    Nat.rec [[]] (fun _ acc => acc.map (false :: ·) ++ acc.map (true :: ·)) m
  have hallWords_len : ∀ m w, w ∈ allWords m ↔ w.length = m := by
    intro m; induction m with
    | zero => intro w; simp [allWords]
    | succ m ih =>
      intro w
      simp only [allWords, List.mem_append, List.mem_map]
      constructor
      · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) <;> simp [(ih u).mp hu]
      · intro hlen
        cases w with
        | nil => simp at hlen
        | cons b u =>
          cases b
          · left; exact ⟨u, (ih u).mpr (by simpa using hlen), rfl⟩
          · right; exact ⟨u, (ih u).mpr (by simpa using hlen), rfl⟩
  have hpart_strips : ∀ (A : BHSec) (m : ℕ),
      A.carrier = ⋃ w ∈ allWords m, (A.strip w).carrier := by
    intro A m; ext x
    simp only [mem_iUnion, exists_prop]
    constructor
    · intro hx
      let w : List Bool := List.ofFn (fun i : Fin m => bitsAt A.level x i)
      refine ⟨w, (hallWords_len m w).mpr List.length_ofFn, (A.mem_strip_carrier_iff w x).mpr ⟨hx, ?_⟩⟩
      intro i hi; simp [w]
    · rintro ⟨w, _, hx⟩; exact A.strip_carrier_subset w hx
  -- Now split on U.level ≤ W.level vs W.level < U.level
  by_cases hle : U.level ≤ W.level
  · let m := W.level - U.level
    have hpieces : ∀ w : List Bool, w.length = m →
        ∃ Lw : List BHSec, W.carrier ∩ (U.strip w).carrier = ⋃ V ∈ Lw, V.carrier ∧
          ∀ V ∈ Lw, V.carrier ⊆ W.carrier ∧ V.carrier ⊆ (U.strip w).carrier := fun w hw =>
      hsame W (U.strip w) (by simp [strip, hw, m]; omega)
    let L : List BHSec := (allWords m).flatMap fun w =>
      if hw : w.length = m then (hpieces w hw).choose else []
    refine ⟨L, ?_, ?_⟩
    · ext x
      simp only [mem_inter_iff, mem_iUnion, exists_prop]
      rw [hpart_strips U m]
      simp only [mem_iUnion, exists_prop]
      constructor
      · rintro ⟨hxW, w, hw, hxUw⟩
        have hw' : w.length = m := (hallWords_len m w).mp hw
        have hmem : x ∈ ⋃ V ∈ (hpieces w hw').choose, V.carrier := by
          rw [← (hpieces w hw').choose_spec.1]; exact ⟨hxW, hxUw⟩
        simp only [mem_iUnion, exists_prop] at hmem
        rcases hmem with ⟨V, hVL, hxV⟩
        refine ⟨V, ?_, hxV⟩
        simp only [L, List.mem_flatMap]
        exact ⟨w, hw, by rw [dif_pos hw']; exact hVL⟩
      · rintro ⟨V, hVL, hxV⟩
        simp only [L, List.mem_flatMap] at hVL
        rcases hVL with ⟨w, hw, hV'⟩
        have hw' : w.length = m := (hallWords_len m w).mp hw
        rw [dif_pos hw'] at hV'
        have hsub := (hpieces w hw').choose_spec.2 V hV'
        exact ⟨hsub.1 hxV, w, hw, hsub.2 hxV⟩
    · intro V hVL
      simp only [L, List.mem_flatMap] at hVL
      rcases hVL with ⟨w, hw, hV'⟩
      have hw' : w.length = m := (hallWords_len m w).mp hw
      rw [dif_pos hw'] at hV'
      have hsub := (hpieces w hw').choose_spec.2 V hV'
      exact ⟨hsub.1, hsub.2.trans (U.strip_carrier_subset w)⟩
  · push Not at hle
    let m := U.level - W.level
    have hpieces : ∀ w : List Bool, w.length = m →
        ∃ Lw : List BHSec, (W.strip w).carrier ∩ U.carrier = ⋃ V ∈ Lw, V.carrier ∧
          ∀ V ∈ Lw, V.carrier ⊆ (W.strip w).carrier ∧ V.carrier ⊆ U.carrier := fun w hw =>
      hsame (W.strip w) U (by simp [strip, hw, m]; omega)
    let L : List BHSec := (allWords m).flatMap fun w =>
      if hw : w.length = m then (hpieces w hw).choose else []
    refine ⟨L, ?_, ?_⟩
    · ext x
      simp only [mem_inter_iff, mem_iUnion, exists_prop]
      rw [hpart_strips W m]
      simp only [mem_iUnion, exists_prop]
      constructor
      · rintro ⟨⟨w, hw, hxWw⟩, hxU⟩
        have hw' : w.length = m := (hallWords_len m w).mp hw
        have hmem : x ∈ ⋃ V ∈ (hpieces w hw').choose, V.carrier := by
          rw [← (hpieces w hw').choose_spec.1]; exact ⟨hxWw, hxU⟩
        simp only [mem_iUnion, exists_prop] at hmem
        rcases hmem with ⟨V, hVL, hxV⟩
        refine ⟨V, ?_, hxV⟩
        simp only [L, List.mem_flatMap]
        exact ⟨w, hw, by rw [dif_pos hw']; exact hVL⟩
      · rintro ⟨V, hVL, hxV⟩
        simp only [L, List.mem_flatMap] at hVL
        rcases hVL with ⟨w, hw, hV'⟩
        have hw' : w.length = m := (hallWords_len m w).mp hw
        rw [dif_pos hw'] at hV'
        have hsub := (hpieces w hw').choose_spec.2 V hV'
        exact ⟨⟨w, hw, hsub.1 hxV⟩, hsub.2 hxV⟩
    · intro V hVL
      simp only [L, List.mem_flatMap] at hVL
      rcases hVL with ⟨w, hw, hV'⟩
      have hw' : w.length = m := (hallWords_len m w).mp hw
      rw [dif_pos hw'] at hV'
      have hsub := (hpieces w hw').choose_spec.2 V hV'
      exact ⟨hsub.1.trans (W.strip_carrier_subset w), hsub.2⟩

end BHSec

/-- A separating set of `BH`: a closed set `S` whose complement splits into two nonempty disjoint open sets. -/
def IsSepSet (S : Set BH) : Prop :=
  IsClosed S ∧ ∃ A B : Set BH, IsOpen A ∧ IsOpen B ∧ Disjoint A B ∧
    A.Nonempty ∧ B.Nonempty ∧ Sᶜ = A ∪ B

/-- Rudin's family `G(S)` of sections whose ends are separated in `U.bar \ S`. -/
def inG (S : Set BH) (U : BHSec) : Prop :=
  Disjoint S U.ends ∧
  ∃ O₀ O₁ : Set BH, IsOpen O₀ ∧ IsOpen O₁ ∧ Disjoint O₀ O₁ ∧
    U.bar \ S ⊆ O₀ ∪ O₁ ∧ U.end0 ⊆ O₀ ∧ U.end1 ⊆ O₁

lemma inG_nonempty_of_isSepSet {S : Set BH} (hS : IsSepSet S) : ∃ U : BHSec, inG S U := by
  rcases hS with ⟨_, A, B, hAo, hBo, hAB, hAne, hBne, hcov⟩
  -- Every nonempty open set in BH contains a point ≠ bhZero (since BH is connected and nontrivial).
  have hex_ne0 : ∀ {O : Set BH}, IsOpen O → O.Nonempty → ∃ p ∈ O, p ≠ bhZero := by
    intro O hO ⟨p, hp⟩
    by_cases hp0 : p = bhZero
    · subst hp0
      -- Find a small point on the 0-fiber close to bhZero
      have hnhds : O ∈ 𝓝 bhZero := hO.mem_nhds hp
      rw [nhds_induced] at hnhds
      rcases hnhds with ⟨V, hV, hVO⟩
      rw [nhds_pi, Filter.mem_pi'] at hV
      rcases hV with ⟨I, t, ht, hIt⟩
      have hball : ∀ n ∈ I, ∃ r : ℝ, 0 < r ∧ Metric.ball (0 : ℝ) r ⊆ t n :=
        fun n _ => by simpa [bhZero] using Metric.mem_nhds_iff.mp (ht n)
      let rad : ℕ → ℝ := fun n => if h : n ∈ I then (hball n h).choose else 1
      let I' := insert 0 I
      let rmin : ℝ := I'.inf' (Finset.insert_nonempty 0 I) rad
      have hrmin_pos : 0 < rmin := (Finset.lt_inf'_iff _).mpr fun n _ => by
        unfold rad; split_ifs with h; exact (hball n h).choose_spec.1; norm_num
      let s : ℝ := min (rmin / 2) (1 / 2)
      have hs_pos : 0 < s := lt_min (by positivity) (by norm_num)
      have hs_le1 : s ≤ 1 := le_trans (min_le_right _ _) (by norm_num)
      let q : BH := chart 0 (fun _ => false) ⟨s, le_of_lt hs_pos, hs_le1⟩
      have hq_val : ∀ n, q.1 n = s / (2 : ℝ) ^ n := by
        intro n
        have h0 : chartAux (fun _ => false) s n = s / (2 : ℝ) ^ n := by
          induction n with
          | zero => simp [chartAux]
          | succ n ih => simp [chartAux, branchBit, ih, pow_succ]; ring
        have := chart_coord_add 0 (fun _ => false) ⟨s, le_of_lt hs_pos, hs_le1⟩ n
        simpa [q] using this.trans h0
      refine ⟨q, hVO (hIt fun n hn => ?_), fun h => by
        have := congrArg (fun z : BH => z.1 0) h; rw [hq_val 0] at this; simp [bhZero] at this; linarith⟩
      apply (hball n hn).choose_spec.2
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, hq_val n, abs_of_pos (by positivity)]
      have hle : rmin ≤ (hball n hn).choose := by
        have h1 : rmin ≤ rad n := Finset.inf'_le (s := I') rad (Finset.mem_insert_of_mem (b := 0) hn)
        have hn' : n ∈ I := Finset.mem_coe.mp hn
        change rmin ≤ (if h : n ∈ I then (hball n h).choose else 1) at h1
        rwa [dif_pos hn'] at h1
      have h2ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
      have hsdiv : s / (2 : ℝ) ^ n ≤ s := div_le_self (le_of_lt hs_pos) h2ge1
      linarith [min_le_left (rmin / 2) (1 / 2)]
    · exact ⟨p, hp, hp0⟩
  obtain ⟨pA, hpA, hpA0⟩ := hex_ne0 hAo hAne
  obtain ⟨pB, hpB, hpB0⟩ := hex_ne0 hBo hBne
  obtain ⟨UA, _, _, _, hUA_sub⟩ := BHSec.exists_sec_bar_subset_of_mem_open hpA0 hAo hpA 0 zero_lt_one
  obtain ⟨UB, _, _, _, hUB_sub⟩ := BHSec.exists_sec_bar_subset_of_mem_open hpB0 hBo hpB 0 zero_lt_one
  let k := max UA.level UB.level
  let wA := List.replicate (k - UA.level) false
  let wB := List.replicate (k - UB.level) false
  let VA := UA.strip wA
  let VB := UB.strip wB
  have hVA_lvl : VA.level = k := by simp [VA, BHSec.strip, wA]; omega
  have hVB_lvl : VB.level = k := by simp [VB, BHSec.strip, wB]; omega
  let rA : ℚ := ((VA.lo + VA.hi) / 2) / 2
  let rB : ℚ := ((VB.lo + VB.hi) / 2) / 2
  have hrA_bounds : 0 < rA ∧ rA < 1 / 2 := by
    have h1 := VA.hlo; have h2 := VA.hlt; have h3 := VA.hhi
    dsimp only [rA]; constructor <;> linarith
  have hrB_bounds : 0 < rB ∧ rB < 1 / 2 := by
    have h1 := VB.hlo; have h2 := VB.hlt; have h3 := VB.hhi
    dsimp only [rB]; constructor <;> linarith
  have hfiberA : {x : BH | x.1 (k + 1) = (rA : ℝ)} ⊆ A := by
    intro x hx
    apply hUA_sub
    have hmemVA : x ∈ VA.bar := by
      change (VA.lo : ℝ) ≤ x.1 VA.level ∧ x.1 VA.level ≤ VA.hi
      rw [hVA_lvl, ← bh_tent x k, show x.1 (k + 1) = (rA : ℝ) from hx]
      have hle : (rA : ℝ) ≤ 1 / 2 := by simpa using (Rat.cast_le (K := ℝ)).mpr (le_of_lt hrA_bounds.2)
      rw [tent_eq_two_mul hle]
      have h2r : 2 * (rA : ℝ) = ((VA.lo : ℝ) + (VA.hi : ℝ)) / 2 := by
        have : (2 : ℚ) * rA = (VA.lo + VA.hi) / 2 := by dsimp only [rA]; ring
        exact_mod_cast this
      rw [h2r]; constructor <;> linarith [VA.lo_lt_hi_real]
    exact ((UA.mem_strip_bar_iff wA x).mp hmemVA).1
  have hfiberB : {x : BH | x.1 (k + 1) = (rB : ℝ)} ⊆ B := by
    intro x hx
    apply hUB_sub
    have hmemVB : x ∈ VB.bar := by
      change (VB.lo : ℝ) ≤ x.1 VB.level ∧ x.1 VB.level ≤ VB.hi
      rw [hVB_lvl, ← bh_tent x k, show x.1 (k + 1) = (rB : ℝ) from hx]
      have hle : (rB : ℝ) ≤ 1 / 2 := by simpa using (Rat.cast_le (K := ℝ)).mpr (le_of_lt hrB_bounds.2)
      rw [tent_eq_two_mul hle]
      have h2r : 2 * (rB : ℝ) = ((VB.lo : ℝ) + (VB.hi : ℝ)) / 2 := by
        have : (2 : ℚ) * rB = (VB.lo + VB.hi) / 2 := by dsimp only [rB]; ring
        exact_mod_cast this
      rw [h2r]; constructor <;> linarith [VB.lo_lt_hi_real]
    exact ((UB.mem_strip_bar_iff wB x).mp hmemVB).1
  have hr_ne : rA ≠ rB := by
    intro heq
    let x := chart (k + 1) (fun _ => false)
      ⟨(rA : ℝ), le_of_lt (by exact_mod_cast hrA_bounds.1), le_of_lt (by exact_mod_cast lt_trans hrA_bounds.2 (by norm_num))⟩
    have hxA : x ∈ A := hfiberA (by simp [x, chart_coord_self])
    have hxB : x ∈ B := hfiberB (by simp [x, chart_coord_self, heq])
    exact disjoint_left.mp hAB hxA hxB
  rcases lt_or_gt_of_ne hr_ne with hlt | hgt
  · let U : BHSec := ⟨k + 1, rA, rB, hrA_bounds.1, hlt, lt_trans hrB_bounds.2 (by norm_num), Or.inl hrB_bounds.2⟩
    refine ⟨U, ?_, A, B, hAo, hBo, hAB, fun x hx => by rw [← hcov]; exact hx.2, hfiberA, hfiberB⟩
    rw [disjoint_left]
    rintro x hxS (h0 | h1)
    · have hA : x ∈ A ∪ B := Or.inl (hfiberA h0); rw [← hcov] at hA; exact hA hxS
    · have hB : x ∈ A ∪ B := Or.inr (hfiberB h1); rw [← hcov] at hB; exact hB hxS
  · let U : BHSec := ⟨k + 1, rB, rA, hrB_bounds.1, hgt, lt_trans hrA_bounds.2 (by norm_num), Or.inl hrA_bounds.2⟩
    refine ⟨U, ?_, B, A, hBo, hAo, hAB.symm, fun x hx => by
        have : x ∈ Sᶜ := hx.2; rw [hcov] at this; exact this.symm, hfiberB, hfiberA⟩
    rw [disjoint_left]
    rintro x hxS (h0 | h1)
    · have hB : x ∈ A ∪ B := Or.inr (hfiberB h0); rw [← hcov] at hB; exact hB hxS
    · have hA : x ∈ A ∪ B := Or.inl (hfiberA h1); rw [← hcov] at hA; exact hA hxS

lemma inG_inter_fiber_nonempty {S : Set BH} {U : BHSec} (hU : inG S U) (ε : ℕ → Bool) :
    ∃ t : Icc (0 : ℝ) 1, t.1 ∈ Ioo (U.lo : ℝ) (U.hi : ℝ) ∧ chart U.level ε t ∈ S := by
  rcases hU with ⟨hdisj, O₀, O₁, hO₀, hO₁, hO01, hcov, hE₀, hE₁⟩
  let γ : ℝ → BH := fun t =>
    chart U.level ε ⟨max 0 (min 1 t), le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hγ_cont : Continuous γ := by
    refine (continuous_chart U.level).comp (continuous_const.prodMk ?_)
    exact Continuous.subtype_mk (continuous_const.max (continuous_const.min continuous_id)) _
  have hγ_eq : ∀ t ∈ Icc (U.lo : ℝ) (U.hi : ℝ),
      (γ t).1 U.level = t := fun t ht => by
    have h0 : 0 ≤ t := le_of_lt (lt_of_lt_of_le U.lo_pos_real ht.1)
    have h1 : t ≤ 1 := le_of_lt (lt_of_le_of_lt ht.2 U.hi_lt_one_real)
    simp [γ, chart_coord_self, min_eq_right h1, max_eq_right h0]
  by_contra hno; push Not at hno
  have hmiss : ∀ t ∈ Icc (U.lo : ℝ) (U.hi : ℝ), γ t ∉ S := by
    intro t ht hS
    rcases eq_or_lt_of_le ht.1 with rfl | h1
    · exact disjoint_left.mp hdisj hS (Or.inl (hγ_eq _ ht))
    · rcases eq_or_lt_of_le ht.2 with rfl | h2
      · exact disjoint_left.mp hdisj hS (Or.inr (hγ_eq _ ht))
      · have h0 : 0 ≤ t := le_of_lt (lt_trans U.lo_pos_real h1)
        have h1' : t ≤ 1 := le_of_lt (lt_trans h2 U.hi_lt_one_real)
        have heq : γ t = chart U.level ε ⟨t, h0, h1'⟩ := by
          dsimp only [γ]; congr 1; apply Subtype.ext; simp [min_eq_right h1', max_eq_right h0]
        rw [heq] at hS
        exact hno ⟨t, h0, h1'⟩ ⟨h1, h2⟩ hS
  have hsub : γ '' Icc (U.lo : ℝ) (U.hi : ℝ) ⊆ O₀ ∪ O₁ := by
    rintro _ ⟨t, ht, rfl⟩
    apply hcov
    exact ⟨⟨by rw [hγ_eq t ht]; exact ht.1, by rw [hγ_eq t ht]; exact ht.2⟩, hmiss t ht⟩
  have hconn : IsPreconnected (γ '' Icc (U.lo : ℝ) (U.hi : ℝ)) :=
    isPreconnected_Icc.image γ hγ_cont.continuousOn
  have h0mem : γ U.lo ∈ (γ '' Icc (U.lo : ℝ) (U.hi : ℝ)) ∩ O₀ :=
    ⟨⟨U.lo, ⟨le_rfl, le_of_lt U.lo_lt_hi_real⟩, rfl⟩, hE₀ (hγ_eq U.lo ⟨le_rfl, le_of_lt U.lo_lt_hi_real⟩)⟩
  have h1mem : γ U.hi ∈ (γ '' Icc (U.lo : ℝ) (U.hi : ℝ)) ∩ O₁ :=
    ⟨⟨U.hi, ⟨le_of_lt U.lo_lt_hi_real, le_rfl⟩, rfl⟩, hE₁ (hγ_eq U.hi ⟨le_of_lt U.lo_lt_hi_real, le_rfl⟩)⟩
  have hinter := hconn O₀ O₁ hO₀ hO₁ hsub ⟨_, h0mem⟩ ⟨_, h1mem⟩
  rcases hinter with ⟨z, _, hz0, hz1⟩
  exact disjoint_left.mp hO01 hz0 hz1

lemma inG_strip {S : Set BH} {U : BHSec} (hU : inG S U) (w : List Bool) : inG S (U.strip w) := by
  rcases hU with ⟨hdisj, O₀, O₁, hO₀, hO₁, hO01, hcov, hE₀, hE₁⟩
  have hbar_sub : (U.strip w).bar ⊆ U.bar := fun x hx => ((U.mem_strip_bar_iff w x).mp hx).1
  have hends := U.strip_ends_subset w
  cases hp : branchParity w
  · obtain ⟨he0, he1⟩ := hends.1 hp
    refine ⟨disjoint_left.mpr fun x hxS hxE => disjoint_left.mp hdisj hxS (hxE.imp (fun h => he0 h) (fun h => he1 h)),
      O₀, O₁, hO₀, hO₁, hO01, fun x hx => hcov ⟨hbar_sub hx.1, hx.2⟩, he0.trans hE₀, he1.trans hE₁⟩
  · obtain ⟨he0, he1⟩ := hends.2 hp
    refine ⟨disjoint_left.mpr fun x hxS hxE => disjoint_left.mp hdisj hxS (hxE.imp (fun h => he0 h) (fun h => he1 h) |>.symm),
      O₁, O₀, hO₁, hO₀, hO01.symm, fun x hx => (hcov ⟨hbar_sub hx.1, hx.2⟩).symm, he0.trans hE₁, he1.trans hE₀⟩

lemma inG_of_block {S : Set BH} {U V : BHSec} (hS : IsClosed S) (hU : inG S U)
    (hblk : BHSec.IsBlock U V) :
    IsSepSet (S ∩ U.bar) ∧ inG (S ∩ U.bar) V := by
  rcases hU with ⟨hdisj, O₀_raw, O₁_raw, hO₀r, hO₁r, hO01r, hcovr, hE₀r, hE₁r⟩
  let O₀ : Set BH := O₀_raw \ S
  let O₁ : Set BH := O₁_raw \ S
  have hO₀ : IsOpen O₀ := hO₀r.sdiff hS
  have hO₁ : IsOpen O₁ := hO₁r.sdiff hS
  have hO01 : Disjoint O₀ O₁ := hO01r.mono sdiff_subset sdiff_subset
  have hcov : U.bar \ S ⊆ O₀ ∪ O₁ := fun x hx =>
    (hcovr hx).imp (fun h => ⟨h, hx.2⟩) (fun h => ⟨h, hx.2⟩)
  have hE₀ : U.end0 ⊆ O₀ := fun x hx => ⟨hE₀r hx, fun hxS => disjoint_left.mp hdisj hxS (Or.inl hx)⟩
  have hE₁ : U.end1 ⊆ O₁ := fun x hx => ⟨hE₁r hx, fun hxS => disjoint_left.mp hdisj hxS (Or.inr hx)⟩
  let D' : Set BH := {x | x.1 U.level < (U.lo : ℝ)} ∪ ({x | x.1 U.level < (U.hi : ℝ)} ∩ O₀)
  let E' : Set BH := {x | (U.hi : ℝ) < x.1 U.level} ∪ ({x | (U.lo : ℝ) < x.1 U.level} ∩ O₁)
  have hD'o : IsOpen D' :=
    (isOpen_lt (continuous_bhCoord U.level) continuous_const).union
      ((isOpen_lt (continuous_bhCoord U.level) continuous_const).inter hO₀)
  have hE'o : IsOpen E' :=
    (isOpen_lt continuous_const (continuous_bhCoord U.level)).union
      ((isOpen_lt continuous_const (continuous_bhCoord U.level)).inter hO₁)
  have hDE' : Disjoint D' E' := by
    rw [disjoint_left]
    rintro x (h1 | ⟨h1, hx0⟩) (h2 | ⟨h2, hx1⟩)
    · exact absurd (lt_trans (show x.1 U.level < U.lo from h1) U.lo_lt_hi_real)
        (not_lt_of_gt (show (U.hi : ℝ) < x.1 U.level from h2))
    · exact not_lt_of_gt (show x.1 U.level < U.lo from h1) (show (U.lo : ℝ) < x.1 U.level from h2)
    · exact not_lt_of_gt (show (U.hi : ℝ) < x.1 U.level from h2) (show x.1 U.level < U.hi from h1)
    · exact disjoint_left.mp hO01 hx0 hx1
  have hcov' : (S ∩ U.bar)ᶜ = D' ∪ E' := by
    ext x
    simp only [mem_compl_iff, mem_inter_iff, not_and, mem_union]
    constructor
    · intro hx
      rcases lt_or_ge (x.1 U.level) (U.lo : ℝ) with hlt | hge
      · exact Or.inl (Or.inl hlt)
      · rcases lt_or_ge (U.hi : ℝ) (x.1 U.level) with hgt | hle
        · exact Or.inr (Or.inl hgt)
        · have hbar : x ∈ U.bar := ⟨hge, hle⟩
          have hxnotS : x ∉ S := fun hS' => hx hS' hbar
          rcases hcov ⟨hbar, hxnotS⟩ with hx0 | hx1
          · have hlt_hi : x.1 U.level < (U.hi : ℝ) :=
              lt_of_le_of_ne hle fun heq => disjoint_left.mp hO01 hx0 (hE₁ heq)
            exact Or.inl (Or.inr ⟨hlt_hi, hx0⟩)
          · have hgt_lo : (U.lo : ℝ) < x.1 U.level :=
              lt_of_le_of_ne hge fun heq => disjoint_left.mp hO01 (hE₀ heq.symm) hx1
            exact Or.inr (Or.inr ⟨hgt_lo, hx1⟩)
    · rintro ((h1 | ⟨_, hx0⟩) | (h2 | ⟨_, hx1⟩)) hS' hbar
      · exact not_lt_of_ge hbar.1 h1
      · exact hx0.2 hS'
      · exact not_lt_of_ge hbar.2 h2
      · exact hx1.2 hS'
  have hD'ne : D'.Nonempty := ⟨chart U.level (fun _ => false) ⟨0, le_rfl, zero_le_one⟩,
    Or.inl (by simp [chart_coord_self, U.lo_pos_real])⟩
  have hE'ne : E'.Nonempty := ⟨chart U.level (fun _ => false) ⟨1, zero_le_one, le_rfl⟩,
    Or.inl (by simp [chart_coord_self, U.hi_lt_one_real])⟩
  have hVE0 : V.end0 ⊆ D' := by
    intro x hx
    have hVlo : (V.lo : ℝ) ≤ U.lo := by exact_mod_cast hblk.2.1
    have hxe : x.1 U.level = V.lo := by rw [hblk.1]; exact hx
    rcases eq_or_lt_of_le hVlo with heq | hlt
    · exact Or.inr ⟨show x.1 U.level < U.hi by linarith [U.lo_lt_hi_real],
        hE₀ (show x.1 U.level = U.lo by rw [hxe, heq])⟩
    · exact Or.inl (show x.1 U.level < U.lo by linarith)
  have hVE1 : V.end1 ⊆ E' := by
    intro x hx
    have hVhi : (U.hi : ℝ) ≤ V.hi := by exact_mod_cast hblk.2.2
    have hxe : x.1 U.level = V.hi := by rw [hblk.1]; exact hx
    rcases eq_or_lt_of_le hVhi with heq | hlt
    · exact Or.inr ⟨show (U.lo : ℝ) < x.1 U.level by linarith [U.lo_lt_hi_real],
        hE₁ (show x.1 U.level = U.hi by rw [hxe, ← heq])⟩
    · exact Or.inl (show (U.hi : ℝ) < x.1 U.level by linarith)
  refine ⟨⟨hS.inter U.isClosed_bar, D', E', hD'o, hE'o, hDE', hD'ne, hE'ne, hcov'⟩, ?_,
    D', E', hD'o, hE'o, hDE', fun x hx => by rw [← hcov']; exact hx.2, hVE0, hVE1⟩
  rw [disjoint_left]
  rintro x hxS (h0 | h1)
  · have hmem : x ∈ D' ∪ E' := Or.inl (hVE0 h0)
    rw [← hcov'] at hmem; exact hmem hxS
  · have hmem : x ∈ D' ∪ E' := Or.inr (hVE1 h1)
    rw [← hcov'] at hmem; exact hmem hxS

/-- Openness in `ℕ → Bool` of a point condition along a continuous chart fiber yields a cylinder. -/
lemma exists_cyl_of_chart_mem_open {k : ℕ} {ε : ℕ → Bool} {t : Icc (0 : ℝ) 1}
    {O : Set BH} (hO : IsOpen O) (hmem : chart k ε t ∈ O) :
    ∃ m : ℕ, ∀ η : ℕ → Bool, BHSec.inCyl (List.ofFn (fun i : Fin m => ε i)) η →
      chart k η t ∈ O := by
  have hc : Continuous (fun η : ℕ → Bool => chart k η t) :=
    (continuous_chart k).comp (continuous_id.prodMk continuous_const)
  have hnhds : (fun η : ℕ → Bool => chart k η t) ⁻¹' O ∈ 𝓝 ε :=
    (hO.preimage hc).mem_nhds hmem
  rw [nhds_pi, Filter.mem_pi'] at hnhds
  rcases hnhds with ⟨I, s, hs, hIs⟩
  let m := I.sup id + 1
  refine ⟨m, fun η hη => hIs fun n hn => ?_⟩
  have hnm : n < m := Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)
  have heq : η n = ε n := by
    have := hη n (by rw [List.length_ofFn]; exact hnm)
    rwa [List.getElem_ofFn] at this
  rw [heq]
  exact mem_of_mem_nhds (hs n)

/-- Rudin's `Y(U)` step (Lemma 3, p. 19): given `U ∈ G(S)` and `p ∈ U.bar \ S`, there is a strip
    `U.strip w` containing `p` in its closure and a block `Y` of `U.strip w` with `Y ∈ G(S)` and `p ∉ Y.bar`. -/
lemma exists_Y_avoiding_point {S : Set BH} {U : BHSec} (hS : IsClosed S) (hU : inG S U)
    {p : BH} (hpU : p ∈ U.bar) (hpS : p ∉ S) :
    ∃ (w : List Bool) (Y : BHSec),
      BHSec.IsBlock Y (U.strip w) ∧ inG S Y ∧ p ∈ (U.strip w).bar ∧ p ∉ Y.bar := by
  rcases hU with ⟨hdisj, O₀_raw, O₁_raw, hO₀r, hO₁r, hO01r, hcovr, hE₀r, hE₁r⟩
  let O₀ : Set BH := O₀_raw \ S
  let O₁ : Set BH := O₁_raw \ S
  have hO₀ : IsOpen O₀ := hO₀r.sdiff hS
  have hO₁ : IsOpen O₁ := hO₁r.sdiff hS
  have hO01 : Disjoint O₀ O₁ := hO01r.mono sdiff_subset sdiff_subset
  have hcov : U.bar \ S ⊆ O₀ ∪ O₁ := fun x hx =>
    (hcovr hx).imp (fun h => ⟨h, hx.2⟩) (fun h => ⟨h, hx.2⟩)
  have hE₀ : U.end0 ⊆ O₀ := fun x hx => ⟨hE₀r hx, fun hxS => disjoint_left.mp hdisj hxS (Or.inl hx)⟩
  have hE₁ : U.end1 ⊆ O₁ := fun x hx => ⟨hE₁r hx, fun hxS => disjoint_left.mp hdisj hxS (Or.inr hx)⟩
  let ε := bitsAt U.level p
  let tp : Icc (0 : ℝ) 1 := ⟨p.1 U.level, bh_mem_Icc p U.level⟩
  have hp_eq : chart U.level ε tp = p := chart_bitsAt U.level p
  -- Helper: given a closed interval [c, d] ⊆ [U.lo, U.hi] with chart U.level ε [c, d] ⊆ O,
  -- compactness + openness gives a cylinder w around ε such that chart U.level (cyl w) × [c, d] ⊆ O.
  -- Even simpler: we only need a SINGLE rational point r ∈ (U.lo, U.hi) in O₀ (if p ∈ O₀) or O₁ (if p ∈ O₁)!
  rcases hcov ⟨hpU, hpS⟩ with hp0 | hp1
  · -- Case p ∈ O₀: p ∉ U.end1, so p.1 U.level < U.hi.
    have hp_lt_hi : p.1 U.level < (U.hi : ℝ) :=
      lt_of_le_of_ne hpU.2 fun heq => disjoint_left.mp hO01 hp0 (hE₁ heq)
    -- Since chart U.level ε is continuous and chart U.level ε tp ∈ O₀, find rational r ∈ (p.1 U.level, U.hi) in O₀!
    have hc_t : Continuous (fun t : Icc (0 : ℝ) 1 => chart U.level ε t) :=
      (continuous_chart U.level).comp (continuous_const.prodMk continuous_id)
    have hpre : (fun t : Icc (0 : ℝ) 1 => chart U.level ε t) ⁻¹' O₀ ∈ 𝓝 tp :=
      (hO₀.preimage hc_t).mem_nhds (show chart U.level ε tp ∈ O₀ by rwa [hp_eq])
    rw [Metric.mem_nhds_iff] at hpre
    rcases hpre with ⟨δ, hδ, hball⟩
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn
      (show p.1 U.level < min (U.hi : ℝ) (p.1 U.level + δ / 2) by
        exact lt_min hp_lt_hi (by linarith))
    have hr_lt_hi : (r : ℝ) < U.hi := lt_of_lt_of_le hr2 (min_le_left _ _)
    have hr_gt_lo : (U.lo : ℝ) < r := lt_of_le_of_lt hpU.1 hr1
    have hr_icc : (r : ℝ) ∈ Icc (0 : ℝ) 1 :=
      ⟨le_of_lt (lt_trans U.lo_pos_real hr_gt_lo), le_of_lt (lt_trans hr_lt_hi U.hi_lt_one_real)⟩
    have hr_mem : chart U.level ε ⟨r, hr_icc⟩ ∈ O₀ := by
      apply hball
      change |(r : ℝ) - p.1 U.level| < δ
      rw [abs_of_pos (by linarith)]
      linarith [lt_of_lt_of_le hr2 (min_le_right _ _)]
    obtain ⟨m, hm⟩ := exists_cyl_of_chart_mem_open hO₀ hr_mem
    let w : List Bool := List.ofFn (fun i : Fin m => ε i)
    -- Build the block B_r := (U.level, r, U.hi) of U, and take Y := B_r.strip w!
    let Br : BHSec :=
      { level := U.level
        lo := r
        hi := U.hi
        hlo := lt_of_lt_of_le U.hlo (by exact_mod_cast le_of_lt hr_gt_lo)
        hlt := by exact_mod_cast hr_lt_hi
        hhi := U.hhi
        hside := U.hside.imp id (fun h => lt_trans h (by exact_mod_cast hr_gt_lo)) }
    have hBr_blk : BHSec.IsBlock Br U := ⟨rfl, by exact_mod_cast le_of_lt hr_gt_lo, le_rfl⟩
    let Y := Br.strip w
    have hY_blk : BHSec.IsBlock Y (U.strip w) := BHSec.isBlock_strip hBr_blk w
    have hp_strip : p ∈ (U.strip w).bar :=
      (U.mem_strip_bar_iff w p).mpr ⟨hpU, fun i hi => by simp [w, ε]⟩
    have hp_notY : p ∉ Y.bar := by
      intro hpY
      have hpBr : p ∈ Br.bar := ((Br.mem_strip_bar_iff w p).mp hpY).1
      linarith [hpBr.1]
    have hBr_end0_O0 : ∀ x ∈ (Br.strip w).bar, x.1 U.level = (r : ℝ) → x ∈ O₀ := by
      intro x hx hxr
      have hcyl : BHSec.inCyl w (bitsAt U.level x) := ((Br.mem_strip_bar_iff w x).mp hx).2
      have hch : chart U.level (bitsAt U.level x) ⟨r, hr_icc⟩ = x := by
        have hsub : (⟨r, hr_icc⟩ : Icc (0 : ℝ) 1) = ⟨x.1 U.level, bh_mem_Icc x U.level⟩ := Subtype.ext hxr.symm
        rw [hsub, chart_bitsAt]
      rw [← hch]
      exact hm (bitsAt U.level x) hcyl
    have hY_inG : inG S Y := by
      have hends := Br.strip_ends_subset w
      have hYbar_sub : Y.bar ⊆ U.bar := BHSec.isBlock_bar_subset hY_blk |>.trans
        (fun x hx => ((U.mem_strip_bar_iff w x).mp hx).1)
      cases hp_par : branchParity w
      · obtain ⟨he0, he1⟩ := hends.1 hp_par
        have hY0 : Y.end0 ⊆ O₀ := fun x hx =>
          hBr_end0_O0 x (Y.bar_eq_carrier_union_ends.symm ▸ Or.inr (Or.inl hx)) (he0 hx)
        have hY1 : Y.end1 ⊆ O₁ := fun x hx => hE₁ (he1 hx)
        refine ⟨disjoint_left.mpr fun x hxS hxE => ?_, O₀, O₁, hO₀, hO₁, hO01,
          fun x hx => hcov ⟨hYbar_sub hx.1, hx.2⟩, hY0, hY1⟩
        rcases hxE with h0 | h1
        · exact (hY0 h0).2 hxS
        · exact (hY1 h1).2 hxS
      · obtain ⟨he0, he1⟩ := hends.2 hp_par
        have hY0 : Y.end0 ⊆ O₁ := fun x hx => hE₁ (he0 hx)
        have hY1 : Y.end1 ⊆ O₀ := fun x hx =>
          hBr_end0_O0 x (Y.bar_eq_carrier_union_ends.symm ▸ Or.inr (Or.inr hx)) (he1 hx)
        refine ⟨disjoint_left.mpr fun x hxS hxE => ?_, O₁, O₀, hO₁, hO₀, hO01.symm,
          fun x hx => (hcov ⟨hYbar_sub hx.1, hx.2⟩).symm, hY0, hY1⟩
        rcases hxE with h0 | h1
        · exact (hY0 h0).2 hxS
        · exact (hY1 h1).2 hxS
    exact ⟨w, Y, hY_blk, hY_inG, hp_strip, hp_notY⟩
  · -- Case p ∈ O₁: symmetric! p ∉ U.end0, so U.lo < p.1 U.level.
    have hp_gt_lo : (U.lo : ℝ) < p.1 U.level :=
      lt_of_le_of_ne hpU.1 fun heq => disjoint_left.mp hO01 (hE₀ heq.symm) hp1
    have hc_t : Continuous (fun t : Icc (0 : ℝ) 1 => chart U.level ε t) :=
      (continuous_chart U.level).comp (continuous_const.prodMk continuous_id)
    have hpre : (fun t : Icc (0 : ℝ) 1 => chart U.level ε t) ⁻¹' O₁ ∈ 𝓝 tp :=
      (hO₁.preimage hc_t).mem_nhds (show chart U.level ε tp ∈ O₁ by rwa [hp_eq])
    rw [Metric.mem_nhds_iff] at hpre
    rcases hpre with ⟨δ, hδ, hball⟩
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn
      (show max (U.lo : ℝ) (p.1 U.level - δ / 2) < p.1 U.level by
        exact max_lt hp_gt_lo (by linarith))
    have hr_gt_lo : (U.lo : ℝ) < r := lt_of_le_of_lt (le_max_left _ _) hr1
    have hr_lt_hi : (r : ℝ) < U.hi := lt_of_lt_of_le hr2 hpU.2
    have hr_icc : (r : ℝ) ∈ Icc (0 : ℝ) 1 :=
      ⟨le_of_lt (lt_trans U.lo_pos_real hr_gt_lo), le_of_lt (lt_trans hr_lt_hi U.hi_lt_one_real)⟩
    have hr_mem : chart U.level ε ⟨r, hr_icc⟩ ∈ O₁ := by
      apply hball
      change |(r : ℝ) - p.1 U.level| < δ
      rw [abs_of_neg (by linarith)]
      linarith [lt_of_le_of_lt (le_max_right _ _) hr1]
    obtain ⟨m, hm⟩ := exists_cyl_of_chart_mem_open hO₁ hr_mem
    let w : List Bool := List.ofFn (fun i : Fin m => ε i)
    let Br : BHSec :=
      { level := U.level
        lo := U.lo
        hi := r
        hlo := U.hlo
        hlt := by exact_mod_cast hr_gt_lo
        hhi := lt_trans (by exact_mod_cast hr_lt_hi) U.hhi
        hside := U.hside.imp (fun h => lt_trans (by exact_mod_cast hr_lt_hi) h) id }
    have hBr_blk : BHSec.IsBlock Br U := ⟨rfl, le_rfl, by exact_mod_cast le_of_lt hr_lt_hi⟩
    let Y := Br.strip w
    have hY_blk : BHSec.IsBlock Y (U.strip w) := BHSec.isBlock_strip hBr_blk w
    have hp_strip : p ∈ (U.strip w).bar :=
      (U.mem_strip_bar_iff w p).mpr ⟨hpU, fun i hi => by simp [w, ε]⟩
    have hp_notY : p ∉ Y.bar := by
      intro hpY
      have hpBr : p ∈ Br.bar := ((Br.mem_strip_bar_iff w p).mp hpY).1
      linarith [hpBr.2]
    have hBr_end1_O1 : ∀ x ∈ (Br.strip w).bar, x.1 U.level = (r : ℝ) → x ∈ O₁ := by
      intro x hx hxr
      have hcyl : BHSec.inCyl w (bitsAt U.level x) := ((Br.mem_strip_bar_iff w x).mp hx).2
      have hch : chart U.level (bitsAt U.level x) ⟨r, hr_icc⟩ = x := by
        have hsub : (⟨r, hr_icc⟩ : Icc (0 : ℝ) 1) = ⟨x.1 U.level, bh_mem_Icc x U.level⟩ := Subtype.ext hxr.symm
        rw [hsub, chart_bitsAt]
      rw [← hch]
      exact hm (bitsAt U.level x) hcyl
    have hY_inG : inG S Y := by
      have hends := Br.strip_ends_subset w
      have hYbar_sub : Y.bar ⊆ U.bar := BHSec.isBlock_bar_subset hY_blk |>.trans
        (fun x hx => ((U.mem_strip_bar_iff w x).mp hx).1)
      cases hp_par : branchParity w
      · obtain ⟨he0, he1⟩ := hends.1 hp_par
        have hY0 : Y.end0 ⊆ O₀ := fun x hx => hE₀ (he0 hx)
        have hY1 : Y.end1 ⊆ O₁ := fun x hx =>
          hBr_end1_O1 x (Y.bar_eq_carrier_union_ends.symm ▸ Or.inr (Or.inr hx)) (he1 hx)
        refine ⟨disjoint_left.mpr fun x hxS hxE => ?_, O₀, O₁, hO₀, hO₁, hO01,
          fun x hx => hcov ⟨hYbar_sub hx.1, hx.2⟩, hY0, hY1⟩
        rcases hxE with h0 | h1
        · exact (hY0 h0).2 hxS
        · exact (hY1 h1).2 hxS
      · obtain ⟨he0, he1⟩ := hends.2 hp_par
        have hY0 : Y.end0 ⊆ O₁ := fun x hx =>
          hBr_end1_O1 x (Y.bar_eq_carrier_union_ends.symm ▸ Or.inr (Or.inl hx)) (he0 hx)
        have hY1 : Y.end1 ⊆ O₀ := fun x hx => hE₀ (he1 hx)
        refine ⟨disjoint_left.mpr fun x hxS hxE => ?_, O₁, O₀, hO₁, hO₀, hO01.symm,
          fun x hx => (hcov ⟨hYbar_sub hx.1, hx.2⟩).symm, hY0, hY1⟩
        rcases hxE with h0 | h1
        · exact (hY0 h0).2 hxS
        · exact (hY1 h1).2 hxS
    exact ⟨w, Y, hY_blk, hY_inG, hp_strip, hp_notY⟩

/-- Rudin Case 2(ii) intersection lemma (p. 24): if `Q ∈ G(S)` and `J ∈ G(S ∩ Q.bar)`,
    then there is a section `V ⊆ J ∩ Q` with `V ∈ G(S)`. -/
lemma exists_inG_subset_inter {S : Set BH} {Q J : BHSec} (hS : IsClosed S)
    (hQ : inG S Q) (hJ : inG (S ∩ Q.bar) J) :
    ∃ V : BHSec, V.carrier ⊆ J.carrier ∧ V.carrier ⊆ Q.carrier ∧ inG S V := by
  -- Helper for Q.level ≤ J'.level
  suffices hmain : ∀ J' : BHSec, Q.level ≤ J'.level → inG (S ∩ Q.bar) J' →
      ∃ V : BHSec, V.carrier ⊆ J'.carrier ∧ V.carrier ⊆ Q.carrier ∧ inG S V by
    by_cases hle : Q.level ≤ J.level
    · exact hmain J hle hJ
    · let J' := J.strip (List.replicate (Q.level - J.level) false)
      have hJ'lvl : Q.level ≤ J'.level := by simp [J', BHSec.strip]; omega
      obtain ⟨V, hVJ', hVQ, hVG⟩ := hmain J' hJ'lvl (inG_strip hJ _)
      exact ⟨V, hVJ'.trans (J.strip_carrier_subset _), hVQ, hVG⟩
  intro J' hle hJ'
  rcases hJ' with ⟨hJdisj, O₀_raw, O₁_raw, hO₀r, hO₁r, hO01r, hcovr, hE₀r, hE₁r⟩
  let S' := S ∩ Q.bar
  have hS'cl : IsClosed S' := hS.inter Q.isClosed_bar
  let O₀ : Set BH := O₀_raw \ S'
  let O₁ : Set BH := O₁_raw \ S'
  have hO₀ : IsOpen O₀ := hO₀r.sdiff hS'cl
  have hO₁ : IsOpen O₁ := hO₁r.sdiff hS'cl
  have hO01 : Disjoint O₀ O₁ := hO01r.mono sdiff_subset sdiff_subset
  have hcov : J'.bar \ S' ⊆ O₀ ∪ O₁ := fun x hx =>
    (hcovr hx).imp (fun h => ⟨h, hx.2⟩) (fun h => ⟨h, hx.2⟩)
  have hE₀ : J'.end0 ⊆ O₀ := fun x hx => ⟨hE₀r hx, fun hxS => disjoint_left.mp hJdisj hxS (Or.inl hx)⟩
  have hE₁ : J'.end1 ⊆ O₁ := fun x hx => ⟨hE₁r hx, fun hxS => disjoint_left.mp hJdisj hxS (Or.inr hx)⟩
  let ε₀ : ℕ → Bool := fun _ => false
  let γ : ℝ → BH := fun t =>
    chart J'.level ε₀ ⟨max 0 (min 1 t), le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hγ_cont : Continuous γ :=
    (continuous_chart J'.level).comp (continuous_const.prodMk
      (Continuous.subtype_mk (continuous_const.max (continuous_const.min continuous_id)) _))
  have hγ_coord : ∀ t ∈ Icc (J'.lo : ℝ) (J'.hi : ℝ), (γ t).1 J'.level = t := fun t ht => by
    have h0 : 0 ≤ t := le_of_lt (lt_of_lt_of_le J'.lo_pos_real ht.1)
    have h1 : t ≤ 1 := le_of_lt (lt_of_le_of_lt ht.2 J'.hi_lt_one_real)
    simp [γ, chart_coord_self, min_eq_right h1, max_eq_right h0]
  let E₀ : Set ℝ := {t ∈ Icc (J'.lo : ℝ) (J'.hi : ℝ) | γ t ∈ O₀}
  have hE₀_ne : E₀.Nonempty :=
    ⟨J'.lo, ⟨le_rfl, le_of_lt J'.lo_lt_hi_real⟩, hE₀ (hγ_coord J'.lo ⟨le_rfl, le_of_lt J'.lo_lt_hi_real⟩)⟩
  have hE₀_bdd : BddAbove E₀ := ⟨J'.hi, fun _ ht => ht.1.2⟩
  let tstar : ℝ := sSup E₀
  have htstar_mem : tstar ∈ Icc (J'.lo : ℝ) (J'.hi : ℝ) :=
    ⟨le_csSup hE₀_bdd hE₀_ne.choose_spec |> fun h => le_trans hE₀_ne.choose_spec.1.1 h,
      csSup_le hE₀_ne fun _ ht => ht.1.2⟩
  have htstar_not0 : γ tstar ∉ O₀ := by
    intro h0
    have hlt_hi : tstar < J'.hi := lt_of_le_of_ne htstar_mem.2 fun heq =>
      disjoint_left.mp hO01 h0 (hE₁ (show (γ tstar).1 J'.level = J'.hi by rw [hγ_coord tstar htstar_mem, heq]))
    have hpre : γ ⁻¹' O₀ ∈ 𝓝 tstar := (hO₀.preimage hγ_cont).mem_nhds h0
    rw [Metric.mem_nhds_iff] at hpre
    rcases hpre with ⟨δ, hδ, hball⟩
    let t' := min (J'.hi : ℝ) (tstar + δ / 2)
    have ht'_gt : tstar < t' := lt_min hlt_hi (by linarith)
    have ht'_mem : t' ∈ E₀ := by
      refine ⟨⟨le_trans htstar_mem.1 (le_of_lt ht'_gt), min_le_left _ _⟩, hball ?_⟩
      rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]
      linarith [min_le_right (J'.hi : ℝ) (tstar + δ / 2)]
    linarith [le_csSup hE₀_bdd ht'_mem]
  have htstar_not1 : γ tstar ∉ O₁ := by
    intro h1
    have hpre : γ ⁻¹' O₁ ∈ 𝓝 tstar := (hO₁.preimage hγ_cont).mem_nhds h1
    rw [Metric.mem_nhds_iff] at hpre
    rcases hpre with ⟨δ, hδ, hball⟩
    obtain ⟨t₁, ht₁E, ht₁gt⟩ := exists_lt_of_lt_csSup hE₀_ne (show tstar - δ / 2 < tstar by linarith)
    have ht₁le : t₁ ≤ tstar := le_csSup hE₀_bdd ht₁E
    have ht₁O1 : γ t₁ ∈ O₁ := by
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (by linarith)]
      linarith
    exact disjoint_left.mp hO01 ht₁E.2 ht₁O1
  have htstar_S' : γ tstar ∈ S' := by
    by_contra hnot
    have hbar : γ tstar ∈ J'.bar := by
      change (J'.lo : ℝ) ≤ (γ tstar).1 J'.level ∧ (γ tstar).1 J'.level ≤ J'.hi
      rw [hγ_coord tstar htstar_mem]; exact htstar_mem
    rcases hcov ⟨hbar, hnot⟩ with h0 | h1
    · exact htstar_not0 h0
    · exact htstar_not1 h1
  -- Since γ tstar ∈ S ∩ Q.bar and Disjoint S Q.ends and Disjoint S' J'.ends:
  have htstar_ioo : tstar ∈ Ioo (J'.lo : ℝ) (J'.hi : ℝ) := by
    refine ⟨lt_of_le_of_ne htstar_mem.1 fun h => disjoint_left.mp hJdisj htstar_S'
        (Or.inl (show (γ tstar).1 J'.level = J'.lo by rw [hγ_coord tstar htstar_mem, ← h])),
      lt_of_le_of_ne htstar_mem.2 fun h => disjoint_left.mp hJdisj htstar_S'
        (Or.inr (show (γ tstar).1 J'.level = J'.hi by rw [hγ_coord tstar htstar_mem, h]))⟩
  have htstar_Q : γ tstar ∈ Q.carrier := by
    have hbar : γ tstar ∈ Q.bar := htstar_S'.2
    rw [Q.bar_eq_carrier_union_ends] at hbar
    exact hbar.resolve_right fun hE => disjoint_left.mp hQ.1 htstar_S'.1 hE
  -- Restrict Q to the strip Qw of level J'.level containing γ tstar!
  let m := J'.level - Q.level
  let w0 : List Bool := List.ofFn (fun i : Fin m => bitsAt Q.level (γ tstar) i)
  let Qw := Q.strip w0
  have hQw_lvl : Qw.level = J'.level := by simp [Qw, BHSec.strip, w0, m]; omega
  have htstar_Qw : γ tstar ∈ Qw.carrier :=
    (Q.mem_strip_carrier_iff w0 (γ tstar)).mpr ⟨htstar_Q, fun i hi => by simp [w0]⟩
  have htstar_Qw_ioo : tstar ∈ Ioo (Qw.lo : ℝ) (Qw.hi : ℝ) := by
    have h : (Qw.lo : ℝ) < (γ tstar).1 Qw.level ∧ (γ tstar).1 Qw.level < Qw.hi := htstar_Qw
    rw [hQw_lvl, hγ_coord tstar htstar_mem] at h
    exact h
  -- Same-level intersection V₀ of J' and Qw
  let lo0 : ℚ := max J'.lo Qw.lo
  let hi0 : ℚ := min J'.hi Qw.hi
  have htstar_V0 : tstar ∈ Ioo (lo0 : ℝ) (hi0 : ℝ) := by
    simp only [lo0, hi0, Rat.cast_max, Rat.cast_min, mem_Ioo, max_lt_iff, lt_min_iff]
    exact ⟨⟨htstar_ioo.1, htstar_Qw_ioo.1⟩, ⟨htstar_ioo.2, htstar_Qw_ioo.2⟩⟩
  have hlo0_lt_hi0 : lo0 < hi0 := by exact_mod_cast lt_trans htstar_V0.1 htstar_V0.2
  have hhi0_mem_J' : (hi0 : ℝ) ∈ Icc (J'.lo : ℝ) (J'.hi : ℝ) :=
    ⟨le_of_lt (lt_trans htstar_ioo.1 htstar_V0.2), by exact_mod_cast min_le_left J'.hi Qw.hi⟩
  -- Key: γ hi0 ∈ O₁!
  have hγ_hi0_O1 : γ hi0 ∈ O₁ := by
    have hnot0 : γ hi0 ∉ O₀ := fun h0 => by
      have hmemE : (hi0 : ℝ) ∈ E₀ := ⟨hhi0_mem_J', h0⟩
      linarith [le_csSup hE₀_bdd hmemE, htstar_V0.2]
    have hnotS' : γ hi0 ∉ S' := by
      rcases le_total J'.hi Qw.hi with hle' | hle'
      · have heq : hi0 = J'.hi := min_eq_left hle'
        intro hS'
        exact disjoint_left.mp hJdisj hS'
          (Or.inr (show (γ hi0).1 J'.level = J'.hi by rw [hγ_coord hi0 hhi0_mem_J', heq]))
      · have heq : hi0 = Qw.hi := min_eq_right hle'
        intro hS'
        have hQw1 : γ hi0 ∈ Qw.end1 := by
          show (γ hi0).1 Qw.level = Qw.hi
          rw [hQw_lvl, hγ_coord hi0 hhi0_mem_J', heq]
        have hQends : γ hi0 ∈ Q.ends := by
          have hs := Q.strip_ends_subset w0
          cases hp : branchParity w0
          · exact Or.inr ((hs.1 hp).2 hQw1)
          · exact Or.inl ((hs.2 hp).2 hQw1)
        exact disjoint_left.mp hQ.1 hS'.1 hQends
    have hbar : γ hi0 ∈ J'.bar := by
      change (J'.lo : ℝ) ≤ (γ hi0).1 J'.level ∧ (γ hi0).1 J'.level ≤ J'.hi
      rw [hγ_coord hi0 hhi0_mem_J']; exact hhi0_mem_J'
    exact (hcov ⟨hbar, hnotS'⟩).resolve_left hnot0
  -- Find rational r1 ∈ (lo0, hi0) with γ r1 ∈ O₀!
  obtain ⟨t₁, ht₁E, ht₁gt⟩ := exists_lt_of_lt_csSup hE₀_ne htstar_V0.1
  have ht₁le : t₁ ≤ tstar := le_csSup hE₀_bdd ht₁E
  have ht₁_lt_hi0 : t₁ < (hi0 : ℝ) := lt_of_le_of_lt ht₁le htstar_V0.2
  have hpre0 : γ ⁻¹' O₀ ∈ 𝓝 t₁ := (hO₀.preimage hγ_cont).mem_nhds ht₁E.2
  rw [Metric.mem_nhds_iff] at hpre0
  rcases hpre0 with ⟨δ, hδ, hball⟩
  obtain ⟨r₁, hr₁1, hr₁2⟩ := exists_rat_btwn
    (show max (lo0 : ℝ) (t₁ - δ / 2) < min (hi0 : ℝ) (t₁ + δ / 2) by
      apply max_lt
      · exact lt_min (by exact_mod_cast hlo0_lt_hi0) (by linarith)
      · exact lt_min (by linarith) (by linarith))
  have hr₁_gt_lo0 : (lo0 : ℝ) < r₁ := lt_of_le_of_lt (le_max_left _ _) hr₁1
  have hr₁_gt_lo0_q : lo0 < r₁ := by exact_mod_cast hr₁_gt_lo0
  have hr₁_lt_hi0 : (r₁ : ℝ) < hi0 := lt_of_lt_of_le hr₁2 (min_le_left _ _)
  have hγ_r1_O0 : γ r₁ ∈ O₀ := by
    apply hball; rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [lt_of_le_of_lt (le_max_right _ _) hr₁1, lt_of_lt_of_le hr₁2 (min_le_right _ _)]
  -- Build section V₁ := (J'.level, r₁, hi0) and shrink to a cylinder strip V := V₁.strip w!
  let V₁ : BHSec :=
    { level := J'.level
      lo := r₁
      hi := hi0
      hlo := lt_trans J'.hlo (lt_of_le_of_lt (le_max_left _ _) hr₁_gt_lo0_q)
      hlt := by exact_mod_cast hr₁_lt_hi0
      hhi := lt_of_le_of_lt (min_le_left _ _) J'.hhi
      hside := J'.hside.imp (fun h => lt_of_le_of_lt (min_le_left _ _) h)
        (fun h => lt_of_le_of_lt (le_trans (le_of_lt h) (le_max_left _ _)) hr₁_gt_lo0_q) }
  have hV₁_J' : BHSec.IsBlock V₁ J' :=
    ⟨rfl, le_trans (le_max_left _ _) (le_of_lt hr₁_gt_lo0_q), min_le_left _ _⟩
  have hV₁_Qw : BHSec.IsBlock V₁ Qw :=
    ⟨hQw_lvl.symm, le_trans (le_max_right _ _) (le_of_lt hr₁_gt_lo0_q), min_le_right _ _⟩
  have hr₁_icc : (r₁ : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt V₁.lo_pos_real, le_of_lt (lt_trans V₁.lo_lt_hi_real V₁.hi_lt_one_real)⟩
  have hhi0_icc : (hi0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt (lt_trans V₁.lo_pos_real V₁.lo_lt_hi_real), le_of_lt V₁.hi_lt_one_real⟩
  have hch_r1 : chart J'.level ε₀ ⟨r₁, hr₁_icc⟩ = γ r₁ := by
    dsimp only [γ]; congr 1; apply Subtype.ext; simp [min_eq_right hr₁_icc.2, max_eq_right hr₁_icc.1]
  have hch_hi0 : chart J'.level ε₀ ⟨hi0, hhi0_icc⟩ = γ hi0 := by
    dsimp only [γ]; congr 1; apply Subtype.ext; simp [min_eq_right hhi0_icc.2, max_eq_right hhi0_icc.1]
  obtain ⟨m₀, hm₀⟩ := exists_cyl_of_chart_mem_open hO₀ (hch_r1.symm ▸ hγ_r1_O0)
  obtain ⟨m₁, hm₁⟩ := exists_cyl_of_chart_mem_open hO₁ (hch_hi0.symm ▸ hγ_hi0_O1)
  let m' := max m₀ m₁
  let w : List Bool := List.ofFn (fun i : Fin m' => ε₀ i)
  let V := V₁.strip w
  have hV_sub_J' : V.carrier ⊆ J'.carrier :=
    (V₁.strip_carrier_subset w).trans (BHSec.isBlock_carrier_subset hV₁_J')
  have hV_sub_Q : V.carrier ⊆ Q.carrier :=
    (V₁.strip_carrier_subset w).trans ((BHSec.isBlock_carrier_subset hV₁_Qw).trans (Q.strip_carrier_subset w0))
  have hVbar_sub_J' : V.bar ⊆ J'.bar :=
    Subset.trans (fun x hx => ((V₁.mem_strip_bar_iff w x).mp hx).1) (BHSec.isBlock_bar_subset hV₁_J')
  have hVbar_sub_Q : V.bar ⊆ Q.bar :=
    Subset.trans (fun x hx => ((V₁.mem_strip_bar_iff w x).mp hx).1)
      (Subset.trans (BHSec.isBlock_bar_subset hV₁_Qw) fun x hx => ((Q.mem_strip_bar_iff w0 x).mp hx).1)
  have hV_e0_O0 : ∀ x ∈ V.bar, x.1 J'.level = (r₁ : ℝ) → x ∈ O₀ := by
    intro x hx hxr
    have hcyl : BHSec.inCyl w (bitsAt J'.level x) := ((V₁.mem_strip_bar_iff w x).mp hx).2
    have hcyl0 : BHSec.inCyl (List.ofFn (fun i : Fin m₀ => ε₀ i)) (bitsAt J'.level x) := by
      intro i hi
      rw [List.length_ofFn] at hi
      have h := hcyl i (by rw [List.length_ofFn]; omega)
      simpa [w] using h
    have hch : chart J'.level (bitsAt J'.level x) ⟨r₁, hr₁_icc⟩ = x := by
      have hsub : (⟨r₁, hr₁_icc⟩ : Icc (0 : ℝ) 1) = ⟨x.1 J'.level, bh_mem_Icc x J'.level⟩ := Subtype.ext hxr.symm
      rw [hsub, chart_bitsAt]
    rw [← hch]; exact hm₀ (bitsAt J'.level x) hcyl0
  have hV_e1_O1 : ∀ x ∈ V.bar, x.1 J'.level = (hi0 : ℝ) → x ∈ O₁ := by
    intro x hx hxh
    have hcyl : BHSec.inCyl w (bitsAt J'.level x) := ((V₁.mem_strip_bar_iff w x).mp hx).2
    have hcyl1 : BHSec.inCyl (List.ofFn (fun i : Fin m₁ => ε₀ i)) (bitsAt J'.level x) := by
      intro i hi
      rw [List.length_ofFn] at hi
      have h := hcyl i (by rw [List.length_ofFn]; omega)
      simpa [w] using h
    have hch : chart J'.level (bitsAt J'.level x) ⟨hi0, hhi0_icc⟩ = x := by
      have hsub : (⟨hi0, hhi0_icc⟩ : Icc (0 : ℝ) 1) = ⟨x.1 J'.level, bh_mem_Icc x J'.level⟩ := Subtype.ext hxh.symm
      rw [hsub, chart_bitsAt]
    rw [← hch]; exact hm₁ (bitsAt J'.level x) hcyl1
  have hV_inG : inG S V := by
    have hends := V₁.strip_ends_subset w
    cases hp_par : branchParity w
    · obtain ⟨he0, he1⟩ := hends.1 hp_par
      have hV0 : V.end0 ⊆ O₀ := fun x hx =>
        hV_e0_O0 x (V.bar_eq_carrier_union_ends.symm ▸ Or.inr (Or.inl hx)) (he0 hx)
      have hV1 : V.end1 ⊆ O₁ := fun x hx =>
        hV_e1_O1 x (V.bar_eq_carrier_union_ends.symm ▸ Or.inr (Or.inr hx)) (he1 hx)
      refine ⟨disjoint_left.mpr fun x hxS hxE => ?_, O₀, O₁, hO₀, hO₁, hO01,
        fun x hx => hcov ⟨hVbar_sub_J' hx.1, fun hS' => hx.2 hS'.1⟩, hV0, hV1⟩
      have hxQ : x ∈ Q.bar := hVbar_sub_Q (V.bar_eq_carrier_union_ends.symm ▸ Or.inr hxE)
      rcases hxE with h0 | h1
      · exact (hV0 h0).2 ⟨hxS, hxQ⟩
      · exact (hV1 h1).2 ⟨hxS, hxQ⟩
    · obtain ⟨he0, he1⟩ := hends.2 hp_par
      have hV0 : V.end0 ⊆ O₁ := fun x hx =>
        hV_e1_O1 x (V.bar_eq_carrier_union_ends.symm ▸ Or.inr (Or.inl hx)) (he0 hx)
      have hV1 : V.end1 ⊆ O₀ := fun x hx =>
        hV_e0_O0 x (V.bar_eq_carrier_union_ends.symm ▸ Or.inr (Or.inr hx)) (he1 hx)
      refine ⟨disjoint_left.mpr fun x hxS hxE => ?_, O₁, O₀, hO₁, hO₀, hO01.symm,
        fun x hx => (hcov ⟨hVbar_sub_J' hx.1, fun hS' => hx.2 hS'.1⟩).symm, hV0, hV1⟩
      have hxQ : x ∈ Q.bar := hVbar_sub_Q (V.bar_eq_carrier_union_ends.symm ▸ Or.inr hxE)
      rcases hxE with h0 | h1
      · exact (hV0 h0).2 ⟨hxS, hxQ⟩
      · exact (hV1 h1).2 ⟨hxS, hxQ⟩
  exact ⟨V, hV_sub_J', hV_sub_Q, hV_inG⟩

/- Section 5: Rudin's Lemmas 1, 2, 3, and 4 -/

/-- All binary words of a given length `m`. -/
def allWords : ℕ → List (List Bool)
  | 0 => [[]]
  | m + 1 => (allWords m).map (false :: ·) ++ (allWords m).map (true :: ·)

lemma mem_allWords_iff (m : ℕ) (w : List Bool) : w ∈ allWords m ↔ w.length = m := by
  induction m generalizing w with
  | zero => simp [allWords]
  | succ m ih =>
    simp only [allWords, List.mem_append, List.mem_map]
    constructor
    · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) <;> simp [(ih u).mp hu]
    · intro hlen
      cases w with
      | nil => simp at hlen
      | cons b u =>
        cases b
        · left; exact ⟨u, (ih u).mpr (by simpa using hlen), rfl⟩
        · right; exact ⟨u, (ih u).mpr (by simpa using hlen), rfl⟩

/-- Open interior of a single arc fiber `chart k ε` over `(0, 1)`. -/
def fiberSeg (k : ℕ) (ε : ℕ → Bool) : Set BH :=
  {x | ∃ t : Icc (0 : ℝ) 1, t.1 ∈ Ioo (0 : ℝ) 1 ∧ x = chart k ε t}

lemma exists_strip_disjoint_fiber (U : BHSec) (k : ℕ) (ε : ℕ → Bool) :
    ∃ w : List Bool, Disjoint (U.strip w).bar (fiberSeg k ε) := by
  let m := max U.level k
  let dU := m - U.level
  let dk := m - k
  let w : List Bool := List.replicate dU false ++ [!(ε dk)]
  refine ⟨w, disjoint_left.mpr ?_⟩
  rintro x hx ⟨t, ht_ioo, rfl⟩
  have hcyl : BHSec.inCyl w (bitsAt U.level (chart k ε t)) :=
    ((U.mem_strip_bar_iff w _).mp hx).2
  have hdU_lt : dU < w.length := by simp [w]
  have h1 : bitsAt U.level (chart k ε t) dU = !(ε dk) := by
    have h := hcyl dU hdU_lt
    have hr : w[dU]'hdU_lt = !(ε dk) := by
      simp only [w, List.getElem_append_right (by simp : (List.replicate dU false).length ≤ dU),
        List.length_replicate, Nat.sub_self, List.getElem_singleton]
    exact h.trans hr
  have h2 : bitsAt U.level (chart k ε t) dU = ε dk := by
    have hbit := congrFun (bitsAt_chart k ε ht_ioo) dk
    have hidx : U.level + dU + 1 = k + dk + 1 := by omega
    calc bitsAt U.level (chart k ε t) dU
      = decide (1 / 2 < (chart k ε t).1 (U.level + dU + 1)) := rfl
      _ = decide (1 / 2 < (chart k ε t).1 (k + dk + 1)) := by rw [hidx]
      _ = bitsAt k (chart k ε t) dk := rfl
      _ = ε dk := hbit
  rw [h2] at h1
  cases h : ε dk <;> simp [h] at h1

/-- `E` is `G(S)`-avoidable: every `U ∈ G(S)` contains `V ∈ G(S)` with `S ∩ V.bar` disjoint from `E`. -/
def GAvd (S E : Set BH) : Prop :=
  ∀ U : BHSec, inG S U → ∃ V : BHSec, V.carrier ⊆ U.carrier ∧ inG S V ∧ Disjoint (S ∩ V.bar) E

lemma gAvd_fiberSeg (S : Set BH) (k : ℕ) (ε : ℕ → Bool) : GAvd S (fiberSeg k ε) := by
  intro U hU
  obtain ⟨w, hdisj⟩ := exists_strip_disjoint_fiber U k ε
  exact ⟨U.strip w, U.strip_carrier_subset w, inG_strip hU w, hdisj.mono_left inter_subset_right⟩

/-- Rudin Lemma 1 (p. 17): A separating set `S` is not covered by a countable family of
    composants and `G(S)`-avoidable sets. -/
lemma rudin_lemma1 {S : Set BH} (hS : IsSepSet S) {K_fam : Set (Set BH)}
    (hK_cnt : K_fam.Countable)
    (hK_prop : ∀ E ∈ K_fam, (∃ q : BH, E = compSet q) ∨ GAvd S E) :
    ∃ p ∈ S, ∀ E ∈ K_fam, p ∉ E := by
  obtain ⟨U₀, hU₀⟩ := inG_nonempty_of_isSepSet hS
  let K₁ : Set (Set BH) := {E ∈ K_fam | GAvd S E}
  let K₂ : Set (Set BH) := {E ∈ K_fam | ∃ q : BH, E = compSet q}
  let Fibs : Set BH → Set (ℕ → Bool) := fun E =>
    {ε | ∃ t : Icc (0 : ℝ) 1, t.1 ∈ Icc (U₀.lo : ℝ) (U₀.hi : ℝ) ∧ chart U₀.level ε t ∈ E}
  let 𝔈 : Set (Set BH) := K₁ ∪ ⋃ E ∈ K₂, (fun ε => fiberSeg U₀.level ε) '' Fibs E
  have h𝔈_cnt : 𝔈.Countable := by
    refine (hK_cnt.mono fun _ h => h.1).union ?_
    refine (hK_cnt.mono fun _ h => h.1).biUnion fun E hE => ?_
    rcases hE.2 with ⟨q, rfl⟩
    exact (compSet_fibers_countable q U₀.level U₀.lo_pos_real U₀.hi_lt_one_real).image _
  have h𝔈_avd : ∀ F ∈ 𝔈, GAvd S F := by
    rintro F (h1 | h2)
    · exact h1.2
    · simp only [mem_iUnion, mem_image, exists_prop] at h2
      rcases h2 with ⟨_, _, ε, _, rfl⟩
      exact gAvd_fiberSeg S U₀.level ε
  have hcov_K : ∀ E ∈ K_fam, E ∩ U₀.bar ⊆ ⋃ F ∈ 𝔈, F := by
    intro E hE x ⟨hxE, hxU⟩
    rcases hK_prop E hE with ⟨q, hq⟩ | havd
    · refine mem_iUnion₂.mpr ⟨fiberSeg U₀.level (bitsAt U₀.level x), ?_, ?_⟩
      · right
        refine mem_iUnion₂.mpr ⟨E, ⟨hE, q, hq⟩, bitsAt U₀.level x, ?_, rfl⟩
        exact ⟨⟨x.1 U₀.level, bh_mem_Icc x U₀.level⟩, hxU, by rwa [chart_bitsAt]⟩
      · exact ⟨⟨x.1 U₀.level, bh_mem_Icc x U₀.level⟩, U₀.bar_mem_Ioo hxU, (chart_bitsAt U₀.level x).symm⟩
    · exact mem_iUnion₂.mpr ⟨E, Or.inl ⟨hE, havd⟩, hxE⟩
  by_cases hne : 𝔈.Nonempty
  · have : Countable 𝔈 := h𝔈_cnt.to_subtype
    have : Nonempty 𝔈 := hne.to_subtype
    obtain ⟨g, hg⟩ := exists_surjective_nat 𝔈
    let f : ℕ → Set BH := fun n => (g n).1
    have hf_mem : ∀ n, f n ∈ 𝔈 := fun n => (g n).2
    let step : {U : BHSec // inG S U} → ℕ → {U : BHSec // inG S U} := fun prev n =>
      let h := h𝔈_avd (f n) (hf_mem n) prev.1 prev.2
      ⟨h.choose, h.choose_spec.2.1⟩
    let seq : ℕ → {U : BHSec // inG S U} := Nat.rec ⟨U₀, hU₀⟩ (fun n prev => step prev n)
    have hsub_bar : ∀ n, (seq (n + 1)).1.bar ⊆ (seq n).1.bar := by
      intro n
      have hc : (seq (n + 1)).1.carrier ⊆ (seq n).1.carrier :=
        (h𝔈_avd (f n) (hf_mem n) (seq n).1 (seq n).2).choose_spec.1
      rw [← (seq (n + 1)).1.closure_carrier, ← (seq n).1.closure_carrier]
      exact closure_mono hc
    have hdisj_step : ∀ n, Disjoint (S ∩ (seq (n + 1)).1.bar) (f n) := fun n =>
      (h𝔈_avd (f n) (hf_mem n) (seq n).1 (seq n).2).choose_spec.2.2
    have hnonempty : ∀ n, (S ∩ (seq n).1.bar).Nonempty := by
      intro n
      obtain ⟨t, ht, hpS⟩ := inG_inter_fiber_nonempty (seq n).2 (fun _ => false)
      refine ⟨chart (seq n).1.level (fun _ => false) t, hpS, ?_⟩
      simp only [BHSec.bar, mem_ofPred_eq, chart_coord_self]
      exact ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hinter := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      (fun n => S ∩ (seq n).1.bar)
      (fun n => inter_subset_inter_right S (hsub_bar n))
      hnonempty
      (hS.1.inter (seq 0).1.isClosed_bar).isCompact
      (fun n => hS.1.inter (seq n).1.isClosed_bar)
    rcases hinter with ⟨p, hp⟩
    rw [mem_iInter] at hp
    refine ⟨p, (hp 0).1, fun E hE hpE => ?_⟩
    have hpU0 : p ∈ U₀.bar := (hp 0).2
    have hmem := hcov_K E hE ⟨hpE, hpU0⟩
    rw [mem_iUnion₂] at hmem
    rcases hmem with ⟨F, hF, hpF⟩
    obtain ⟨n, hn⟩ := hg ⟨F, hF⟩
    have hfn : f n = F := congrArg Subtype.val hn
    rw [← hfn] at hpF
    exact disjoint_left.mp (hdisj_step n) (hp (n + 1)) hpF
  · rw [not_nonempty_iff_eq_empty] at hne
    obtain ⟨t, ht, hpS⟩ := inG_inter_fiber_nonempty hU₀ (fun _ => false)
    let p := chart U₀.level (fun _ => false) t
    have hpU0 : p ∈ U₀.bar := by
      simp only [p, BHSec.bar, mem_ofPred_eq, chart_coord_self]
      exact ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    refine ⟨p, hpS, fun E hE hpE => ?_⟩
    have hmem := hcov_K E hE ⟨hpE, hpU0⟩
    rw [hne] at hmem
    simp at hmem

/-- Rudin Lemma 2 (p. 17–18): If `E ⊆ V.carrier` and every strip `X` of `V` has a substrip `Y`
    with `Disjoint (Y.carrier ∩ E) S`, then every `U ∈ G(S)` has a strip `U.strip w`
    with `Disjoint (S ∩ (U.strip w).bar) E`. -/
lemma rudin_lemma2 {S : Set BH} {V : BHSec} {E : Set BH} (hEV : E ⊆ V.carrier)
    (hstrip : ∀ w : List Bool, ∃ u : List Bool, Disjoint (((V.strip w).strip u).carrier ∩ E) S)
    {U : BHSec} (hU : inG S U) :
    ∃ w : List Bool, Disjoint (S ∩ (U.strip w).bar) E := by
  -- Helper when V.level ≤ U'.level
  have hge : ∀ (U' : BHSec), inG S U' → V.level ≤ U'.level →
      ∃ w : List Bool, Disjoint (S ∩ (U'.strip w).bar) E := by
    intro U' hU' hle
    let m := U'.level - V.level
    have hVm : V.level + m = U'.level := by omega
    have hind : ∀ L : List (List Bool), (∀ v ∈ L, v.length = m) →
        ∃ w : List Bool, ∀ v ∈ L, Disjoint (S ∩ (U'.strip w).carrier) ((V.strip v).carrier ∩ E) := by
      intro L
      induction L with
      | nil => intro _; exact ⟨[], by simp⟩
      | cons v rest ih =>
        intro hlen
        obtain ⟨w₁, hw₁⟩ := ih (fun v' hv' => hlen v' (List.mem_cons_of_mem v hv'))
        obtain ⟨u, hu⟩ := hstrip (v ++ w₁)
        refine ⟨w₁ ++ u, fun v' hv' => ?_⟩
        rw [List.mem_cons] at hv'
        rcases hv' with hv_eq | hmem
        · subst v'
          rw [disjoint_left]
          rintro x ⟨hxS, hxUw⟩ ⟨hxVv, hxE⟩
          have hcyl : BHSec.inCyl (w₁ ++ u) (bitsAt U'.level x) :=
            ((U'.mem_strip_carrier_iff (w₁ ++ u) x).mp hxUw).2
          have hVvlvl : (V.strip v).level = U'.level := by
            simp [BHSec.strip, hlen v List.mem_cons_self, hVm]
          have hx_strip : x ∈ ((V.strip v).strip (w₁ ++ u)).carrier :=
            ((V.strip v).mem_strip_carrier_iff (w₁ ++ u) x).mpr ⟨hxVv, by rwa [hVvlvl]⟩
          rw [BHSec.strip_append, ← List.append_assoc, ← BHSec.strip_append] at hx_strip
          exact disjoint_left.mp hu ⟨hx_strip, hxE⟩ hxS
        · refine (hw₁ v' hmem).mono_left ?_
          rw [← BHSec.strip_append]
          exact inter_subset_inter_right S ((U'.strip w₁).strip_carrier_subset u)
    obtain ⟨w, hw⟩ := hind (allWords m) (fun v hv => (mem_allWords_iff m v).mp hv)
    refine ⟨w, disjoint_left.mpr fun x ⟨hxS, hxbar⟩ hxE => ?_⟩
    have hxcar : x ∈ (U'.strip w).carrier := by
      rw [(U'.strip w).bar_eq_carrier_union_ends] at hxbar
      exact hxbar.resolve_right fun hEnd => disjoint_left.mp (inG_strip hU' w).1 hxS hEnd
    let v : List Bool := List.ofFn (fun i : Fin m => bitsAt V.level x i)
    have hv_mem : v ∈ allWords m := (mem_allWords_iff m v).mpr List.length_ofFn
    have hxVv : x ∈ (V.strip v).carrier :=
      (V.mem_strip_carrier_iff v x).mpr ⟨hEV hxE, fun i hi => by simp [v]⟩
    exact disjoint_left.mp (hw v hv_mem) ⟨hxS, hxcar⟩ ⟨hxVv, hxE⟩
  by_cases hle : V.level ≤ U.level
  · exact hge U hU hle
  · let w₀ := List.replicate (V.level - U.level) false
    have hU'lvl : V.level ≤ (U.strip w₀).level := by simp [BHSec.strip, w₀]; omega
    obtain ⟨w₁, hw₁⟩ := hge (U.strip w₀) (inG_strip hU w₀) hU'lvl
    refine ⟨w₀ ++ w₁, ?_⟩
    rwa [← BHSec.strip_append]

/-- Rudin's canonical separating sets `𝒮` (Lemma 4, p. 21): separating sets `S` whose
    complement splits into disjoint nonempty open sets `D, E` such that every section meeting `S`
    meets both `D` and `E`. -/
def CanSep (S : Set BH) : Prop :=
  IsClosed S ∧ ∃ D E : Set BH, IsOpen D ∧ IsOpen E ∧ Disjoint D E ∧
    D.Nonempty ∧ E.Nonempty ∧ Sᶜ = D ∪ E ∧
    ∀ U : BHSec, (U.carrier ∩ S).Nonempty →
      (U.carrier ∩ D).Nonempty ∧ (U.carrier ∩ E).Nonempty

lemma canSep_isSepSet {S : Set BH} (h : CanSep S) : IsSepSet S := by
  rcases h with ⟨hcl, D, E, hDo, hEo, hDE, hDne, hEne, hcov, _⟩
  exact ⟨hcl, D, E, hDo, hEo, hDE, hDne, hEne, hcov⟩

/-- Rudin Lemma 4 (p. 21): Every separating set `R` contains a canonical separating set `S ∈ CanSep`. -/
lemma rudin_lemma4 {R : Set BH} (hR : IsSepSet R) : ∃ S : Set BH, CanSep S ∧ S ⊆ R := by
  rcases hR with ⟨_, D₀, E₀, hD₀o, hE₀o, hDE₀, hD₀ne, hE₀ne, hcov₀⟩
  have hne_sec : Nonempty BHSec :=
    ⟨⟨0, 1 / 8, 3 / 8, by norm_num, by norm_num, by norm_num, Or.inl (by norm_num)⟩⟩
  obtain ⟨sec, hsec⟩ := exists_surjective_nat BHSec
  let step : Set BH × Set BH → ℕ → Set BH × Set BH := fun ⟨Dn, En⟩ n =>
    if Disjoint (sec n).carrier Dn then (Dn, En ∪ (sec n).carrier)
    else if Disjoint (sec n).carrier En then (Dn ∪ (sec n).carrier, En)
    else (Dn, En)
  let seq : ℕ → Set BH × Set BH := Nat.rec (D₀, E₀) (fun n p => step p n)
  have hinv : ∀ n, IsOpen (seq n).1 ∧ IsOpen (seq n).2 ∧ Disjoint (seq n).1 (seq n).2 := by
    intro n
    induction n with
    | zero => exact ⟨hD₀o, hE₀o, hDE₀⟩
    | succ n ih =>
      rcases ih with ⟨hDo, hEo, hDE⟩
      change IsOpen (step (seq n) n).1 ∧ IsOpen (step (seq n) n).2 ∧
        Disjoint (step (seq n) n).1 (step (seq n) n).2
      dsimp only [step]
      split_ifs with h1 h2
      · exact ⟨hDo, hEo.union (sec n).isOpen_carrier, disjoint_union_right.mpr ⟨hDE, h1.symm⟩⟩
      · exact ⟨hDo.union (sec n).isOpen_carrier, hEo, disjoint_union_left.mpr ⟨hDE, h2⟩⟩
      · exact ⟨hDo, hEo, hDE⟩
  have hmono1 : Monotone (fun n => (seq n).1) := monotone_nat_of_le_succ fun n => by
    change (seq n).1 ⊆ (step (seq n) n).1; dsimp only [step]; split_ifs <;> simp [subset_union_left]
  have hmono2 : Monotone (fun n => (seq n).2) := monotone_nat_of_le_succ fun n => by
    change (seq n).2 ⊆ (step (seq n) n).2; dsimp only [step]; split_ifs <;> simp [subset_union_left]
  let D : Set BH := ⋃ n, (seq n).1
  let E : Set BH := ⋃ n, (seq n).2
  let S : Set BH := (D ∪ E)ᶜ
  have hDo : IsOpen D := isOpen_iUnion fun n => (hinv n).1
  have hEo : IsOpen E := isOpen_iUnion fun n => (hinv n).2.1
  have hDE : Disjoint D E := by
    rw [disjoint_left]
    intro x hxD hxE
    rcases mem_iUnion.mp hxD with ⟨m, hm⟩
    rcases mem_iUnion.mp hxE with ⟨n, hn⟩
    exact disjoint_left.mp (hinv (max m n)).2.2
      (hmono1 (le_max_left m n) hm) (hmono2 (le_max_right m n) hn)
  have hDne : D.Nonempty := hD₀ne.mono (subset_iUnion (fun n => (seq n).1) 0)
  have hEne : E.Nonempty := hE₀ne.mono (subset_iUnion (fun n => (seq n).2) 0)
  have hSR : S ⊆ R := by
    intro x hxS
    by_contra hxR
    have hx0 : x ∈ D₀ ∪ E₀ := by rw [← hcov₀]; exact hxR
    apply hxS
    rcases hx0 with hD0 | hE0
    · exact Or.inl (mem_iUnion.mpr ⟨0, hD0⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨0, hE0⟩)
  refine ⟨S, ⟨(hDo.union hEo).isClosed_compl, D, E, hDo, hEo, hDE, hDne, hEne, compl_compl _, ?_⟩, hSR⟩
  intro U ⟨x, hxU, hxS⟩
  obtain ⟨n, hn⟩ := hsec U
  constructor
  · by_contra hno
    have hdisjD : Disjoint U.carrier D := Set.not_nonempty_iff_eq_empty.mp hno |> disjoint_iff_inter_eq_empty.mpr
    have hdisjDn : Disjoint (sec n).carrier (seq n).1 := by
      rw [hn]; exact hdisjD.mono_right (subset_iUnion (fun k => (seq k).1) n)
    have hU_sub_E : U.carrier ⊆ (seq (n + 1)).2 := by
      change U.carrier ⊆ (step (seq n) n).2
      dsimp only [step]
      rw [if_pos hdisjDn, hn]
      exact subset_union_right
    exact hxS (Or.inr (mem_iUnion.mpr ⟨n + 1, hU_sub_E hxU⟩))
  · by_contra hno
    have hdisjE : Disjoint U.carrier E := Set.not_nonempty_iff_eq_empty.mp hno |> disjoint_iff_inter_eq_empty.mpr
    have hdisjEn : Disjoint (sec n).carrier (seq n).2 := by
      rw [hn]; exact hdisjE.mono_right (subset_iUnion (fun k => (seq k).2) n)
    by_cases h1 : Disjoint (sec n).carrier (seq n).1
    · have hU_sub_E : U.carrier ⊆ (seq (n + 1)).2 := by
        change U.carrier ⊆ (step (seq n) n).2; dsimp only [step]; rw [if_pos h1, hn]; exact subset_union_right
      exact hxS (Or.inr (mem_iUnion.mpr ⟨n + 1, hU_sub_E hxU⟩))
    · have hU_sub_D : U.carrier ⊆ (seq (n + 1)).1 := by
        change U.carrier ⊆ (step (seq n) n).1; dsimp only [step]; rw [if_neg h1, if_pos hdisjEn, hn]
        exact subset_union_right
      exact hxS (Or.inl (mem_iUnion.mpr ⟨n + 1, hU_sub_D hxU⟩))

/- Helper lemmas for Rudin's Lemma 3 -/

/-- Basic countable neighborhood basis around `q ∈ BH`. -/
def bhBall (q : BH) (i : ℕ) : Set BH :=
  {y | ∀ n ≤ i, |y.1 n - q.1 n| < 1 / ((i : ℝ) + 1)}

lemma isOpen_bhBall (q : BH) (i : ℕ) : IsOpen (bhBall q i) := by
  have heq : bhBall q i = ⋂ n ∈ Finset.range (i + 1), {y : BH | |y.1 n - q.1 n| < 1 / ((i : ℝ) + 1)} := by
    ext y
    simp only [bhBall, mem_ofPred_eq, mem_iInter, Finset.mem_range, Nat.lt_succ_iff]
  rw [heq]
  exact isOpen_biInter_finset fun n _ =>
    isOpen_lt (continuous_abs.comp ((continuous_bhCoord n).sub continuous_const)) continuous_const

lemma mem_bhBall_self (q : BH) (i : ℕ) : q ∈ bhBall q i := by
  intro n _
  rw [sub_self, abs_zero]
  positivity

lemma exists_bhBall_subset_of_isOpen {q : BH} {G : Set BH} (hG : IsOpen G) (hq : q ∈ G) :
    ∃ i : ℕ, bhBall q i ⊆ G := by
  have hnhds : G ∈ 𝓝 q := hG.mem_nhds hq
  rw [nhds_induced] at hnhds
  rcases hnhds with ⟨V, hV, hVG⟩
  rw [nhds_pi, Filter.mem_pi'] at hV
  rcases hV with ⟨I, t, ht, hIt⟩
  have hball : ∀ n ∈ I, ∃ r : ℝ, 0 < r ∧ Metric.ball (q.1 n) r ⊆ t n :=
    fun n _ => Metric.mem_nhds_iff.mp (ht n)
  let rad : ℕ → ℝ := fun n => if h : n ∈ I then (hball n h).choose else 1
  let I' := insert 0 I
  let rmin : ℝ := I'.inf' (Finset.insert_nonempty 0 I) rad
  have hrmin_pos : 0 < rmin := (Finset.lt_inf'_iff _).mpr fun n _ => by
    unfold rad; split_ifs with h; exact (hball n h).choose_spec.1; norm_num
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / rmin)
  let i := max (I.sup id) N
  refine ⟨i, fun y hy => hVG (hIt fun n hn => ?_)⟩
  have hn' : n ∈ I := Finset.mem_coe.mp hn
  have hni : n ≤ i := le_trans (Finset.le_sup (f := id) hn') (le_max_left _ _)
  have hrad_le : rmin ≤ (hball n hn').choose := by
    have h1 : rmin ≤ rad n := Finset.inf'_le (s := I') rad (Finset.mem_insert_of_mem (b := 0) hn')
    change rmin ≤ (if h : n ∈ I then (hball n h).choose else 1) at h1
    rwa [dif_pos hn'] at h1
  apply (hball n hn').choose_spec.2
  rw [Metric.mem_ball, Real.dist_eq]
  have h1 : |y.1 n - q.1 n| < 1 / ((i : ℝ) + 1) := hy n hni
  have h2 : 1 / ((i : ℝ) + 1) < rmin := by
    rw [div_lt_iff₀ (by positivity)]
    have hNi : (N : ℝ) ≤ i := by exact_mod_cast le_max_right (I.sup id) N
    have hgt : 1 / rmin < (i : ℝ) + 1 := by linarith
    have := (div_lt_iff₀ hrmin_pos).mp hgt
    linarith
  linarith

/-- Cantor diagonalization: every cylinder contains an infinite bit sequence outside any countable set. -/
lemma exists_inCyl_avoiding_countable (w : List Bool) {C : Set (ℕ → Bool)} (hC : C.Countable) :
    ∃ ε : ℕ → Bool, BHSec.inCyl w ε ∧ ε ∉ C := by
  by_cases hCne : C.Nonempty
  · have : Countable C := hC.to_subtype
    have : Nonempty C := hCne.to_subtype
    obtain ⟨g, hg⟩ := exists_surjective_nat C
    let η : ℕ → Bool := fun j => !(g j).1 (w.length + j)
    refine ⟨prependWord w η, BHSec.inCyl_prepend w η, fun hmem => ?_⟩
    obtain ⟨j, hj⟩ := hg ⟨prependWord w η, hmem⟩
    have h1 := congrFun (congrArg Subtype.val hj) (w.length + j)
    have h2 : prependWord w η (w.length + j) = η j := by
      unfold prependWord
      rw [dif_neg (by omega), Nat.add_sub_cancel_left]
    dsimp only at h1
    rw [h2] at h1
    dsimp only [η] at h1
    cases hb : (g j).1 (w.length + j) <;> simp [hb] at h1
  · rw [not_nonempty_iff_eq_empty] at hCne
    exact ⟨prependWord w (fun _ => false), BHSec.inCyl_prepend w _, by simp [hCne]⟩

/-- Cylinder inclusion `inCyl u ⊆ inCyl w` implies `u` extends `w`. -/
lemma inCyl_prefix_of_subset {w u : List Bool}
    (h : ∀ ε : ℕ → Bool, BHSec.inCyl u ε → BHSec.inCyl w ε) :
    ∃ s : List Bool, u = w ++ s := by
  have hlen : w.length ≤ u.length := by
    by_contra hlt; push Not at hlt
    have h0 := h (prependWord u (fun _ => false)) (BHSec.inCyl_prepend u _) u.length hlt
    have h1 := h (prependWord u (fun _ => true)) (BHSec.inCyl_prepend u _) u.length hlt
    have he0 : prependWord u (fun _ => false) u.length = false := by
      unfold prependWord; rw [dif_neg (lt_irrefl _)]
    have he1 : prependWord u (fun _ => true) u.length = true := by
      unfold prependWord; rw [dif_neg (lt_irrefl _)]
    rw [he0] at h0; rw [he1] at h1
    exact Bool.false_ne_true (h0.trans h1.symm)
  refine ⟨u.drop w.length, ?_⟩
  have htake : u.take w.length = w := by
    apply List.ext_getElem (by simp [hlen])
    intro i hi1 hi2
    have h0 := h (prependWord u (fun _ => false)) (BHSec.inCyl_prepend u _) i hi2
    have hiu : i < u.length := lt_of_lt_of_le hi2 hlen
    have he : prependWord u (fun _ => false) i = u[i] := by unfold prependWord; rw [dif_pos hiu]
    rw [List.getElem_take, ← he, h0]
  conv_lhs => rw [← List.take_append_drop w.length u, htake]

/-- If `E : BHSec` has `V.level ≤ E.level` and meets both `{x | x.1 V.level < V.lo}` and
    `{x | V.hi < x.1 V.level}`, then `E` contains a full strip `V.strip w` of `V`. -/
lemma exists_strip_subset_of_meets_R1_R2 {V E : BHSec} (hle : V.level ≤ E.level)
    {y₁ y₂ : BH} (hy₁E : y₁ ∈ E.carrier) (hy₁R1 : y₁.1 V.level < (V.lo : ℝ))
    (hy₂E : y₂ ∈ E.carrier) (hy₂R2 : (V.hi : ℝ) < y₂.1 V.level) :
    ∃ w : List Bool, w.length = E.level - V.level ∧ (V.strip w).carrier ⊆ E.carrier := by
  let m := E.level - V.level
  let s₁ := y₁.1 E.level
  let s₂ := y₂.1 E.level
  have hf1 : tent^[m] s₁ = y₁.1 V.level := bh_tent_iterate_of_le y₁ hle
  have hf2 : tent^[m] s₂ = y₂.1 V.level := bh_tent_iterate_of_le y₂ hle
  let a := min s₁ s₂
  let b := max s₁ s₂
  have hab_sub : Icc a b ⊆ Ioo (E.lo : ℝ) (E.hi : ℝ) := fun t ht =>
    ⟨lt_of_lt_of_le (lt_min hy₁E.1 hy₂E.1) ht.1, lt_of_le_of_lt ht.2 (max_lt hy₁E.2 hy₂E.2)⟩
  have hmid_mem : ((V.lo : ℝ) + (V.hi : ℝ)) / 2 ∈ tent^[m] '' Icc a b := by
    have hconn : IsPreconnected (tent^[m] '' Icc a b) :=
      isPreconnected_Icc.image _ (continuous_tent.iterate m).continuousOn
    have h1 : y₁.1 V.level ∈ tent^[m] '' Icc a b := ⟨s₁, ⟨min_le_left _ _, le_max_left _ _⟩, hf1⟩
    have h2 : y₂.1 V.level ∈ tent^[m] '' Icc a b := ⟨s₂, ⟨min_le_right _ _, le_max_right _ _⟩, hf2⟩
    exact hconn.Icc_subset h1 h2 ⟨by linarith [V.lo_lt_hi_real], by linarith [V.lo_lt_hi_real]⟩
  rcases hmid_mem with ⟨tstar, htstar_J, htstar_f⟩
  have htstar_icc : tstar ∈ Icc (0 : ℝ) 1 :=
    ⟨le_of_lt (lt_trans E.lo_pos_real (hab_sub htstar_J).1),
     le_of_lt (lt_trans (hab_sub htstar_J).2 E.hi_lt_one_real)⟩
  let xstar : BH := chart E.level (fun _ => false) ⟨tstar, htstar_icc⟩
  have hxstar_E : xstar.1 E.level = tstar := chart_coord_self E.level _ _
  have hxstar_V : xstar.1 V.level = ((V.lo : ℝ) + (V.hi : ℝ)) / 2 := by
    rw [← bh_tent_iterate_of_le xstar hle, hxstar_E, htstar_f]
  let w : List Bool := List.ofFn (fun i : Fin m => bitsAt V.level xstar i)
  have hwlen : w.length = m := List.length_ofFn
  have hstrip_lvl : (V.strip w).level = E.level := by simp [BHSec.strip, hwlen, m]; omega
  have hxstar_strip : xstar ∈ (V.strip w).carrier := by
    rw [V.mem_strip_carrier_iff w xstar]
    refine ⟨?_, fun i hi => by simp [w]⟩
    change (V.lo : ℝ) < xstar.1 V.level ∧ xstar.1 V.level < V.hi
    rw [hxstar_V]; constructor <;> linarith [V.lo_lt_hi_real]
  have htstar_ioo : tstar ∈ Ioo ((V.strip w).lo : ℝ) ((V.strip w).hi : ℝ) := by
    have h : (V.strip w).lo < xstar.1 (V.strip w).level ∧ xstar.1 (V.strip w).level < (V.strip w).hi := hxstar_strip
    rwa [hstrip_lvl, hxstar_E] at h
  have hnot_in : ∀ s ∈ ({s₁, s₂} : Set ℝ), s ∉ Icc ((V.strip w).lo : ℝ) ((V.strip w).hi : ℝ) := by
    intro s hs hmem
    have hs_icc : s ∈ Icc (0 : ℝ) 1 :=
      ⟨le_of_lt (lt_of_lt_of_le (V.strip w).lo_pos_real hmem.1),
       le_of_lt (lt_of_le_of_lt hmem.2 (V.strip w).hi_lt_one_real)⟩
    let z := chart E.level (fun _ => false) ⟨s, hs_icc⟩
    have hz_strip : z ∈ (V.strip w).bar := by
      change ((V.strip w).lo : ℝ) ≤ z.1 (V.strip w).level ∧ z.1 (V.strip w).level ≤ (V.strip w).hi
      rw [hstrip_lvl, chart_coord_self]; exact hmem
    have hz_V : z ∈ V.bar := ((V.mem_strip_bar_iff w z).mp hz_strip).1
    have hzf : tent^[m] s = z.1 V.level := by
      have := bh_tent_iterate_of_le z hle; rwa [chart_coord_self] at this
    rcases hs with rfl | rfl
    · linarith [hz_V.1, hf1]
    · linarith [hz_V.2, hf2]
  have ha_lt : a < ((V.strip w).lo : ℝ) := by
    by_contra hge; push Not at hge
    have ha_mem : a ∈ Icc ((V.strip w).lo : ℝ) ((V.strip w).hi : ℝ) :=
      ⟨hge, le_trans htstar_J.1 (le_of_lt htstar_ioo.2)⟩
    rcases min_choice s₁ s₂ with h | h
    · exact hnot_in s₁ (Or.inl rfl) (h ▸ ha_mem)
    · exact hnot_in s₂ (Or.inr rfl) (h ▸ ha_mem)
  have hb_gt : ((V.strip w).hi : ℝ) < b := by
    by_contra hle'; push Not at hle'
    have hb_mem : b ∈ Icc ((V.strip w).lo : ℝ) ((V.strip w).hi : ℝ) :=
      ⟨le_trans (le_of_lt htstar_ioo.1) htstar_J.2, hle'⟩
    rcases max_choice s₁ s₂ with h | h
    · exact hnot_in s₁ (Or.inl rfl) (h ▸ hb_mem)
    · exact hnot_in s₂ (Or.inr rfl) (h ▸ hb_mem)
  refine ⟨w, hwlen, fun x hx => ?_⟩
  change (E.lo : ℝ) < x.1 E.level ∧ x.1 E.level < E.hi
  have hx' : ((V.strip w).lo : ℝ) < x.1 E.level ∧ x.1 E.level < ((V.strip w).hi : ℝ) := by
    rwa [← hstrip_lvl]
  exact ⟨lt_trans (lt_min hy₁E.1 hy₂E.1) (lt_trans ha_lt hx'.1),
    lt_trans hx'.2 (lt_trans hb_gt (max_lt hy₁E.2 hy₂E.2))⟩

/-- Unified Corridor Lemma for Rudin Lemma 3 Property (B): if `Z` is a block of `V.strip w`,
    and `E'` (`V.level ≤ E'.level`) avoids `R₂`, meets `R₁`, and meets the `R₂`-side of `Z`
    inside `(V.strip w).bar`, then `E'` contains a strip `Z.strip u` of `Z`. -/
lemma corridor_strip_subset {V Z E' : BHSec} {w : List Bool} (hblk : BHSec.IsBlock Z (V.strip w))
    (hle : V.level ≤ E'.level)
    (hnoR2 : Disjoint E'.carrier {x : BH | (V.hi : ℝ) < x.1 V.level})
    {y₁ y : BH} (hy₁E : y₁ ∈ E'.carrier) (hy₁R1 : y₁.1 V.level < (V.lo : ℝ))
    (hyE : y ∈ E'.carrier) (hybar : y ∈ (V.strip w).bar)
    (hyside : (branchParity w = false → (Z.hi : ℝ) < y.1 Z.level) ∧
              (branchParity w = true → y.1 Z.level < (Z.lo : ℝ))) :
    ∃ u : List Bool, (Z.strip u).carrier ⊆ E'.carrier := by
  have hZlvl : Z.level = V.level + w.length := hblk.1
  have hlo_r : ((V.strip w).lo : ℝ) = min (branchWord w V.lo) (branchWord w V.hi) := by
    simp [BHSec.strip, branchWordQ_cast]
  have hhi_r : ((V.strip w).hi : ℝ) = max (branchWord w V.lo) (branchWord w V.hi) := by
    simp [BHSec.strip, branchWordQ_cast]
  have hma := branchWord_strictMono_or_anti w V.lo_lt_hi_real
  -- Helper: no point of E' has V.level coordinate > V.hi
  have hE'_le_hi : ∀ z ∈ E'.carrier, z.1 V.level ≤ (V.hi : ℝ) := fun z hz =>
    not_lt.mp fun hgt => disjoint_left.mp hnoR2 hz hgt
  by_cases hEk : E'.level < Z.level
  · -- Subcase E'.level < Z.level: show Z.carrier ⊆ E'.carrier (u = [])
    let d := E'.level - V.level
    have hd_lt : d < w.length := by omega
    let w' := w.take d
    have hw'_len : w'.length = d := by simp [w', le_of_lt hd_lt]
    have hVd : V.level + d = E'.level := by omega
    -- Show y.1 V.level > z.1 V.level for every z ∈ Z.carrier
    have hV_lt_y : ∀ z ∈ Z.carrier, z.1 V.level < y.1 V.level := by
      intro z hz
      have hz_strip : z ∈ (V.strip w).carrier := BHSec.isBlock_carrier_subset hblk hz
      have hzy : z.1 Z.level < y.1 Z.level ∧ branchParity w = false ∨
                 y.1 Z.level < z.1 Z.level ∧ branchParity w = true := by
        cases hp : branchParity w
        · left; exact ⟨lt_trans hz.2 (hyside.1 hp), rfl⟩
        · right; exact ⟨lt_trans (hyside.2 hp) hz.1, rfl⟩
      have hzb : branchWord w (z.1 V.level) = z.1 Z.level := by
        have hcyl := ((V.mem_strip_carrier_iff w z).mp hz_strip).2
        have hprep : bitsAt V.level z = prependWord w (bitsAt (V.level + w.length) z) := by
          funext n; unfold prependWord; by_cases hn : n < w.length
          · rw [dif_pos hn]; exact hcyl n hn
          · rw [dif_neg hn]; simp only [bitsAt]; apply congrArg (fun k => decide (1 / 2 < z.1 k)); omega
        have h1 := chart_shift_word V.level w (bitsAt (V.level + w.length) z) ⟨z.1 V.level, bh_mem_Icc z V.level⟩
        rw [← hprep, chart_bitsAt] at h1
        have := congrArg (fun q : BH => q.1 (V.level + w.length)) h1
        rw [chart_coord_self] at this; rw [hZlvl]; exact this
      have hyb : branchWord w (y.1 V.level) = y.1 Z.level := by
        have hcyl := ((V.mem_strip_bar_iff w y).mp hybar).2
        have hprep : bitsAt V.level y = prependWord w (bitsAt (V.level + w.length) y) := by
          funext n; unfold prependWord; by_cases hn : n < w.length
          · rw [dif_pos hn]; exact hcyl n hn
          · rw [dif_neg hn]; simp only [bitsAt]; apply congrArg (fun k => decide (1 / 2 < y.1 k)); omega
        have h1 := chart_shift_word V.level w (bitsAt (V.level + w.length) y) ⟨y.1 V.level, bh_mem_Icc y V.level⟩
        rw [← hprep, chart_bitsAt] at h1
        have := congrArg (fun q : BH => q.1 (V.level + w.length)) h1
        rw [chart_coord_self] at this; rw [hZlvl]; exact this
      by_contra hge; push Not at hge
      rcases eq_or_lt_of_le hge with heq | hlt
      · rw [heq] at hyb
        rcases hzy with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith [hzb, hyb]
      · have hm' := branchWord_strictMono_or_anti w hlt
        rcases hzy with ⟨h1, hp⟩ | ⟨h1, hp⟩
        · linarith [hm'.1 hp, hzb, hyb]
        · linarith [hm'.2 hp, hzb, hyb]
    -- Show branchWord w' (z.1 V.level) = z.1 E'.level for z ∈ (V.strip w).bar
    have hbw'_eq : ∀ z ∈ (V.strip w).bar, branchWord w' (z.1 V.level) = z.1 E'.level := by
      intro z hz
      have hcyl : BHSec.inCyl w (bitsAt V.level z) := ((V.mem_strip_bar_iff w z).mp hz).2
      have hcyl' : BHSec.inCyl w' (bitsAt V.level z) := fun i hi => by
        rw [hw'_len] at hi
        have h := hcyl i (lt_trans hi hd_lt)
        rwa [List.getElem_take]
      have hprep : bitsAt V.level z = prependWord w' (bitsAt (V.level + w'.length) z) := by
        funext n; unfold prependWord; by_cases hn : n < w'.length
        · rw [dif_pos hn]; exact hcyl' n hn
        · rw [dif_neg hn]; simp only [bitsAt]; apply congrArg (fun k => decide (1 / 2 < z.1 k)); omega
      have h1 := chart_shift_word V.level w' (bitsAt (V.level + w'.length) z) ⟨z.1 V.level, bh_mem_Icc z V.level⟩
      rw [← hprep, chart_bitsAt] at h1
      have := congrArg (fun q : BH => q.1 (V.level + w'.length)) h1
      rw [chart_coord_self, hw'_len, hVd] at this; exact this
    have hy_V_gt_lo : (V.lo : ℝ) < y.1 V.level := by
      let t0 : ℝ := ((Z.lo : ℝ) + (Z.hi : ℝ)) / 2
      have ht0_Z : t0 ∈ Ioo (Z.lo : ℝ) (Z.hi : ℝ) := by dsimp only [t0]; constructor <;> linarith [Z.lo_lt_hi_real]
      have ht0_icc : t0 ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt (lt_trans Z.lo_pos_real ht0_Z.1), le_of_lt (lt_trans ht0_Z.2 Z.hi_lt_one_real)⟩
      let z0 := chart Z.level (fun _ => false) ⟨t0, ht0_icc⟩
      have hz0Z : z0 ∈ Z.carrier := by simp only [z0, BHSec.carrier, mem_ofPred_eq, chart_coord_self]; exact ht0_Z
      have hz0V : z0 ∈ V.carrier := (V.strip_carrier_subset w) (BHSec.isBlock_carrier_subset hblk hz0Z)
      exact lt_trans hz0V.1 (hV_lt_y z0 hz0Z)
    have hy_V_le_hi : y.1 V.level ≤ (V.hi : ℝ) := (((V.mem_strip_bar_iff w y).mp hybar).1).2
    let t_bad : ℝ := ((V.hi : ℝ) + 1) / 2
    have ht_bad_gt : (V.hi : ℝ) < t_bad := by dsimp only [t_bad]; linarith [V.hi_lt_one_real]
    have ht_bad_icc : t_bad ∈ Icc (0 : ℝ) 1 := ⟨by dsimp only [t_bad]; linarith [V.lo_pos_real, V.lo_lt_hi_real],
      by dsimp only [t_bad]; linarith [V.hi_lt_one_real]⟩
    have hbad_not_E' : branchWord w' t_bad ∉ Icc (min (y₁.1 E'.level) (y.1 E'.level)) (max (y₁.1 E'.level) (y.1 E'.level)) := by
      intro hmem
      have hioo : branchWord w' t_bad ∈ Ioo (E'.lo : ℝ) (E'.hi : ℝ) :=
        ⟨lt_of_lt_of_le (lt_min hy₁E.1 hyE.1) hmem.1, lt_of_le_of_lt hmem.2 (max_lt hy₁E.2 hyE.2)⟩
      let q := chart E'.level (fun _ => false) ⟨branchWord w' t_bad, branchWord_mem_Icc w' ht_bad_icc⟩
      have hqE' : q ∈ E'.carrier := by simp only [q, BHSec.carrier, mem_ofPred_eq, chart_coord_self]; exact hioo
      have hqV : q.1 V.level = t_bad := by
        rw [← bh_tent_iterate_of_le q hle, chart_coord_self, show E'.level - V.level = w'.length by omega]
        exact tent_iterate_branchWord w' ht_bad_icc
      linarith [hE'_le_hi q hqE', hqV]
    have hnot_in_lo_y : y₁.1 E'.level ∉ Icc (min (branchWord w' V.lo) (branchWord w' (y.1 V.level)))
        (max (branchWord w' V.lo) (branchWord w' (y.1 V.level))) := by
      intro hmem
      have hsurj : ∃ t ∈ Icc (V.lo : ℝ) (y.1 V.level), branchWord w' t = y₁.1 E'.level := by
        have hcont_bw : Continuous (branchWord w') := by
          have hc : Continuous (fun t : ℝ => branchWord w' 0 + branchSign w' * t / (2 : ℝ) ^ w'.length) := by fun_prop
          exact hc.congr fun t => (branchWord_affine w' t).symm
        have hconn : IsPreconnected (branchWord w' '' Icc (V.lo : ℝ) (y.1 V.level)) :=
          isPreconnected_Icc.image (branchWord w') hcont_bw.continuousOn
        have h1 : branchWord w' V.lo ∈ branchWord w' '' Icc (V.lo : ℝ) (y.1 V.level) :=
          ⟨V.lo, ⟨le_rfl, le_of_lt hy_V_gt_lo⟩, rfl⟩
        have h2 : branchWord w' (y.1 V.level) ∈ branchWord w' '' Icc (V.lo : ℝ) (y.1 V.level) :=
          ⟨y.1 V.level, ⟨le_of_lt hy_V_gt_lo, le_rfl⟩, rfl⟩
        exact hconn.Icc_subset (by rcases min_choice (branchWord w' V.lo) (branchWord w' (y.1 V.level)) with h | h <;> rw [h] <;> assumption)
          (by rcases max_choice (branchWord w' V.lo) (branchWord w' (y.1 V.level)) with h | h <;> rw [h] <;> assumption) hmem
      rcases hsurj with ⟨t, ht, hbt⟩
      have ht_icc : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt (lt_of_lt_of_le V.lo_pos_real ht.1),
        le_of_lt (lt_of_le_of_lt (le_trans ht.2 hy_V_le_hi) V.hi_lt_one_real)⟩
      have hf : y₁.1 V.level = t := by
        rw [← bh_tent_iterate_of_le y₁ hle, ← hbt, show E'.level - V.level = w'.length by omega]
        exact tent_iterate_branchWord w' ht_icc
      linarith [ht.1]
    -- Conclude Z.carrier ⊆ E'.carrier
    refine ⟨[], fun z hz => ?_⟩
    rw [Z.strip_nil] at hz
    have hz_bar : z ∈ (V.strip w).bar := BHSec.isBlock_bar_subset hblk (Z.carrier_subset_bar hz)
    have hz_V_lo : (V.lo : ℝ) < z.1 V.level := ((V.strip_carrier_subset w) (BHSec.isBlock_carrier_subset hblk hz)).1
    have hz_V_y : z.1 V.level < y.1 V.level := hV_lt_y z hz
    have hze : z.1 E'.level = branchWord w' (z.1 V.level) := (hbw'_eq z hz_bar).symm
    have hye : y.1 E'.level = branchWord w' (y.1 V.level) := (hbw'_eq y hybar).symm
    cases hp' : branchParity w'
    · have h1 : branchWord w' V.lo < branchWord w' (z.1 V.level) := (branchWord_strictMono_or_anti w' hz_V_lo).1 hp'
      have h2 : branchWord w' (z.1 V.level) < branchWord w' (y.1 V.level) := (branchWord_strictMono_or_anti w' hz_V_y).1 hp'
      have h3 : branchWord w' (y.1 V.level) < branchWord w' t_bad :=
        (branchWord_strictMono_or_anti w' (lt_of_le_of_lt hy_V_le_hi ht_bad_gt)).1 hp'
      have hy1_lt : y₁.1 E'.level < branchWord w' V.lo := by
        by_contra hge; push Not at hge
        by_cases hle' : y₁.1 E'.level ≤ branchWord w' (y.1 V.level)
        · apply hnot_in_lo_y
          rw [min_eq_left (le_of_lt (lt_trans h1 h2)), max_eq_right (le_of_lt (lt_trans h1 h2))]
          exact ⟨hge, hle'⟩
        · push Not at hle'
          by_cases hbad : branchWord w' t_bad ≤ y₁.1 E'.level
          · apply hbad_not_E'
            rw [min_eq_right (le_of_lt (by rwa [hye])), max_eq_left (le_of_lt (by rwa [hye]))]
            exact ⟨le_of_lt (by rwa [hye]), hbad⟩
          · push Not at hbad
            have hsurj : ∃ t ∈ Ioo (y.1 V.level) t_bad, branchWord w' t = y₁.1 E'.level := by
              have h2pos : (0 : ℝ) < (2 : ℝ) ^ w'.length := by positivity
              let t := (y₁.1 E'.level - branchWord w' 0) * (2 : ℝ) ^ w'.length
              have hbt : branchWord w' t = y₁.1 E'.level := by
                rw [branchWord_affine w' t]; simp only [branchSign, hp', Bool.false_eq_true, ↓reduceIte, one_mul, t]
                field_simp; ring
              have hmem_ioo : branchWord w' t ∈ Ioo (min (branchWord w' (y.1 V.level)) (branchWord w' t_bad))
                  (max (branchWord w' (y.1 V.level)) (branchWord w' t_bad)) := by
                rw [min_eq_left (le_of_lt h3), max_eq_right (le_of_lt h3), hbt]; exact ⟨hle', hbad⟩
              exact ⟨t, (branchWord_mem_Ioo_iff w' (lt_of_le_of_lt hy_V_le_hi ht_bad_gt)).mp hmem_ioo, hbt⟩
            rcases hsurj with ⟨t, ht, hbt⟩
            have ht_icc : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt (lt_trans V.lo_pos_real (lt_trans hy_V_gt_lo ht.1)),
              le_of_lt (lt_of_lt_of_le ht.2 ht_bad_icc.2)⟩
            have hf : y₁.1 V.level = t := by
              rw [← bh_tent_iterate_of_le y₁ hle, ← hbt, show E'.level - V.level = w'.length by omega]
              exact tent_iterate_branchWord w' ht_icc
            linarith [ht.1, hy_V_gt_lo]
      change (E'.lo : ℝ) < z.1 E'.level ∧ z.1 E'.level < E'.hi
      rw [hze]; exact ⟨lt_trans hy₁E.1 (lt_trans hy1_lt h1), lt_trans h2 (by rw [← hye]; exact hyE.2)⟩
    · have h1 : branchWord w' (z.1 V.level) < branchWord w' V.lo := (branchWord_strictMono_or_anti w' hz_V_lo).2 hp'
      have h2 : branchWord w' (y.1 V.level) < branchWord w' (z.1 V.level) := (branchWord_strictMono_or_anti w' hz_V_y).2 hp'
      have h3 : branchWord w' t_bad < branchWord w' (y.1 V.level) :=
        (branchWord_strictMono_or_anti w' (lt_of_le_of_lt hy_V_le_hi ht_bad_gt)).2 hp'
      have hy1_gt : branchWord w' V.lo < y₁.1 E'.level := by
        by_contra hle'; push Not at hle'
        by_cases hge : branchWord w' (y.1 V.level) ≤ y₁.1 E'.level
        · apply hnot_in_lo_y
          rw [min_eq_right (le_of_lt (lt_trans h2 h1)), max_eq_left (le_of_lt (lt_trans h2 h1))]
          exact ⟨hge, hle'⟩
        · push Not at hge
          by_cases hbad : y₁.1 E'.level ≤ branchWord w' t_bad
          · apply hbad_not_E'
            rw [min_eq_left (le_of_lt (by rwa [hye])), max_eq_right (le_of_lt (by rwa [hye]))]
            exact ⟨hbad, le_of_lt (by rwa [hye])⟩
          · push Not at hbad
            have hsurj : ∃ t ∈ Ioo (y.1 V.level) t_bad, branchWord w' t = y₁.1 E'.level := by
              have h2pos : (0 : ℝ) < (2 : ℝ) ^ w'.length := by positivity
              let t := -(y₁.1 E'.level - branchWord w' 0) * (2 : ℝ) ^ w'.length
              have hbt : branchWord w' t = y₁.1 E'.level := by
                rw [branchWord_affine w' t]; simp only [branchSign, hp', ↓reduceIte, neg_mul, one_mul, t]
                field_simp; ring
              have hmem_ioo : branchWord w' t ∈ Ioo (min (branchWord w' (y.1 V.level)) (branchWord w' t_bad))
                  (max (branchWord w' (y.1 V.level)) (branchWord w' t_bad)) := by
                rw [min_eq_right (le_of_lt h3), max_eq_left (le_of_lt h3), hbt]; exact ⟨hbad, hge⟩
              exact ⟨t, (branchWord_mem_Ioo_iff w' (lt_of_le_of_lt hy_V_le_hi ht_bad_gt)).mp hmem_ioo, hbt⟩
            rcases hsurj with ⟨t, ht, hbt⟩
            have ht_icc : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt (lt_trans V.lo_pos_real (lt_trans hy_V_gt_lo ht.1)),
              le_of_lt (lt_of_lt_of_le ht.2 ht_bad_icc.2)⟩
            have hf : y₁.1 V.level = t := by
              rw [← bh_tent_iterate_of_le y₁ hle, ← hbt, show E'.level - V.level = w'.length by omega]
              exact tent_iterate_branchWord w' ht_icc
            linarith [ht.1, hy_V_gt_lo]
      change (E'.lo : ℝ) < z.1 E'.level ∧ z.1 E'.level < E'.hi
      rw [hze]; exact ⟨lt_trans (by rw [← hye]; exact hyE.1) h2, lt_trans h1 (lt_trans hy1_gt hy₁E.2)⟩
  · -- Subcase Z.level ≤ E'.level: show y₁.1 Z.level lies on the opposite side of Z from y.1 Z.level, then apply exists_strip_subset_of_meets_R1_R2!
    push Not at hEk
    let r := E'.level - Z.level
    let s₁ := y₁.1 E'.level
    let s₂ := y.1 E'.level
    have hf1 : tent^[r] s₁ = y₁.1 Z.level := bh_tent_iterate_of_le y₁ hEk
    have hf2 : tent^[r] s₂ = y.1 Z.level := bh_tent_iterate_of_le y hEk
    let a := min s₁ s₂
    let b := max s₁ s₂
    have hab_sub : Icc a b ⊆ Ioo (E'.lo : ℝ) (E'.hi : ℝ) := fun t ht =>
      ⟨lt_of_lt_of_le (lt_min hy₁E.1 hyE.1) ht.1, lt_of_le_of_lt ht.2 (max_lt hy₁E.2 hyE.2)⟩
    have hconn_r : IsPreconnected (tent^[r] '' Icc a b) :=
      isPreconnected_Icc.image _ (continuous_tent.iterate r).continuousOn
    have h1_img : y₁.1 Z.level ∈ tent^[r] '' Icc a b := ⟨s₁, ⟨min_le_left _ _, le_max_left _ _⟩, hf1⟩
    have h2_img : y.1 Z.level ∈ tent^[r] '' Icc a b := ⟨s₂, ⟨min_le_right _ _, le_max_right _ _⟩, hf2⟩
    let t_bad : ℝ := ((V.hi : ℝ) + 1) / 2
    have ht_bad_gt : (V.hi : ℝ) < t_bad := by dsimp only [t_bad]; linarith [V.hi_lt_one_real]
    have ht_bad_icc : t_bad ∈ Icc (0 : ℝ) 1 := ⟨by dsimp only [t_bad]; linarith [V.lo_pos_real, V.lo_lt_hi_real],
      by dsimp only [t_bad]; linarith [V.hi_lt_one_real]⟩
    have hbad_not_img : branchWord w t_bad ∉ tent^[r] '' Icc a b := by
      rintro ⟨t, htJ, htf⟩
      have ht_ioo := hab_sub htJ
      have ht_icc : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt (lt_trans E'.lo_pos_real ht_ioo.1),
        le_of_lt (lt_trans ht_ioo.2 E'.hi_lt_one_real)⟩
      let q := chart E'.level (fun _ => false) ⟨t, ht_icc⟩
      have hqE' : q ∈ E'.carrier := by simp only [q, BHSec.carrier, mem_ofPred_eq, chart_coord_self]; exact ht_ioo
      have hqZ : q.1 Z.level = branchWord w t_bad := by
        rw [← bh_tent_iterate_of_le q hEk, chart_coord_self, htf]
      have hqV : q.1 V.level = t_bad := by
        rw [← bh_tent_iterate q V.level w.length, ← hZlvl, hqZ, tent_iterate_branchWord w ht_bad_icc]
      linarith [hE'_le_hi q hqE', hqV]
    have hy1_not_bar : y₁.1 Z.level ∉ Icc ((V.strip w).lo : ℝ) ((V.strip w).hi : ℝ) := by
      intro hmem
      have h_icc : y₁.1 Z.level ∈ Icc (0 : ℝ) 1 := bh_mem_Icc y₁ Z.level
      have hy1_strip : y₁ ∈ (V.strip w).bar := by
        change ((V.strip w).lo : ℝ) ≤ y₁.1 (V.strip w).level ∧ y₁.1 (V.strip w).level ≤ (V.strip w).hi
        rwa [← hblk.1]
      linarith [(((V.mem_strip_bar_iff w y₁).mp hy1_strip).1).1]
    have hy_in_bar : y.1 Z.level ∈ Icc ((V.strip w).lo : ℝ) ((V.strip w).hi : ℝ) := by
      have : ((V.strip w).lo : ℝ) ≤ y.1 (V.strip w).level ∧ y.1 (V.strip w).level ≤ (V.strip w).hi := hybar
      rwa [← hblk.1] at this
    have hZlo_ge : ((V.strip w).lo : ℝ) ≤ Z.lo := by exact_mod_cast hblk.2.1
    have hZhi_le : (Z.hi : ℝ) ≤ (V.strip w).hi := by exact_mod_cast hblk.2.2
    cases hp : branchParity w
    · have hy_gt : (Z.hi : ℝ) < y.1 Z.level := hyside.1 hp
      have hbad_gt : ((V.strip w).hi : ℝ) < branchWord w t_bad := by
        rw [hhi_r, max_eq_right (le_of_lt (hma.1 hp))]
        exact (branchWord_strictMono_or_anti w ht_bad_gt).1 hp
      have hy1_lt : y₁.1 Z.level < (Z.lo : ℝ) := by
        by_contra hge; push Not at hge
        have hy1_gt_hi : ((V.strip w).hi : ℝ) < y₁.1 Z.level := by
          by_contra hle'; push Not at hle'
          exact hy1_not_bar ⟨le_trans hZlo_ge hge, hle'⟩
        by_cases hbad : branchWord w t_bad ≤ y₁.1 Z.level
        · exact hbad_not_img (hconn_r.Icc_subset h2_img h1_img ⟨le_of_lt (lt_of_le_of_lt hy_in_bar.2 hbad_gt), hbad⟩)
        · push Not at hbad
          have hhi_eq : ((V.strip w).hi : ℝ) = branchWord w V.hi := by
            rw [hhi_r, max_eq_right (le_of_lt (hma.1 hp))]
          have hsurj : ∃ t ∈ Ioo (V.hi : ℝ) t_bad, branchWord w t = y₁.1 Z.level := by
            have h2pos : (0 : ℝ) < (2 : ℝ) ^ w.length := by positivity
            let t := (y₁.1 Z.level - branchWord w 0) * (2 : ℝ) ^ w.length
            have hbt : branchWord w t = y₁.1 Z.level := by
              rw [branchWord_affine w t]; simp only [branchSign, hp, Bool.false_eq_true, ↓reduceIte, one_mul, t]
              field_simp; ring
            have hmem_ioo : branchWord w t ∈ Ioo (min (branchWord w V.hi) (branchWord w t_bad))
                (max (branchWord w V.hi) (branchWord w t_bad)) := by
              have h3 := (branchWord_strictMono_or_anti w ht_bad_gt).1 hp
              rw [min_eq_left (le_of_lt h3), max_eq_right (le_of_lt h3), hbt, ← hhi_eq]
              exact ⟨hy1_gt_hi, hbad⟩
            exact ⟨t, (branchWord_mem_Ioo_iff w ht_bad_gt).mp hmem_ioo, hbt⟩
          rcases hsurj with ⟨t, ht, hbt⟩
          have ht_icc : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt (lt_trans V.lo_pos_real (lt_trans V.lo_lt_hi_real ht.1)),
            le_of_lt (lt_of_lt_of_le ht.2 ht_bad_icc.2)⟩
          have hf : y₁.1 V.level = t := by
            rw [← bh_tent_iterate y₁ V.level w.length, ← hZlvl, ← hbt, tent_iterate_branchWord w ht_icc]
          linarith [ht.1, V.lo_lt_hi_real]
      obtain ⟨u, _, hsub⟩ := exists_strip_subset_of_meets_R1_R2 hEk hy₁E hy1_lt hyE hy_gt
      exact ⟨u, hsub⟩
    · have hy_lt : y.1 Z.level < (Z.lo : ℝ) := hyside.2 hp
      have hbad_lt : branchWord w t_bad < ((V.strip w).lo : ℝ) := by
        rw [hlo_r, min_eq_right (le_of_lt (hma.2 hp))]
        exact (branchWord_strictMono_or_anti w ht_bad_gt).2 hp
      have hy1_gt : (Z.hi : ℝ) < y₁.1 Z.level := by
        by_contra hle'; push Not at hle'
        have hy1_lt_lo : y₁.1 Z.level < ((V.strip w).lo : ℝ) := by
          by_contra hge; push Not at hge
          exact hy1_not_bar ⟨hge, le_trans hle' hZhi_le⟩
        by_cases hbad : y₁.1 Z.level ≤ branchWord w t_bad
        · exact hbad_not_img (hconn_r.Icc_subset h1_img h2_img ⟨hbad, le_of_lt (lt_of_lt_of_le hbad_lt hy_in_bar.1)⟩)
        · push Not at hbad
          have hlo_eq : ((V.strip w).lo : ℝ) = branchWord w V.hi := by
            rw [hlo_r, min_eq_right (le_of_lt (hma.2 hp))]
          have hsurj : ∃ t ∈ Ioo (V.hi : ℝ) t_bad, branchWord w t = y₁.1 Z.level := by
            have h2pos : (0 : ℝ) < (2 : ℝ) ^ w.length := by positivity
            let t := -(y₁.1 Z.level - branchWord w 0) * (2 : ℝ) ^ w.length
            have hbt : branchWord w t = y₁.1 Z.level := by
              rw [branchWord_affine w t]; simp only [branchSign, hp, ↓reduceIte, neg_mul, one_mul, t]
              field_simp; ring
            have hmem_ioo : branchWord w t ∈ Ioo (min (branchWord w V.hi) (branchWord w t_bad))
                (max (branchWord w V.hi) (branchWord w t_bad)) := by
              have h3 := (branchWord_strictMono_or_anti w ht_bad_gt).2 hp
              rw [min_eq_right (le_of_lt h3), max_eq_left (le_of_lt h3), hbt, ← hlo_eq]
              exact ⟨hbad, hy1_lt_lo⟩
            exact ⟨t, (branchWord_mem_Ioo_iff w ht_bad_gt).mp hmem_ioo, hbt⟩
          rcases hsurj with ⟨t, ht, hbt⟩
          have ht_icc : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt (lt_trans V.lo_pos_real (lt_trans V.lo_lt_hi_real ht.1)),
            le_of_lt (lt_of_lt_of_le ht.2 ht_bad_icc.2)⟩
          have hf : y₁.1 V.level = t := by
            rw [← bh_tent_iterate y₁ V.level w.length, ← hZlvl, ← hbt, tent_iterate_branchWord w ht_icc]
          linarith [ht.1, V.lo_lt_hi_real]
      obtain ⟨u, _, hsub⟩ := exists_strip_subset_of_meets_R1_R2 hEk hyE hy_lt hy₁E hy1_gt
      exact ⟨u, hsub⟩

/-- Left (`R₁`-side) guard section for Rudin Lemma 3 Property (B). -/
lemma exists_left_guard_sec {V Z : BHSec} {w : List Bool} (hblk : BHSec.IsBlock Z (V.strip w))
    {x : BH} (hxbar : x ∈ (V.strip w).bar)
    (hxside : (branchParity w = false → x.1 Z.level < (Z.lo : ℝ)) ∧
              (branchParity w = true → (Z.hi : ℝ) < x.1 Z.level)) :
    ∃ E : BHSec, E.level = Z.level ∧ x ∈ E.carrier ∧
      (E.carrier ∩ {z : BH | z.1 V.level < (V.lo : ℝ)}).Nonempty ∧
      E.carrier ∩ V.carrier ⊆ (V.strip w).carrier \ Z.carrier := by
  have hZlvl : Z.level = V.level + w.length := hblk.1
  have hlo_r : ((V.strip w).lo : ℝ) = min (branchWord w V.lo) (branchWord w V.hi) := by
    simp [BHSec.strip, branchWordQ_cast]
  have hhi_r : ((V.strip w).hi : ℝ) = max (branchWord w V.lo) (branchWord w V.hi) := by
    simp [BHSec.strip, branchWordQ_cast]
  have hma := branchWord_strictMono_or_anti w V.lo_lt_hi_real
  have hx_bar' : ((V.strip w).lo : ℝ) ≤ x.1 Z.level ∧ x.1 Z.level ≤ ((V.strip w).hi : ℝ) := by
    have : ((V.strip w).lo : ℝ) ≤ x.1 (V.strip w).level ∧ x.1 (V.strip w).level ≤ (V.strip w).hi := hxbar
    rwa [← hblk.1] at this
  cases hp : branchParity w
  · have hx_lt : x.1 Z.level < (Z.lo : ℝ) := hxside.1 hp
    have hlo_eq : ((V.strip w).lo : ℝ) = branchWord w V.lo := by
      rw [hlo_r, min_eq_left (le_of_lt (hma.1 hp))]
    have h0_lt : branchWord w 0 < ((V.strip w).lo : ℝ) := by
      rw [hlo_eq]; exact (branchWord_strictMono_or_anti w V.lo_pos_real).1 hp
    have hlow_lt : max (if (V.strip w).hi < 1 / 2 then (0 : ℝ) else 1 / 2) (branchWord w 0) < ((V.strip w).lo : ℝ) := by
      apply max_lt _ h0_lt
      split_ifs with hlt
      · exact (V.strip w).lo_pos_real
      · rcases (V.strip w).hside with h1 | h2
        · exact absurd h1 hlt
        · exact by simpa using (Rat.cast_lt (K := ℝ)).mpr h2
    obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn hlow_lt
    have ha_gt_bw0 : branchWord w 0 < (a : ℝ) := lt_of_le_of_lt (le_max_right _ _) ha1
    have ha_pos : (0 : ℚ) < a := by
      have hbw0_nn : (0 : ℝ) ≤ branchWord w 0 := (branchWord_mem_Icc w ⟨le_rfl, zero_le_one⟩).1
      exact_mod_cast lt_of_le_of_lt hbw0_nn ha_gt_bw0
    have ha_lt_Zlo : a < Z.lo := by
      exact_mod_cast lt_of_lt_of_le ha2 (by exact_mod_cast hblk.2.1 : ((V.strip w).lo : ℝ) ≤ Z.lo)
    have hE_side : Z.lo < 1 / 2 ∨ 1 / 2 < a := by
      rcases (V.strip w).hside with h1 | h2
      · left; exact lt_trans (lt_of_lt_of_le Z.hlt hblk.2.2) h1
      · right
        have hnot : ¬ (V.strip w).hi < 1 / 2 := not_lt.mpr (le_of_lt (lt_trans h2 (V.strip w).hlt))
        have h12 : ((1 / 2 : ℚ) : ℝ) < a := by
          have := lt_of_le_of_lt (le_max_left _ _) ha1
          rw [if_neg hnot] at this; simpa using this
        exact Rat.cast_lt.mp h12
    let E : BHSec := ⟨Z.level, a, Z.lo, ha_pos, ha_lt_Zlo, lt_trans Z.hlt Z.hhi, hE_side⟩
    refine ⟨E, rfl, ⟨lt_of_lt_of_le ha2 hx_bar'.1, hx_lt⟩, ?_, ?_⟩
    · -- Witness in E.carrier ∩ R₁
      let s : ℝ := ((a : ℝ) + ((V.strip w).lo : ℝ)) / 2
      have hs_ioo : s ∈ Ioo (a : ℝ) ((V.strip w).lo : ℝ) := by dsimp only [s]; constructor <;> linarith
      have hs_icc : s ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt (lt_trans E.lo_pos_real hs_ioo.1),
        le_of_lt (lt_trans hs_ioo.2 (lt_trans (V.strip w).lo_lt_hi_real (V.strip w).hi_lt_one_real))⟩
      let z := chart Z.level (fun _ => false) ⟨s, hs_icc⟩
      refine ⟨z, ?_, ?_⟩
      · simp only [E, z, BHSec.carrier, mem_ofPred_eq, chart_coord_self]
        exact ⟨hs_ioo.1, lt_of_lt_of_le hs_ioo.2 (by exact_mod_cast hblk.2.1)⟩
      · have h2pos : (0 : ℝ) < (2 : ℝ) ^ w.length := by positivity
        let t := (s - branchWord w 0) * (2 : ℝ) ^ w.length
        have hbt : branchWord w t = s := by
          rw [branchWord_affine w t]; simp only [branchSign, hp, Bool.false_eq_true, ↓reduceIte, one_mul, t]
          field_simp; ring
        have ht_ioo : t ∈ Ioo (0 : ℝ) (V.lo : ℝ) := by
          apply (branchWord_mem_Ioo_iff w V.lo_pos_real).mp
          have h01 := (branchWord_strictMono_or_anti w V.lo_pos_real).1 hp
          rw [min_eq_left (le_of_lt h01), max_eq_right (le_of_lt h01), hbt, ← hlo_eq]
          exact ⟨lt_trans ha_gt_bw0 hs_ioo.1, hs_ioo.2⟩
        have ht_icc : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt ht_ioo.1,
          le_of_lt (lt_trans ht_ioo.2 (lt_trans V.lo_lt_hi_real V.hi_lt_one_real))⟩
        have hzV : z.1 V.level = t := by
          rw [← bh_tent_iterate z V.level w.length, ← hZlvl, chart_coord_self]
          dsimp only
          rw [← hbt, tent_iterate_branchWord w ht_icc]
        change z.1 V.level < (V.lo : ℝ); rw [hzV]; exact ht_ioo.2
    · intro y ⟨hyE, hyV⟩
      refine ⟨?_, fun hyZ => not_lt_of_gt hyE.2 hyZ.1⟩
      have hy_gt : ((V.strip w).lo : ℝ) < y.1 Z.level := by
        by_contra hle'; push Not at hle'
        have h2pos : (0 : ℝ) < (2 : ℝ) ^ w.length := by positivity
        let t := (y.1 Z.level - branchWord w 0) * (2 : ℝ) ^ w.length
        have hbt : branchWord w t = y.1 Z.level := by
          rw [branchWord_affine w t]; simp only [branchSign, hp, Bool.false_eq_true, ↓reduceIte, one_mul, t]
          field_simp; ring
        have htl : (0 : ℝ) < t := by
          have : branchWord w 0 < y.1 Z.level := lt_trans ha_gt_bw0 hyE.1
          dsimp only [t]; exact mul_pos (by linarith) h2pos
        have htu : t ≤ (V.lo : ℝ) := by
          have hle2 : y.1 Z.level ≤ branchWord w V.lo := by rwa [← hlo_eq]
          rw [branchWord_affine w V.lo] at hle2
          simp only [branchSign, hp, Bool.false_eq_true, ↓reduceIte, one_mul] at hle2
          have : y.1 Z.level - branchWord w 0 ≤ (V.lo : ℝ) / (2 : ℝ) ^ w.length := by linarith
          dsimp only [t]; exact (le_div_iff₀ h2pos).mp this
        have ht_icc : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt htl, le_of_lt (lt_of_le_of_lt htu (lt_trans V.lo_lt_hi_real V.hi_lt_one_real))⟩
        have hy_V_eq : y.1 V.level = t := by
          rw [← bh_tent_iterate y V.level w.length, ← hZlvl, ← hbt, tent_iterate_branchWord w ht_icc]
        linarith [hyV.1]
      change ((V.strip w).lo : ℝ) < y.1 (V.strip w).level ∧ y.1 (V.strip w).level < (V.strip w).hi
      rw [← hblk.1]
      exact ⟨hy_gt, lt_of_lt_of_le hyE.2 (le_trans (le_of_lt Z.lo_lt_hi_real) (by exact_mod_cast hblk.2.2))⟩
  · have hx_gt : (Z.hi : ℝ) < x.1 Z.level := hxside.2 hp
    have hhi_eq : ((V.strip w).hi : ℝ) = branchWord w V.lo := by
      rw [hhi_r, max_eq_left (le_of_lt (hma.2 hp))]
    have h0_gt : ((V.strip w).hi : ℝ) < branchWord w 0 := by
      rw [hhi_eq]; exact (branchWord_strictMono_or_anti w V.lo_pos_real).2 hp
    have hhigh_gt : ((V.strip w).hi : ℝ) < min (if (V.strip w).hi < 1 / 2 then (1 / 2 : ℝ) else 1) (branchWord w 0) := by
      apply lt_min _ h0_gt
      split_ifs with hlt
      · exact by simpa using (Rat.cast_lt (K := ℝ)).mpr hlt
      · exact (V.strip w).hi_lt_one_real
    obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn hhigh_gt
    have hb_lt_bw0 : (b : ℝ) < branchWord w 0 := lt_of_lt_of_le hb2 (min_le_right _ _)
    have hb_lt_one : b < 1 := by
      have hbw0_le : branchWord w 0 ≤ 1 := (branchWord_mem_Icc w ⟨le_rfl, zero_le_one⟩).2
      exact_mod_cast lt_of_lt_of_le hb_lt_bw0 hbw0_le
    have hZhi_lt_b : Z.hi < b := by
      exact_mod_cast lt_of_le_of_lt (by exact_mod_cast hblk.2.2 : (Z.hi : ℝ) ≤ (V.strip w).hi) hb1
    have hE_side : b < 1 / 2 ∨ 1 / 2 < Z.hi := by
      rcases (V.strip w).hside with h1 | h2
      · left
        have h12 : (b : ℝ) < ((1 / 2 : ℚ) : ℝ) := by
          have := lt_of_lt_of_le hb2 (min_le_left _ _)
          rw [if_pos h1] at this; simpa using this
        exact Rat.cast_lt.mp h12
      · right; exact lt_trans (lt_of_lt_of_le h2 hblk.2.1) Z.hlt
    let E : BHSec := ⟨Z.level, Z.hi, b, lt_trans Z.hlo Z.hlt, hZhi_lt_b, hb_lt_one, hE_side⟩
    refine ⟨E, rfl, ⟨hx_gt, lt_of_le_of_lt hx_bar'.2 hb1⟩, ?_, ?_⟩
    · let s : ℝ := (((V.strip w).hi : ℝ) + (b : ℝ)) / 2
      have hs_ioo : s ∈ Ioo ((V.strip w).hi : ℝ) (b : ℝ) := by dsimp only [s]; constructor <;> linarith
      have hs_icc : s ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt (lt_trans (V.strip w).lo_pos_real (lt_trans (V.strip w).lo_lt_hi_real hs_ioo.1)),
        le_of_lt (lt_trans hs_ioo.2 E.hi_lt_one_real)⟩
      let z := chart Z.level (fun _ => false) ⟨s, hs_icc⟩
      refine ⟨z, ?_, ?_⟩
      · simp only [E, z, BHSec.carrier, mem_ofPred_eq, chart_coord_self]
        exact ⟨lt_of_le_of_lt (by exact_mod_cast hblk.2.2) hs_ioo.1, hs_ioo.2⟩
      · have h2pos : (0 : ℝ) < (2 : ℝ) ^ w.length := by positivity
        let t := -(s - branchWord w 0) * (2 : ℝ) ^ w.length
        have hbt : branchWord w t = s := by
          rw [branchWord_affine w t]; simp only [branchSign, hp, ↓reduceIte, neg_mul, one_mul, t]
          field_simp; ring
        have ht_ioo : t ∈ Ioo (0 : ℝ) (V.lo : ℝ) := by
          apply (branchWord_mem_Ioo_iff w V.lo_pos_real).mp
          have h01 := (branchWord_strictMono_or_anti w V.lo_pos_real).2 hp
          rw [min_eq_right (le_of_lt h01), max_eq_left (le_of_lt h01), hbt, ← hhi_eq]
          exact ⟨hs_ioo.1, lt_trans hs_ioo.2 hb_lt_bw0⟩
        have ht_icc : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt ht_ioo.1,
          le_of_lt (lt_trans ht_ioo.2 (lt_trans V.lo_lt_hi_real V.hi_lt_one_real))⟩
        have hzV : z.1 V.level = t := by
          rw [← bh_tent_iterate z V.level w.length, ← hZlvl, chart_coord_self]
          dsimp only
          rw [← hbt, tent_iterate_branchWord w ht_icc]
        change z.1 V.level < (V.lo : ℝ); rw [hzV]; exact ht_ioo.2
    · intro y ⟨hyE, hyV⟩
      refine ⟨?_, fun hyZ => not_lt_of_gt hyE.1 hyZ.2⟩
      have hy_lt : y.1 Z.level < ((V.strip w).hi : ℝ) := by
        by_contra hge; push Not at hge
        have h2pos : (0 : ℝ) < (2 : ℝ) ^ w.length := by positivity
        let t := -(y.1 Z.level - branchWord w 0) * (2 : ℝ) ^ w.length
        have hbt : branchWord w t = y.1 Z.level := by
          rw [branchWord_affine w t]; simp only [branchSign, hp, ↓reduceIte, neg_mul, one_mul, t]
          field_simp; ring
        have htl : (0 : ℝ) < t := by
          have : y.1 Z.level < branchWord w 0 := lt_trans hyE.2 hb_lt_bw0
          dsimp only [t]; exact mul_pos (by linarith) h2pos
        have htu : t ≤ (V.lo : ℝ) := by
          have hge2 : branchWord w V.lo ≤ y.1 Z.level := by rwa [← hhi_eq]
          rw [branchWord_affine w V.lo] at hge2
          simp only [branchSign, hp, ↓reduceIte, neg_mul, one_mul, neg_div] at hge2
          have : -(y.1 Z.level - branchWord w 0) ≤ (V.lo : ℝ) / (2 : ℝ) ^ w.length := by linarith
          dsimp only [t]; exact (le_div_iff₀ h2pos).mp this
        have ht_icc : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt htl, le_of_lt (lt_of_le_of_lt htu (lt_trans V.lo_lt_hi_real V.hi_lt_one_real))⟩
        have hy_V_eq : y.1 V.level = t := by
          rw [← bh_tent_iterate y V.level w.length, ← hZlvl, ← hbt, tent_iterate_branchWord w ht_icc]
        linarith [hyV.1]
      change ((V.strip w).lo : ℝ) < y.1 (V.strip w).level ∧ y.1 (V.strip w).level < (V.strip w).hi
      rw [← hblk.1]
      exact ⟨lt_of_le_of_lt (le_trans (by exact_mod_cast hblk.2.1) (le_of_lt Z.lo_lt_hi_real)) hyE.1, hy_lt⟩

/-- Rudin's property `λ` (Lemma 3, p. 19). -/
def propLambda (A B : Set BH) (U : BHSec) : Prop :=
  ∃ S : Set BH, IsSepSet S ∧ Disjoint S A ∧ inG S U ∧
    ∀ W : BHSec, inG S W → (W.carrier ∩ B).Nonempty

lemma propLambda_strip {A B : Set BH} {U : BHSec} (h : propLambda A B U) (w : List Bool) :
    propLambda A B (U.strip w) := by
  rcases h with ⟨S, hS, hSA, hSU, hSB⟩
  exact ⟨S, hS, hSA, inG_strip hSU w, hSB⟩

lemma propLambda_inter_B {A B : Set BH} {U : BHSec} (h : propLambda A B U) :
    (U.carrier ∩ B).Nonempty := by
  rcases h with ⟨_, _, _, hSU, hSB⟩; exact hSB U hSU

lemma pairwise_inCyl_eq {l : List (List Bool)}
    (hpw : l.Pairwise (fun u₁ u₂ => ∀ ε, ¬ (BHSec.inCyl u₁ ε ∧ BHSec.inCyl u₂ ε)))
    {u₁ u₂ : List Bool} (h1 : u₁ ∈ l) (h2 : u₂ ∈ l)
    (hmeet : ∃ ε, BHSec.inCyl u₁ ε ∧ BHSec.inCyl u₂ ε) : u₁ = u₂ := by
  induction l with
  | nil => simp at h1
  | cons a rest ih =>
    rw [List.pairwise_cons] at hpw
    rcases hmeet with ⟨ε, hε1, hε2⟩
    rcases List.mem_cons.mp h1 with rfl | h1' <;> rcases List.mem_cons.mp h2 with rfl | h2'
    · rfl
    · exact absurd ⟨hε1, hε2⟩ (hpw.1 u₂ h2' ε)
    · exact absurd ⟨hε2, hε1⟩ (hpw.1 u₁ h1' ε)
    · exact ih hpw.2 h1' h2'

/-- Odd-step cylinder partition of `U` around `q ∈ U.carrier ∩ B` (Rudin Lemma 3, p. 20). -/
lemma odd_step_partition {A B : Set BH}
    (hW_lam : ∀ W : BHSec, (W.carrier ∩ B).Nonempty → ∃ w : List Bool, propLambda A B (W.strip w))
    {U : BHSec} (hU : propLambda A B U) {q : BH} (hqU : q ∈ U.carrier) (hqB : q ∈ B) :
    ∃ K : Set (List Bool × BHSec),
      (∀ p ∈ K, BHSec.IsBlock p.2 (U.strip p.1) ∧ propLambda A B p.2) ∧
      (∀ p₁ ∈ K, ∀ p₂ ∈ K, (∃ ε, BHSec.inCyl p₁.1 ε ∧ BHSec.inCyl p₂.1 ε) → p₁ = p₂) ∧
      (∀ ε : ℕ → Bool, ε ≠ bitsAt U.level q → ∃ p ∈ K, BHSec.inCyl p.1 ε) ∧
      (∀ i : ℕ, ∃ p ∈ K, p.2.bar ⊆ bhBall q i) := by
  -- Recursively construct Q_i ⊆ U with q ∈ Q_i.carrier, Q_{i+1}.bar ⊆ bhBall q i,
  -- and P_i = Q_i.strip u_i disjoint from Q_{i+1}'s cylinder inside Q_i.
  have hstep_Q : ∀ (i : ℕ) (Qi : BHSec), q ∈ Qi.carrier → Qi.carrier ⊆ U.carrier →
      ∃ (Pi Qnext : BHSec) (wi : List Bool),
        Pi = Qi.strip (wi ++ [!(bitsAt Qi.level q wi.length)]) ∧
        propLambda A B Pi ∧
        q ∈ Qnext.carrier ∧
        Qnext.bar ⊆ (Qi.strip (List.ofFn (fun j : Fin (wi.length + 1) => bitsAt Qi.level q j))).carrier ∩ bhBall q i := by
    intro i Qi hqQi _
    obtain ⟨wi, hwi_lam⟩ := hW_lam Qi ⟨q, hqQi, hqB⟩
    let b_opp := !(bitsAt Qi.level q wi.length)
    let Pi := Qi.strip (wi ++ [b_opp])
    have hPi_lam : propLambda A B Pi := by
      dsimp only [Pi]; rw [← BHSec.strip_append]; exact propLambda_strip hwi_lam [b_opp]
    let uq : List Bool := List.ofFn (fun j : Fin (wi.length + 1) => bitsAt Qi.level q j)
    let Qq := Qi.strip uq
    have hqQq : q ∈ Qq.carrier := (Qi.mem_strip_carrier_iff uq q).mpr ⟨hqQi, fun j hj => by rw [List.getElem_ofFn]⟩
    have hq_ne0 : q ≠ bhZero := Qi.ne_bhZero_of_mem_bar (Qi.carrier_subset_bar hqQi)
    obtain ⟨Qnext, _, _, hqQn, hQn_sub⟩ := BHSec.exists_sec_bar_subset_of_mem_open hq_ne0
      (Qq.isOpen_carrier.inter (isOpen_bhBall q i)) ⟨hqQq, mem_bhBall_self q i⟩ 0 zero_lt_one
    exact ⟨Pi, Qnext, wi, rfl, hPi_lam, hqQn, hQn_sub⟩
  let QPack := {S : BHSec // q ∈ S.carrier ∧ S.carrier ⊆ U.carrier}
  let nextQ : ℕ → QPack → QPack := fun i prev =>
    let h := hstep_Q i prev.1 prev.2.1 prev.2.2
    let Qn := h.choose_spec.choose
    let hspec := h.choose_spec.choose_spec.choose_spec
    ⟨Qn, hspec.2.2.1, fun x hx =>
      prev.2.2 ((prev.1.strip_carrier_subset _) (hspec.2.2.2 (Qn.carrier_subset_bar hx)).1)⟩
  let Qseq : ℕ → QPack := Nat.rec ⟨U, hqU, Subset.rfl⟩ (fun i prev => nextQ i prev)
  let Pseq : ℕ → BHSec := fun i => (hstep_Q i (Qseq i).1 (Qseq i).2.1 (Qseq i).2.2).choose
  let wseq : ℕ → List Bool := fun i =>
    (hstep_Q i (Qseq i).1 (Qseq i).2.1 (Qseq i).2.2).choose_spec.choose_spec.choose
  have hPQ_spec : ∀ i,
      Pseq i = (Qseq i).1.strip (wseq i ++ [!(bitsAt (Qseq i).1.level q (wseq i).length)]) ∧
      propLambda A B (Pseq i) ∧
      q ∈ (Qseq (i + 1)).1.carrier ∧
      (Qseq (i + 1)).1.bar ⊆
        ((Qseq i).1.strip (List.ofFn (fun j : Fin ((wseq i).length + 1) => bitsAt (Qseq i).1.level q j))).carrier ∩
          bhBall q i := fun i =>
    (hstep_Q i (Qseq i).1 (Qseq i).2.1 (Qseq i).2.2).choose_spec.choose_spec.choose_spec
  have hP_sub_U : ∀ i, (Pseq i).carrier ⊆ U.carrier := fun i => by
    rw [(hPQ_spec i).1]; exact ((Qseq i).1.strip_carrier_subset _).trans (Qseq i).2.2
  have hQ_sub_U : ∀ i, (Qseq i).1.carrier ⊆ U.carrier := fun i => (Qseq i).2.2
  let wq : ℕ → List Bool := fun i => BHSec.subsecWord (hQ_sub_U i)
  let wp : ℕ → List Bool := fun i => BHSec.subsecWord (hP_sub_U i)
  have hwq_blk : ∀ i, BHSec.IsBlock (Qseq i).1 (U.strip (wq i)) := fun i => (BHSec.subsecWord_spec (hQ_sub_U i)).2
  have hwp_blk : ∀ i, BHSec.IsBlock (Pseq i) (U.strip (wp i)) := fun i => (BHSec.subsecWord_spec (hP_sub_U i)).2
  have hwq0 : wq 0 = [] := by
    have hlen := (BHSec.subsecWord_spec (hQ_sub_U 0)).1
    have h0 : (Qseq 0).1.level = U.level := rfl
    rw [h0, Nat.sub_self] at hlen
    exact List.eq_nil_of_length_eq_zero hlen
  have hwq_q : ∀ i, BHSec.inCyl (wq i) (bitsAt U.level q) := fun i =>
    ((U.mem_strip_carrier_iff (wq i) q).mp (BHSec.isBlock_carrier_subset (hwq_blk i) (Qseq i).2.1)).2
  have hQ_step_sub : ∀ i, (Qseq (i + 1)).1.carrier ⊆ (Qseq i).1.carrier := fun i x hx =>
    ((Qseq i).1.strip_carrier_subset _) ((hPQ_spec i).2.2.2 ((Qseq (i + 1)).1.carrier_subset_bar hx)).1
  have hP_step_sub : ∀ i, (Pseq i).carrier ⊆ (Qseq i).1.carrier := fun i => by
    rw [(hPQ_spec i).1]; exact (Qseq i).1.strip_carrier_subset _
  -- Cylinder inclusions: wp i ⊆ wq i, wq (i+1) ⊆ wq i, wp i ∩ wq (i+1) = ∅, len(wq i) < len(wq (i+1))
  have hcyl_of_sub : ∀ {W₁ W₂ : BHSec} {u₁ u₂ : List Bool},
      BHSec.IsBlock W₁ (U.strip u₁) → BHSec.IsBlock W₂ (U.strip u₂) →
      W₁.carrier ⊆ W₂.carrier → ∀ ε, BHSec.inCyl u₁ ε → BHSec.inCyl u₂ ε := by
    intro W₁ W₂ u₁ u₂ hb₁ hb₂ hsub ε hε
    let t : ℝ := ((W₁.lo : ℝ) + (W₁.hi : ℝ)) / 2
    have ht_W : t ∈ Ioo (W₁.lo : ℝ) (W₁.hi : ℝ) := by dsimp only [t]; constructor <;> linarith [W₁.lo_lt_hi_real]
    have ht_icc : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt (lt_trans W₁.lo_pos_real ht_W.1),
      le_of_lt (lt_trans ht_W.2 W₁.hi_lt_one_real)⟩
    let η : ℕ → Bool := fun j => ε (u₁.length + j)
    let x := chart W₁.level η ⟨t, ht_icc⟩
    have hxW1 : x ∈ W₁.carrier := by simp only [x, BHSec.carrier, mem_ofPred_eq, chart_coord_self]; exact ht_W
    have hxU1 : x ∈ (U.strip u₁).carrier := BHSec.isBlock_carrier_subset hb₁ hxW1
    have hxU2 : x ∈ (U.strip u₂).carrier := BHSec.isBlock_carrier_subset hb₂ (hsub hxW1)
    have hbits_x : bitsAt U.level x = ε := by
      have hcyl1 : BHSec.inCyl u₁ (bitsAt U.level x) := ((U.mem_strip_carrier_iff u₁ x).mp hxU1).2
      have hx_ioo : (⟨t, ht_icc⟩ : Icc (0 : ℝ) 1).1 ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_trans W₁.lo_pos_real ht_W.1, lt_trans ht_W.2 W₁.hi_lt_one_real⟩
      have htail := bitsAt_chart W₁.level η hx_ioo
      funext n
      by_cases hn : n < u₁.length
      · rw [hcyl1 n hn, hε n hn]
      · have hidx : U.level + n + 1 = W₁.level + (n - u₁.length) + 1 := by
          have : W₁.level = U.level + u₁.length := hb₁.1; omega
        have h1 : bitsAt U.level x n = bitsAt W₁.level x (n - u₁.length) := by
          unfold bitsAt; rw [hidx]
        rw [h1, htail]; dsimp only [η]; congr 1; omega
    rw [← hbits_x]
    exact ((U.mem_strip_carrier_iff u₂ x).mp hxU2).2
  have hwp_in_wq : ∀ i ε, BHSec.inCyl (wp i) ε → BHSec.inCyl (wq i) ε := fun i =>
    hcyl_of_sub (hwp_blk i) (hwq_blk i) (hP_step_sub i)
  have hwq_succ_in : ∀ i ε, BHSec.inCyl (wq (i + 1)) ε → BHSec.inCyl (wq i) ε := fun i =>
    hcyl_of_sub (hwq_blk (i + 1)) (hwq_blk i) (hQ_step_sub i)
  have hwq_mono : ∀ {i j}, i ≤ j → ∀ ε, BHSec.inCyl (wq j) ε → BHSec.inCyl (wq i) ε := by
    intro i j hij
    induction hij with
    | refl => exact fun _ h => h
    | step _ ih => exact fun ε h => ih ε (hwq_succ_in _ ε h)
  have hwq_len_lt : ∀ i, (wq i).length < (wq (i + 1)).length := by
    intro i
    have h1 : (wq i).length = (Qseq i).1.level - U.level := (BHSec.subsecWord_spec (hQ_sub_U i)).1
    have h2 : (wq (i + 1)).length = (Qseq (i + 1)).1.level - U.level := (BHSec.subsecWord_spec (hQ_sub_U (i + 1))).1
    have hsub_qq : (Qseq (i + 1)).1.carrier ⊆
        ((Qseq i).1.strip (List.ofFn (fun j : Fin ((wseq i).length + 1) => bitsAt (Qseq i).1.level q j))).carrier :=
      fun x hx => ((hPQ_spec i).2.2.2 ((Qseq (i + 1)).1.carrier_subset_bar hx)).1
    have hle_lvl := (BHSec.subsec_eq_block_of_strip hsub_qq).1
    have hU_le := (BHSec.subsec_eq_block_of_strip (hQ_sub_U i)).1
    simp only [BHSec.strip, List.length_ofFn] at hle_lvl
    omega
  have hwq_len_ge : ∀ i, i ≤ (wq i).length := by
    intro i; induction i with
    | zero => exact Nat.zero_le _
    | succ i ih => have := hwq_len_lt i; omega
  have hwp_disj_wq : ∀ i ε, ¬ (BHSec.inCyl (wp i) ε ∧ BHSec.inCyl (wq (i + 1)) ε) := by
    intro i ε ⟨hp, hq'⟩
    -- At index (wq i).length + (wseq i).length, wp i has !(bitsAt ...) while wq (i+1) has bitsAt ...
    have hP_cyl : ∀ η, BHSec.inCyl (wp i) η →
        BHSec.inCyl (wq i ++ (wseq i ++ [!(bitsAt (Qseq i).1.level q (wseq i).length)])) η := by
      have hblk_P : BHSec.IsBlock (Pseq i)
          (U.strip (wq i ++ (wseq i ++ [!(bitsAt (Qseq i).1.level q (wseq i).length)]))) := by
        rw [← BHSec.strip_append, (hPQ_spec i).1]
        exact BHSec.isBlock_strip (hwq_blk i) _
      exact hcyl_of_sub (hwp_blk i) hblk_P Subset.rfl
    have hQ_cyl : ∀ η, BHSec.inCyl (wq (i + 1)) η →
        BHSec.inCyl (wq i ++ List.ofFn (fun j : Fin ((wseq i).length + 1) => bitsAt (Qseq i).1.level q j)) η := by
      have hsub_qq : (Qseq (i + 1)).1.carrier ⊆
          ((Qseq i).1.strip (List.ofFn (fun j : Fin ((wseq i).length + 1) => bitsAt (Qseq i).1.level q j))).carrier :=
        fun x hx => ((hPQ_spec i).2.2.2 ((Qseq (i + 1)).1.carrier_subset_bar hx)).1
      have hblk_Q : BHSec.IsBlock
          ((Qseq i).1.strip (List.ofFn (fun j : Fin ((wseq i).length + 1) => bitsAt (Qseq i).1.level q j)))
          (U.strip (wq i ++ List.ofFn (fun j : Fin ((wseq i).length + 1) => bitsAt (Qseq i).1.level q j))) := by
        rw [← BHSec.strip_append]; exact BHSec.isBlock_strip (hwq_blk i) _
      exact hcyl_of_sub (hwq_blk (i + 1)) hblk_Q hsub_qq
    have hc1 := ((BHSec.inCyl_append _ _ _).mp (hP_cyl ε hp)).2 (wseq i).length (by simp)
    have hc2 := ((BHSec.inCyl_append _ _ _).mp (hQ_cyl ε hq')).2 (wseq i).length (by simp)
    simp only [List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_singleton] at hc1
    simp only [List.getElem_ofFn] at hc2
    rw [hc2] at hc1
    cases hb : bitsAt (Qseq i).1.level q (wseq i).length <;> simp [hb] at hc1
  -- Define K explicitly: for each i, emit (wp i, Pseq i) and all side strips disjoint from wp i and wq (i+1)
  let sideWords : ℕ → Set (List Bool) := fun i =>
    {u' | ∃ u ∈ BHSec.splitCyl (wq i) (wp i),
      (∀ η, ¬ (BHSec.inCyl u η ∧ BHSec.inCyl (wp i) η)) ∧
      u' ∈ BHSec.splitCyl u (wq (i + 1)) ∧
      (∀ η, ¬ (BHSec.inCyl u' η ∧ BHSec.inCyl (wq (i + 1)) η))}
  let K : Set (List Bool × BHSec) :=
    (⋃ i : ℕ, {(wp i, Pseq i)}) ∪
    (⋃ i : ℕ, (fun u' => (u', U.strip u')) '' sideWords i)
  have hside_in_wq : ∀ i u', u' ∈ sideWords i → ∀ ε, BHSec.inCyl u' ε →
      BHSec.inCyl (wq i) ε ∧ ¬ BHSec.inCyl (wq (i + 1)) ε := by
    rintro i u' ⟨u, hu, _, hu', hdisj_q⟩ ε hε
    have hεu : BHSec.inCyl u ε := (BHSec.splitCyl_spec u (wq (i + 1))).1 ε |>.mpr ⟨u', hu', hε⟩
    have hεwq : BHSec.inCyl (wq i) ε := (BHSec.splitCyl_spec (wq i) (wp i)).1 ε |>.mpr ⟨u, hu, hεu⟩
    exact ⟨hεwq, fun hq' => hdisj_q ε ⟨hε, hq'⟩⟩
  refine ⟨K, ?_, ?_, ?_, ?_⟩
  · -- Valid blocks with propLambda
    rintro p (h1 | h2)
    · rcases mem_iUnion.mp h1 with ⟨i, hi⟩
      rw [mem_singleton_iff] at hi; subst hi
      exact ⟨hwp_blk i, (hPQ_spec i).2.1⟩
    · rcases mem_iUnion.mp h2 with ⟨i, u', _, rfl⟩
      exact ⟨BHSec.isBlock_refl _, propLambda_strip hU u'⟩
  · -- Pairwise disjointness: intersecting cylinders imply equal pairs
    have htier : ∀ p ∈ K, ∃ i : ℕ, (p = (wp i, Pseq i) ∨ ∃ u' ∈ sideWords i, p = (u', U.strip u')) ∧
        ∀ ε, BHSec.inCyl p.1 ε → BHSec.inCyl (wq i) ε ∧ ¬ BHSec.inCyl (wq (i + 1)) ε := by
      rintro p (h1 | h2)
      · rcases mem_iUnion.mp h1 with ⟨i, hi⟩
        rw [mem_singleton_iff] at hi; subst hi
        exact ⟨i, Or.inl rfl, fun ε hε => ⟨hwp_in_wq i ε hε, fun hq' => hwp_disj_wq i ε ⟨hε, hq'⟩⟩⟩
      · rcases mem_iUnion.mp h2 with ⟨i, u', hu', rfl⟩
        exact ⟨i, Or.inr ⟨u', hu', rfl⟩, hside_in_wq i u' hu'⟩
    intro p₁ hp₁ p₂ hp₂ ⟨ε, hε1, hε2⟩
    obtain ⟨i₁, hform₁, hband₁⟩ := htier p₁ hp₁
    obtain ⟨i₂, hform₂, hband₂⟩ := htier p₂ hp₂
    have hi_eq : i₁ = i₂ := by
      rcases lt_trichotomy i₁ i₂ with hlt | heq | hgt
      · exact absurd (hwq_mono (Nat.succ_le_of_lt hlt) ε (hband₂ ε hε2).1) (hband₁ ε hε1).2
      · exact heq
      · exact absurd (hwq_mono (Nat.succ_le_of_lt hgt) ε (hband₁ ε hε1).1) (hband₂ ε hε2).2
    subst hi_eq
    rcases hform₁ with rfl | ⟨u₁', ⟨u₁, hu₁, hdisj_p1, hu₁', _⟩, rfl⟩
    · rcases hform₂ with rfl | ⟨u₂', ⟨u₂, hu₂, hdisj_p2, hu₂', _⟩, rfl⟩
      · rfl
      · have hεu₂ : BHSec.inCyl u₂ ε := (BHSec.splitCyl_spec u₂ (wq (i₁ + 1))).1 ε |>.mpr ⟨u₂', hu₂', hε2⟩
        exact absurd ⟨hεu₂, hε1⟩ (hdisj_p2 ε)
    · rcases hform₂ with rfl | ⟨u₂', ⟨u₂, hu₂, hdisj_p2, hu₂', _⟩, rfl⟩
      · have hεu₁ : BHSec.inCyl u₁ ε := (BHSec.splitCyl_spec u₁ (wq (i₁ + 1))).1 ε |>.mpr ⟨u₁', hu₁', hε1⟩
        exact absurd ⟨hεu₁, hε2⟩ (hdisj_p1 ε)
      · have hεu₁ : BHSec.inCyl u₁ ε := (BHSec.splitCyl_spec u₁ (wq (i₁ + 1))).1 ε |>.mpr ⟨u₁', hu₁', hε1⟩
        have hεu₂ : BHSec.inCyl u₂ ε := (BHSec.splitCyl_spec u₂ (wq (i₁ + 1))).1 ε |>.mpr ⟨u₂', hu₂', hε2⟩
        have hu_eq : u₁ = u₂ := pairwise_inCyl_eq (BHSec.splitCyl_spec (wq i₁) (wp i₁)).2.1 hu₁ hu₂ ⟨ε, hεu₁, hεu₂⟩
        subst hu_eq
        have hu'_eq : u₁' = u₂' := pairwise_inCyl_eq (BHSec.splitCyl_spec u₁ (wq (i₁ + 1))).2.1 hu₁' hu₂' ⟨ε, hε1, hε2⟩
        subst hu'_eq; rfl
  · -- Every ε ≠ bitsAt U.level q is covered
    intro ε hne
    have hex_exit : ∃ m : ℕ, ¬ BHSec.inCyl (wq (m + 1)) ε := by
      have hex_k : ∃ k : ℕ, ε k ≠ bitsAt U.level q k := by
        by_contra hall; push Not at hall; exact hne (funext hall)
      rcases hex_k with ⟨k, hk⟩
      refine ⟨k, fun hcyl => hk ?_⟩
      have hk_lt : k < (wq (k + 1)).length := by have := hwq_len_ge (k + 1); omega
      exact (hcyl k hk_lt).trans (hwq_q (k + 1) k hk_lt).symm
    let i := Nat.find hex_exit
    have hi_not : ¬ BHSec.inCyl (wq (i + 1)) ε := Nat.find_spec hex_exit
    have hi_in : BHSec.inCyl (wq i) ε := by
      cases hi : i with
      | zero => rw [hwq0]; exact BHSec.inCyl_nil ε
      | succ j =>
        by_contra hnot
        have hle := Nat.find_min' hex_exit hnot
        omega
    obtain ⟨u, hu, hεu⟩ := (BHSec.splitCyl_spec (wq i) (wp i)).1 ε |>.mp hi_in
    rcases (BHSec.splitCyl_spec (wq i) (wp i)).2.2.2 u hu with hsub_p | hdisj_p
    · exact ⟨(wp i, Pseq i), Or.inl (mem_iUnion.mpr ⟨i, mem_singleton _⟩), hsub_p ε hεu⟩
    · obtain ⟨u', hu', hεu'⟩ := (BHSec.splitCyl_spec u (wq (i + 1))).1 ε |>.mp hεu
      rcases (BHSec.splitCyl_spec u (wq (i + 1))).2.2.2 u' hu' with hsub_q | hdisj_q
      · exact absurd (hsub_q ε hεu') hi_not
      · exact ⟨(u', U.strip u'), Or.inr (mem_iUnion.mpr ⟨i, u', ⟨u, hu, hdisj_p, hu', hdisj_q⟩, rfl⟩), hεu'⟩
  · -- For every i, Pseq (i + 1) ∈ K and (Pseq (i + 1)).bar ⊆ bhBall q i
    intro i
    refine ⟨(wp (i + 1), Pseq (i + 1)), Or.inl (mem_iUnion.mpr ⟨i + 1, mem_singleton _⟩), fun x hx => ?_⟩
    have hxQ : x ∈ (Qseq (i + 1)).1.bar := by
      rw [(hPQ_spec (i + 1)).1] at hx
      exact (((Qseq (i + 1)).1.mem_strip_bar_iff _ x).mp hx).1
    exact ((hPQ_spec i).2.2.2 hxQ).2

/-- Even-step cylinder partition of `U` avoiding a chosen point `pA ∈ A ∩ U.bar` (Rudin Lemma 3, p. 19). -/
lemma even_step_partition {A B : Set BH} {U : BHSec} (hU : propLambda A B U)
    (pA_of : (A ∩ U.bar).Nonempty → BH) (hpA_mem : ∀ hne, pA_of hne ∈ A ∩ U.bar) :
    ∃ K : Set (List Bool × BHSec),
      (∀ p ∈ K, BHSec.IsBlock p.2 (U.strip p.1) ∧ propLambda A B p.2) ∧
      (∀ p₁ ∈ K, ∀ p₂ ∈ K, (∃ ε, BHSec.inCyl p₁.1 ε ∧ BHSec.inCyl p₂.1 ε) → p₁ = p₂) ∧
      (∀ ε : ℕ → Bool, ∃ p ∈ K, BHSec.inCyl p.1 ε) ∧
      (∀ hne : (A ∩ U.bar).Nonempty, ∀ p ∈ K, pA_of hne ∉ p.2.bar) := by
  by_cases hne : (A ∩ U.bar).Nonempty
  · let pA := pA_of hne
    have hpA : pA ∈ A ∩ U.bar := hpA_mem hne
    rcases hU with ⟨S, hS, hSA, hSU, hSB⟩
    have hpS : pA ∉ S := fun h => disjoint_left.mp hSA h hpA.1
    obtain ⟨yw, Y, hYblk, hYinG, hp_strip, hp_notY⟩ := exists_Y_avoiding_point hS.1 hSU hpA.2 hpS
    have hY_lam : propLambda A B Y := ⟨S, hS, hSA, hYinG, hSB⟩
    let K : Set (List Bool × BHSec) :=
      {(yw, Y)} ∪ {p | ∃ u ∈ BHSec.splitCyl [] yw, (∀ η, ¬ (BHSec.inCyl u η ∧ BHSec.inCyl yw η)) ∧ p = (u, U.strip u)}
    refine ⟨K, ?_, ?_, ?_, ?_⟩
    · rintro p (hp1 | ⟨u, _, _, rfl⟩)
      · rw [mem_singleton_iff] at hp1; subst hp1; exact ⟨hYblk, hY_lam⟩
      · exact ⟨BHSec.isBlock_refl _, propLambda_strip ⟨S, hS, hSA, hSU, hSB⟩ u⟩
    · intro p₁ hp₁ p₂ hp₂ ⟨ε, hε1, hε2⟩
      rcases hp₁ with h1 | ⟨u₁, hu₁, hd₁, rfl⟩
      · rw [mem_singleton_iff] at h1; subst h1
        rcases hp₂ with h2 | ⟨u₂, hu₂, hd₂, rfl⟩
        · rw [mem_singleton_iff] at h2; exact h2.symm
        · exact absurd ⟨hε2, hε1⟩ (hd₂ ε)
      · rcases hp₂ with h2 | ⟨u₂, hu₂, hd₂, rfl⟩
        · rw [mem_singleton_iff] at h2; subst h2; exact absurd ⟨hε1, hε2⟩ (hd₁ ε)
        · have heq := pairwise_inCyl_eq (BHSec.splitCyl_spec [] yw).2.1 hu₁ hu₂ ⟨ε, hε1, hε2⟩
          subst heq; rfl
    · intro ε
      obtain ⟨u, hu, hεu⟩ := (BHSec.splitCyl_spec [] yw).1 ε |>.mp (BHSec.inCyl_nil ε)
      rcases (BHSec.splitCyl_spec [] yw).2.2.2 u hu with hsub | hdisj
      · exact ⟨(yw, Y), Or.inl rfl, hsub ε hεu⟩
      · exact ⟨(u, U.strip u), Or.inr ⟨u, hu, hdisj, rfl⟩, hεu⟩
    · intro hne' p hp
      have heq_p : pA_of hne' = pA := rfl
      rw [heq_p]
      rcases hp with h1 | ⟨u, _, hdisj, rfl⟩
      · rw [mem_singleton_iff] at h1; subst h1; exact hp_notY
      · intro hmem
        exact disjoint_left.mp (U.strip_carrier_disjoint_of_incomp hdisj) hmem hp_strip
  · refine ⟨{([], U)}, ?_, ?_, ?_, fun h => absurd h hne⟩
    · intro p hp; rw [mem_singleton_iff] at hp; subst hp
      rw [U.strip_nil]; exact ⟨BHSec.isBlock_refl U, hU⟩
    · intro p₁ hp₁ p₂ hp₂ _; rw [mem_singleton_iff] at hp₁ hp₂; exact hp₁.trans hp₂.symm
    · intro ε; exact ⟨([], U), mem_singleton _, BHSec.inCyl_nil ε⟩

/-- Construction of the separating set `T = closure D \ D` from a Lemma 3 hierarchy `F`. -/
lemma lem3_build_T_from_F (V : BHSec) (F : ℕ → Set (List Bool × BHSec))
    (hF_blk : ∀ n, ∀ p ∈ F n, BHSec.IsBlock p.2 (V.strip p.1))
    (hF_disj : ∀ n, ∀ p₁ ∈ F n, ∀ p₂ ∈ F n, (∃ ε, BHSec.inCyl p₁.1 ε ∧ BHSec.inCyl p₂.1 ε) → p₁ = p₂)
    (hstrip_meets : ∀ n (w : List Bool), ∃ p ∈ F n, ((V.strip w).carrier ∩ p.2.carrier).Nonempty)
    (hZstrip_meets : ∀ n p, p ∈ F n → ∀ m (u : List Bool), ∃ q ∈ F m, ((p.2.strip u).carrier ∩ q.2.carrier).Nonempty) :
    ∃ T : Set BH, IsSepSet T ∧ T ⊆ V.bar ∧
      ∀ n, ∀ p ∈ F n, (V.strip p.1).bar ∩ T ⊆ p.2.bar := by
  let R₁ : Set BH := {x | x.1 V.level < (V.lo : ℝ)}
  let R₂ : Set BH := {x | (V.hi : ℝ) < x.1 V.level}
  let GoodE (E : BHSec) : Prop :=
    V.level ≤ E.level ∧ (E.carrier ∩ R₁).Nonempty ∧ ∃ n : ℕ, ∀ p ∈ F n, Disjoint E.carrier p.2.carrier
  let D : Set BH := R₁ ∪ ⋃ (E : BHSec) (_ : GoodE E), E.carrier
  let T : Set BH := closure D \ D
  have hR1_open : IsOpen R₁ := isOpen_lt (continuous_bhCoord V.level) continuous_const
  have hR2_open : IsOpen R₂ := isOpen_lt continuous_const (continuous_bhCoord V.level)
  have hD_open : IsOpen D := hR1_open.union (isOpen_iUnion fun E => isOpen_iUnion fun _ => E.isOpen_carrier)
  have hGood_disj_R2 : ∀ E : BHSec, GoodE E → Disjoint E.carrier R₂ := by
    rintro E ⟨hle, ⟨y₁, hy₁E, hy₁R1⟩, n, hmiss⟩
    rw [disjoint_left]
    intro y₂ hy₂E hy₂R2
    obtain ⟨w, _, hsub⟩ := exists_strip_subset_of_meets_R1_R2 hle hy₁E hy₁R1 hy₂E hy₂R2
    obtain ⟨p, hp, z, hzV, hzW⟩ := hstrip_meets n w
    exact disjoint_left.mp (hmiss p hp) (hsub hzV) hzW
  have hD_disj_R2 : Disjoint D R₂ := by
    rw [disjoint_left]
    rintro x (h1 | h2) hR2
    · exact not_lt_of_gt (lt_trans (show x.1 V.level < V.lo from h1) V.lo_lt_hi_real)
        (show (V.hi : ℝ) < x.1 V.level from hR2)
    · rcases mem_iUnion₂.mp h2 with ⟨E, hE, hxE⟩
      exact disjoint_left.mp (hGood_disj_R2 E hE) hxE hR2
  have hR2_sub_compl : R₂ ⊆ (closure D)ᶜ := fun x hxR2 hxcl => by
    rcases mem_closure_iff.mp hxcl R₂ hR2_open hxR2 with ⟨y, hyR2, hyD⟩
    exact disjoint_left.mp hD_disj_R2 hyD hyR2
  have hR1_ne : R₁.Nonempty := ⟨chart V.level (fun _ => false) ⟨0, le_rfl, zero_le_one⟩,
    by simp [R₁, chart_coord_self, V.lo_pos_real]⟩
  have hR2_ne : R₂.Nonempty := ⟨chart V.level (fun _ => false) ⟨1, zero_le_one, le_rfl⟩,
    by simp [R₂, chart_coord_self, V.hi_lt_one_real]⟩
  have hT_sep : IsSepSet T := by
    refine ⟨isClosed_closure.sdiff hD_open, D, (closure D)ᶜ, hD_open, isClosed_closure.isOpen_compl,
      disjoint_compl_right.mono_left subset_closure, hR1_ne.mono subset_union_left,
      hR2_ne.mono hR2_sub_compl, ?_⟩
    ext x; simp only [T, mem_compl_iff, Set.mem_sdiff, mem_union, not_and, not_not]
    tauto
  have hT_sub_Vbar : T ⊆ V.bar := fun x hxT =>
    ⟨not_lt.mp fun hlt => hxT.2 (Or.inl hlt), not_lt.mp fun hgt => hR2_sub_compl hgt hxT.1⟩
  refine ⟨T, hT_sep, hT_sub_Vbar, ?_⟩
  intro n ⟨w, Z⟩ hp x ⟨hxbar, hxT⟩
  have hblk := hF_blk n (w, Z) hp
  have hZlvl : Z.level = V.level + w.length := hblk.1
  by_contra hxnotZ
  have hlo_or_hi : x.1 Z.level < (Z.lo : ℝ) ∨ (Z.hi : ℝ) < x.1 Z.level := by
    by_contra hno; push Not at hno; exact hxnotZ hno
  have hR1_side : (branchParity w = false → x.1 Z.level < (Z.lo : ℝ)) ∧
      (branchParity w = true → (Z.hi : ℝ) < x.1 Z.level) → False := by
    intro hxside
    obtain ⟨E, hElvl, hxE, hER1, hEV_sub⟩ := exists_left_guard_sec hblk hxbar hxside
    have hE_good : GoodE E := by
      have hElvl' : V.level ≤ E.level := by rw [hElvl, hZlvl]; exact Nat.le_add_right _ _
      refine ⟨hElvl', hER1, n, fun p' hp' => disjoint_left.mpr fun y hyE hyp' => ?_⟩
      have hyV : y ∈ V.carrier := (V.strip_carrier_subset p'.1)
        (BHSec.isBlock_carrier_subset (hF_blk n p' hp') hyp')
      obtain ⟨hyVw, hynotZ⟩ := hEV_sub ⟨hyE, hyV⟩
      have hmeet : ∃ ε, BHSec.inCyl w ε ∧ BHSec.inCyl p'.1 ε :=
        ⟨bitsAt V.level y, ((V.mem_strip_carrier_iff w y).mp hyVw).2,
          ((V.mem_strip_carrier_iff p'.1 y).mp (BHSec.isBlock_carrier_subset (hF_blk n p' hp') hyp')).2⟩
      have heq := hF_disj n (w, Z) hp p' hp' hmeet
      rw [← heq] at hyp'; exact hynotZ hyp'
    exact hxT.2 (Or.inr (mem_iUnion₂.mpr ⟨E, hE_good, hxE⟩))
  have hR2_side : (branchParity w = false → (Z.hi : ℝ) < x.1 Z.level) ∧
      (branchParity w = true → x.1 Z.level < (Z.lo : ℝ)) → False := by
    intro hxside
    let E₂ : Set BH := if branchParity w = false
      then {z | (Z.hi : ℝ) < z.1 Z.level ∧ z.1 Z.level < branchWord w 1}
      else {z | branchWord w 1 < z.1 Z.level ∧ z.1 Z.level < (Z.lo : ℝ)}
    have hE2_open : IsOpen E₂ := by
      dsimp only [E₂]; split_ifs
      · exact (isOpen_lt continuous_const (continuous_bhCoord Z.level)).inter
          (isOpen_lt (continuous_bhCoord Z.level) continuous_const)
      · exact (isOpen_lt continuous_const (continuous_bhCoord Z.level)).inter
          (isOpen_lt (continuous_bhCoord Z.level) continuous_const)
    have hx_in_E2 : x ∈ E₂ := by
      have hlo_r : ((V.strip w).lo : ℝ) = min (branchWord w V.lo) (branchWord w V.hi) := by
        simp [BHSec.strip, branchWordQ_cast]
      have hhi_r : ((V.strip w).hi : ℝ) = max (branchWord w V.lo) (branchWord w V.hi) := by
        simp [BHSec.strip, branchWordQ_cast]
      have hma := branchWord_strictMono_or_anti w V.lo_lt_hi_real
      have hxbar' : ((V.strip w).lo : ℝ) ≤ x.1 Z.level ∧ x.1 Z.level ≤ (V.strip w).hi := by
        have : ((V.strip w).lo : ℝ) ≤ x.1 (V.strip w).level ∧ x.1 (V.strip w).level ≤ (V.strip w).hi := hxbar
        rwa [← hblk.1] at this
      dsimp only [E₂]
      cases hp_par : branchParity w
      · rw [if_pos rfl]
        have hlt1 : ((V.strip w).hi : ℝ) < branchWord w 1 := by
          rw [hhi_r, max_eq_right (le_of_lt (hma.1 hp_par))]
          exact (branchWord_strictMono_or_anti w V.hi_lt_one_real).1 hp_par
        exact ⟨hxside.1 hp_par, lt_of_le_of_lt hxbar'.2 hlt1⟩
      · rw [if_neg Bool.false_ne_true.symm]
        have hlt1 : branchWord w 1 < ((V.strip w).lo : ℝ) := by
          rw [hlo_r, min_eq_right (le_of_lt (hma.2 hp_par))]
          exact (branchWord_strictMono_or_anti w V.hi_lt_one_real).2 hp_par
        exact ⟨lt_of_lt_of_le hlt1 hxbar'.1, hxside.2 hp_par⟩
    have hE2_disj_D : Disjoint E₂ D := by
      rw [disjoint_left]
      intro y hyE2 hyD
      have hy_bar_or_R2 : y ∈ (V.strip w).bar ∨ y ∈ R₂ := by
        have hlo_r : ((V.strip w).lo : ℝ) = min (branchWord w V.lo) (branchWord w V.hi) := by
          simp [BHSec.strip, branchWordQ_cast]
        have hhi_r : ((V.strip w).hi : ℝ) = max (branchWord w V.lo) (branchWord w V.hi) := by
          simp [BHSec.strip, branchWordQ_cast]
        have hma := branchWord_strictMono_or_anti w V.lo_lt_hi_real
        have h2pos : (0 : ℝ) < (2 : ℝ) ^ w.length := by positivity
        dsimp only [E₂] at hyE2
        cases hp_par : branchParity w
        · rw [if_pos hp_par] at hyE2
          by_cases hle' : y.1 Z.level ≤ (V.strip w).hi
          · left
            change ((V.strip w).lo : ℝ) ≤ y.1 (V.strip w).level ∧ y.1 (V.strip w).level ≤ (V.strip w).hi
            rw [← hblk.1]
            exact ⟨le_trans (by exact_mod_cast hblk.2.1) (le_of_lt (lt_trans Z.lo_lt_hi_real hyE2.1)), hle'⟩
          · right; push Not at hle'
            let t := (y.1 Z.level - branchWord w 0) * (2 : ℝ) ^ w.length
            have hbt : branchWord w t = y.1 Z.level := by
              rw [branchWord_affine w t]; simp only [branchSign, hp_par, Bool.false_eq_true, ↓reduceIte, one_mul, t]
              field_simp; ring
            have ht_ioo : t ∈ Ioo (V.hi : ℝ) 1 := by
              apply (branchWord_mem_Ioo_iff w V.hi_lt_one_real).mp
              have h3 := (branchWord_strictMono_or_anti w V.hi_lt_one_real).1 hp_par
              have hhi_eq : ((V.strip w).hi : ℝ) = branchWord w V.hi := by
                rw [hhi_r, max_eq_right (le_of_lt (hma.1 hp_par))]
              rw [min_eq_left (le_of_lt h3), max_eq_right (le_of_lt h3), hbt, ← hhi_eq]
              exact ⟨hle', hyE2.2⟩
            have ht_icc : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt (lt_trans V.lo_pos_real (lt_trans V.lo_lt_hi_real ht_ioo.1)),
              le_of_lt ht_ioo.2⟩
            have hyV : y.1 V.level = t := by
              rw [← bh_tent_iterate y V.level w.length, ← hZlvl, ← hbt, tent_iterate_branchWord w ht_icc]
            change (V.hi : ℝ) < y.1 V.level; rw [hyV]; exact ht_ioo.1
        · rw [if_neg (by rw [hp_par]; exact Bool.false_ne_true.symm)] at hyE2
          by_cases hge' : ((V.strip w).lo : ℝ) ≤ y.1 Z.level
          · left
            change ((V.strip w).lo : ℝ) ≤ y.1 (V.strip w).level ∧ y.1 (V.strip w).level ≤ (V.strip w).hi
            rw [← hblk.1]
            exact ⟨hge', le_trans (le_of_lt (lt_trans hyE2.2 Z.lo_lt_hi_real)) (by exact_mod_cast hblk.2.2)⟩
          · right; push Not at hge'
            let t := -(y.1 Z.level - branchWord w 0) * (2 : ℝ) ^ w.length
            have hbt : branchWord w t = y.1 Z.level := by
              rw [branchWord_affine w t]; simp only [branchSign, hp_par, ↓reduceIte, neg_mul, one_mul, t]
              field_simp; ring
            have ht_ioo : t ∈ Ioo (V.hi : ℝ) 1 := by
              apply (branchWord_mem_Ioo_iff w V.hi_lt_one_real).mp
              have h3 := (branchWord_strictMono_or_anti w V.hi_lt_one_real).2 hp_par
              have hlo_eq : ((V.strip w).lo : ℝ) = branchWord w V.hi := by
                rw [hlo_r, min_eq_right (le_of_lt (hma.2 hp_par))]
              rw [min_eq_right (le_of_lt h3), max_eq_left (le_of_lt h3), hbt, ← hlo_eq]
              exact ⟨hyE2.1, hge'⟩
            have ht_icc : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt (lt_trans V.lo_pos_real (lt_trans V.lo_lt_hi_real ht_ioo.1)),
              le_of_lt ht_ioo.2⟩
            have hyV : y.1 V.level = t := by
              rw [← bh_tent_iterate y V.level w.length, ← hZlvl, ← hbt, tent_iterate_branchWord w ht_icc]
            change (V.hi : ℝ) < y.1 V.level; rw [hyV]; exact ht_ioo.1
      rcases hy_bar_or_R2 with hybar | hyR2
      · rcases hyD with hyR1 | hyU
        · exact not_lt_of_ge (((V.mem_strip_bar_iff w y).mp hybar).1).1 hyR1
        · rcases mem_iUnion₂.mp hyU with ⟨E', hE'good, hyE'⟩
          rcases hE'good with ⟨hleE', ⟨y₁, hy₁E', hy₁R1⟩, m, hmiss⟩
          have hyside' : (branchParity w = false → (Z.hi : ℝ) < y.1 Z.level) ∧
              (branchParity w = true → y.1 Z.level < (Z.lo : ℝ)) := by
            dsimp only [E₂] at hyE2
            exact ⟨fun h => by rw [if_pos h] at hyE2; exact hyE2.1,
              fun h => by rw [if_neg (by rw [h]; exact Bool.false_ne_true.symm)] at hyE2; exact hyE2.2⟩
          obtain ⟨u, hsub⟩ := corridor_strip_subset hblk hleE' (hGood_disj_R2 E' ⟨hleE', ⟨y₁, hy₁E', hy₁R1⟩, m, hmiss⟩)
            hy₁E' hy₁R1 hyE' hybar hyside'
          obtain ⟨q, hq, z, hzZu, hzQ⟩ := hZstrip_meets n (w, Z) hp m u
          exact disjoint_left.mp (hmiss q hq) (hsub hzZu) hzQ
      · exact disjoint_left.mp hD_disj_R2 hyD hyR2
    rcases mem_closure_iff.mp hxT.1 E₂ hE2_open hx_in_E2 with ⟨y, hyE2, hyD⟩
    exact disjoint_left.mp hE2_disj_D hyE2 hyD
  cases hp_par : branchParity w
  · rcases hlo_or_hi with h1 | h2
    · exact hR1_side ⟨fun _ => h1, fun h => absurd (hp_par.symm.trans h) Bool.false_ne_true⟩
    · exact hR2_side ⟨fun _ => h2, fun h => absurd (hp_par.symm.trans h) Bool.false_ne_true⟩
  · rcases hlo_or_hi with h1 | h2
    · exact hR2_side ⟨fun h => absurd (hp_par.symm.trans h) Bool.false_ne_true.symm, fun _ => h1⟩
    · exact hR1_side ⟨fun h => absurd (hp_par.symm.trans h) Bool.false_ne_true.symm, fun _ => h2⟩

/-- Rudin Lemma 3 (pp. 19–21). -/
lemma rudin_lemma3 {A B : Set BH} (_hAB_disj : Disjoint A B)
    (hAB_comp : ∀ a ∈ A, ∀ b ∈ B, ¬ SameComp a b)
    (hAB_cnt : (A ∪ B).Countable)
    (hB_ne0 : ∃ b ∈ B, b ≠ bhZero)
    (hW_lam : ∀ W : BHSec, (W.carrier ∩ B).Nonempty → ∃ w : List Bool, propLambda A B (W.strip w)) :
    ∃ T : Set BH, IsSepSet T ∧ Disjoint T A ∧
      ∀ S : Set BH, IsSepSet S → Disjoint S B → GAvd S T := by
  -- Step 1: Index A ∪ B into ℕ and define firstOf
  have : Countable ↑(A ∪ B) := hAB_cnt.to_subtype
  obtain ⟨ord, hord_inj⟩ := exists_injective_nat ↑(A ∪ B)
  let idx : BH → ℕ := fun x => if h : x ∈ A ∪ B then ord ⟨x, h⟩ else 0
  have hidx_inj : ∀ {x y : BH}, x ∈ A ∪ B → y ∈ A ∪ B → idx x = idx y → x = y := by
    intro x y hx hy heq
    simp only [idx, dif_pos hx, dif_pos hy] at heq
    exact congrArg Subtype.val (hord_inj heq)
  obtain ⟨firstOf, hfirst_mem, hfirst_le⟩ :
      ∃ firstOf : ∀ (E : Set BH), E.Nonempty → BH,
        (∀ (E : Set BH) (hE : E.Nonempty), firstOf E hE ∈ E) ∧
        (∀ (E : Set BH) (hE : E.Nonempty) (x : BH), x ∈ E → idx (firstOf E hE) ≤ idx x) := by
    let f : ∀ (E : Set BH), E.Nonempty → BH := fun E hE =>
      let hex : ∃ n : ℕ, ∃ x ∈ E, idx x = n := ⟨idx hE.choose, hE.choose, hE.choose_spec, rfl⟩
      (Nat.find_spec hex).choose
    refine ⟨f, fun E hE =>
      (Nat.find_spec (⟨idx hE.choose, hE.choose, hE.choose_spec, rfl⟩ : ∃ n, ∃ x ∈ E, idx x = n)).choose_spec.1,
      fun E hE x hx => ?_⟩
    have hspec := (Nat.find_spec (⟨idx hE.choose, hE.choose, hE.choose_spec, rfl⟩ : ∃ n, ∃ x ∈ E, idx x = n)).choose_spec.2
    change idx (f E hE) ≤ idx x
    rw [show idx (f E hE) = _ from hspec]
    exact Nat.find_min' _ ⟨x, hx, rfl⟩
  have hfirst_lt_of_not_mem : ∀ {E₁ E₂ : Set BH} (h₁ : E₁.Nonempty) (h₂ : E₂.Nonempty),
      E₁ ⊆ E₂ → E₂ ⊆ A ∪ B → firstOf E₂ h₂ ∉ E₁ → idx (firstOf E₂ h₂) < idx (firstOf E₁ h₁) := by
    intro E₁ E₂ h₁ h₂ hsub hAB hnot
    have hle := hfirst_le E₂ h₂ (firstOf E₁ h₁) (hsub (hfirst_mem E₁ h₁))
    refine lt_of_le_of_ne hle fun heq => hnot ?_
    have hxeq := hidx_inj (hAB (hfirst_mem E₂ h₂)) (hAB (hsub (hfirst_mem E₁ h₁))) heq
    rw [hxeq]; exact hfirst_mem E₁ h₁
  -- Step 2: Pick initial section V with propLambda A B V
  rcases hB_ne0 with ⟨b₀, hb₀B, hb₀_ne0⟩
  obtain ⟨W₀, _, _, hb₀W, _⟩ := BHSec.exists_sec_bar_subset_of_mem_open hb₀_ne0 isOpen_univ (mem_univ b₀) 0 zero_lt_one
  obtain ⟨w₀, hV_lam⟩ := hW_lam W₀ ⟨b₀, hb₀W, hb₀B⟩
  let V : BHSec := W₀.strip w₀
  -- Step 3: Enumerate all words v_seq : ℕ → List Bool
  obtain ⟨v_seq, hv_surj⟩ := exists_surjective_nat (List Bool)
  -- Step 4: Build the step operator children(n, w, U) refining by v_seq n
  let refineByV : ℕ → List Bool × BHSec → Set (List Bool × BHSec) := fun n ⟨w, W⟩ =>
    {p | ∃ u ∈ BHSec.splitCyl w (v_seq n), p = (u, W.strip (u.drop w.length))}
  let children : ℕ → List Bool × BHSec → Set (List Bool × BHSec) := fun n ⟨w, U⟩ =>
    if hU : propLambda A B U then
      let K0 : Set (List Bool × BHSec) :=
        if Even n then (even_step_partition hU (fun hne => firstOf (A ∩ U.bar) hne) (fun hne => hfirst_mem _ hne)).choose
        else
          let hneB := propLambda_inter_B hU
          let q := firstOf (U.carrier ∩ B) hneB
          have hq := hfirst_mem (U.carrier ∩ B) hneB
          (odd_step_partition hW_lam hU hq.1 hq.2).choose
      ⋃ p ∈ K0, refineByV n (w ++ p.1, p.2)
    else ∅
  obtain ⟨F, hF0, hFsucc⟩ : ∃ F : ℕ → Set (List Bool × BHSec),
      F 0 = {([], V)} ∧ ∀ n, F (n + 1) = ⋃ p ∈ F n, children n p :=
    ⟨Nat.rec {([], V)} (fun n prev => ⋃ p ∈ prev, children n p), rfl, fun _ => rfl⟩
  have hrefine_spec : ∀ (n : ℕ) (w : List Bool) (W : BHSec),
      BHSec.IsBlock W (V.strip w) → propLambda A B W →
      (∀ p ∈ refineByV n (w, W),
        BHSec.IsBlock p.2 (V.strip p.1) ∧ propLambda A B p.2 ∧ p.2.bar ⊆ W.bar ∧
        ((∀ ε, BHSec.inCyl p.1 ε → BHSec.inCyl (v_seq n) ε) ∨
         (∀ ε, ¬ (BHSec.inCyl p.1 ε ∧ BHSec.inCyl (v_seq n) ε)))) ∧
      (∀ p₁ ∈ refineByV n (w, W), ∀ p₂ ∈ refineByV n (w, W),
        (∃ ε, BHSec.inCyl p₁.1 ε ∧ BHSec.inCyl p₂.1 ε) → p₁ = p₂) ∧
      (∀ ε, BHSec.inCyl w ε ↔ ∃ p ∈ refineByV n (w, W), BHSec.inCyl p.1 ε) := by
    intro n w W hblk hW
    have hsp := BHSec.splitCyl_spec w (v_seq n)
    refine ⟨?_, ?_, ?_⟩
    · rintro p ⟨u, hu, rfl⟩
      obtain ⟨s, hs⟩ := hsp.2.2.1 u hu
      have hdrop : u.drop w.length = s := by simp [hs]
      refine ⟨?_, propLambda_strip hW _, fun x hx => ((W.mem_strip_bar_iff _ x).mp hx).1, hsp.2.2.2 u hu⟩
      rw [hdrop, hs, ← BHSec.strip_append]
      exact BHSec.isBlock_strip hblk s
    · rintro p₁ ⟨u₁, hu₁, rfl⟩ p₂ ⟨u₂, hu₂, rfl⟩ hmeet
      have heq := pairwise_inCyl_eq hsp.2.1 hu₁ hu₂ hmeet
      subst heq; rfl
    · intro ε
      rw [hsp.1 ε]
      constructor
      · rintro ⟨u, hu, hεu⟩; exact ⟨(u, W.strip (u.drop w.length)), ⟨u, hu, rfl⟩, hεu⟩
      · rintro ⟨_, ⟨u, hu, rfl⟩, hεu⟩; exact ⟨u, hu, hεu⟩
  -- Invariants of F n
  have hF_inv : ∀ n,
      (∀ p ∈ F n, BHSec.IsBlock p.2 (V.strip p.1) ∧ propLambda A B p.2) ∧
      (∀ p₁ ∈ F n, ∀ p₂ ∈ F n, (∃ ε, BHSec.inCyl p₁.1 ε ∧ BHSec.inCyl p₂.1 ε) → p₁ = p₂) ∧
      (∀ ε : ℕ → Bool, (∀ b ∈ B ∩ V.carrier, bitsAt V.level b ≠ ε) → ∃ p ∈ F n, BHSec.inCyl p.1 ε) := by
    intro n
    induction n with
    | zero =>
      rw [hF0]
      refine ⟨?_, ?_, ?_⟩
      · intro p hp; rw [mem_singleton_iff] at hp; subst hp
        rw [V.strip_nil]; exact ⟨BHSec.isBlock_refl V, hV_lam⟩
      · intro p₁ hp₁ p₂ hp₂ _
        rw [mem_singleton_iff] at hp₁ hp₂; exact hp₁.trans hp₂.symm
      · intro ε _; exact ⟨([], V), mem_singleton _, BHSec.inCyl_nil ε⟩
    | succ n ih =>
      rcases ih with ⟨hvalid, hdisj, hcov⟩
      have hch_inv : ∀ p0 ∈ F n,
          (∀ p ∈ children n p0, BHSec.IsBlock p.2 (V.strip p.1) ∧ propLambda A B p.2 ∧
            p.2.bar ⊆ p0.2.bar ∧ (∀ ε, BHSec.inCyl p.1 ε → BHSec.inCyl p0.1 ε)) ∧
          (∀ p₁ ∈ children n p0, ∀ p₂ ∈ children n p0,
            (∃ ε, BHSec.inCyl p₁.1 ε ∧ BHSec.inCyl p₂.1 ε) → p₁ = p₂) ∧
          (∀ ε, BHSec.inCyl p0.1 ε → (∀ b ∈ B ∩ V.carrier, bitsAt V.level b ≠ ε) →
            ∃ p ∈ children n p0, BHSec.inCyl p.1 ε) := by
        intro ⟨w, U⟩ hp0
        obtain ⟨hUblk, hUlam⟩ := hvalid (w, U) hp0
        let hEv := even_step_partition hUlam (fun hne => firstOf (A ∩ U.bar) hne) (fun hne => hfirst_mem _ hne)
        let hOd := odd_step_partition hW_lam hUlam (hfirst_mem _ (propLambda_inter_B hUlam)).1
          (hfirst_mem _ (propLambda_inter_B hUlam)).2
        let K0 := if Even n then hEv.choose else hOd.choose
        have hch_eq : children n (w, U) = ⋃ p ∈ K0, refineByV n (w ++ p.1, p.2) := by
          dsimp only [children, K0, hEv, hOd]; rw [dif_pos hUlam]
        have hK0_valid : ∀ p ∈ K0, BHSec.IsBlock p.2 (U.strip p.1) ∧ propLambda A B p.2 := by
          dsimp only [K0]; split_ifs with hev
          · exact hEv.choose_spec.1
          · exact hOd.choose_spec.1
        have hK0_disj : ∀ p₁ ∈ K0, ∀ p₂ ∈ K0, (∃ η, BHSec.inCyl p₁.1 η ∧ BHSec.inCyl p₂.1 η) → p₁ = p₂ := by
          dsimp only [K0]; split_ifs with hev
          · exact hEv.choose_spec.2.1
          · exact hOd.choose_spec.2.1
        have hK0_cov : ∀ ε, BHSec.inCyl w ε → (∀ b ∈ B ∩ V.carrier, bitsAt V.level b ≠ ε) →
            ∃ p ∈ K0, BHSec.inCyl (w ++ p.1) ε := by
          intro ε hεw hnoB
          let η : ℕ → Bool := fun j => ε (w.length + j)
          dsimp only [K0]; split_ifs with hev
          · obtain ⟨p, hp, hη⟩ := hEv.choose_spec.2.2.1 η
            exact ⟨p, hp, (BHSec.inCyl_append w p.1 ε).mpr ⟨hεw, hη⟩⟩
          · let hneB := propLambda_inter_B hUlam
            let q := firstOf (U.carrier ∩ B) hneB
            have hq := hfirst_mem (U.carrier ∩ B) hneB
            have hη_ne : η ≠ bitsAt U.level q := by
              intro heq
              have hqV : q ∈ V.carrier := (V.strip_carrier_subset w) (BHSec.isBlock_carrier_subset hUblk hq.1)
              have hq_cyl : BHSec.inCyl w (bitsAt V.level q) :=
                ((V.mem_strip_carrier_iff w q).mp (BHSec.isBlock_carrier_subset hUblk hq.1)).2
              apply hnoB q ⟨hq.2, hqV⟩
              funext k
              by_cases hk : k < w.length
              · rw [hq_cyl k hk, hεw k hk]
              · have hidx : V.level + k + 1 = U.level + (k - w.length) + 1 := by
                  have : U.level = V.level + w.length := hUblk.1; omega
                have h1 : bitsAt V.level q k = bitsAt U.level q (k - w.length) := by unfold bitsAt; rw [hidx]
                rw [h1, ← heq]; dsimp only [η]; congr 1; omega
            obtain ⟨p, hp, hη⟩ := hOd.choose_spec.2.2.1 η hη_ne
            exact ⟨p, hp, (BHSec.inCyl_append w p.1 ε).mpr ⟨hεw, hη⟩⟩
        have hK0_blkV : ∀ p ∈ K0, BHSec.IsBlock p.2 (V.strip (w ++ p.1)) := fun p hp => by
          rw [← BHSec.strip_append]
          exact BHSec.isBlock_trans (hK0_valid p hp).1 (BHSec.isBlock_strip hUblk p.1)
        refine ⟨?_, ?_, ?_⟩
        · intro p hp
          rw [hch_eq] at hp; rcases mem_iUnion₂.mp hp with ⟨p1, hp1, hp2⟩
          have href := hrefine_spec n (w ++ p1.1) p1.2 (hK0_blkV p1 hp1) (hK0_valid p1 hp1).2
          obtain ⟨hblk, hlam, hbar, _⟩ := href.1 p hp2
          refine ⟨hblk, hlam, hbar.trans ?_, fun ε hε => ?_⟩
          · exact Subset.trans (BHSec.isBlock_bar_subset (hK0_valid p1 hp1).1)
              fun x hx => ((U.mem_strip_bar_iff p1.1 x).mp hx).1
          · exact ((BHSec.inCyl_append w p1.1 ε).mp ((href.2.2 ε).mpr ⟨p, hp2, hε⟩)).1
        · intro p₁ hp₁ p₂ hp₂ ⟨ε, hε1, hε2⟩
          rw [hch_eq] at hp₁ hp₂
          rcases mem_iUnion₂.mp hp₁ with ⟨q₁, hq₁, hp₁'⟩
          rcases mem_iUnion₂.mp hp₂ with ⟨q₂, hq₂, hp₂'⟩
          have href1 := hrefine_spec n (w ++ q₁.1) q₁.2 (hK0_blkV q₁ hq₁) (hK0_valid q₁ hq₁).2
          have href2 := hrefine_spec n (w ++ q₂.1) q₂.2 (hK0_blkV q₂ hq₂) (hK0_valid q₂ hq₂).2
          have hεq1 := (BHSec.inCyl_append w q₁.1 ε).mp ((href1.2.2 ε).mpr ⟨p₁, hp₁', hε1⟩)
          have hεq2 := (BHSec.inCyl_append w q₂.1 ε).mp ((href2.2.2 ε).mpr ⟨p₂, hp₂', hε2⟩)
          have hq_eq : q₁ = q₂ := hK0_disj q₁ hq₁ q₂ hq₂ ⟨fun j => ε (w.length + j), hεq1.2, hεq2.2⟩
          subst hq_eq
          exact href1.2.1 p₁ hp₁' p₂ hp₂' ⟨ε, hε1, hε2⟩
        · intro ε hεw hnoB
          obtain ⟨p1, hp1, hε1⟩ := hK0_cov ε hεw hnoB
          have href := hrefine_spec n (w ++ p1.1) p1.2 (hK0_blkV p1 hp1) (hK0_valid p1 hp1).2
          obtain ⟨p, hp, hεp⟩ := (href.2.2 ε).mp hε1
          exact ⟨p, by rw [hch_eq]; exact mem_iUnion₂.mpr ⟨p1, hp1, hp⟩, hεp⟩
      rw [hFsucc n]
      refine ⟨?_, ?_, ?_⟩
      · intro p hp
        rcases mem_iUnion₂.mp hp with ⟨p0, hp0, hp1⟩
        have h := (hch_inv p0 hp0).1 p hp1
        exact ⟨h.1, h.2.1⟩
      · intro p₁ hp₁ p₂ hp₂ ⟨ε, hε1, hε2⟩
        rcases mem_iUnion₂.mp hp₁ with ⟨q₁, hq₁, hp₁'⟩
        rcases mem_iUnion₂.mp hp₂ with ⟨q₂, hq₂, hp₂'⟩
        have hεq1 := ((hch_inv q₁ hq₁).1 p₁ hp₁').2.2.2 ε hε1
        have hεq2 := ((hch_inv q₂ hq₂).1 p₂ hp₂').2.2.2 ε hε2
        have hq_eq := hdisj q₁ hq₁ q₂ hq₂ ⟨ε, hεq1, hεq2⟩
        subst hq_eq
        exact (hch_inv q₁ hq₁).2.1 p₁ hp₁' p₂ hp₂' ⟨ε, hε1, hε2⟩
      · intro ε hnoB
        obtain ⟨p0, hp0, hε0⟩ := hcov ε hnoB
        obtain ⟨p, hp, hεp⟩ := (hch_inv p0 hp0).2.2 ε hε0 hnoB
        exact ⟨p, mem_iUnion₂.mpr ⟨p0, hp0, hp⟩, hεp⟩
  -- Helper: make a point on fiber ε inside a block W of V.strip wW
  have hmk_pt : ∀ (ε : ℕ → Bool) (W : BHSec) (wW : List Bool), BHSec.IsBlock W (V.strip wW) → BHSec.inCyl wW ε →
      ∃ x ∈ W.carrier, bitsAt V.level x = ε := by
    intro ε W wW hbW hεW
    let t : ℝ := ((W.lo : ℝ) + (W.hi : ℝ)) / 2
    have ht_W : t ∈ Ioo (W.lo : ℝ) (W.hi : ℝ) := by dsimp only [t]; constructor <;> linarith [W.lo_lt_hi_real]
    have ht_icc : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt (lt_trans W.lo_pos_real ht_W.1),
      le_of_lt (lt_trans ht_W.2 W.hi_lt_one_real)⟩
    have ht_ioo : (⟨t, ht_icc⟩ : Icc (0 : ℝ) 1).1 ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_trans W.lo_pos_real ht_W.1, lt_trans ht_W.2 W.hi_lt_one_real⟩
    let η : ℕ → Bool := fun j => ε (wW.length + j)
    let x := chart W.level η ⟨t, ht_icc⟩
    have hxW : x ∈ W.carrier := by simp only [x, BHSec.carrier, mem_ofPred_eq, chart_coord_self]; exact ht_W
    have hxVW : x ∈ (V.strip wW).carrier := BHSec.isBlock_carrier_subset hbW hxW
    refine ⟨x, hxW, ?_⟩
    have hcylW := ((V.mem_strip_carrier_iff wW x).mp hxVW).2
    have htail := bitsAt_chart W.level η ht_ioo
    funext k
    by_cases hk : k < wW.length
    · rw [hcylW k hk, hεW k hk]
    · have hidx : V.level + k + 1 = W.level + (k - wW.length) + 1 := by
        have : W.level = V.level + wW.length := hbW.1; omega
      have h1 : bitsAt V.level x k = bitsAt W.level x (k - wW.length) := by unfold bitsAt; rw [hidx]
      rw [h1, htail]; dsimp only [η]; congr 1; omega
  have hstrip_meets_F : ∀ (n : ℕ) (w : List Bool), ∃ p ∈ F n, ((V.strip w).carrier ∩ p.2.carrier).Nonempty := by
    intro n w
    let C : Set (ℕ → Bool) := (fun b => bitsAt V.level b) '' (B ∩ V.carrier)
    have hC_cnt : C.Countable := (hAB_cnt.mono (inter_subset_left.trans subset_union_right)).image _
    obtain ⟨ε, hεw, hεC⟩ := exists_inCyl_avoiding_countable w hC_cnt
    have hnoB : ∀ b ∈ B ∩ V.carrier, bitsAt V.level b ≠ ε := fun b hb heq => hεC ⟨b, hb, heq⟩
    obtain ⟨p, hp, hεp⟩ := (hF_inv n).2.2 ε hnoB
    have hblk := ((hF_inv n).1 p hp).1
    obtain ⟨x, hxW, hbits⟩ := hmk_pt ε p.2 p.1 hblk hεp
    have hxV : x ∈ V.carrier := (V.strip_carrier_subset p.1) (BHSec.isBlock_carrier_subset hblk hxW)
    exact ⟨p, hp, x, (V.mem_strip_carrier_iff w x).mpr ⟨hxV, hbits.symm ▸ hεw⟩, hxW⟩
  have hZstrip_meets_F : ∀ (n : ℕ) (p : List Bool × BHSec), p ∈ F n →
      ∀ (m : ℕ) (u : List Bool), ∃ q ∈ F m, ((p.2.strip u).carrier ∩ q.2.carrier).Nonempty := by
    intro n p hp m u
    have hblk := ((hF_inv n).1 p hp).1
    let C : Set (ℕ → Bool) := (fun b => bitsAt V.level b) '' (B ∩ V.carrier)
    have hC_cnt : C.Countable := (hAB_cnt.mono (inter_subset_left.trans subset_union_right)).image _
    obtain ⟨ε, hεwu, hεC⟩ := exists_inCyl_avoiding_countable (p.1 ++ u) hC_cnt
    have hnoB : ∀ b ∈ B ∩ V.carrier, bitsAt V.level b ≠ ε := fun b hb heq => hεC ⟨b, hb, heq⟩
    obtain ⟨q, hq, hεq⟩ := (hF_inv m).2.2 ε hnoB
    have hqblk := ((hF_inv m).1 q hq).1
    have hdesc : ∀ {k₁ k₂ : ℕ}, k₁ ≤ k₂ → ∀ {p₁ : List Bool × BHSec}, p₁ ∈ F k₁ →
        ∀ {p₂ : List Bool × BHSec}, p₂ ∈ F k₂ → BHSec.inCyl p₁.1 ε → BHSec.inCyl p₂.1 ε →
        p₂.2.carrier ⊆ p₁.2.carrier := by
      intro k₁ k₂ hle
      induction hle with
      | refl =>
        intro p₁ hp₁ p₂ hp₂ h1 h2
        have heq := (hF_inv k₁).2.1 p₁ hp₁ p₂ hp₂ ⟨ε, h1, h2⟩
        subst heq; exact Subset.rfl
      | @step k _ ih =>
        intro p₁ hp₁ p₂ hp₂ h1 h2
        rw [hFsucc k] at hp₂
        rcases mem_iUnion₂.mp hp₂ with ⟨pm, hpm, hp2_ch⟩
        have hpm_valid := (hF_inv k).1 pm hpm
        dsimp only [children] at hp2_ch
        rw [dif_pos hpm_valid.2] at hp2_ch
        rcases mem_iUnion₂.mp hp2_ch with ⟨p_mid, hp_mid, u_r, hu_r, hp2_eq⟩
        have hsp := BHSec.splitCyl_spec (pm.1 ++ p_mid.1) (v_seq k)
        have hε_pm : BHSec.inCyl pm.1 ε := by
          have hfst : p₂.1 = u_r := congrArg Prod.fst hp2_eq
          have h1' : BHSec.inCyl u_r ε := hfst ▸ h2
          exact ((BHSec.inCyl_append _ _ _).mp ((hsp.1 ε).mpr ⟨u_r, hu_r, h1'⟩)).1
        have hp2_sub_mid : p₂.2.carrier ⊆ p_mid.2.carrier := by
          rw [hp2_eq]; exact p_mid.2.strip_carrier_subset _
        have hmid_blk : BHSec.IsBlock p_mid.2 (pm.2.strip p_mid.1) := by
          by_cases hev : Even k
          · rw [if_pos hev] at hp_mid
            exact ((even_step_partition hpm_valid.2 (fun hne => firstOf (A ∩ pm.2.bar) hne)
              (fun hne => hfirst_mem _ hne)).choose_spec.1 p_mid hp_mid).1
          · rw [if_neg hev] at hp_mid
            exact ((odd_step_partition hW_lam hpm_valid.2
              (hfirst_mem _ (propLambda_inter_B hpm_valid.2)).1
              (hfirst_mem _ (propLambda_inter_B hpm_valid.2)).2).choose_spec.1 p_mid hp_mid).1
        have hmid_sub_pm : p_mid.2.carrier ⊆ pm.2.carrier :=
          (BHSec.isBlock_carrier_subset hmid_blk).trans (pm.2.strip_carrier_subset _)
        exact hp2_sub_mid.trans (hmid_sub_pm.trans (ih hp₁ hpm h1 hε_pm))
    have hεp : BHSec.inCyl p.1 ε := ((BHSec.inCyl_append p.1 u ε).mp hεwu).1
    rcases le_total n m with hnm | hmn
    · have hsub := hdesc hnm hp hq hεp hεq
      obtain ⟨x, hxq, hbits⟩ := hmk_pt ε q.2 q.1 hqblk hεq
      have hxp : x ∈ p.2.carrier := hsub hxq
      have hxpu : x ∈ (p.2.strip u).carrier := by
        rw [p.2.mem_strip_carrier_iff u x]
        refine ⟨hxp, fun i hi => ?_⟩
        have hidx : p.2.level + i + 1 = V.level + (p.1.length + i) + 1 := by
          have : p.2.level = V.level + p.1.length := hblk.1; omega
        have h1 : bitsAt p.2.level x i = bitsAt V.level x (p.1.length + i) := by unfold bitsAt; rw [hidx]
        rw [h1, hbits]
        exact ((BHSec.inCyl_append p.1 u ε).mp hεwu).2 i hi
      exact ⟨q, hq, x, hxpu, hxq⟩
    · have hsub := hdesc hmn hq hp hεq hεp
      have hblk_u : BHSec.IsBlock (p.2.strip u) (V.strip (p.1 ++ u)) := by
        rw [← BHSec.strip_append]; exact BHSec.isBlock_strip hblk u
      obtain ⟨x, hxpu, _⟩ := hmk_pt ε (p.2.strip u) (p.1 ++ u) hblk_u hεwu
      exact ⟨q, hq, x, hxpu, hsub (p.2.strip_carrier_subset u hxpu)⟩
  -- Step 5: Build T via lem3_build_T_from_F!
  obtain ⟨T, hT_sep, hT_sub_Vbar, hPropB⟩ := lem3_build_T_from_F V F
    (fun n p hp => ((hF_inv n).1 p hp).1) (fun n => (hF_inv n).2.1) hstrip_meets_F hZstrip_meets_F
  -- Step 6: Property (C): Disjoint T A
  have hT_disj_A : Disjoint T A := by
    rw [disjoint_left]
    intro p hpT hpA
    have hpV : p ∈ V.bar := hT_sub_Vbar hpT
    let ε := bitsAt V.level p
    have hnoB : ∀ b ∈ B ∩ V.carrier, bitsAt V.level b ≠ ε := by
      intro b ⟨hbB, hbV⟩ heq
      apply hAB_comp p hpA b hbB
      refine ⟨V.level, ε, ⟨⟨p.1 V.level, bh_mem_Icc p V.level⟩, chart_bitsAt V.level p⟩,
        ⟨⟨b.1 V.level, bh_mem_Icc b V.level⟩, ?_⟩⟩
      rw [← heq]; exact chart_bitsAt V.level b
    have hexF : ∀ n, ∃ q ∈ F n, BHSec.inCyl q.1 ε := fun n => (hF_inv n).2.2 ε hnoB
    obtain ⟨qseq, hq_mem, hq_cyl⟩ : ∃ qseq : ℕ → List Bool × BHSec,
        (∀ n, qseq n ∈ F n) ∧ (∀ n, BHSec.inCyl (qseq n).1 ε) :=
      ⟨fun n => (hexF n).choose, fun n => (hexF n).choose_spec.1, fun n => (hexF n).choose_spec.2⟩
    have hp_in_qbar : ∀ n, p ∈ (qseq n).2.bar := fun n =>
      hPropB n (qseq n) (hq_mem n) ⟨(V.mem_strip_bar_iff (qseq n).1 p).mpr ⟨hpV, hq_cyl n⟩, hpT⟩
    have hne_A : ∀ n, (A ∩ (qseq n).2.bar).Nonempty := fun n => ⟨p, hpA, hp_in_qbar n⟩
    have hq_step : ∀ n, (qseq (n + 1)).2.bar ⊆ (qseq n).2.bar ∧
        (Even n → firstOf (A ∩ (qseq n).2.bar) (hne_A n) ∉ (qseq (n + 1)).2.bar) := by
      intro n
      have hmem1 : qseq (n + 1) ∈ ⋃ q ∈ F n, children n q := by rw [← hFsucc n]; exact hq_mem (n + 1)
      rcases mem_iUnion₂.mp hmem1 with ⟨pm, hpm, hch⟩
      have hpm_valid := (hF_inv n).1 pm hpm
      dsimp only [children] at hch
      rw [dif_pos hpm_valid.2] at hch
      rcases mem_iUnion₂.mp hch with ⟨p_mid, hp_mid, u_r, hu_r, hq_eq⟩
      have hsp := BHSec.splitCyl_spec (pm.1 ++ p_mid.1) (v_seq n)
      have hε_pm : BHSec.inCyl pm.1 ε := by
        have hfst : (qseq (n + 1)).1 = u_r := congrArg Prod.fst hq_eq
        have h1 : BHSec.inCyl u_r ε := hfst ▸ hq_cyl (n + 1)
        exact ((BHSec.inCyl_append _ _ _).mp ((hsp.1 ε).mpr ⟨u_r, hu_r, h1⟩)).1
      have hpm_eq : pm = qseq n := (hF_inv n).2.1 pm hpm (qseq n) (hq_mem n) ⟨ε, hε_pm, hq_cyl n⟩
      subst hpm_eq
      have hsub1 : (qseq (n + 1)).2.bar ⊆ p_mid.2.bar := by
        rw [hq_eq]; exact fun x hx => ((p_mid.2.mem_strip_bar_iff _ x).mp hx).1
      have hmid_blk : BHSec.IsBlock p_mid.2 ((qseq n).2.strip p_mid.1) := by
        by_cases hev : Even n
        · rw [if_pos hev] at hp_mid
          exact ((even_step_partition hpm_valid.2 (fun hne => firstOf (A ∩ (qseq n).2.bar) hne)
            (fun hne => hfirst_mem _ hne)).choose_spec.1 p_mid hp_mid).1
        · rw [if_neg hev] at hp_mid
          exact ((odd_step_partition hW_lam hpm_valid.2
            (hfirst_mem _ (propLambda_inter_B hpm_valid.2)).1
            (hfirst_mem _ (propLambda_inter_B hpm_valid.2)).2).choose_spec.1 p_mid hp_mid).1
      refine ⟨hsub1.trans (Subset.trans (BHSec.isBlock_bar_subset hmid_blk)
          (fun x hx => (((qseq n).2.mem_strip_bar_iff _ x).mp hx).1)), fun hev hmem => ?_⟩
      rw [if_pos hev] at hp_mid
      exact (even_step_partition hpm_valid.2 (fun hne => firstOf (A ∩ (qseq n).2.bar) hne)
        (fun hne => hfirst_mem _ hne)).choose_spec.2.2.2 (hne_A n) p_mid hp_mid (hsub1 hmem)
    have hidx_grow : ∀ k : ℕ, k ≤ idx (firstOf (A ∩ (qseq (2 * k)).2.bar) (hne_A (2 * k))) := by
      intro k
      induction k with
      | zero => exact Nat.zero_le _
      | succ k ih =>
        have hstep1 : idx (firstOf (A ∩ (qseq (2 * k)).2.bar) (hne_A (2 * k))) <
            idx (firstOf (A ∩ (qseq (2 * k + 1)).2.bar) (hne_A (2 * k + 1))) :=
          hfirst_lt_of_not_mem (hne_A (2 * k + 1)) (hne_A (2 * k))
            (inter_subset_inter_right A (hq_step (2 * k)).1)
            (inter_subset_left.trans subset_union_left)
            (fun h => (hq_step (2 * k)).2 ⟨k, by omega⟩ h.2)
        have hstep2 : idx (firstOf (A ∩ (qseq (2 * k + 1)).2.bar) (hne_A (2 * k + 1))) ≤
            idx (firstOf (A ∩ (qseq (2 * (k + 1))).2.bar) (hne_A (2 * (k + 1)))) := by
          have hsub : A ∩ (qseq (2 * (k + 1))).2.bar ⊆ A ∩ (qseq (2 * k + 1)).2.bar := by
            rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega]
            exact inter_subset_inter_right A (hq_step (2 * k + 1)).1
          exact hfirst_le (A ∩ (qseq (2 * k + 1)).2.bar) (hne_A (2 * k + 1))
            (firstOf (A ∩ (qseq (2 * (k + 1))).2.bar) (hne_A (2 * (k + 1))))
            (hsub (hfirst_mem (A ∩ (qseq (2 * (k + 1))).2.bar) (hne_A (2 * (k + 1)))))
        omega
    have hle_p := hfirst_le (A ∩ (qseq (2 * (idx p + 1))).2.bar) (hne_A (2 * (idx p + 1))) p
      ⟨hpA, hp_in_qbar (2 * (idx p + 1))⟩
    have hge_p := hidx_grow (idx p + 1)
    omega
  -- Step 7: Property (D): For every IsSepSet S with Disjoint S B, GAvd S T
  refine ⟨T, hT_sep, hT_disj_A, fun S hS hSB => ?_⟩
  let lo_plus : ℚ := if V.hi < 1 / 2 then V.lo / 2 else (1 / 2 + V.lo) / 2
  let hi_plus : ℚ := if V.hi < 1 / 2 then (V.hi + 1 / 2) / 2 else (V.hi + 1) / 2
  have hlo_plus : 0 < lo_plus ∧ lo_plus < V.lo := by
    dsimp only [lo_plus]; split_ifs with h1
    · constructor <;> linarith [V.hlo]
    · rcases V.hside with h2 | h2
      · exact absurd h2 h1
      · constructor <;> linarith
  have hhi_plus : V.hi < hi_plus ∧ hi_plus < 1 := by
    dsimp only [hi_plus]; split_ifs with h1
    · constructor <;> linarith [V.hhi]
    · constructor <;> linarith [V.hhi]
  have hside_plus : hi_plus < 1 / 2 ∨ 1 / 2 < lo_plus := by
    dsimp only [lo_plus, hi_plus]; split_ifs with h1
    · left; linarith
    · rcases V.hside with h2 | h2
      · exact absurd h2 h1
      · right; linarith
  let Vplus : BHSec := ⟨V.level, lo_plus, hi_plus, hlo_plus.1,
    lt_trans hlo_plus.2 (lt_trans V.hlt hhi_plus.1), hhi_plus.2, hside_plus⟩
  have hT_sub_Vp : T ⊆ Vplus.carrier := fun x hx => by
    have hxV := hT_sub_Vbar hx
    exact ⟨lt_of_lt_of_le (by exact_mod_cast hlo_plus.2) hxV.1,
      lt_of_le_of_lt hxV.2 (by exact_mod_cast hhi_plus.1)⟩
  intro U hU
  have hlem2_hyp : ∀ w : List Bool, ∃ u : List Bool, Disjoint (((Vplus.strip w).strip u).carrier ∩ T) S := by
    intro w
    obtain ⟨n, hn⟩ := hv_surj w
    let C : Set (ℕ → Bool) := (fun b => bitsAt V.level b) '' (B ∩ V.carrier)
    have hC_cnt : C.Countable := (hAB_cnt.mono (inter_subset_left.trans subset_union_right)).image _
    obtain ⟨ε, hεw, hεC⟩ := exists_inCyl_avoiding_countable w hC_cnt
    have hnoB : ∀ b ∈ B ∩ V.carrier, bitsAt V.level b ≠ ε := fun b hb heq => hεC ⟨b, hb, heq⟩
    obtain ⟨p₁, hp₁, hε1⟩ := (hF_inv (n + 1)).2.2 ε hnoB
    have hp1_sub_w : ∀ η, BHSec.inCyl p₁.1 η → BHSec.inCyl w η := by
      have hp₁' : p₁ ∈ ⋃ p ∈ F n, children n p := by rw [← hFsucc n]; exact hp₁
      rcases mem_iUnion₂.mp hp₁' with ⟨pm, hpm, hch⟩
      have hpm_valid := (hF_inv n).1 pm hpm
      dsimp only [children] at hch
      rw [dif_pos hpm_valid.2] at hch
      rcases mem_iUnion₂.mp hch with ⟨p_mid, _, u_r, hu_r, hp1_eq⟩
      have hdec := (BHSec.splitCyl_spec (pm.1 ++ p_mid.1) (v_seq n)).2.2.2 u_r hu_r
      rw [hn] at hdec
      have hfst : p₁.1 = u_r := congrArg Prod.fst hp1_eq
      rcases hdec with hsub | hdisj
      · rw [hfst]; exact hsub
      · exfalso; exact hdisj ε ⟨hfst ▸ hε1, hεw⟩
    let m := if Odd (n + 1) then n + 1 else n + 2
    have hm_odd : Odd m := by
      dsimp only [m]; split_ifs with ho
      · exact ho
      · rw [Nat.not_odd_iff_even] at ho; rcases ho with ⟨k, hk⟩; exact ⟨k, by omega⟩
    have hm_not_even : ¬ Even m := Nat.not_even_iff_odd.mpr hm_odd
    obtain ⟨pW, hpW, hεW⟩ := (hF_inv m).2.2 ε hnoB
    have hpW_sub_w : ∀ η, BHSec.inCyl pW.1 η → BHSec.inCyl w η := by
      dsimp only [m] at hpW
      by_cases ho : Odd (n + 1)
      · rw [if_pos ho] at hpW
        have heq := (hF_inv (n + 1)).2.1 pW hpW p₁ hp₁ ⟨ε, hεW, hε1⟩
        rw [heq]; exact hp1_sub_w
      · rw [if_neg ho] at hpW
        have hpW' : pW ∈ ⋃ p ∈ F (n + 1), children (n + 1) p := by rw [← hFsucc (n + 1)]; exact hpW
        rcases mem_iUnion₂.mp hpW' with ⟨pm, hpm, hch⟩
        have hpm_valid := (hF_inv (n + 1)).1 pm hpm
        dsimp only [children] at hch
        rw [dif_pos hpm_valid.2] at hch
        rcases mem_iUnion₂.mp hch with ⟨p_mid, _, u_r, hu_r, hpW_eq⟩
        have hsp := BHSec.splitCyl_spec (pm.1 ++ p_mid.1) (v_seq (n + 1))
        have hfst : pW.1 = u_r := congrArg Prod.fst hpW_eq
        have hε_pm : BHSec.inCyl pm.1 ε :=
          ((BHSec.inCyl_append _ _ _).mp ((hsp.1 ε).mpr ⟨u_r, hu_r, hfst ▸ hεW⟩)).1
        have hpm_eq := (hF_inv (n + 1)).2.1 pm hpm p₁ hp₁ ⟨ε, hε_pm, hε1⟩
        subst hpm_eq
        intro η hη
        have h2 : BHSec.inCyl pm.1 η := ((BHSec.inCyl_append _ _ _).mp ((hsp.1 η).mpr ⟨u_r, hu_r, hfst ▸ hη⟩)).1
        exact hp1_sub_w η h2
    have hpW_lam := ((hF_inv m).1 pW hpW).2
    let hneB := propLambda_inter_B hpW_lam
    let q := firstOf (pW.2.carrier ∩ B) hneB
    have hq := hfirst_mem (pW.2.carrier ∩ B) hneB
    have hq_notS : q ∈ Sᶜ := fun h => disjoint_left.mp hSB h hq.2
    obtain ⟨i, hi_sub⟩ := exists_bhBall_subset_of_isOpen hS.1.isOpen_compl hq_notS
    obtain ⟨p_mid, hp_mid, hmid_ball⟩ := (odd_step_partition hW_lam hpW_lam hq.1 hq.2).choose_spec.2.2.2 i
    have hsp := BHSec.splitCyl_spec (pW.1 ++ p_mid.1) (v_seq m)
    obtain ⟨u_r, hu_r, _⟩ := (hsp.1 (prependWord (pW.1 ++ p_mid.1) (fun _ => false))).mp (BHSec.inCyl_prepend _ _)
    let pZ : List Bool × BHSec := (u_r, p_mid.2.strip (u_r.drop (pW.1 ++ p_mid.1).length))
    have hpZ_mem : pZ ∈ F (m + 1) := by
      rw [hFsucc m]
      refine mem_iUnion₂.mpr ⟨pW, hpW, ?_⟩
      dsimp only [children]; rw [dif_pos hpW_lam, if_neg hm_not_even]
      exact mem_iUnion₂.mpr ⟨p_mid, hp_mid, u_r, hu_r, rfl⟩
    have hpZ_sub_w : ∀ η, BHSec.inCyl pZ.1 η → BHSec.inCyl w η := fun η hη => by
      have h1 : BHSec.inCyl (pW.1 ++ p_mid.1) η := (hsp.1 η).mpr ⟨u_r, hu_r, hη⟩
      exact hpW_sub_w η ((BHSec.inCyl_append _ _ _).mp h1).1
    obtain ⟨u, hu_eq⟩ := inCyl_prefix_of_subset hpZ_sub_w
    refine ⟨u, disjoint_left.mpr fun x ⟨hxVp, hxT⟩ hxS => ?_⟩
    rw [BHSec.strip_append, ← hu_eq] at hxVp
    have hcyl_Z : BHSec.inCyl pZ.1 (bitsAt V.level x) := ((Vplus.mem_strip_carrier_iff pZ.1 x).mp hxVp).2
    have hx_Vstrip : x ∈ (V.strip pZ.1).bar := (V.mem_strip_bar_iff pZ.1 x).mpr ⟨hT_sub_Vbar hxT, hcyl_Z⟩
    have hx_pZ : x ∈ pZ.2.bar := hPropB (m + 1) pZ hpZ_mem ⟨hx_Vstrip, hxT⟩
    have hx_mid : x ∈ p_mid.2.bar := ((p_mid.2.mem_strip_bar_iff _ x).mp hx_pZ).1
    exact hi_sub (hmid_ball hx_mid) hxS
  obtain ⟨w_out, hdisj_out⟩ := rudin_lemma2 hT_sub_Vp hlem2_hyp hU
  exact ⟨U.strip w_out, U.strip_carrier_subset w_out, inG_strip hU w_out, hdisj_out⟩

/- Section 6: Transfinite recursion under CH and main theorem -/

/-- Rudin Case 2(ii)(b) (pp. 23–24): if no strip of `W` satisfies `propLambda A B`,
    then `W.carrier ∩ closure B` is `G(S)`-avoidable for every `S ∈ CanSep` disjoint from `A`. -/
lemma rudin_case2iib_avoidable {A B : Set BH} {W : BHSec}
    (hnot_lam : ∀ w : List Bool, ¬ propLambda A B (W.strip w))
    {S : Set BH} (hS : CanSep S) (hSA : Disjoint S A) :
    GAvd S (W.carrier ∩ closure B) := by
  intro U hU
  obtain ⟨L, hL_eq, hL_sub⟩ := BHSec.section_inter_decompose W U
  by_cases hall : ∀ Wi ∈ L, ∀ w : List Bool, ∃ u : List Bool,
      Disjoint (((Wi.strip w).strip u).carrier ∩ (Wi.carrier ∩ closure B)) S
  · -- Apply Lemma 2 sequentially to each piece Wi ∈ L
    have hind : ∀ L' : List BHSec,
        (∀ Wi ∈ L', ∀ w : List Bool, ∃ u : List Bool,
          Disjoint (((Wi.strip w).strip u).carrier ∩ (Wi.carrier ∩ closure B)) S) →
        ∀ U₀ : BHSec, inG S U₀ →
          ∃ V : BHSec, V.carrier ⊆ U₀.carrier ∧ inG S V ∧
            ∀ Wi ∈ L', Disjoint (S ∩ V.bar) (Wi.carrier ∩ closure B) := by
      intro L'
      induction L' with
      | nil => intro _ U₀ hU₀; exact ⟨U₀, Subset.rfl, hU₀, by simp⟩
      | cons Wi rest ih =>
        intro hL' U₀ hU₀
        have hWi := hL' Wi List.mem_cons_self
        obtain ⟨w, hdisj_w⟩ := rudin_lemma2 (inter_subset_left : Wi.carrier ∩ closure B ⊆ Wi.carrier) hWi hU₀
        obtain ⟨V, hVU1, hVinG, hrest⟩ := ih (fun Wj hWj => hL' Wj (List.mem_cons_of_mem Wi hWj))
          (U₀.strip w) (inG_strip hU₀ w)
        refine ⟨V, hVU1.trans (U₀.strip_carrier_subset w), hVinG, fun Wj hWj => ?_⟩
        rw [List.mem_cons] at hWj
        rcases hWj with rfl | hmem
        · have hVbar : V.bar ⊆ (U₀.strip w).bar := by
            rw [← V.closure_carrier, ← (U₀.strip w).closure_carrier]; exact closure_mono hVU1
          exact hdisj_w.mono_left (inter_subset_inter_right S hVbar)
        · exact hrest Wj hmem
    obtain ⟨V, hVU, hVinG, hall_disj⟩ := hind L hall U hU
    refine ⟨V, hVU, hVinG, disjoint_left.mpr fun x ⟨hxS, hxVbar⟩ ⟨hxW, hxclB⟩ => ?_⟩
    have hxV : x ∈ V.carrier := by
      rw [V.bar_eq_carrier_union_ends] at hxVbar
      exact hxVbar.resolve_right fun hE => disjoint_left.mp hVinG.1 hxS hE
    have hxWU : x ∈ ⋃ Wi ∈ L, Wi.carrier := by rw [← hL_eq]; exact ⟨hxW, hVU hxV⟩
    rcases mem_iUnion₂.mp hxWU with ⟨Wi, hWi, hxWi⟩
    exact disjoint_left.mp (hall_disj Wi hWi) ⟨hxS, hxVbar⟩ ⟨hxWi, hxclB⟩
  · -- Some Wi ∈ L has a strip X every strip of which meets S!
    push Not at hall
    rcases hall with ⟨Wi, hWiL, w₀, hall_hit⟩
    have hWiW : Wi.carrier ⊆ W.carrier := (hL_sub Wi hWiL).1
    have hWiU : Wi.carrier ⊆ U.carrier := (hL_sub Wi hWiL).2
    obtain ⟨_, uW, _, hWi_blk⟩ := BHSec.subsec_eq_block_of_strip hWiW
    let X := Wi.strip w₀
    have hX_blk_W : BHSec.IsBlock X (W.strip (uW ++ w₀)) := by
      rw [← BHSec.strip_append]; exact BHSec.isBlock_strip hWi_blk w₀
    have hX_sub_U : X.carrier ⊆ U.carrier := (Wi.strip_carrier_subset w₀).trans hWiU
    have hX_hits : ∀ u : List Bool, ((X.strip u).carrier ∩ S).Nonempty := by
      intro u
      have hnd := hall_hit u
      rw [Set.not_disjoint_iff] at hnd
      rcases hnd with ⟨x, ⟨hxX, _⟩, hxS⟩
      exact ⟨x, hxX, hxS⟩
    rcases hS with ⟨hScl, D, E, hDo, hEo, hDE, hDne, hEne, hScov, hScan⟩
    have hXD_ne : (X.carrier ∩ D).Nonempty := by
      have hXS : (X.carrier ∩ S).Nonempty := by simpa [X.strip_nil] using hX_hits []
      exact (hScan X hXS).1
    rcases hXD_ne with ⟨pD, hpDX, hpDD⟩
    obtain ⟨L_sec, _, _, _, hL_sub_XD⟩ := BHSec.exists_sec_bar_subset_of_mem_open
      (X.ne_bhZero_of_mem_bar (X.carrier_subset_bar hpDX)) (X.isOpen_carrier.inter hDo) ⟨hpDX, hpDD⟩ 0 zero_lt_one
    obtain ⟨_, w₁, _, hL_blk⟩ := BHSec.subsec_eq_block_of_strip
      (fun x hx => (hL_sub_XD (L_sec.carrier_subset_bar hx)).1)
    let Y := X.strip w₁
    have hYE_ne : (Y.carrier ∩ E).Nonempty := (hScan Y (hX_hits w₁)).2
    rcases hYE_ne with ⟨pE, hpEY, hpEE⟩
    obtain ⟨N_sec, _, _, _, hN_sub_YE⟩ := BHSec.exists_sec_bar_subset_of_mem_open
      (Y.ne_bhZero_of_mem_bar (Y.carrier_subset_bar hpEY)) (Y.isOpen_carrier.inter hEo) ⟨hpEY, hpEE⟩ 0 zero_lt_one
    obtain ⟨_, w₂, _, hN_blk⟩ := BHSec.subsec_eq_block_of_strip
      (fun x hx => (hN_sub_YE (N_sec.carrier_subset_bar hx)).1)
    let Z := Y.strip w₂
    let L' := L_sec.strip w₂
    have hL'_blk : BHSec.IsBlock L' Z := BHSec.isBlock_strip hL_blk w₂
    have hL'_D : L'.bar ⊆ D := fun x hx =>
      (hL_sub_XD ((L_sec.mem_strip_bar_iff w₂ x).mp hx).1).2
    have hN_E : N_sec.bar ⊆ E := fun x hx => (hN_sub_YE hx).2
    have hdisj_LN : L'.hi < N_sec.lo ∨ N_sec.hi < L'.lo := by
      by_contra hno; push Not at hno
      let t_q : ℚ := max L'.lo N_sec.lo
      have ht_le : t_q ≤ min L'.hi N_sec.hi :=
        max_le (le_min (le_of_lt L'.hlt) hno.2) (le_min hno.1 (le_of_lt N_sec.hlt))
      have ht_icc : (t_q : ℝ) ∈ Icc (0 : ℝ) 1 :=
        ⟨le_of_lt (by exact_mod_cast lt_of_lt_of_le L'.hlo (le_max_left _ _)),
         le_of_lt (by exact_mod_cast lt_of_le_of_lt (le_trans ht_le (min_le_left _ _)) L'.hhi)⟩
      let pt := chart Z.level (fun _ => false) ⟨(t_q : ℝ), ht_icc⟩
      have hptL : pt ∈ L'.bar := by
        change (L'.lo : ℝ) ≤ pt.1 L'.level ∧ pt.1 L'.level ≤ L'.hi
        rw [hL'_blk.1, chart_coord_self]
        exact ⟨Rat.cast_le.mpr (le_max_left L'.lo N_sec.lo),
          Rat.cast_le.mpr (le_trans ht_le (min_le_left L'.hi N_sec.hi))⟩
      have hptN : pt ∈ N_sec.bar := by
        change (N_sec.lo : ℝ) ≤ pt.1 N_sec.level ∧ pt.1 N_sec.level ≤ N_sec.hi
        rw [hN_blk.1, chart_coord_self]
        exact ⟨Rat.cast_le.mpr (le_max_right L'.lo N_sec.lo),
          Rat.cast_le.mpr (le_trans ht_le (min_le_right L'.hi N_sec.hi))⟩
      exact disjoint_left.mp hDE (hL'_D hptL) (hN_E hptN)
    -- Construct Q : BHSec between L' and N_sec inside Z with inG S Q
    have hexQ : ∃ Q : BHSec, BHSec.IsBlock Q Z ∧ inG S Q := by
      rcases hdisj_LN with hlt | hlt
      · let Q : BHSec :=
          { level := Z.level
            lo := L'.hi
            hi := N_sec.lo
            hlo := lt_trans L'.hlo L'.hlt
            hlt := hlt
            hhi := lt_trans N_sec.hlt N_sec.hhi
            hside := Z.hside.imp (fun h => lt_trans (lt_of_lt_of_le N_sec.hlt hN_blk.2.2) h)
              (fun h => lt_trans (lt_of_lt_of_le h hL'_blk.2.1) L'.hlt) }
        have hQ_blk : BHSec.IsBlock Q Z :=
          ⟨rfl, le_trans hL'_blk.2.1 (le_of_lt L'.hlt), le_trans (le_of_lt N_sec.hlt) hN_blk.2.2⟩
        have hQe0 : Q.end0 ⊆ D := fun x hx => hL'_D (by
          change (L'.lo : ℝ) ≤ x.1 L'.level ∧ x.1 L'.level ≤ L'.hi
          rw [hL'_blk.1, show x.1 Z.level = (L'.hi : ℝ) from hx]; exact ⟨le_of_lt L'.lo_lt_hi_real, le_rfl⟩)
        have hQe1 : Q.end1 ⊆ E := fun x hx => hN_E (by
          change (N_sec.lo : ℝ) ≤ x.1 N_sec.level ∧ x.1 N_sec.level ≤ N_sec.hi
          rw [hN_blk.1, show x.1 Z.level = (N_sec.lo : ℝ) from hx]; exact ⟨le_rfl, le_of_lt N_sec.lo_lt_hi_real⟩)
        refine ⟨Q, hQ_blk, disjoint_left.mpr fun x hxS hxE => ?_, D, E, hDo, hEo, hDE,
          fun x hx => by rw [← hScov]; exact hx.2, hQe0, hQe1⟩
        have hmem : x ∈ D ∪ E := hxE.imp (fun h => hQe0 h) (fun h => hQe1 h)
        rw [← hScov] at hmem; exact hmem hxS
      · let Q : BHSec :=
          { level := Z.level
            lo := N_sec.hi
            hi := L'.lo
            hlo := lt_trans N_sec.hlo N_sec.hlt
            hlt := hlt
            hhi := lt_trans L'.hlt L'.hhi
            hside := Z.hside.imp (fun h => lt_trans (lt_of_lt_of_le L'.hlt hL'_blk.2.2) h)
              (fun h => lt_trans (lt_of_lt_of_le h hN_blk.2.1) N_sec.hlt) }
        have hQ_blk : BHSec.IsBlock Q Z :=
          ⟨rfl, le_trans hN_blk.2.1 (le_of_lt N_sec.hlt), le_trans (le_of_lt L'.hlt) hL'_blk.2.2⟩
        have hQe0 : Q.end0 ⊆ E := fun x hx => hN_E (by
          change (N_sec.lo : ℝ) ≤ x.1 N_sec.level ∧ x.1 N_sec.level ≤ N_sec.hi
          rw [hN_blk.1, show x.1 Z.level = (N_sec.hi : ℝ) from hx]; exact ⟨le_of_lt N_sec.lo_lt_hi_real, le_rfl⟩)
        have hQe1 : Q.end1 ⊆ D := fun x hx => hL'_D (by
          change (L'.lo : ℝ) ≤ x.1 L'.level ∧ x.1 L'.level ≤ L'.hi
          rw [hL'_blk.1, show x.1 Z.level = (L'.lo : ℝ) from hx]; exact ⟨le_rfl, le_of_lt L'.lo_lt_hi_real⟩)
        refine ⟨Q, hQ_blk, disjoint_left.mpr fun x hxS hxE => ?_, E, D, hEo, hDo, hDE.symm,
          fun x hx => by have : x ∈ Sᶜ := hx.2; rw [hScov] at this; exact this.symm, hQe0, hQe1⟩
        have hmem : x ∈ D ∪ E := (hxE.imp (fun h => hQe0 h) (fun h => hQe1 h)).symm
        rw [← hScov] at hmem; exact hmem hxS
    rcases hexQ with ⟨Q, hQ_blk_Z, hQ_inG⟩
    have hZ_blk_W : BHSec.IsBlock Z (W.strip ((uW ++ w₀) ++ (w₁ ++ w₂))) := by
      change BHSec.IsBlock ((X.strip w₁).strip w₂) (W.strip ((uW ++ w₀) ++ (w₁ ++ w₂)))
      rw [BHSec.strip_append X w₁ w₂, ← BHSec.strip_append W (uW ++ w₀) (w₁ ++ w₂)]
      exact BHSec.isBlock_strip hX_blk_W (w₁ ++ w₂)
    have hQ_blk_W : BHSec.IsBlock Q (W.strip ((uW ++ w₀) ++ (w₁ ++ w₂))) :=
      BHSec.isBlock_trans hQ_blk_Z hZ_blk_W
    obtain ⟨hSQ_sep, hSQ_inG⟩ := inG_of_block hScl hQ_inG hQ_blk_W
    have hSQ_disj_A : Disjoint (S ∩ Q.bar) A := hSA.mono_left inter_subset_left
    have hexJ : ∃ J : BHSec, inG (S ∩ Q.bar) J ∧ Disjoint J.carrier B := by
      by_contra hno; push Not at hno
      apply hnot_lam ((uW ++ w₀) ++ (w₁ ++ w₂))
      refine ⟨S ∩ Q.bar, hSQ_sep, hSQ_disj_A, hSQ_inG, fun J hJ => ?_⟩
      exact Set.not_disjoint_iff.mp (hno J hJ)
    rcases hexJ with ⟨J, hJ_inG, hJ_disj_B⟩
    obtain ⟨V, hVJ, hVQ, hV_inG⟩ := exists_inG_subset_inter hScl hQ_inG hJ_inG
    have hQ_sub_U : Q.carrier ⊆ U.carrier :=
      (BHSec.isBlock_carrier_subset hQ_blk_Z).trans
        ((Y.strip_carrier_subset w₂).trans ((X.strip_carrier_subset w₁).trans hX_sub_U))
    refine ⟨V, hVQ.trans hQ_sub_U, hV_inG, disjoint_left.mpr fun x ⟨hxS, hxVbar⟩ ⟨_, hxclB⟩ => ?_⟩
    have hxV : x ∈ V.carrier := by
      rw [V.bar_eq_carrier_union_ends] at hxVbar
      exact hxVbar.resolve_right fun hE => disjoint_left.mp hV_inG.1 hxS hE
    rcases mem_closure_iff.mp hxclB J.carrier J.isOpen_carrier (hVJ hxV) with ⟨y, hyJ, hyB⟩
    exact disjoint_left.mp hJ_disj_B hyJ hyB

/-- Cardinality of `BH` is at most `𝔠`. -/
lemma mk_BH_le_continuum : Cardinal.mk BH ≤ 𝔠 := by
  have h1 : Cardinal.mk BH ≤ Cardinal.mk (ℝ × ℝ) := Cardinal.mk_le_of_injective injective_embedBH2
  have h2 : Cardinal.mk (ℝ × ℝ) = 𝔠 := by
    rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.mk_real,
      Cardinal.mul_eq_self Cardinal.aleph0_le_continuum]
  exact h1.trans_eq h2

/-- The family of countable single-point-per-composant subsets of `BH` (`ℬ` in Rudin p. 22). -/
def FamB : Type := {B : Set BH // B.Countable ∧ ∀ x ∈ B, ∀ y ∈ B, SameComp x y → x = y}

/-- The family of canonical separating sets of `BH` (`𝒮` in Rudin p. 22). -/
def FamS : Type := {S : Set BH // CanSep S}

lemma mk_FamB_le_continuum : Cardinal.mk FamB ≤ 𝔠 := by
  let fromOpt : Option (ℕ → BH) → Set BH
    | none => ∅
    | some f => range f
  have hsurj : ∀ B : FamB, ∃ x : Option (ℕ → BH), fromOpt x = B.1 := by
    intro B
    by_cases hne : B.1.Nonempty
    · have : Countable B.1 := B.2.1.to_subtype
      have : Nonempty B.1 := hne.to_subtype
      obtain ⟨g, hg⟩ := exists_surjective_nat B.1
      refine ⟨some (fun n => (g n).1), ?_⟩
      ext y; simp only [fromOpt, mem_range]
      constructor
      · rintro ⟨n, rfl⟩; exact (g n).2
      · intro hy; obtain ⟨n, hn⟩ := hg ⟨y, hy⟩; exact ⟨n, congrArg Subtype.val hn⟩
    · rw [not_nonempty_iff_eq_empty] at hne
      exact ⟨none, hne.symm⟩
  let toOpt : FamB → Option (ℕ → BH) := fun B => (hsurj B).choose
  have hinj : Function.Injective toOpt := fun B₁ B₂ heq => by
    have hval : B₁.1 = B₂.1 := by
      rw [← (hsurj B₁).choose_spec, ← (hsurj B₂).choose_spec]
      exact congrArg fromOpt heq
    exact Subtype.ext hval
  have h1 : Cardinal.mk FamB ≤ Cardinal.mk (Option (ℕ → BH)) := Cardinal.mk_le_of_injective hinj
  have h2 : Cardinal.mk (Option (ℕ → BH)) ≤ 𝔠 := by
    simp only [Cardinal.mk_option, Cardinal.mk_pi, Cardinal.prod_const,
      Cardinal.mk_denumerable ℕ, Cardinal.lift_id]
    have hpow : Cardinal.mk BH ^ ℵ₀ ≤ 𝔠 := by
      calc Cardinal.mk BH ^ ℵ₀ ≤ 𝔠 ^ ℵ₀ := Cardinal.power_le_power_right mk_BH_le_continuum
        _ = (2 ^ ℵ₀) ^ ℵ₀ := by rw [Cardinal.two_power_aleph0]
        _ = 2 ^ (ℵ₀ * ℵ₀) := by rw [← Cardinal.power_mul]
        _ = 2 ^ ℵ₀ := by rw [Cardinal.aleph0_mul_aleph0]
        _ = 𝔠 := Cardinal.two_power_aleph0
    calc Cardinal.mk BH ^ ℵ₀ + 1 ≤ 𝔠 + 1 := add_le_add hpow le_rfl
      _ ≤ 𝔠 + 𝔠 := add_le_add le_rfl (le_trans (by norm_num : (1 : Cardinal) ≤ ℵ₀) Cardinal.aleph0_le_continuum)
      _ = 𝔠 := Cardinal.add_eq_self Cardinal.aleph0_le_continuum
  exact h1.trans h2

lemma mk_FamS_le_continuum : Cardinal.mk FamS ≤ 𝔠 := by
  obtain ⟨b, hb_cnt, _, hb_basis⟩ := TopologicalSpace.exists_countable_basis BH
  let f : FamS → Set ↑b := fun S => {U : ↑b | Disjoint U.1 S.1}
  have hinj : Function.Injective f := by
    intro S₁ S₂ heq
    apply Subtype.ext
    have hcompl : S₁.1ᶜ = S₂.1ᶜ := by
      ext x
      have hiff : ∀ S : FamS, x ∈ S.1ᶜ ↔ ∃ U : ↑b, x ∈ U.1 ∧ U ∈ f S := by
        intro S
        constructor
        · intro hx
          obtain ⟨U, hUb, hxU, hUS⟩ := hb_basis.isOpen_iff.mp S.2.1.isOpen_compl x hx
          exact ⟨⟨U, hUb⟩, hxU, disjoint_left.mpr fun y hyU hyS => hUS hyU hyS⟩
        · rintro ⟨U, hxU, hdisj⟩
          exact fun hxS => disjoint_left.mp hdisj hxU hxS
      rw [hiff S₁, hiff S₂, heq]
    exact compl_injective hcompl
  have h1 : Cardinal.mk FamS ≤ Cardinal.mk (Set ↑b) := Cardinal.mk_le_of_injective hinj
  have hb_le : Cardinal.mk ↑b ≤ ℵ₀ := Cardinal.le_aleph0_iff_set_countable.mpr hb_cnt
  have h2 : Cardinal.mk (Set ↑b) ≤ 𝔠 := by
    rw [Cardinal.mk_set, ← Cardinal.two_power_aleph0]
    exact Cardinal.power_le_power_left (by norm_num) hb_le
  exact h1.trans h2

/-- State maintained during Rudin's transfinite recursion. -/
structure RudinState where
  A : Set BH
  Z : Set BH
  K : Set (Set BH)

/-- Rudin's induction invariants H1–H5 (p. 22). -/
def ValidState (st : RudinState) : Prop :=
  Disjoint st.A st.Z ∧
  (∀ p ∈ st.A, compSet p \ {p} ⊆ st.Z) ∧
  st.A.Countable ∧
  st.K.Countable ∧
  st.Z ⊆ ⋃ E ∈ st.K, E ∧
  (∀ S : Set BH, CanSep S → ∀ E ∈ st.K,
    (S ∩ st.A).Nonempty ∨ (∃ q : BH, E = compSet q) ∨ GAvd S E) ∧
  compSet bhZero ⊆ st.Z

/-- One transfinite recursion step processing `x : FamB ⊕ FamS` on top of `st`. -/
def stepState (x : FamB ⊕ FamS) (st : RudinState) : RudinState :=
  if hst : ValidState st then
    match x with
    | Sum.inr ⟨S, hS⟩ =>
      if hmeet : (S ∩ st.A).Nonempty then st
      else
        have hK_prop : ∀ E ∈ st.K, (∃ q : BH, E = compSet q) ∨ GAvd S E := fun E hE =>
          (hst.2.2.2.2.2.1 S hS E hE).resolve_left hmeet
        let p := (rudin_lemma1 (canSep_isSepSet hS) hst.2.2.2.1 hK_prop).choose
        { A := st.A ∪ {p}
          Z := st.Z ∪ (compSet p \ {p})
          K := st.K ∪ {compSet p} }
    | Sum.inl ⟨B₀, hB₀_cnt, hB₀_comp⟩ =>
      let B := B₀ \ st.Z
      let A := st.A \ B₀
      if hBne : B.Nonempty then
        if hlam : ∀ W : BHSec, (W.carrier ∩ B).Nonempty → ∃ w : List Bool, propLambda A B (W.strip w) then
          have hAB_disj : Disjoint A B := disjoint_left.mpr fun _ hA hB => hA.2 hB.1
          have hAB_comp : ∀ a ∈ A, ∀ b ∈ B, ¬ SameComp a b := fun a ha b hb hsc => by
            by_cases heq : a = b
            · exact ha.2 (heq ▸ hb.1)
            · exact hb.2 (hst.2.1 a ha.1 ⟨hsc, Ne.symm heq⟩)
          have hAB_cnt : (A ∪ B).Countable :=
            (hst.2.2.1.mono sdiff_subset).union (hB₀_cnt.mono sdiff_subset)
          have hB_ne0 : ∃ b ∈ B, b ≠ bhZero := by
            rcases hBne with ⟨b, hb⟩
            exact ⟨b, hb, fun h => hb.2 (hst.2.2.2.2.2.2 (h ▸ mem_compSet_self bhZero))⟩
          let T := (rudin_lemma3 hAB_disj hAB_comp hAB_cnt hB_ne0 hlam).choose
          { A := st.A ∪ B
            Z := st.Z ∪ (⋃ p ∈ B, compSet p \ {p}) ∪ (T \ B)
            K := st.K ∪ ((fun p => compSet p) '' B) ∪ {T} }
        else
          have hexW : ∃ W : BHSec, (W.carrier ∩ B).Nonempty ∧ ∀ w : List Bool, ¬ propLambda A B (W.strip w) := by
            push Not at hlam; exact hlam
          let W := hexW.choose
          { A := st.A
            Z := st.Z ∪ ((W.carrier ∩ closure B) \ st.A)
            K := st.K ∪ {W.carrier ∩ closure B} }
      else st
  else st

lemma stepState_mono (x : FamB ⊕ FamS) (st : RudinState) :
    st.A ⊆ (stepState x st).A ∧ st.Z ⊆ (stepState x st).Z ∧ st.K ⊆ (stepState x st).K := by
  unfold stepState
  split_ifs with hst
  · cases x with
    | inr Spack =>
      rcases Spack with ⟨S, hS⟩
      dsimp only; split_ifs
      · exact ⟨Subset.rfl, Subset.rfl, Subset.rfl⟩
      · exact ⟨subset_union_left, subset_union_left, subset_union_left⟩
    | inl Bpack =>
      rcases Bpack with ⟨B₀, hB₀_cnt, hB₀_comp⟩
      dsimp only; split_ifs
      · exact ⟨subset_union_left, subset_union_left.trans subset_union_left,
          subset_union_left.trans subset_union_left⟩
      · exact ⟨Subset.rfl, subset_union_left, subset_union_left⟩
      · exact ⟨Subset.rfl, Subset.rfl, Subset.rfl⟩
  · exact ⟨Subset.rfl, Subset.rfl, Subset.rfl⟩

lemma validState_stepState (x : FamB ⊕ FamS) {st : RudinState} (hst : ValidState st) :
    ValidState (stepState x st) := by
  unfold stepState
  rw [dif_pos hst]
  rcases hst with ⟨hH1, hH2, hH3, hH4, hZcov, hH5, hZ0⟩
  cases x with
  | inr Spack =>
    rcases Spack with ⟨S, hS⟩
    dsimp only
    split_ifs with hmeet
    · exact ⟨hH1, hH2, hH3, hH4, hZcov, hH5, hZ0⟩
    · have hK_prop : ∀ E ∈ st.K, (∃ q : BH, E = compSet q) ∨ GAvd S E := fun E hE =>
        (hH5 S hS E hE).resolve_left hmeet
      set p := (rudin_lemma1 (canSep_isSepSet hS) hH4 hK_prop).choose
      have hp_spec := (rudin_lemma1 (canSep_isSepSet hS) hH4 hK_prop).choose_spec
      have hp_notZ : p ∉ st.Z := fun hpZ => by
        rcases mem_iUnion₂.mp (hZcov hpZ) with ⟨E, hE, hpE⟩
        exact hp_spec.2 E hE hpE
      refine ⟨?_, ?_, hH3.union (countable_singleton p), hH4.union (countable_singleton _), ?_, ?_,
        hZ0.trans subset_union_left⟩
      · rw [disjoint_left]
        rintro x (hxA | rfl) (hxZ | ⟨hxC, hxne⟩)
        · exact disjoint_left.mp hH1 hxA hxZ
        · exact hp_notZ (hH2 x hxA ⟨sameComp_symm hxC, Ne.symm hxne⟩)
        · exact hp_notZ hxZ
        · exact hxne rfl
      · rintro q (hqA | rfl)
        · exact (hH2 q hqA).trans subset_union_left
        · exact subset_union_right
      · rintro x (hxZ | ⟨hxC, _⟩)
        · rcases mem_iUnion₂.mp (hZcov hxZ) with ⟨E, hE, hxE⟩
          exact mem_iUnion₂.mpr ⟨E, Or.inl hE, hxE⟩
        · exact mem_iUnion₂.mpr ⟨compSet p, Or.inr rfl, hxC⟩
      · intro S' hS' E hE
        rcases hE with hEK | rfl
        · rcases hH5 S' hS' E hEK with ⟨y, hyS', hyA⟩ | hcomp | havd
          · exact Or.inl ⟨y, hyS', Or.inl hyA⟩
          · exact Or.inr (Or.inl hcomp)
          · exact Or.inr (Or.inr havd)
        · exact Or.inr (Or.inl ⟨p, rfl⟩)
  | inl Bpack =>
    rcases Bpack with ⟨B₀, hB₀_cnt, hB₀_comp⟩
    dsimp only
    let B := B₀ \ st.Z
    let A := st.A \ B₀
    split_ifs with hBne hlam
    · have hAB_disj : Disjoint A B := disjoint_left.mpr fun _ hA hB => hA.2 hB.1
      have hAB_comp : ∀ a ∈ A, ∀ b ∈ B, ¬ SameComp a b := fun a ha b hb hsc => by
        by_cases heq : a = b
        · exact ha.2 (heq ▸ hb.1)
        · exact hb.2 (hH2 a ha.1 ⟨hsc, Ne.symm heq⟩)
      have hAB_cnt : (A ∪ B).Countable :=
        (hH3.mono sdiff_subset).union (hB₀_cnt.mono sdiff_subset)
      have hB_ne0 : ∃ b ∈ B, b ≠ bhZero := by
        rcases hBne with ⟨b, hb⟩
        exact ⟨b, hb, fun h => hb.2 (hZ0 (h ▸ mem_compSet_self bhZero))⟩
      set T := (rudin_lemma3 hAB_disj hAB_comp hAB_cnt hB_ne0 hlam).choose
      have hT_spec := (rudin_lemma3 hAB_disj hAB_comp hAB_cnt hB_ne0 hlam).choose_spec
      have hB_cnt : B.Countable := hB₀_cnt.mono sdiff_subset
      refine ⟨?_, ?_, hH3.union hB_cnt,
        (hH4.union (hB_cnt.image _)).union (countable_singleton T), ?_, ?_,
        hZ0.trans (subset_union_left.trans subset_union_left)⟩
      · rw [disjoint_left]
        rintro x (hxA | hxB) ((hxZ | hxC) | ⟨hxT, hxnotB⟩)
        · exact disjoint_left.mp hH1 hxA hxZ
        · rcases mem_iUnion₂.mp hxC with ⟨p, hpB, hxpC, hxpne⟩
          exact hpB.2 (hH2 x hxA ⟨sameComp_symm hxpC, Ne.symm hxpne⟩)
        · have hxnotB0 : x ∉ B₀ := fun hxB0 => hxnotB ⟨hxB0, fun hxZ => disjoint_left.mp hH1 hxA hxZ⟩
          exact disjoint_left.mp hT_spec.2.1 hxT ⟨hxA, hxnotB0⟩
        · exact hxB.2 hxZ
        · rcases mem_iUnion₂.mp hxC with ⟨p, hpB, hxpC, hxpne⟩
          exact hxpne (hB₀_comp x hxB.1 p hpB.1 (sameComp_symm hxpC))
        · exact hxnotB hxB
      · rintro p (hpA | hpB)
        · exact (hH2 p hpA).trans (subset_union_left.trans subset_union_left)
        · exact fun x hx => Or.inl (Or.inr (mem_iUnion₂.mpr ⟨p, hpB, hx⟩))
      · rintro x ((hxZ | hxC) | ⟨hxT, _⟩)
        · rcases mem_iUnion₂.mp (hZcov hxZ) with ⟨E, hE, hxE⟩
          exact mem_iUnion₂.mpr ⟨E, Or.inl (Or.inl hE), hxE⟩
        · rcases mem_iUnion₂.mp hxC with ⟨p, hpB, hxpC, _⟩
          exact mem_iUnion₂.mpr ⟨compSet p, Or.inl (Or.inr ⟨p, hpB, rfl⟩), hxpC⟩
        · exact mem_iUnion₂.mpr ⟨T, Or.inr rfl, hxT⟩
      · intro S hS E hE
        by_cases hmeet : (S ∩ (st.A ∪ B)).Nonempty
        · exact Or.inl hmeet
        · rcases hE with (hEK | ⟨p, _, rfl⟩) | rfl
          · rcases hH5 S hS E hEK with ⟨y, hyS, hyA⟩ | hcomp | havd
            · exact absurd ⟨y, hyS, Or.inl hyA⟩ hmeet
            · exact Or.inr (Or.inl hcomp)
            · exact Or.inr (Or.inr havd)
          · exact Or.inr (Or.inl ⟨p, rfl⟩)
          · have hSB : Disjoint S B := disjoint_left.mpr fun y hyS hyB => hmeet ⟨y, hyS, Or.inr hyB⟩
            exact Or.inr (Or.inr (hT_spec.2.2 S (canSep_isSepSet hS) hSB))
    · have hexW : ∃ W : BHSec, (W.carrier ∩ B).Nonempty ∧ ∀ w : List Bool, ¬ propLambda A B (W.strip w) := by
        push Not at hlam; exact hlam
      set W := hexW.choose
      have hW_spec := hexW.choose_spec
      refine ⟨?_, fun p hp => (hH2 p hp).trans subset_union_left, hH3,
        hH4.union (countable_singleton _), ?_, ?_, hZ0.trans subset_union_left⟩
      · rw [disjoint_left]
        rintro x hxA (hxZ | ⟨_, hxnotA⟩)
        · exact disjoint_left.mp hH1 hxA hxZ
        · exact hxnotA hxA
      · rintro x (hxZ | ⟨hxW, _⟩)
        · rcases mem_iUnion₂.mp (hZcov hxZ) with ⟨E, hE, hxE⟩
          exact mem_iUnion₂.mpr ⟨E, Or.inl hE, hxE⟩
        · exact mem_iUnion₂.mpr ⟨W.carrier ∩ closure B, Or.inr rfl, hxW⟩
      · intro S hS E hE
        rcases hE with hEK | rfl
        · exact hH5 S hS E hEK
        · by_cases hmeet : (S ∩ st.A).Nonempty
          · exact Or.inl hmeet
          · have hSA : Disjoint S A := disjoint_left.mpr fun y hyS hyA => hmeet ⟨y, hyS, hyA.1⟩
            exact Or.inr (Or.inr (rudin_case2iib_avoidable hW_spec.2 hS hSA))
    · exact ⟨hH1, hH2, hH3, hH4, hZcov, hH5, hZ0⟩

lemma stepState_meets_canSep (S : FamS) {st : RudinState} (hst : ValidState st) :
    (S.1 ∩ (stepState (Sum.inr S) st).A).Nonempty := by
  rcases S with ⟨S, hS⟩
  unfold stepState
  rw [dif_pos hst]
  dsimp only
  split_ifs with hmeet
  · exact hmeet
  · have hK_prop : ∀ E ∈ st.K, (∃ q : BH, E = compSet q) ∨ GAvd S E := fun E hE =>
      (hst.2.2.2.2.2.1 S hS E hE).resolve_left hmeet
    exact ⟨_, (rudin_lemma1 (canSep_isSepSet hS) hst.2.2.2.1 hK_prop).choose_spec.1, Or.inr rfl⟩

/-- Main theorem inside `BH` under CH. -/
lemma rudin_exists_on_BH (hCH : (ℵ₁ : Cardinal.{0}) = 𝔠) :
    ∃ M : Set BH, (∀ S : Set BH, IsSepSet S → (M ∩ S).Nonempty) ∧
      (∀ x ∈ M, ∀ y ∈ M, SameComp x y → x = y) ∧
      (∀ N ⊆ M, IsConnected N → N.Nontrivial → (M \ N).Countable) := by
  -- Step 1: Obtain a Type 0 well-ordering (α, r) of order type (ℵ₁).ord
  obtain ⟨α, r, hwo, htype⟩ : ∃ (α : Type) (r : α → α → Prop) (_ : IsWellOrder α r),
      Ordinal.type r = (ℵ₁ : Cardinal.{0}).ord := by
    refine Ordinal.inductionOn (Cardinal.ord (ℵ₁ : Cardinal.{0})) ?_
    intro α r _
    exact ⟨α, r, inferInstance, rfl⟩
  have hmk_α : Cardinal.mk α = ℵ₁ := by
    rw [← Ordinal.card_type r, htype, Cardinal.card_ord]
  have hinit_cnt : ∀ a : α, Countable {b : α // r b a} := by
    intro a
    have hlt_ord : Ordinal.typein r a < (ℵ₁ : Cardinal.{0}).ord := by
      rw [← htype]; exact Ordinal.typein_lt_type r a
    have hcard_lt : (Ordinal.typein r a).card < ℵ₁ := Cardinal.lt_ord.mp hlt_ord
    have hA1 : (ℵ₁ : Cardinal.{0}) = Order.succ ℵ₀ := by
      rw [← Cardinal.aleph_zero, Cardinal.succ_aleph 0, zero_add]
    have hcard_le : (Ordinal.typein r a).card ≤ ℵ₀ := by
      rw [hA1] at hcard_lt; exact Order.lt_succ_iff.mp hcard_lt
    have hinj : Function.Injective (fun b : {b : α // r b a} =>
        (⟨Ordinal.typein r b.1, (Ordinal.typein_lt_typein r).mpr b.2⟩ : Set.Iio (Ordinal.typein r a))) := by
      intro b₁ b₂ heq
      apply Subtype.ext
      exact (Ordinal.typein_inj r).mp (congrArg Subtype.val heq)
    have hmk_le : Cardinal.mk {b : α // r b a} ≤ (Ordinal.typein r a).card := by
      have h1 : Cardinal.lift.{1} (Cardinal.mk {b : α // r b a}) ≤
          Cardinal.mk (Set.Iio (Ordinal.typein r a)) := by
        rw [← Cardinal.mk_uLift]
        exact Cardinal.mk_le_of_injective
          (f := fun x : ULift.{1, 0} {b : α // r b a} =>
            (⟨Ordinal.typein r x.down.1, (Ordinal.typein_lt_typein r).mpr x.down.2⟩ :
              Set.Iio (Ordinal.typein r a)))
          (fun x y h => ULift.ext _ _ (hinj h))
      rw [Cardinal.mk_Iio_ordinal] at h1
      exact Cardinal.lift_le.mp h1
    exact Cardinal.le_aleph0_iff_subtype_countable.mp (hmk_le.trans hcard_le)
  -- Step 2: Surject α onto FamB ⊕ FamS using CH
  have hmk_sum : Cardinal.mk (FamB ⊕ FamS) ≤ Cardinal.mk α := by
    rw [hmk_α, hCH, Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    calc Cardinal.mk FamB + Cardinal.mk FamS ≤ 𝔠 + 𝔠 := add_le_add mk_FamB_le_continuum mk_FamS_le_continuum
      _ = 𝔠 := Cardinal.add_eq_self Cardinal.aleph0_le_continuum
  obtain ⟨emb⟩ := (Cardinal.le_def _ _).mp hmk_sum
  have hne_sum : Nonempty (FamB ⊕ FamS) := ⟨Sum.inl ⟨∅, countable_empty, by simp⟩⟩
  obtain ⟨enum, henum_surj⟩ : ∃ enum : α → FamB ⊕ FamS, Function.Surjective enum :=
    ⟨Function.invFun emb, Function.invFun_surjective emb.injective⟩
  -- Step 3: Transfinite recursion on (α, r)
  let preState : ∀ (a : α), (∀ b : α, r b a → RudinState) → RudinState := fun a prev =>
    { A := ⋃ (b : {b : α // r b a}), (prev b.1 b.2).A
      Z := compSet bhZero ∪ ⋃ (b : {b : α // r b a}), (prev b.1 b.2).Z
      K := {compSet bhZero} ∪ ⋃ (b : {b : α // r b a}), (prev b.1 b.2).K }
  obtain ⟨F_rec, hF_eq0⟩ : ∃ F_rec : α → RudinState,
      ∀ a : α, F_rec a = stepState (enum a) (preState a (fun b _ => F_rec b)) :=
    ⟨hwo.wf.fix fun a prev => stepState (enum a) (preState a prev),
     fun a => hwo.wf.fix_eq _ a⟩
  let F_pre : α → RudinState := fun a => preState a (fun b _ => F_rec b)
  have hF_eq : ∀ a : α, F_rec a = stepState (enum a) (F_pre a) := hF_eq0
  -- Step 4: Verify monotonicity and ValidState by well-founded induction
  have hrec_inv : ∀ a : α,
      ValidState (F_pre a) ∧ ValidState (F_rec a) ∧
      (∀ b : α, r b a → (F_rec b).A ⊆ (F_pre a).A ∧ (F_rec b).Z ⊆ (F_pre a).Z ∧ (F_rec b).K ⊆ (F_pre a).K) ∧
      (∀ b : α, r b a → (F_rec b).A ⊆ (F_rec a).A ∧ (F_rec b).Z ⊆ (F_rec a).Z ∧ (F_rec b).K ⊆ (F_rec a).K) := by
    intro a
    refine @WellFounded.induction α r hwo.wf
      (fun a => ValidState (F_pre a) ∧ ValidState (F_rec a) ∧
        (∀ b : α, r b a → (F_rec b).A ⊆ (F_pre a).A ∧ (F_rec b).Z ⊆ (F_pre a).Z ∧ (F_rec b).K ⊆ (F_pre a).K) ∧
        (∀ b : α, r b a → (F_rec b).A ⊆ (F_rec a).A ∧ (F_rec b).Z ⊆ (F_rec a).Z ∧ (F_rec b).K ⊆ (F_rec a).K))
      a fun a ih => ?_
    have hmono_pre : ∀ b : α, r b a →
        (F_rec b).A ⊆ (F_pre a).A ∧ (F_rec b).Z ⊆ (F_pre a).Z ∧ (F_rec b).K ⊆ (F_pre a).K := by
      intro b hb
      refine ⟨subset_iUnion (fun x : {b : α // r b a} => (F_rec x.1).A) ⟨b, hb⟩,
        (subset_iUnion (fun x : {b : α // r b a} => (F_rec x.1).Z) ⟨b, hb⟩).trans subset_union_right,
        (subset_iUnion (fun x : {b : α // r b a} => (F_rec x.1).K) ⟨b, hb⟩).trans subset_union_right⟩
    have hpre_valid : ValidState (F_pre a) := by
      have : Countable {b : α // r b a} := hinit_cnt a
      refine ⟨?_, ?_, countable_iUnion fun b => (ih b.1 b.2).2.1.2.2.1,
        (countable_singleton _).union (countable_iUnion fun b => (ih b.1 b.2).2.1.2.2.2.1),
        ?_, ?_, subset_union_left⟩
      · rw [disjoint_left]
        rintro x hxA hxZ
        rcases mem_iUnion.mp hxA with ⟨⟨b₁, hb₁⟩, hxA1⟩
        rcases hxZ with hx0 | hxZ'
        · exact disjoint_left.mp (ih b₁ hb₁).2.1.1 hxA1 ((ih b₁ hb₁).2.1.2.2.2.2.2.2 hx0)
        · rcases mem_iUnion.mp hxZ' with ⟨⟨b₂, hb₂⟩, hxZ2⟩
          rcases trichotomous_of r b₁ b₂ with h12 | rfl | h21
          · exact disjoint_left.mp (ih b₂ hb₂).2.1.1 (((ih b₂ hb₂).2.2.2 b₁ h12).1 hxA1) hxZ2
          · exact disjoint_left.mp (ih b₁ hb₁).2.1.1 hxA1 hxZ2
          · exact disjoint_left.mp (ih b₁ hb₁).2.1.1 hxA1 (((ih b₁ hb₁).2.2.2 b₂ h21).2.1 hxZ2)
      · intro p hpA
        rcases mem_iUnion.mp hpA with ⟨⟨b, hb⟩, hpb⟩
        exact ((ih b hb).2.1.2.1 p hpb).trans (hmono_pre b hb).2.1
      · rintro x (hx0 | hxZ')
        · exact mem_iUnion₂.mpr ⟨compSet bhZero, Or.inl rfl, hx0⟩
        · rcases mem_iUnion.mp hxZ' with ⟨⟨b, hb⟩, hxb⟩
          rcases mem_iUnion₂.mp ((ih b hb).2.1.2.2.2.2.1 hxb) with ⟨E, hEb, hxE⟩
          exact mem_iUnion₂.mpr ⟨E, Or.inr (mem_iUnion.mpr ⟨⟨b, hb⟩, hEb⟩), hxE⟩
      · rintro S hS E (rfl | hEK)
        · exact Or.inr (Or.inl ⟨bhZero, rfl⟩)
        · rcases mem_iUnion.mp hEK with ⟨⟨b, hb⟩, hEb⟩
          rcases (ih b hb).2.1.2.2.2.2.2.1 S hS E hEb with ⟨y, hyS, hyA⟩ | hcomp | havd
          · exact Or.inl ⟨y, hyS, (hmono_pre b hb).1 hyA⟩
          · exact Or.inr (Or.inl hcomp)
          · exact Or.inr (Or.inr havd)
    have hrec_valid : ValidState (F_rec a) := by
      rw [hF_eq a]; exact validState_stepState (enum a) hpre_valid
    have hstep_m := stepState_mono (enum a) (F_pre a)
    rw [← hF_eq a] at hstep_m
    refine ⟨hpre_valid, hrec_valid, hmono_pre, fun b hb =>
      ⟨(hmono_pre b hb).1.trans hstep_m.1, (hmono_pre b hb).2.1.trans hstep_m.2.1,
       (hmono_pre b hb).2.2.trans hstep_m.2.2⟩⟩
  -- Step 5: Define M := ⋃ a, (F_rec a).A and verify all 3 properties
  let M : Set BH := ⋃ a : α, (F_rec a).A
  have hM_disj_Z : ∀ a : α, Disjoint M (F_rec a).Z := by
    intro a
    rw [disjoint_left]
    intro x hxM hxZa
    rcases mem_iUnion.mp hxM with ⟨b, hxb⟩
    rcases trichotomous_of r b a with hba | rfl | hab
    · exact disjoint_left.mp (hrec_inv a).2.1.1 (((hrec_inv a).2.2.2 b hba).1 hxb) hxZa
    · exact disjoint_left.mp (hrec_inv b).2.1.1 hxb hxZa
    · exact disjoint_left.mp (hrec_inv b).2.1.1 hxb (((hrec_inv b).2.2.2 a hab).2.1 hxZa)
  have hM_sep : ∀ S : Set BH, IsSepSet S → (M ∩ S).Nonempty := by
    intro S hS
    obtain ⟨S', hS'can, hS'sub⟩ := rudin_lemma4 hS
    obtain ⟨a, ha⟩ := henum_surj (Sum.inr ⟨S', hS'can⟩)
    have hmeet := stepState_meets_canSep ⟨S', hS'can⟩ (hrec_inv a).1
    rw [← ha, ← hF_eq a] at hmeet
    rcases hmeet with ⟨p, hpS', hpA⟩
    exact ⟨p, mem_iUnion.mpr ⟨a, hpA⟩, hS'sub hpS'⟩
  have hM_comp : ∀ x ∈ M, ∀ y ∈ M, SameComp x y → x = y := by
    intro x hx y hy hsc
    by_contra hne
    rcases mem_iUnion.mp hx with ⟨a, hxa⟩
    have hyZ : y ∈ (F_rec a).Z := (hrec_inv a).2.1.2.1 x hxa ⟨hsc, Ne.symm hne⟩
    exact disjoint_left.mp (hM_disj_Z a) hy hyZ
  refine ⟨M, hM_sep, hM_comp, fun N hNM hN_conn hN_nt => ?_⟩
  -- Step 6: Prove (M \ N).Countable!
  have hclN_univ : closure N = univ := by
    by_contra hne
    obtain ⟨m, η, hsub⟩ := proper_subcontinuum_subset_fiber isClosed_closure hN_conn.closure hne
    rcases hN_nt with ⟨x, hxN, y, hyN, hxy⟩
    exact hxy (hM_comp x (hNM hxN) y (hNM hyN) ⟨m, η, hsub (subset_closure hxN), hsub (subset_closure hyN)⟩)
  by_contra huncnt
  obtain ⟨b, hb_cnt, _, hb_basis⟩ := TopologicalSpace.exists_countable_basis BH
  let E_cond : Set BH := {x ∈ M \ N | ∀ O : Set BH, IsOpen O → x ∈ O → ¬ (O ∩ (M \ N)).Countable}
  have hdiff_cnt : ((M \ N) \ E_cond).Countable := by
    let b_small : Set (Set BH) := {U ∈ b | (U ∩ (M \ N)).Countable}
    have hsub : (M \ N) \ E_cond ⊆ ⋃ U ∈ b_small, U ∩ (M \ N) := by
      rintro x ⟨hxMN, hxnotE⟩
      have hexO : ∃ O : Set BH, IsOpen O ∧ x ∈ O ∧ (O ∩ (M \ N)).Countable := by
        by_contra hall; push Not at hall; exact hxnotE ⟨hxMN, hall⟩
      rcases hexO with ⟨O, hOo, hxO, hOcnt⟩
      obtain ⟨U, hUb, hxU, hUO⟩ := hb_basis.isOpen_iff.mp hOo x hxO
      exact mem_iUnion₂.mpr ⟨U, ⟨hUb, hOcnt.mono (inter_subset_inter_left _ hUO)⟩, hxU, hxMN⟩
    have hb_small_cnt : b_small.Countable := hb_cnt.mono (sep_subset b _)
    exact (hb_small_cnt.biUnion fun _ hU => hU.2).mono hsub
  -- Extract countable dense subset B₀ ⊆ E_cond
  let b_hit : Set (Set BH) := {U ∈ b | (U ∩ E_cond).Nonempty}
  let pick : ↑b_hit → BH := fun U => U.2.2.choose
  let B₀ : Set BH := range pick
  have hB₀_sub : B₀ ⊆ E_cond := by
    rintro _ ⟨U, rfl⟩; exact U.2.2.choose_spec.2
  have hB₀_cnt : B₀.Countable := by
    have : Countable ↑b_hit := (hb_cnt.mono (sep_subset b _)).to_subtype
    exact countable_range pick
  have hE_ne : E_cond.Nonempty := by
    by_contra hemp; rw [not_nonempty_iff_eq_empty] at hemp
    have heq : (M \ N) \ E_cond = M \ N := by simp [hemp]
    rw [heq] at hdiff_cnt; exact huncnt hdiff_cnt
  have hB₀_ne : B₀.Nonempty := by
    rcases hE_ne with ⟨x, hxE⟩
    obtain ⟨U, hUb, hxU, _⟩ := hb_basis.isOpen_iff.mp isOpen_univ x (mem_univ x)
    exact ⟨pick ⟨U, hUb, x, hxU, hxE⟩, ⟨⟨U, hUb, x, hxU, hxE⟩, rfl⟩⟩
  have hE_sub_clB₀ : E_cond ⊆ closure B₀ := by
    intro x hxE
    rw [mem_closure_iff]
    intro O hOo hxO
    obtain ⟨U, hUb, hxU, hUO⟩ := hb_basis.isOpen_iff.mp hOo x hxO
    let U' : ↑b_hit := ⟨U, hUb, x, hxU, hxE⟩
    exact ⟨pick U', hUO U'.2.2.choose_spec.1, ⟨U', rfl⟩⟩
  have hB₀_comp : ∀ x ∈ B₀, ∀ y ∈ B₀, SameComp x y → x = y := fun x hx y hy =>
    hM_comp x (hB₀_sub hx).1.1 y (hB₀_sub hy).1.1
  obtain ⟨a, ha⟩ := henum_surj (Sum.inl ⟨B₀, hB₀_cnt, hB₀_comp⟩)
  have hstep_m := stepState_mono (enum a) (F_pre a)
  rw [← hF_eq a] at hstep_m
  have hB_eq : B₀ \ (F_pre a).Z = B₀ := by
    ext x; simp only [Set.mem_sdiff, and_iff_left_iff_imp]
    intro hxB₀ hxZ
    exact disjoint_left.mp (hM_disj_Z a) (hB₀_sub hxB₀).1.1 (hstep_m.2.1 hxZ)
  -- Unfold F_rec a = stepState (Sum.inl ⟨B₀, ...⟩) (F_pre a)
  have hFa_unfold : F_rec a = stepState (Sum.inl ⟨B₀, hB₀_cnt, hB₀_comp⟩) (F_pre a) := by
    rw [hF_eq a, ha]
  unfold stepState at hFa_unfold
  rw [dif_pos (hrec_inv a).1] at hFa_unfold
  dsimp only at hFa_unfold
  have hBne' : (B₀ \ (F_pre a).Z).Nonempty := hB_eq.symm ▸ hB₀_ne
  rw [dif_pos hBne'] at hFa_unfold
  by_cases hlam : ∀ W : BHSec, (W.carrier ∩ (B₀ \ (F_pre a).Z)).Nonempty →
      ∃ w : List Bool, propLambda ((F_pre a).A \ B₀) (B₀ \ (F_pre a).Z) (W.strip w)
  · -- Case 2(i): Separating set T separates BH and misses N, contradicting closure N = univ!
    rw [dif_pos hlam] at hFa_unfold
    have hAB_disj : Disjoint ((F_pre a).A \ B₀) (B₀ \ (F_pre a).Z) := disjoint_left.mpr fun _ hA hB => hA.2 hB.1
    have hAB_comp : ∀ x ∈ (F_pre a).A \ B₀, ∀ y ∈ B₀ \ (F_pre a).Z, ¬ SameComp x y := fun x hx y hy hsc => by
      by_cases heq : x = y
      · exact hx.2 (heq ▸ hy.1)
      · exact hy.2 ((hrec_inv a).1.2.1 x hx.1 ⟨hsc, Ne.symm heq⟩)
    have hAB_cnt : (((F_pre a).A \ B₀) ∪ (B₀ \ (F_pre a).Z)).Countable :=
      ((hrec_inv a).1.2.2.1.mono sdiff_subset).union (hB₀_cnt.mono sdiff_subset)
    have hB_ne0 : ∃ b ∈ B₀ \ (F_pre a).Z, b ≠ bhZero := by
      rcases hBne' with ⟨b, hb⟩
      exact ⟨b, hb, fun h => hb.2 ((hrec_inv a).1.2.2.2.2.2.2 (h ▸ mem_compSet_self bhZero))⟩
    set T := (rudin_lemma3 hAB_disj hAB_comp hAB_cnt hB_ne0 hlam).choose
    have hT_sep : IsSepSet T := (rudin_lemma3 hAB_disj hAB_comp hAB_cnt hB_ne0 hlam).choose_spec.1
    have hTsubZ : T \ (B₀ \ (F_pre a).Z) ⊆ (F_rec a).Z := by
      rw [hFa_unfold]; exact subset_union_right
    have hN_disj_T : Disjoint N T := by
      rw [disjoint_left]
      intro x hxN hxT
      have hxnotB : x ∉ B₀ \ (F_pre a).Z := fun hxB => (hB₀_sub hxB.1).1.2 hxN
      exact disjoint_left.mp (hM_disj_Z a) (hNM hxN) (hTsubZ ⟨hxT, hxnotB⟩)
    rcases hT_sep with ⟨_, D, E, hDo, hEo, hDE, hDne, hEne, hTcov⟩
    have hNsub : N ⊆ D ∪ E := fun x hxN => by
      rw [← hTcov]; exact fun hxT => disjoint_left.mp hN_disj_T hxN hxT
    have hdisj_or : Disjoint N D ∨ Disjoint N E := by
      by_contra hno; push Not at hno
      rcases Set.not_disjoint_iff.mp hno.1 with ⟨xD, hxND, hxD⟩
      rcases Set.not_disjoint_iff.mp hno.2 with ⟨xE, hxNE, hxE⟩
      rcases hN_conn.isPreconnected D E hDo hEo hNsub ⟨xD, hxND, hxD⟩ ⟨xE, hxNE, hxE⟩ with ⟨z, _, hzD, hzE⟩
      exact disjoint_left.mp hDE hzD hzE
    rcases hdisj_or with hND | hNE
    · rcases hDne with ⟨d, hd⟩
      have hdcl : d ∈ closure N := by rw [hclN_univ]; trivial
      rcases mem_closure_iff.mp hdcl D hDo hd with ⟨z, hzD, hzN⟩
      exact disjoint_left.mp hND hzN hzD
    · rcases hEne with ⟨e, he⟩
      have hecl : e ∈ closure N := by rw [hclN_univ]; trivial
      rcases mem_closure_iff.mp hecl E hEo he with ⟨z, hzE, hzN⟩
      exact disjoint_left.mp hNE hzN hzE
  · -- Case 2(ii)(b): (W.carrier ∩ closure B₀) \ A_pre ⊆ Z_a meets M \ N, contradicting Disjoint M Z_a!
    rw [dif_neg hlam] at hFa_unfold
    have hexW : ∃ W : BHSec, (W.carrier ∩ (B₀ \ (F_pre a).Z)).Nonempty ∧
        ∀ w : List Bool, ¬ propLambda ((F_pre a).A \ B₀) (B₀ \ (F_pre a).Z) (W.strip w) := by
      push Not at hlam; exact hlam
    set W := hexW.choose
    have hW_ne : (W.carrier ∩ B₀).Nonempty := by
      rcases hexW.choose_spec.1 with ⟨x, hxW, hxB⟩
      exact ⟨x, hxW, hxB.1⟩
    have hW_subZ : (W.carrier ∩ closure B₀) \ (F_pre a).A ⊆ (F_rec a).Z := by
      rw [hFa_unfold, hB_eq]; exact subset_union_right
    rcases hW_ne with ⟨b0, hb0W, hb0B⟩
    have hW_MN_uncnt : ¬ (W.carrier ∩ (M \ N)).Countable :=
      (hB₀_sub hb0B).2 W.carrier W.isOpen_carrier hb0W
    have hW_E_uncnt : ¬ (W.carrier ∩ E_cond).Countable := by
      intro hcnt
      apply hW_MN_uncnt
      have hsub : W.carrier ∩ (M \ N) ⊆ (W.carrier ∩ E_cond) ∪ ((M \ N) \ E_cond) := fun x ⟨hxW, hxMN⟩ =>
        by by_cases hxE : x ∈ E_cond; exact Or.inl ⟨hxW, hxE⟩; exact Or.inr ⟨hxMN, hxE⟩
      exact (hcnt.union hdiff_cnt).mono hsub
    have hWE_diff_ne : ((W.carrier ∩ E_cond) \ (F_pre a).A).Nonempty := by
      by_contra hemp; rw [not_nonempty_iff_eq_empty, sdiff_eq_empty] at hemp
      exact hW_E_uncnt ((hrec_inv a).1.2.2.1.mono hemp)
    rcases hWE_diff_ne with ⟨z, ⟨hzW, hzE⟩, hznotA⟩
    exact disjoint_left.mp (hM_disj_Z a) hzE.1.1 (hW_subZ ⟨⟨hzW, hE_sub_clB₀ hzE⟩, hznotA⟩)

end

end Erdos910RudinCH

theorem OMA.solution : type_of% @Erdos910.erdos_910.variants.rudin_CH := by
  intro hCH
  have hCH0 : (ℵ₁ : Cardinal.{0}) = (𝔠 : Cardinal.{0}) := by
    refine Cardinal.lift_inj.mp ?_
    calc Cardinal.lift (ℵ₁ : Cardinal.{0})
        = ℵ₁ := by
          rw [show (ℵ₁ : Cardinal.{0}) = Cardinal.aleph 1 from rfl,
            Cardinal.lift_aleph, Ordinal.lift_one]
      _ = 𝔠 := hCH
      _ = Cardinal.lift (𝔠 : Cardinal.{0}) := Cardinal.lift_continuum.symm
  obtain ⟨M, hM_sep, _, hM_widely⟩ := Erdos910RudinCH.rudin_exists_on_BH hCH0
  let M_plane : Set (EuclideanSpace ℝ (Fin 2)) := Erdos910RudinCH.embedBH '' M
  have hinj : Function.Injective Erdos910RudinCH.embedBH := Erdos910RudinCH.isEmbedding_embedBH.injective
  have hcont : Continuous Erdos910RudinCH.embedBH := Erdos910RudinCH.isEmbedding_embedBH.continuous
  -- Two separating sets {x.1 0 = 1/3} and {x.1 0 = 2/3} witness M.Nontrivial
  have hM_hit : ∀ c : ℝ, 0 < c → c < 1 → ∃ x ∈ M, x.1 0 = c := by
    intro c hc0 hc1
    let S : Set Erdos910RudinCH.BH := {x | x.1 0 = c}
    have hS : Erdos910RudinCH.IsSepSet S := by
      refine ⟨isClosed_eq (Erdos910RudinCH.continuous_bhCoord 0) continuous_const,
        {x | x.1 0 < c}, {x | c < x.1 0},
        isOpen_lt (Erdos910RudinCH.continuous_bhCoord 0) continuous_const,
        isOpen_lt continuous_const (Erdos910RudinCH.continuous_bhCoord 0),
        disjoint_left.mpr fun x h1 h2 => lt_asymm (show x.1 0 < c from h1) (show c < x.1 0 from h2),
        ⟨Erdos910RudinCH.chart 0 (fun _ => false) ⟨0, le_rfl, zero_le_one⟩,
          by simp [Erdos910RudinCH.chart_coord_self, hc0]⟩,
        ⟨Erdos910RudinCH.chart 0 (fun _ => false) ⟨1, zero_le_one, le_rfl⟩,
          by simp [Erdos910RudinCH.chart_coord_self, hc1]⟩, ?_⟩
      ext x; simp only [S, mem_compl_iff, mem_union, mem_ofPred_eq]; exact ne_iff_lt_or_gt
    exact hM_sep S hS
  obtain ⟨x₁, hx₁M, hx₁0⟩ := hM_hit (1 / 3) (by norm_num) (by norm_num)
  obtain ⟨x₂, hx₂M, hx₂0⟩ := hM_hit (2 / 3) (by norm_num) (by norm_num)
  have hM_nt : M_plane.Nontrivial := by
    refine ⟨Erdos910RudinCH.embedBH x₁, ⟨x₁, hx₁M, rfl⟩, Erdos910RudinCH.embedBH x₂, ⟨x₂, hx₂M, rfl⟩, ?_⟩
    intro heq
    have hx12 := hinj heq
    rw [hx12] at hx₁0; linarith
  -- Connectedness of M_plane via the Metric.infDist glue lemma
  have hM_conn : IsConnected M_plane := by
    refine ⟨hM_nt.nonempty, fun U V hUo hVo hcov hU_ne hV_ne => ?_⟩
    by_contra hno
    have hdisj_PQ : Disjoint (M_plane ∩ U) (M_plane ∩ V) := by
      rw [disjoint_left]
      intro z ⟨hzM, hzU⟩ ⟨_, hzV⟩
      exact hno ⟨z, hzM, hzU, hzV⟩
    let P := M_plane ∩ U
    let Q := M_plane ∩ V
    let U' : Set (EuclideanSpace ℝ (Fin 2)) := {z | Metric.infDist z P < Metric.infDist z Q}
    let V' : Set (EuclideanSpace ℝ (Fin 2)) := {z | Metric.infDist z Q < Metric.infDist z P}
    have hU'o : IsOpen U' := isOpen_lt (Metric.continuous_infDist_pt P) (Metric.continuous_infDist_pt Q)
    have hV'o : IsOpen V' := isOpen_lt (Metric.continuous_infDist_pt Q) (Metric.continuous_infDist_pt P)
    have hU'V' : Disjoint U' V' :=
      disjoint_left.mpr fun z h1 h2 =>
        lt_asymm (show Metric.infDist z P < Metric.infDist z Q from h1)
          (show Metric.infDist z Q < Metric.infDist z P from h2)
    have hP_sub : P ⊆ U' := by
      intro z hzP
      change Metric.infDist z P < Metric.infDist z Q
      rw [Metric.infDist_zero_of_mem hzP]
      obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hUo.mem_nhds hzP.2)
      have hdisj_ball : ∀ q ∈ Q, r ≤ dist z q := fun q hqQ => by
        by_contra hlt; push Not at hlt
        exact disjoint_left.mp hdisj_PQ ⟨hqQ.1, hball (by rw [Metric.mem_ball, dist_comm]; exact hlt)⟩ hqQ
      exact lt_of_lt_of_le hr ((Metric.le_infDist hV_ne).mpr hdisj_ball)
    have hQ_sub : Q ⊆ V' := by
      intro z hzQ
      change Metric.infDist z Q < Metric.infDist z P
      rw [Metric.infDist_zero_of_mem hzQ]
      obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hVo.mem_nhds hzQ.2)
      have hdisj_ball : ∀ p ∈ P, r ≤ dist z p := fun p hpP => by
        by_contra hlt; push Not at hlt
        exact disjoint_left.mp hdisj_PQ hpP ⟨hpP.1, hball (by rw [Metric.mem_ball, dist_comm]; exact hlt)⟩
      exact lt_of_lt_of_le hr ((Metric.le_infDist hU_ne).mpr hdisj_ball)
    let A := Erdos910RudinCH.embedBH ⁻¹' U'
    let B := Erdos910RudinCH.embedBH ⁻¹' V'
    have hAo : IsOpen A := hU'o.preimage hcont
    have hBo : IsOpen B := hV'o.preimage hcont
    have hAB : Disjoint A B := disjoint_left.mpr fun x h1 h2 => disjoint_left.mp hU'V' h1 h2
    have hAne : A.Nonempty := by
      rcases hU_ne with ⟨_, ⟨x, hxM, rfl⟩, hxU⟩
      exact ⟨x, hP_sub ⟨⟨x, hxM, rfl⟩, hxU⟩⟩
    have hBne : B.Nonempty := by
      rcases hV_ne with ⟨_, ⟨x, hxM, rfl⟩, hxV⟩
      exact ⟨x, hQ_sub ⟨⟨x, hxM, rfl⟩, hxV⟩⟩
    have hM_sub : M ⊆ A ∪ B := fun x hxM => by
      rcases hcov ⟨x, hxM, rfl⟩ with hxU | hxV
      · exact Or.inl (hP_sub ⟨⟨x, hxM, rfl⟩, hxU⟩)
      · exact Or.inr (hQ_sub ⟨⟨x, hxM, rfl⟩, hxV⟩)
    let S : Set Erdos910RudinCH.BH := (A ∪ B)ᶜ
    have hS : Erdos910RudinCH.IsSepSet S :=
      ⟨(hAo.union hBo).isClosed_compl, A, B, hAo, hBo, hAB, hAne, hBne, compl_compl _⟩
    rcases hM_sep S hS with ⟨x, hxM, hxS⟩
    exact hxS (hM_sub hxM)
  refine ⟨M_plane, hM_conn, hM_nt, fun N' hN'M hN'_conn hN'_nt => ?_⟩
  let N : Set Erdos910RudinCH.BH := Erdos910RudinCH.embedBH ⁻¹' N' ∩ M
  have himgN : Erdos910RudinCH.embedBH '' N = N' := by
    ext z
    constructor
    · rintro ⟨x, ⟨hxN', _⟩, rfl⟩; exact hxN'
    · intro hzN'
      rcases hN'M hzN' with ⟨x, hxM, rfl⟩
      exact ⟨x, ⟨hzN', hxM⟩, rfl⟩
  have hN_nt : N.Nontrivial := by
    rcases hN'_nt with ⟨z₁, hz₁, z₂, hz₂, hne⟩
    rw [← himgN] at hz₁ hz₂
    rcases hz₁ with ⟨x₁, hx₁, rfl⟩
    rcases hz₂ with ⟨x₂, hx₂, rfl⟩
    exact ⟨x₁, hx₁, x₂, hx₂, fun h => hne (congrArg Erdos910RudinCH.embedBH h)⟩
  have hN_conn : IsConnected N := by
    refine ⟨hN_nt.nonempty, fun U V hUo hVo hcov ⟨xU, hxNU, hxU⟩ ⟨xV, hxNV, hxV⟩ => ?_⟩
    obtain ⟨U', hU'o, hU'eq⟩ := Erdos910RudinCH.isEmbedding_embedBH.isOpen_iff.mp hUo
    obtain ⟨V', hV'o, hV'eq⟩ := Erdos910RudinCH.isEmbedding_embedBH.isOpen_iff.mp hVo
    have hcov' : N' ⊆ U' ∪ V' := by
      intro z hz; rw [← himgN] at hz; rcases hz with ⟨x, hxN, rfl⟩
      rcases hcov hxN with h1 | h2
      · rw [← hU'eq] at h1; exact Or.inl h1
      · rw [← hV'eq] at h2; exact Or.inr h2
    have hU'ne : (N' ∩ U').Nonempty :=
      ⟨Erdos910RudinCH.embedBH xU, himgN ▸ ⟨xU, hxNU, rfl⟩, by rwa [← hU'eq] at hxU⟩
    have hV'ne : (N' ∩ V').Nonempty :=
      ⟨Erdos910RudinCH.embedBH xV, himgN ▸ ⟨xV, hxNV, rfl⟩, by rwa [← hV'eq] at hxV⟩
    rcases hN'_conn.isPreconnected U' V' hU'o hV'o hcov' hU'ne hV'ne with ⟨z, hzN', hzU', hzV'⟩
    rw [← himgN] at hzN'
    rcases hzN' with ⟨x, hxN, rfl⟩
    exact ⟨x, hxN, by rwa [← hU'eq], by rwa [← hV'eq]⟩
  have hMN_cnt : (M \ N).Countable := hM_widely N inter_subset_right hN_conn hN_nt
  have hdiff_eq : M_plane \ N' = Erdos910RudinCH.embedBH '' (M \ N) := by
    ext z
    constructor
    · rintro ⟨⟨x, hxM, rfl⟩, hxnotN'⟩
      exact ⟨x, ⟨hxM, fun hxN => hxnotN' hxN.1⟩, rfl⟩
    · rintro ⟨x, ⟨hxM, hxnotN⟩, rfl⟩
      exact ⟨⟨x, hxM, rfl⟩, fun hxN' => hxnotN ⟨hxN', hxM⟩⟩
  rw [hdiff_eq]
  exact hMN_cnt.image _
