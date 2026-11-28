import FormalConjectures.GreensOpenProblems.«17»

/-!
Reduction of `Green17.green_17.variants.bklm` (Bhangale, Khot, Liu, and Minzer,
*On approximability of satisfiable k-CSPs: VI*, arXiv:2411.15133, Theorem 3) to
two unconditional analytic inverse theorems from BKLM24 (`H1`: local inverse theorem
for 3-wise correlations over the restricted 3-AP distribution yielding L^2-bounded
product correlations under random restrictions, Theorems 2/5/7; `H2`: upgrading
L^2-bounded product correlations to 1-bounded product correlations, Theorem 10).

In `main`, we prove completely from scratch in Lean 4:
1. Shifted combinatorial subspaces, injectivity, composition, and restricted-AP lifting.
2. Exact 3-AP telescoping deviation lemma for AP-free subsets of `𝔽₃ n`.
3. Bernoulli subset variance / Chebyshev concentration and Lemma 8.2 subcube dichotomy.
4. Product-function correlation to shifted combinatorial subspace density increment via
   complex-disk bucketing, pigeonhole extraction of disjoint same-bucket triples,
   canonical balanced-triple equivalence classes, and Chebyshev concentration.
5. Multi-step density-increment induction and triple-logarithmic asymptotics yielding
   `Green17.green_17.variants.bklm`.
-/

namespace OMA.R_Green17_green_17_variants_bklm_R1

/- Local inverse theorem for 3-wise correlations over the uniform restricted 3-AP distribution
on F_3^3 (BKLM24 Theorems 2, 5, and 7): any 1-bounded f, g, h with 3-wise correlation >= eps
exhibit, with probability >= delta over delta-random free sets J and uniform restrictions z,
correlation >= delta with an L^2-bounded product function over J, where delta >= exp(-C1 * eps^(-C1)). -/
def H1 : Prop :=
  ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
    ∃ δ : ℝ, Real.exp (-(C₁ * ε ^ (-C₁))) ≤ δ ∧ δ ≤ 1 / 2 ∧
      ∀ (n : ℕ) (f g h : 𝔽₃ n → ℝ),
        (∀ x, |f x| ≤ 1) → (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
        ε ≤ |((∑ x : 𝔽₃ n, ∑ b : Fin n → Bool,
            f x * g (x + fun i => if b i then 1 else 0) *
              h (x + 2 • fun i => if b i then 1 else 0)) / (6 : ℝ) ^ n)| →
        δ ≤ ∑ J : Finset (Fin n),
          δ ^ J.card * (1 - δ) ^ (n - J.card) *
            (({z : 𝔽₃ n | ∃ P : Fin n → ZMod 3 → ℂ,
                (∀ i, ∑ a : ZMod 3, ‖P i a‖ ^ 2 ≤ 3) ∧
                δ ≤ ‖(∑ w : 𝔽₃ n,
                  ((f (fun i => if i ∈ J then w i else z i) : ℂ) *
                    ∏ i ∈ J, P i (w i))) / (3 : ℂ) ^ n‖}.ncard : ℝ) / (3 : ℝ) ^ n)

/- Upgrading L^2-bounded product correlation to 1-bounded product correlation (BKLM24 Theorem 10):
if a 1-bounded real function f on F_3^m correlates >= delta with an L^2-bounded product function,
then it correlates >= delta^C2 with a 1-bounded product function. -/
def H2 : Prop :=
  ∃ C₂ : ℝ, 1 ≤ C₂ ∧ ∀ (m : ℕ) (f : 𝔽₃ m → ℝ) (P : Fin m → ZMod 3 → ℂ) (δ : ℝ),
    0 < δ → δ ≤ 1 / 2 →
    (∀ x, |f x| ≤ 1) →
    (∀ i, ∑ a : ZMod 3, ‖P i a‖ ^ 2 ≤ 3) →
    δ ≤ ‖(∑ x : 𝔽₃ m, (f x : ℂ) * ∏ i : Fin m, P i (x i)) / (3 : ℂ) ^ m‖ →
    ∃ Q : Fin m → ZMod 3 → ℂ,
      (∀ i a, ‖Q i a‖ ≤ 1) ∧
      δ ^ C₂ ≤ ‖(∑ x : 𝔽₃ m, (f x : ℂ) * ∏ i : Fin m, Q i (x i)) / (3 : ℂ) ^ m‖

/- ============================================================================
   Part 1: Shifted Combinatorial Subspaces, Composition, and AP Lifting
   ============================================================================ -/

/- A shifted combinatorial subspace phi(y)_i = z_i + y_j (on block j) or z_i (outside)
is injective whenever every block j in Fin m is nonempty. -/
lemma combSubspace_injective {m n : ℕ} (blk : Fin n → Option (Fin m))
    (hblk : ∀ j : Fin m, ∃ i : Fin n, blk i = some j) (z : 𝔽₃ n) :
    Function.Injective (fun (y : 𝔽₃ m) (i : Fin n) =>
      match blk i with | some j => z i + y j | none => z i) := by
  intro y₁ y₂ heq
  funext j
  obtain ⟨i, hi⟩ := hblk j
  have h1 := congrFun heq i
  simp only [hi] at h1
  exact add_left_cancel h1

/- Composition of two shifted combinatorial subspaces is a shifted combinatorial subspace. -/
lemma combSubspace_comp {k m n : ℕ}
    (blk₁ : Fin m → Option (Fin k)) (hblk₁ : ∀ l : Fin k, ∃ j : Fin m, blk₁ j = some l) (z₁ : 𝔽₃ m)
    (blk₂ : Fin n → Option (Fin m)) (hblk₂ : ∀ j : Fin m, ∃ i : Fin n, blk₂ i = some j) (z₂ : 𝔽₃ n) :
    ∃ (blk : Fin n → Option (Fin k)) (z : 𝔽₃ n),
      (∀ l : Fin k, ∃ i : Fin n, blk i = some l) ∧
      (∀ (y : 𝔽₃ k) (i : Fin n),
        (match blk i with | some l => z i + y l | none => z i) =
        (match blk₂ i with
          | some j => z₂ i + (match blk₁ j with | some l => z₁ j + y l | none => z₁ j)
          | none => z₂ i)) := by
  let blk : Fin n → Option (Fin k) := fun i => (blk₂ i).bind blk₁
  let z : 𝔽₃ n := fun i => match blk₂ i with | some j => z₂ i + z₁ j | none => z₂ i
  refine ⟨blk, z, ?_, ?_⟩
  · intro l
    obtain ⟨j, hj⟩ := hblk₁ l
    obtain ⟨i, hi⟩ := hblk₂ j
    refine ⟨i, ?_⟩
    simp only [blk, hi, Option.bind_some, hj]
  · intro y i
    dsimp only [blk, z]
    cases h2 : blk₂ i with
    | none => simp
    | some j =>
      simp only [Option.bind_some]
      cases h1 : blk₁ j with
      | none => rfl
      | some l => exact add_assoc (z₂ i) (z₁ j) (y l)

/- Restricted arithmetic progressions lift through any shifted combinatorial subspace. -/
lemma hasRestrictedAP_of_combSubspace {m n : ℕ} (blk : Fin n → Option (Fin m))
    (hblk : ∀ j : Fin m, ∃ i : Fin n, blk i = some j) (z : 𝔽₃ n) (A : Finset (𝔽₃ n))
    (B : Finset (𝔽₃ m))
    (hB : ∀ y ∈ B, (fun i : Fin n => match blk i with | some j => z i + y j | none => z i) ∈ A)
    (hAP : Green17.HasRestrictedAP B) :
    Green17.HasRestrictedAP A := by
  let φ : 𝔽₃ m → 𝔽₃ n := fun y i => match blk i with | some j => z i + y j | none => z i
  obtain ⟨x, d, hd0, hd01, hx, hxd, hx2d⟩ := hAP
  have hxA : φ x ∈ A := hB x hx
  have hxdA : φ (x + d) ∈ A := hB (x + d) hxd
  have hx2dA : φ (x + 2 • d) ∈ A := hB (x + 2 • d) hx2d
  let d' : 𝔽₃ n := fun i => match blk i with | some j => d j | none => 0
  refine ⟨φ x, d', ?_, ?_, hxA, ?_, ?_⟩
  · intro hd'0
    apply hd0
    funext j
    obtain ⟨i, hi⟩ := hblk j
    have h1 := congrFun hd'0 i
    simpa only [d', hi, Pi.zero_apply] using h1
  · intro i
    dsimp only [d']
    cases h : blk i with
    | none => left; rfl
    | some j => exact hd01 j
  · have hstep : φ x + d' = φ (x + d) := by
      funext i
      simp only [Pi.add_apply, φ, d']
      cases blk i with
      | none => exact add_zero (z i)
      | some j => exact (add_assoc (z i) (x j) (d j))
    rw [hstep]
    exact hxdA
  · have hstep2 : φ x + 2 • d' = φ (x + 2 • d) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, φ, d']
      cases blk i with
      | none => simp
      | some j => exact add_assoc (z i) (x j) (2 • d j)
    rw [hstep2]
    exact hx2dA

/- ============================================================================
   Part 2: Exact 3-AP Telescoping Deviation Lemma
   ============================================================================ -/

/- Cardinality of F_3^n is 3^n. -/
lemma card_F3 (n : ℕ) : Fintype.card (𝔽₃ n) = 3 ^ n := by
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]

/- If A subset F_3^n has density alpha > 0, no restricted 3-AP, and 2 / alpha^2 <= 2^n,
then 1_A - alpha has 3-wise correlation at least alpha^3 / 4 with 1-bounded real g, h. -/
lemma three_ap_correlation_of_not_hasRestrictedAP {n : ℕ} (A : Finset (𝔽₃ n))
    (hno : ¬ Green17.HasRestrictedAP A)
    (hpos : 0 < (A.card : ℝ) / (3 : ℝ) ^ n)
    (hn : 2 / ((A.card : ℝ) / (3 : ℝ) ^ n) ^ 2 ≤ (2 : ℝ) ^ n) :
    ∃ g h : 𝔽₃ n → ℝ, (∀ x, |g x| ≤ 1) ∧ (∀ x, |h x| ≤ 1) ∧
      ((A.card : ℝ) / (3 : ℝ) ^ n) ^ 3 / 4 ≤
        |((∑ x : 𝔽₃ n, ∑ b : Fin n → Bool,
            ((if x ∈ A then (1 : ℝ) else 0) - (A.card : ℝ) / (3 : ℝ) ^ n) *
              g (x + fun i => if b i then 1 else 0) *
              h (x + 2 • fun i => if b i then 1 else 0)) / (6 : ℝ) ^ n)| := by
  let α : ℝ := (A.card : ℝ) / (3 : ℝ) ^ n
  let ind : 𝔽₃ n → ℝ := fun x => if x ∈ A then 1 else 0
  let dvec : (Fin n → Bool) → 𝔽₃ n := fun b i => if b i then 1 else 0
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have h6pos : (0 : ℝ) < (6 : ℝ) ^ n := by positivity
  have h6eq : (6 : ℝ) ^ n = (3 : ℝ) ^ n * (2 : ℝ) ^ n := by
    rw [← mul_pow]; norm_num
  have hα_le_one : α ≤ 1 := by
    have hcard : A.card ≤ 3 ^ n := by
      calc A.card ≤ Fintype.card (𝔽₃ n) := Finset.card_le_univ A
      _ = 3 ^ n := card_F3 n
    have hR : (A.card : ℝ) ≤ (3 : ℝ) ^ n := by exact_mod_cast hcard
    exact (div_le_one h3pos).mpr hR
  have hsum_ind : (∑ x : 𝔽₃ n, ind x) = α * (3 : ℝ) ^ n := by
    have h1 : (∑ x : 𝔽₃ n, ind x) = (A.card : ℝ) := by
      simp [ind]
    rw [h1]
    dsimp only [α]
    field_simp
  have htriple_sum :
      (∑ x : 𝔽₃ n, ∑ b : Fin n → Bool, ind x * ind (x + dvec b) * ind (x + 2 • dvec b)) =
        α * (3 : ℝ) ^ n := by
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single (fun _ : Fin n => false)]
    · have h0 : dvec (fun _ : Fin n => false) = 0 := by funext i; simp [dvec]
      simp only [h0, smul_zero, add_zero]
      have hterm : ∀ x : 𝔽₃ n, ind x * ind x * ind x = ind x := by
        intro x; dsimp only [ind]; split_ifs <;> ring
      simp only [hterm]
      exact hsum_ind
    · intro b _ hb
      apply Finset.sum_eq_zero
      intro x _
      by_cases hx : x ∈ A
      · by_cases hxd : x + dvec b ∈ A
        · by_cases hx2d : x + 2 • dvec b ∈ A
          · exfalso
            apply hno
            refine ⟨x, dvec b, ?_, ?_, hx, hxd, hx2d⟩
            · intro hd0
              apply hb
              funext i
              have hi := congrFun hd0 i
              dsimp only [dvec] at hi
              cases hbi : b i with
              | false => rfl
              | true =>
                rw [hbi] at hi
                simp at hi
            · intro i
              dsimp only [dvec]
              cases b i <;> simp
          · simp only [ind, hx2d, ↓reduceIte, mul_zero]
        · simp only [ind, hxd, ↓reduceIte, mul_zero, zero_mul]
      · simp only [ind, hx, ↓reduceIte, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hpair_shift :
      (∑ x : 𝔽₃ n, ∑ b : Fin n → Bool, ind (x + dvec b) * ind (x + 2 • dvec b)) =
        ∑ x : 𝔽₃ n, ∑ b : Fin n → Bool, ind x * ind (x + dvec b) := by
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    refine Fintype.sum_equiv (Equiv.addRight (dvec b)) _ _ ?_
    intro x
    have h2 : x + 2 • dvec b = (x + dvec b) + dvec b := by
      rw [two_nsmul, add_assoc]
    rw [h2]
    rfl
  have hsingle_shift :
      (∑ x : 𝔽₃ n, ∑ b : Fin n → Bool, ind (x + dvec b)) = α * (6 : ℝ) ^ n := by
    rw [Finset.sum_comm]
    have hinner : ∀ b : Fin n → Bool, (∑ x : 𝔽₃ n, ind (x + dvec b)) = α * (3 : ℝ) ^ n := by
      intro b
      have h1 : (∑ x : 𝔽₃ n, ind (x + dvec b)) = ∑ x : 𝔽₃ n, ind x :=
        Fintype.sum_equiv (Equiv.addRight (dvec b)) _ _ (fun _ => rfl)
      rw [h1, hsum_ind]
    simp only [hinner, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [h6eq]
    ring
  let T₁ : ℝ :=
    (∑ x : 𝔽₃ n, ∑ b : Fin n → Bool, (ind x - α) * ind (x + dvec b) * ind (x + 2 • dvec b)) /
      (6 : ℝ) ^ n
  let T₂ : ℝ :=
    (∑ x : 𝔽₃ n, ∑ b : Fin n → Bool, (ind x - α) * ind (x + dvec b) * 1) / (6 : ℝ) ^ n
  have htelesc : T₁ + α * T₂ = α / (2 : ℝ) ^ n - α ^ 3 := by
    have hT1 : T₁ = α / (2 : ℝ) ^ n -
        α * ((∑ x : 𝔽₃ n, ∑ b : Fin n → Bool, ind x * ind (x + dvec b)) / (6 : ℝ) ^ n) := by
      have hexp :
          (∑ x : 𝔽₃ n, ∑ b : Fin n → Bool,
              (ind x - α) * ind (x + dvec b) * ind (x + 2 • dvec b)) =
          (∑ x : 𝔽₃ n, ∑ b : Fin n → Bool, ind x * ind (x + dvec b) * ind (x + 2 • dvec b)) -
          α * (∑ x : 𝔽₃ n, ∑ b : Fin n → Bool, ind (x + dvec b) * ind (x + 2 • dvec b)) := by
        simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, Finset.mul_sum]
      dsimp only [T₁]
      rw [hexp, htriple_sum, hpair_shift, sub_div, h6eq]
      have h3ne : (3 : ℝ) ^ n ≠ 0 := ne_of_gt h3pos
      have h2ne : (2 : ℝ) ^ n ≠ 0 := by positivity
      field_simp
    have hT2 : T₂ =
        (∑ x : 𝔽₃ n, ∑ b : Fin n → Bool, ind x * ind (x + dvec b)) / (6 : ℝ) ^ n - α ^ 2 := by
      have hexp :
          (∑ x : 𝔽₃ n, ∑ b : Fin n → Bool, (ind x - α) * ind (x + dvec b) * 1) =
          (∑ x : 𝔽₃ n, ∑ b : Fin n → Bool, ind x * ind (x + dvec b)) -
          α * (∑ x : 𝔽₃ n, ∑ b : Fin n → Bool, ind (x + dvec b)) := by
        simp only [mul_one, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
      dsimp only [T₂]
      rw [hexp, hsingle_shift, sub_div]
      have h6ne : (6 : ℝ) ^ n ≠ 0 := ne_of_gt h6pos
      field_simp
    rw [hT1, hT2]
    ring
  have hsmall : α / (2 : ℝ) ^ n ≤ α ^ 3 / 2 := by
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    have hα2 : 0 < α ^ 2 := by positivity
    have h1 : 2 ≤ α ^ 2 * (2 : ℝ) ^ n := by
      have := mul_le_mul_of_nonneg_left hn (le_of_lt hα2)
      have hαne : α ≠ 0 := ne_of_gt hpos
      have hcancel : α ^ 2 * (2 / α ^ 2) = 2 := by field_simp
      linarith
    rw [div_le_div_iff₀ h2pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have hdev : α ^ 3 / 2 ≤ |T₁ + α * T₂| := by
    have hα3 : 0 < α ^ 3 := pow_pos hpos 3
    rw [htelesc, abs_of_nonpos (by linarith)]
    linarith
  have htri : |T₁ + α * T₂| ≤ |T₁| + α * |T₂| := by
    calc |T₁ + α * T₂| ≤ |T₁| + |α * T₂| := abs_add_le _ _
    _ = |T₁| + α * |T₂| := by rw [abs_mul, abs_of_pos hpos]
  have hind_bdd : ∀ x, |ind x| ≤ 1 := by
    intro x; dsimp only [ind]; split_ifs <;> norm_num
  by_cases h1 : α ^ 3 / 4 ≤ |T₁|
  · exact ⟨ind, ind, hind_bdd, hind_bdd, h1⟩
  · refine ⟨ind, fun _ => 1, hind_bdd, fun _ => by norm_num, ?_⟩
    have hαT2 : α ^ 3 / 4 ≤ α * |T₂| := by linarith
    have hT2_ge : α ^ 2 / 4 ≤ |T₂| := by
      nlinarith
    have hα3_le : α ^ 3 / 4 ≤ α ^ 2 / 4 := by
      have : α ^ 3 ≤ α ^ 2 := by nlinarith
      linarith
    exact le_trans hα3_le hT2_ge

/- ============================================================================
   Part 3: Bernoulli Subset Moments, Patch Averaging, and Subcube Dichotomy
   ============================================================================ -/

/- Exact 0th, 1st, and centered 2nd moments of the p-biased subset distribution on Fin n. -/
lemma bernoulli_subset_moments (n : ℕ) (p : ℝ) :
    (∑ J : Finset (Fin n), p ^ J.card * (1 - p) ^ (n - J.card)) = 1 ∧
    (∑ J : Finset (Fin n), p ^ J.card * (1 - p) ^ (n - J.card) * (J.card : ℝ)) = n * p ∧
    (∑ J : Finset (Fin n),
        p ^ J.card * (1 - p) ^ (n - J.card) * ((J.card : ℝ) - n * p) ^ 2) =
      n * p * (1 - p) := by
  induction n with
  | zero =>
    have hdef : (default : Finset (Fin 0)) = ∅ := Subsingleton.elim _ _
    refine ⟨?_, ?_, ?_⟩ <;> simp [hdef]
  | succ n ih =>
    rcases ih with ⟨ih0, ih1, ih2⟩
    let emb : Fin n ↪ Fin (n + 1) := Fin.castSuccEmb
    let e : Finset (Fin n) × Bool ≃ Finset (Fin (n + 1)) :=
      { toFun := fun Jb =>
          if Jb.2 then insert (Fin.last n) (Jb.1.map emb) else Jb.1.map emb
        invFun := fun J =>
          (Finset.univ.filter fun i : Fin n => i.castSucc ∈ J, decide (Fin.last n ∈ J))
        left_inv := by
          rintro ⟨J₀, b⟩
          apply Prod.ext
          · ext i
            cases b <;> simp [emb, Fin.castSucc_ne_last]
          · cases b <;> simp [emb, Fin.ne_of_lt (Fin.castSucc_lt_last _)]
        right_inv := by
          intro J
          by_cases hlast : Fin.last n ∈ J
          · simp only [hlast, decide_true, ↓reduceIte]
            ext i
            refine Fin.lastCases ?_ ?_ i
            · simp [hlast]
            · intro j
              simp [emb, Fin.castSucc_ne_last]
          · simp only [hlast, decide_false, Bool.false_eq_true, ↓reduceIte]
            ext i
            refine Fin.lastCases ?_ ?_ i
            · simp [hlast, emb, Fin.ne_of_lt (Fin.castSucc_lt_last _)]
            · intro j
              simp [emb] }
    have hcard_f : ∀ J₀ : Finset (Fin n), (e (J₀, false)).card = J₀.card := by
      intro J₀; simp [e]
    have hcard_t : ∀ J₀ : Finset (Fin n), (e (J₀, true)).card = J₀.card + 1 := by
      intro J₀
      have hnot : Fin.last n ∉ J₀.map emb := by
        simp [emb, Fin.ne_of_lt (Fin.castSucc_lt_last _)]
      simp [e, Finset.card_insert_of_notMem hnot]
    have hsub_f : ∀ J₀ : Finset (Fin n), n + 1 - (e (J₀, false)).card = (n - J₀.card) + 1 := by
      intro J₀
      rw [hcard_f]
      have hle : J₀.card ≤ n := by simpa using Finset.card_le_univ J₀
      omega
    have hsub_t : ∀ J₀ : Finset (Fin n), n + 1 - (e (J₀, true)).card = n - J₀.card := by
      intro J₀
      rw [hcard_t]
      omega
    have hsplit : ∀ F : Finset (Fin (n + 1)) → ℝ,
        (∑ J : Finset (Fin (n + 1)), F J) =
        (∑ J₀ : Finset (Fin n), F (e (J₀, false))) +
        (∑ J₀ : Finset (Fin n), F (e (J₀, true))) := by
      intro F
      rw [← Fintype.sum_equiv e _ _ (fun _ => rfl), Fintype.sum_prod_type, Finset.sum_comm]
      rw [Fintype.sum_bool, add_comm]
    have hwt_f : ∀ J₀ : Finset (Fin n),
        p ^ (e (J₀, false)).card * (1 - p) ^ (n + 1 - (e (J₀, false)).card) =
          (1 - p) * (p ^ J₀.card * (1 - p) ^ (n - J₀.card)) := by
      intro J₀
      rw [hsub_f, hcard_f, pow_succ]
      ring
    have hwt_t : ∀ J₀ : Finset (Fin n),
        p ^ (e (J₀, true)).card * (1 - p) ^ (n + 1 - (e (J₀, true)).card) =
          p * (p ^ J₀.card * (1 - p) ^ (n - J₀.card)) := by
      intro J₀
      rw [hsub_t, hcard_t, pow_succ]
      ring
    refine ⟨?_, ?_, ?_⟩
    · rw [hsplit]
      simp only [hwt_f, hwt_t, ← Finset.mul_sum, ih0]
      ring
    · rw [hsplit]
      simp only [hwt_f, hwt_t]
      simp only [hcard_f, hcard_t, Nat.cast_add, Nat.cast_one]
      have hA : (∑ J₀ : Finset (Fin n),
          (1 - p) * (p ^ J₀.card * (1 - p) ^ (n - J₀.card)) * (J₀.card : ℝ)) =
          (1 - p) * (n * p) := by
        rw [← ih1, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro J₀ _; ring
      have hB : (∑ J₀ : Finset (Fin n),
          p * (p ^ J₀.card * (1 - p) ^ (n - J₀.card)) * ((J₀.card : ℝ) + 1)) =
          p * (n * p + 1) := by
        have hstep : (∑ J₀ : Finset (Fin n),
            p * (p ^ J₀.card * (1 - p) ^ (n - J₀.card)) * ((J₀.card : ℝ) + 1)) =
          p * ((∑ J₀ : Finset (Fin n), p ^ J₀.card * (1 - p) ^ (n - J₀.card) * (J₀.card : ℝ)) +
            (∑ J₀ : Finset (Fin n), p ^ J₀.card * (1 - p) ^ (n - J₀.card))) := by
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro J₀ _
          ring
        rw [hstep, ih1, ih0]
      rw [hA, hB]
      ring
    · rw [hsplit]
      simp only [hwt_f, hwt_t]
      simp only [hcard_f, hcard_t, Nat.cast_add, Nat.cast_one]
      have hcomb :
          (∑ J₀ : Finset (Fin n),
              (1 - p) * (p ^ J₀.card * (1 - p) ^ (n - J₀.card)) *
                ((J₀.card : ℝ) - ((n : ℝ) + 1) * p) ^ 2) +
          (∑ J₀ : Finset (Fin n),
              p * (p ^ J₀.card * (1 - p) ^ (n - J₀.card)) *
                (((J₀.card : ℝ) + 1) - ((n : ℝ) + 1) * p) ^ 2) =
          (∑ J₀ : Finset (Fin n),
              p ^ J₀.card * (1 - p) ^ (n - J₀.card) * ((J₀.card : ℝ) - n * p) ^ 2) +
          p * (1 - p) * (∑ J₀ : Finset (Fin n), p ^ J₀.card * (1 - p) ^ (n - J₀.card)) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro J₀ _
        ring
      rw [hcomb, ih2, ih0]
      ring

/- Chebyshev lower-tail bound for the p-biased subset size: Pr(|J| < p*n/2) <= 4 / (p*n). -/
lemma bernoulli_subset_tail_bound {n : ℕ} {p : ℝ} (hn : 0 < n) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    (∑ J ∈ Finset.univ.filter (fun J : Finset (Fin n) => (J.card : ℝ) < p * n / 2),
      p ^ J.card * (1 - p) ^ (n - J.card)) ≤ 4 / (p * n) := by
  have hvar := (bernoulli_subset_moments n p).2.2
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hpn : 0 < p * (n : ℝ) := mul_pos hp0 hnR
  have hquad :
      (p * n / 2) ^ 2 *
        (∑ J ∈ Finset.univ.filter (fun J : Finset (Fin n) => (J.card : ℝ) < p * n / 2),
          p ^ J.card * (1 - p) ^ (n - J.card)) ≤
      (n : ℝ) * p * (1 - p) := by
    rw [Finset.mul_sum, ← hvar]
    calc
      (∑ J ∈ Finset.univ.filter (fun J : Finset (Fin n) => (J.card : ℝ) < p * n / 2),
          (p * n / 2) ^ 2 * (p ^ J.card * (1 - p) ^ (n - J.card)))
        ≤ ∑ J ∈ Finset.univ.filter (fun J : Finset (Fin n) => (J.card : ℝ) < p * n / 2),
            p ^ J.card * (1 - p) ^ (n - J.card) * ((J.card : ℝ) - n * p) ^ 2 := by
          apply Finset.sum_le_sum
          intro J hJ
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hJ
          have hw_nn : 0 ≤ p ^ J.card * (1 - p) ^ (n - J.card) := by
            apply mul_nonneg (pow_nonneg (le_of_lt hp0) _) (pow_nonneg (by linarith) _)
          have hsq : (p * n / 2) ^ 2 ≤ ((J.card : ℝ) - n * p) ^ 2 := by nlinarith
          nlinarith
      _ ≤ ∑ J : Finset (Fin n),
            p ^ J.card * (1 - p) ^ (n - J.card) * ((J.card : ℝ) - n * p) ^ 2 := by
          apply Finset.sum_le_univ_sum_of_nonneg
          intro J
          apply mul_nonneg
          · exact mul_nonneg (pow_nonneg (le_of_lt hp0) _) (pow_nonneg (by linarith) _)
          · exact sq_nonneg _
  have h1mp : (n : ℝ) * p * (1 - p) ≤ (n : ℝ) * p := by nlinarith
  have h2 : (p * n / 2) ^ 2 *
      (∑ J ∈ Finset.univ.filter (fun J : Finset (Fin n) => (J.card : ℝ) < p * n / 2),
        p ^ J.card * (1 - p) ^ (n - J.card)) ≤ p * n := by linarith
  have hsq_pos : 0 < (p * n / 2) ^ 2 := by positivity
  rw [le_div_iff₀ hpn]
  nlinarith

/- Exact double-sum invariance for coordinate-subcube patching via the swap involution. -/
lemma sum_patch_eq {n : ℕ} (J : Finset (Fin n)) (G : 𝔽₃ n → ℝ) :
    (∑ z : 𝔽₃ n, ∑ w : 𝔽₃ n, G (fun i => if i ∈ J then w i else z i)) =
      (3 : ℝ) ^ n * ∑ x : 𝔽₃ n, G x := by
  let sw : 𝔽₃ n × 𝔽₃ n ≃ 𝔽₃ n × 𝔽₃ n :=
    { toFun := fun zw =>
        (fun i => if i ∈ J then zw.2 i else zw.1 i,
         fun i => if i ∈ J then zw.1 i else zw.2 i)
      invFun := fun zw =>
        (fun i => if i ∈ J then zw.2 i else zw.1 i,
         fun i => if i ∈ J then zw.1 i else zw.2 i)
      left_inv := by
        rintro ⟨z, w⟩
        apply Prod.ext <;> funext i <;> by_cases hi : i ∈ J <;> simp [hi]
      right_inv := by
        rintro ⟨z, w⟩
        apply Prod.ext <;> funext i <;> by_cases hi : i ∈ J <;> simp [hi] }
  have h0 : (∑ z : 𝔽₃ n, ∑ w : 𝔽₃ n, G (fun i => if i ∈ J then w i else z i)) =
      ∑ zw : 𝔽₃ n × 𝔽₃ n, G (fun i => if i ∈ J then zw.2 i else zw.1 i) :=
    (Fintype.sum_prod_type (fun zw : 𝔽₃ n × 𝔽₃ n =>
      G (fun i => if i ∈ J then zw.2 i else zw.1 i))).symm
  have h1 : (∑ zw : 𝔽₃ n × 𝔽₃ n, G (fun i => if i ∈ J then zw.2 i else zw.1 i)) =
      ∑ xy : 𝔽₃ n × 𝔽₃ n, G xy.1 :=
    Fintype.sum_equiv sw _ _ (fun _ => rfl)
  rw [h0, h1, Fintype.sum_prod_type, Finset.sum_comm]
  simp [Finset.sum_const]

/- Transporting a coordinate subcube (J, z) along an order equivalence e : Fin J.card ≃ J
gives a shifted combinatorial subspace (with zero shift on J) and preserves pullback density. -/
lemma subcube_to_combSubspace {n : ℕ} (J : Finset (Fin n)) (z : 𝔽₃ n) (A : Finset (𝔽₃ n)) :
    ∃ (blk : Fin n → Option (Fin J.card)) (z₀ : 𝔽₃ n) (e : Fin J.card ≃ J),
      (∀ j : Fin J.card, ∃ i : Fin n, blk i = some j) ∧
      (∀ (y : 𝔽₃ J.card) (i : Fin n),
        (match blk i with | some j => z₀ i + y j | none => z₀ i) =
        (if hi : i ∈ J then y (e.symm ⟨i, hi⟩) else z i)) ∧
      ((∑ w : 𝔽₃ n, if (fun i => if i ∈ J then w i else z i) ∈ A then (1 : ℝ) else 0) /
          (3 : ℝ) ^ n =
        ((Finset.univ.filter fun y : 𝔽₃ J.card =>
            (fun i => match blk i with | some j => z₀ i + y j | none => z₀ i) ∈ A).card : ℝ) /
          (3 : ℝ) ^ J.card) := by
  classical
  let e : Fin J.card ≃ J := (Fintype.equivFinOfCardEq (Fintype.card_coe J)).symm
  let blk : Fin n → Option (Fin J.card) := fun i =>
    if hi : i ∈ J then some (e.symm ⟨i, hi⟩) else none
  let z₀ : 𝔽₃ n := fun i => if i ∈ J then 0 else z i
  refine ⟨blk, z₀, e, ?_, ?_, ?_⟩
  · intro j
    refine ⟨(e j).1, ?_⟩
    have hj : (e j).1 ∈ J := (e j).2
    simp only [blk, hj, dite_true, Subtype.coe_eta, Equiv.symm_apply_apply]
  · intro y i
    by_cases hi : i ∈ J
    · simp only [blk, z₀, hi, dite_true, ↓reduceIte, zero_add]
    · simp only [blk, z₀, hi, dite_false, ↓reduceIte]
  · let A' : Finset (𝔽₃ J.card) := Finset.univ.filter fun y : 𝔽₃ J.card =>
      (fun i => match blk i with | some j => z₀ i + y j | none => z₀ i) ∈ A
    let proj : 𝔽₃ n → 𝔽₃ J.card := fun w j => w (e j).1
    have hmatch : ∀ w : 𝔽₃ n,
        (fun i => if i ∈ J then w i else z i) =
        (fun i => match blk i with | some j => z₀ i + proj w j | none => z₀ i) := by
      intro w
      funext i
      by_cases hi : i ∈ J
      · simp only [blk, z₀, proj, hi, dite_true, ↓reduceIte, zero_add, Equiv.apply_symm_apply]
      · simp only [blk, z₀, hi, dite_false, ↓reduceIte]
    have hsum_eq :
        (∑ w : 𝔽₃ n, if (fun i => if i ∈ J then w i else z i) ∈ A then (1 : ℝ) else 0) =
        (3 : ℝ) ^ (n - J.card) * (A'.card : ℝ) := by
      have hcard_eq :
          (Finset.univ.filter fun w : 𝔽₃ n => (fun i => if i ∈ J then w i else z i) ∈ A).card =
          3 ^ (n - J.card) * A'.card := by
        let Jc : Finset (Fin n) := Jᶜ
        have hJc_card : Jc.card = n - J.card := by
          rw [Finset.card_compl, Fintype.card_fin]
        let ec : Fin (n - J.card) ≃ Jc :=
          (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hJc_card])).symm
        let bij : 𝔽₃ n ≃ 𝔽₃ J.card × 𝔽₃ (n - J.card) :=
          { toFun := fun w => (fun j => w (e j).1, fun j => w (ec j).1)
            invFun := fun yv i =>
              if hi : i ∈ J then yv.1 (e.symm ⟨i, hi⟩)
              else yv.2 (ec.symm ⟨i, Finset.mem_compl.mpr hi⟩)
            left_inv := by
              intro w
              funext i
              by_cases hi : i ∈ J
              · simp [hi]
              · simp [hi]
            right_inv := by
              rintro ⟨y, v⟩
              apply Prod.ext
              · funext j
                have hj : (e j).1 ∈ J := (e j).2
                simp [hj]
              · funext j
                have hj : (ec j).1 ∉ J := Finset.mem_compl.mp (ec j).2
                simp [hj] }
        have hfbij :
            (Finset.univ.filter fun w : 𝔽₃ n => (fun i => if i ∈ J then w i else z i) ∈ A).card =
            (A' ×ˢ (Finset.univ : Finset (𝔽₃ (n - J.card)))).card := by
          refine Finset.card_bij (fun w _ => bij w) ?_ ?_ ?_
          · intro w hw
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
            simp only [Finset.mem_product, Finset.mem_univ, and_true, A',
              Finset.mem_filter, true_and]
            rw [hmatch w] at hw
            exact hw
          · intro w₁ _ w₂ _ h
            exact bij.injective h
          · intro yv hyv
            simp only [Finset.mem_product, Finset.mem_univ, and_true, A',
              Finset.mem_filter, true_and] at hyv
            refine ⟨bij.symm yv, ?_, bij.apply_symm_apply yv⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            rw [hmatch (bij.symm yv)]
            have hproj : proj (bij.symm yv) = yv.1 := by
              funext j
              have h1 := congrArg Prod.fst (bij.apply_symm_apply yv)
              exact congrFun h1 j
            rw [hproj]
            exact hyv
        rw [hfbij, Finset.card_product, Finset.card_univ, card_F3, mul_comm]
      have hsum_card :
          (∑ w : 𝔽₃ n, if (fun i => if i ∈ J then w i else z i) ∈ A then (1 : ℝ) else 0) =
          ((Finset.univ.filter fun w : 𝔽₃ n =>
              (fun i => if i ∈ J then w i else z i) ∈ A).card : ℝ) := by
        simp
      rw [hsum_card, hcard_eq]
      push_cast
      rfl
    rw [hsum_eq]
    have hle : J.card ≤ n := by simpa using Finset.card_le_univ J
    have hpow : (3 : ℝ) ^ n = (3 : ℝ) ^ (n - J.card) * (3 : ℝ) ^ J.card := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    rw [hpow]
    have h3a : (3 : ℝ) ^ (n - J.card) ≠ 0 := by positivity
    exact mul_div_mul_left _ _ h3a

/- Transporting a product correlation over J on F_3^n to F_3^(J.card) along e : Fin J.card ≃ J. -/
lemma sum_patch_prod_eq {n : ℕ} (J : Finset (Fin n)) (z : 𝔽₃ n) (e : Fin J.card ≃ J)
    (f : 𝔽₃ n → ℝ) (P : Fin n → ZMod 3 → ℂ) :
    (∑ w : 𝔽₃ n, (f (fun i => if i ∈ J then w i else z i) : ℂ) * ∏ i ∈ J, P i (w i)) /
      (3 : ℂ) ^ n =
    (∑ y : 𝔽₃ J.card,
      (f (fun i => if hi : i ∈ J then y (e.symm ⟨i, hi⟩) else z i) : ℂ) *
        ∏ j : Fin J.card, P (e j).1 (y j)) / (3 : ℂ) ^ J.card := by
  classical
  let Jc : Finset (Fin n) := Jᶜ
  have hJc_card : Jc.card = n - J.card := by
    rw [Finset.card_compl, Fintype.card_fin]
  let ec : Fin (n - J.card) ≃ Jc :=
    (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hJc_card])).symm
  let bij : 𝔽₃ n ≃ 𝔽₃ J.card × 𝔽₃ (n - J.card) :=
    { toFun := fun w => (fun j => w (e j).1, fun j => w (ec j).1)
      invFun := fun yv i =>
        if hi : i ∈ J then yv.1 (e.symm ⟨i, hi⟩)
        else yv.2 (ec.symm ⟨i, Finset.mem_compl.mpr hi⟩)
      left_inv := by
        intro w; funext i; by_cases hi : i ∈ J <;> simp [hi]
      right_inv := by
        rintro ⟨y, v⟩
        apply Prod.ext
        · funext j; have hj : (e j).1 ∈ J := (e j).2; simp [hj]
        · funext j; have hj : (ec j).1 ∉ J := Finset.mem_compl.mp (ec j).2; simp [hj] }
  have hsum :
      (∑ w : 𝔽₃ n, (f (fun i => if i ∈ J then w i else z i) : ℂ) * ∏ i ∈ J, P i (w i)) =
      (3 : ℂ) ^ (n - J.card) *
        (∑ y : 𝔽₃ J.card,
          (f (fun i => if hi : i ∈ J then y (e.symm ⟨i, hi⟩) else z i) : ℂ) *
            ∏ j : Fin J.card, P (e j).1 (y j)) := by
    rw [Fintype.sum_equiv bij _ (fun yv =>
      (f (fun i => if hi : i ∈ J then yv.1 (e.symm ⟨i, hi⟩) else z i) : ℂ) *
        ∏ j : Fin J.card, P (e j).1 (yv.1 j))]
    · rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp only [Finset.sum_const, Finset.card_univ, card_F3, nsmul_eq_mul,
        Nat.cast_pow, Nat.cast_ofNat]
    · intro w
      congr 1
      · congr 1
        congr 1
        funext i
        by_cases hi : i ∈ J
        · simp [bij, hi]
        · simp [hi]
      · rw [← Finset.prod_coe_sort J]
        refine Fintype.prod_equiv e.symm _ _ ?_
        intro x
        simp [bij]
  rw [hsum]
  have hle : J.card ≤ n := by simpa using Finset.card_le_univ J
  have hpow : (3 : ℂ) ^ n = (3 : ℂ) ^ (n - J.card) * (3 : ℂ) ^ J.card := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [hpow]
  have h3a : (3 : ℂ) ^ (n - J.card) ≠ 0 := pow_ne_zero _ (by norm_num)
  exact mul_div_mul_left _ _ h3a

/- ============================================================================
   Part 4: Product-Function Correlation to Shifted Combinatorial Subspace Increment
   ============================================================================ -/

/- Elementary complex norm bound: ||z|| <= |z.re| + |z.im|. -/
lemma complex_norm_le_abs_re_add_abs_im (z : ℂ) : ‖z‖ ≤ |z.re| + |z.im| := by
  have hnn : 0 ≤ |z.re| + |z.im| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hsq : ‖z‖ ^ 2 ≤ (|z.re| + |z.im|) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have hre : z.re * z.re = |z.re| ^ 2 := by rw [sq_abs, sq]
    have him : z.im * z.im = |z.im| ^ 2 := by rw [sq_abs, sq]
    have hprod : 0 ≤ |z.re| * |z.im| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
    nlinarith
  nlinarith [norm_nonneg z]

/- Telescoping product error bound in C: if ||u_i|| <= 1, ||v_i|| <= 1, and ||u_i - v_i|| <= eta
on a finite set S, then ||prod u - prod v|| <= S.card * eta. -/
lemma norm_prod_sub_prod_le {ι : Type*} (S : Finset ι) (u v : ι → ℂ) {η : ℝ}
    (hu : ∀ i ∈ S, ‖u i‖ ≤ 1) (hv : ∀ i ∈ S, ‖v i‖ ≤ 1)
    (hdiff : ∀ i ∈ S, ‖u i - v i‖ ≤ η) :
    ‖(∏ i ∈ S, u i) - (∏ i ∈ S, v i)‖ ≤ (S.card : ℝ) * η := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha,
      Nat.cast_add, Nat.cast_one]
    have hsplit : u a * ∏ i ∈ s, u i - v a * ∏ i ∈ s, v i =
        (u a - v a) * (∏ i ∈ s, u i) + v a * ((∏ i ∈ s, u i) - (∏ i ∈ s, v i)) := by ring
    rw [hsplit]
    have hprod_u : ‖∏ i ∈ s, u i‖ ≤ 1 := by
      rw [norm_prod]
      exact Finset.prod_le_one (fun i _ => norm_nonneg _)
        (fun i hi => hu i (Finset.mem_insert_of_mem hi))
    have hva : ‖v a‖ ≤ 1 := hv a (Finset.mem_insert_self a s)
    have hda : ‖u a - v a‖ ≤ η := hdiff a (Finset.mem_insert_self a s)
    have hih := ih (fun i hi => hu i (Finset.mem_insert_of_mem hi))
      (fun i hi => hv i (Finset.mem_insert_of_mem hi))
      (fun i hi => hdiff i (Finset.mem_insert_of_mem hi))
    calc
      ‖(u a - v a) * (∏ i ∈ s, u i) + v a * ((∏ i ∈ s, u i) - (∏ i ∈ s, v i))‖
        ≤ ‖(u a - v a) * (∏ i ∈ s, u i)‖ + ‖v a * ((∏ i ∈ s, u i) - (∏ i ∈ s, v i))‖ :=
          norm_add_le _ _
      _ = ‖u a - v a‖ * ‖∏ i ∈ s, u i‖ + ‖v a‖ * ‖(∏ i ∈ s, u i) - (∏ i ∈ s, v i)‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ η * 1 + 1 * ((s.card : ℝ) * η) := by
          apply add_le_add
          · exact mul_le_mul hda hprod_u (norm_nonneg _) (le_trans (norm_nonneg _) hda)
          · exact mul_le_mul hva hih (norm_nonneg _) (by norm_num)
      _ = ((s.card : ℝ) + 1) * η := by ring

/- Interval discretization of [-1, 1] into B bins of width <= 2/B. -/
lemma exists_unit_interval_bucketing (B : ℕ) (hB : 1 ≤ B) :
    ∃ slot : ℝ → Fin B, ∀ u v : ℝ,
      |u| ≤ 1 → |v| ≤ 1 → slot u = slot v → |u - v| ≤ 2 / (B : ℝ) := by
  let slot : ℝ → Fin B := fun u =>
    ⟨min (B - 1) (Nat.floor (((u + 1) / 2) * (B : ℝ))), by omega⟩
  refine ⟨slot, ?_⟩
  intro u v hu hv heq
  have hval : min (B - 1) (Nat.floor (((u + 1) / 2) * (B : ℝ))) =
      min (B - 1) (Nat.floor (((v + 1) / 2) * (B : ℝ))) := congrArg Fin.val heq
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast (by omega : 0 < B)
  have hu0 : 0 ≤ ((u + 1) / 2) * (B : ℝ) := by
    have h1 : -1 ≤ u := neg_le_of_abs_le hu
    nlinarith
  have hv0 : 0 ≤ ((v + 1) / 2) * (B : ℝ) := by
    have h1 : -1 ≤ v := neg_le_of_abs_le hv
    nlinarith
  have huB : ((u + 1) / 2) * (B : ℝ) ≤ (B : ℝ) := by
    have h1 : u ≤ 1 := le_of_abs_le hu
    nlinarith
  have hvB : ((v + 1) / 2) * (B : ℝ) ≤ (B : ℝ) := by
    have h1 : v ≤ 1 := le_of_abs_le hv
    nlinarith
  set fu := Nat.floor (((u + 1) / 2) * (B : ℝ))
  set fv := Nat.floor (((v + 1) / 2) * (B : ℝ))
  have hdiff1 : |((u + 1) / 2) * (B : ℝ) - ((v + 1) / 2) * (B : ℝ)| ≤ 1 := by
    by_cases hlt : fu < B - 1
    · have hminu : min (B - 1) fu = fu := Nat.min_eq_right (by omega)
      rw [hminu] at hval
      have hltv : fv < B - 1 := by omega
      have hfeq : fu = fv := by omega
      have hu_lo : (fu : ℝ) ≤ ((u + 1) / 2) * (B : ℝ) := Nat.floor_le hu0
      have hu_hi : ((u + 1) / 2) * (B : ℝ) < (fu : ℝ) + 1 := Nat.lt_floor_add_one _
      have hv_lo : (fu : ℝ) ≤ ((v + 1) / 2) * (B : ℝ) := by rw [hfeq]; exact Nat.floor_le hv0
      have hv_hi : ((v + 1) / 2) * (B : ℝ) < (fu : ℝ) + 1 := by
        rw [hfeq]; exact Nat.lt_floor_add_one _
      rw [abs_le]
      constructor <;> linarith
    · have hminu : min (B - 1) fu = B - 1 := Nat.min_eq_left (by omega)
      rw [hminu] at hval
      have hgev : B - 1 ≤ fv := by omega
      have hu_lo : ((B - 1 : ℕ) : ℝ) ≤ ((u + 1) / 2) * (B : ℝ) :=
        le_trans (Nat.cast_le.mpr (by omega : B - 1 ≤ fu)) (Nat.floor_le hu0)
      have hv_lo : ((B - 1 : ℕ) : ℝ) ≤ ((v + 1) / 2) * (B : ℝ) :=
        le_trans (Nat.cast_le.mpr hgev) (Nat.floor_le hv0)
      have hBm1 : ((B - 1 : ℕ) : ℝ) = (B : ℝ) - 1 := by
        rw [Nat.cast_sub hB, Nat.cast_one]
      rw [hBm1] at hu_lo hv_lo
      rw [abs_le]
      constructor <;> linarith
  have hscaled : |u - v| * ((B : ℝ) / 2) ≤ 1 := by
    have heq_sub : ((u + 1) / 2) * (B : ℝ) - ((v + 1) / 2) * (B : ℝ) = (u - v) * ((B : ℝ) / 2) := by
      ring
    rw [heq_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (B : ℝ) / 2)] at hdiff1
    exact hdiff1
  rw [le_div_iff₀ hBpos]
  linarith

/- Pigeonhole extraction of r pairwise-disjoint same-fiber triples from any finset of size
>= 2 * |beta| + 3 * r. -/
lemma exists_disjoint_same_fiber_triples {α β : Type*} [Fintype β] [DecidableEq α] [DecidableEq β]
    (key : α → β) :
    ∀ (r : ℕ) (s : Finset α), 2 * Fintype.card β + 3 * r ≤ s.card →
      ∃ T : Fin r → Fin 3 → α,
        (∀ j a, T j a ∈ s) ∧
        Function.Injective (fun ja : Fin r × Fin 3 => T ja.1 ja.2) ∧
        (∀ j a, key (T j a) = key (T j 0)) := by
  intro r
  induction r with
  | zero =>
    intro s _
    exact ⟨fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun ⟨j, _⟩ => Fin.elim0 j,
      fun j => Fin.elim0 j⟩
  | succ r ih =>
    intro s hs
    have hgt : Fintype.card β * 2 < s.card := by omega
    have hex_b : ∃ b : β, 3 ≤ (s.filter fun x => key x = b).card := by
      by_contra hall
      push Not at hall
      have hsum : s.card ≤ Fintype.card β * 2 := by
        rw [Finset.card_eq_sum_card_fiberwise (f := key) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
        calc
          (∑ b : β, (s.filter fun x => key x = b).card) ≤ ∑ _b : β, 2 :=
            Finset.sum_le_sum (fun b _ => Nat.le_of_lt_succ (hall b))
          _ = Fintype.card β * 2 := by simp
      omega
    obtain ⟨b, hb3⟩ := hex_b
    let fib := s.filter fun x => key x = b
    have hfib3 : 3 ≤ fib.card := hb3
    have h1 : fib.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨x₀, hx₀⟩ := h1
    have h2 : (fib.erase x₀).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hx₀]
      omega
    obtain ⟨x₁, hx₁⟩ := h2
    have h3 : ((fib.erase x₀).erase x₁).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hx₁, Finset.card_erase_of_mem hx₀]
      omega
    obtain ⟨x₂, hx₂⟩ := h3
    have hx₁_ne_x₀ : x₁ ≠ x₀ := (Finset.mem_erase.mp hx₁).1
    have hx₂_ne_x₁ : x₂ ≠ x₁ := (Finset.mem_erase.mp hx₂).1
    have hx₂_ne_x₀ : x₂ ≠ x₀ := (Finset.mem_erase.mp (Finset.mem_erase.mp hx₂).2).1
    have hx₀_fib : x₀ ∈ fib := hx₀
    have hx₁_fib : x₁ ∈ fib := (Finset.mem_erase.mp hx₁).2
    have hx₂_fib : x₂ ∈ fib := (Finset.mem_erase.mp (Finset.mem_erase.mp hx₂).2).2
    have hx₀_s : x₀ ∈ s := (Finset.mem_filter.mp hx₀_fib).1
    have hx₁_s : x₁ ∈ s := (Finset.mem_filter.mp hx₁_fib).1
    have hx₂_s : x₂ ∈ s := (Finset.mem_filter.mp hx₂_fib).1
    have hk₀ : key x₀ = b := (Finset.mem_filter.mp hx₀_fib).2
    have hk₁ : key x₁ = b := (Finset.mem_filter.mp hx₁_fib).2
    have hk₂ : key x₂ = b := (Finset.mem_filter.mp hx₂_fib).2
    let s' := ((s.erase x₀).erase x₁).erase x₂
    have hs'_card : 2 * Fintype.card β + 3 * r ≤ s'.card := by
      have hx₁_in : x₁ ∈ s.erase x₀ := Finset.mem_erase.mpr ⟨hx₁_ne_x₀, hx₁_s⟩
      have hx₂_in : x₂ ∈ (s.erase x₀).erase x₁ :=
        Finset.mem_erase.mpr ⟨hx₂_ne_x₁, Finset.mem_erase.mpr ⟨hx₂_ne_x₀, hx₂_s⟩⟩
      have hc : s'.card = s.card - 3 := by
        dsimp only [s']
        rw [Finset.card_erase_of_mem hx₂_in, Finset.card_erase_of_mem hx₁_in,
          Finset.card_erase_of_mem hx₀_s]
        omega
      omega
    obtain ⟨T₀, hT₀_mem, hT₀_inj, hT₀_key⟩ := ih s' hs'_card
    let trip : Fin 3 → α := fun a => match a.val with | 0 => x₀ | 1 => x₁ | _ => x₂
    let T : Fin (r + 1) → Fin 3 → α := Fin.cons trip T₀
    have hnot_mem : ∀ j a, T₀ j a ≠ x₀ ∧ T₀ j a ≠ x₁ ∧ T₀ j a ≠ x₂ := by
      intro j a
      have hm := hT₀_mem j a
      dsimp only [s'] at hm
      have h2' := Finset.mem_erase.mp hm
      have h1' := Finset.mem_erase.mp h2'.2
      have h0' := Finset.mem_erase.mp h1'.2
      exact ⟨h0'.1, h1'.1, h2'.1⟩
    refine ⟨T, ?_, ?_, ?_⟩
    · intro j a
      refine Fin.cases ?_ ?_ j
      · simp only [T, Fin.cons_zero, trip]
        fin_cases a
        · exact hx₀_s
        · exact hx₁_s
        · exact hx₂_s
      · intro j'
        simp only [T, Fin.cons_succ]
        have hm := hT₀_mem j' a
        exact Finset.erase_subset _ _ (Finset.erase_subset _ _ (Finset.erase_subset _ _ hm))
    · rintro ⟨j₁, a₁⟩ ⟨j₂, a₂⟩ heq
      refine Fin.cases (motive := fun j₁ => ∀ j₂ a₁ a₂, T j₁ a₁ = T j₂ a₂ → (j₁, a₁) = (j₂, a₂))
        ?_ ?_ j₁ j₂ a₁ a₂ heq
      · intro j₂ a₁ a₂ h
        refine Fin.cases (motive := fun j₂ => T 0 a₁ = T j₂ a₂ → ((0 : Fin (r + 1)), a₁) = (j₂, a₂))
          ?_ ?_ j₂ h
        · intro h'
          simp only [T, Fin.cons_zero, trip] at h'
          have ha : a₁ = a₂ := by
            fin_cases a₁ <;> fin_cases a₂ <;> simp_all
          rw [ha]
        · intro j₂' h'
          simp only [T, Fin.cons_zero, Fin.cons_succ, trip] at h'
          exfalso
          have hnm := hnot_mem j₂' a₂
          fin_cases a₁
          · exact hnm.1 h'.symm
          · exact hnm.2.1 h'.symm
          · exact hnm.2.2 h'.symm
      · intro j₁' j₂ a₁ a₂ h
        refine Fin.cases (motive := fun j₂ => T j₁'.succ a₁ = T j₂ a₂ → (j₁'.succ, a₁) = (j₂, a₂))
          ?_ ?_ j₂ h
        · intro h'
          simp only [T, Fin.cons_zero, Fin.cons_succ, trip] at h'
          exfalso
          have hnm := hnot_mem j₁' a₁
          fin_cases a₂
          · exact hnm.1 h'
          · exact hnm.2.1 h'
          · exact hnm.2.2 h'
        · intro j₂' h'
          simp only [T, Fin.cons_succ] at h'
          have hpair := hT₀_inj (a₁ := (j₁', a₁)) (a₂ := (j₂', a₂)) h'
          rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
          rfl
    · intro j a
      refine Fin.cases ?_ ?_ j
      · simp only [T, Fin.cons_zero, trip]
        fin_cases a <;> simp [hk₀, hk₁, hk₂]
      · intro j'
        simp only [T, Fin.cons_succ]
        exact hT₀_key j' a

/- Balanced triple invariance in ZMod 3: if (a, b, c) are pairwise distinct in ZMod 3, then
for every y in ZMod 3, q(a + y) * q(b + y) * q(c + y) = q(0) * q(1) * q(2). -/
lemma prod_balanced_triple_zmod3 (q : ZMod 3 → ℂ) {a b c : ZMod 3}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (y : ZMod 3) :
    q (a + y) * q (b + y) * q (c + y) = q 0 * q 1 * q 2 := by
  have h3 : ∀ u : ZMod 3, u = 0 ∨ u = 1 ∨ u = 2 := by
    intro u
    fin_cases u
    · left; rfl
    · right; left; rfl
    · right; right; rfl
  have h11 : (1 : ZMod 3) + 1 = 2 := by decide
  have h12 : (1 : ZMod 3) + 2 = 0 := by decide
  have h21 : (2 : ZMod 3) + 1 = 0 := by decide
  have h22 : (2 : ZMod 3) + 2 = 1 := by decide
  rcases h3 a with rfl | rfl | rfl <;>
    rcases h3 b with rfl | rfl | rfl <;>
    rcases h3 c with rfl | rfl | rfl
  all_goals first | exact absurd rfl hab | exact absurd rfl hac | exact absurd rfl hbc | skip
  all_goals (rcases h3 y with rfl | rfl | rfl <;>
    simp only [add_zero, zero_add, h11, h12, h21, h22] <;> ring)

/- Chebyshev bound on the number of balanced triples among r pairwise-disjoint triples
in F_3^m: the fraction of w with fewer than r/9 balanced triples is at most 14/r. -/
lemma balanced_triple_chebyshev {m r : ℕ} (hr : 1 ≤ r) (T : Fin r → Fin 3 → Fin m)
    (hT : Function.Injective (fun ja : Fin r × Fin 3 => T ja.1 ja.2)) :
    ((Finset.univ.filter fun w : 𝔽₃ m =>
        (Finset.univ.filter fun j : Fin r =>
          w (T j 0) ≠ w (T j 1) ∧ w (T j 0) ≠ w (T j 2) ∧ w (T j 1) ≠ w (T j 2)).card < r / 9).card : ℝ) ≤
      (14 : ℝ) / (r : ℝ) * (3 : ℝ) ^ m := by
  have hnat6 :
      (∑ a : ZMod 3, ∑ b : ZMod 3, ∑ c : ZMod 3,
        if a ≠ b ∧ a ≠ c ∧ b ≠ c then (1 : ℕ) else 0) = 6 := by decide
  classical
  have hcount6 :
      (∑ u : Fin 3 → ZMod 3,
        if u 0 ≠ u 1 ∧ u 0 ≠ u 2 ∧ u 1 ≠ u 2 then (1 : ℝ) else 0) = 6 := by
    let e3 : (Fin 3 → ZMod 3) ≃ ZMod 3 × ZMod 3 × ZMod 3 :=
      { toFun := fun u => (u 0, u 1, u 2)
        invFun := fun abc a => match a.val with | 0 => abc.1 | 1 => abc.2.1 | _ => abc.2.2
        left_inv := by intro u; funext a; fin_cases a <;> rfl
        right_inv := by rintro ⟨a, b, c⟩; rfl }
    have heq3 :
        (∑ u : Fin 3 → ZMod 3,
          if u 0 ≠ u 1 ∧ u 0 ≠ u 2 ∧ u 1 ≠ u 2 then (1 : ℝ) else 0) =
        ∑ abc : ZMod 3 × ZMod 3 × ZMod 3,
          if abc.1 ≠ abc.2.1 ∧ abc.1 ≠ abc.2.2 ∧ abc.2.1 ≠ abc.2.2 then (1 : ℝ) else 0 :=
      Fintype.sum_equiv e3
        (fun u => if u 0 ≠ u 1 ∧ u 0 ≠ u 2 ∧ u 1 ≠ u 2 then (1 : ℝ) else 0)
        (fun abc => if abc.1 ≠ abc.2.1 ∧ abc.1 ≠ abc.2.2 ∧ abc.2.1 ≠ abc.2.2 then (1 : ℝ) else 0)
        (fun _ => rfl)
    have hsplit3 :
        (∑ abc : ZMod 3 × ZMod 3 × ZMod 3,
          if abc.1 ≠ abc.2.1 ∧ abc.1 ≠ abc.2.2 ∧ abc.2.1 ≠ abc.2.2 then (1 : ℝ) else 0) =
        ∑ a : ZMod 3, ∑ b : ZMod 3, ∑ c : ZMod 3,
          if a ≠ b ∧ a ≠ c ∧ b ≠ c then (1 : ℝ) else 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl; intro a _
      exact Fintype.sum_prod_type _
    rw [heq3, hsplit3]
    have hnatR : ((6 : ℕ) : ℝ) = 6 := by norm_num
    rw [← hnatR, ← hnat6]
    rw [Nat.cast_sum]; apply Finset.sum_congr rfl; intro a _
    rw [Nat.cast_sum]; apply Finset.sum_congr rfl; intro b _
    rw [Nat.cast_sum]; apply Finset.sum_congr rfl; intro c _
    by_cases h : a ≠ b ∧ a ≠ c ∧ b ≠ c <;> simp [h]
  let X : Fin r → 𝔽₃ m → ℝ := fun j w =>
    if w (T j 0) ≠ w (T j 1) ∧ w (T j 0) ≠ w (T j 2) ∧ w (T j 1) ≠ w (T j 2) then 1 else 0
  have hsingle : ∀ j : Fin r, (∑ w : 𝔽₃ m, X j w) = (2 / 9 : ℝ) * (3 : ℝ) ^ m := by
    intro j
    let S : Finset (Fin m) := {T j 0, T j 1, T j 2}
    have h01 : T j 0 ≠ T j 1 := fun h => by
      have := hT (a₁ := (j, 0)) (a₂ := (j, 1)) h; simp at this
    have h02 : T j 0 ≠ T j 2 := fun h => by
      have := hT (a₁ := (j, 0)) (a₂ := (j, 2)) h; simp at this
    have h12 : T j 1 ≠ T j 2 := fun h => by
      have := hT (a₁ := (j, 1)) (a₂ := (j, 2)) h; simp at this
    have hScard : S.card = 3 := by
      dsimp only [S]
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [h12]
      · simp [h01, h02]
    let eS : Fin 3 ≃ S :=
      { toFun := fun a => ⟨T j a, by fin_cases a <;> simp [S]⟩
        invFun := fun i =>
          if i.1 = T j 0 then 0 else if i.1 = T j 1 then 1 else 2
        left_inv := by
          intro a; fin_cases a <;> simp [h01.symm, h02.symm, h12.symm]
        right_inv := by
          rintro ⟨i, hi⟩
          simp only [S, Finset.mem_insert, Finset.mem_singleton] at hi
          rcases hi with rfl | rfl | rfl <;> simp [h01.symm, h02.symm, h12.symm] }
    let Sc : Finset (Fin m) := Sᶜ
    have hScc : Sc.card = m - 3 := by rw [Finset.card_compl, Fintype.card_fin, hScard]
    let eSc : Fin (m - 3) ≃ Sc :=
      (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hScc])).symm
    let bij : 𝔽₃ m ≃ (Fin 3 → ZMod 3) × 𝔽₃ (m - 3) :=
      { toFun := fun w => (fun a => w (T j a), fun l => w (eSc l).1)
        invFun := fun uv i =>
          if hi : i ∈ S then uv.1 (eS.symm ⟨i, hi⟩)
          else uv.2 (eSc.symm ⟨i, Finset.mem_compl.mpr hi⟩)
        left_inv := by
          intro w; funext i
          by_cases hi : i ∈ S
          · simp only [hi, dite_true]
            have h1 : T j (eS.symm ⟨i, hi⟩) = i := congrArg Subtype.val (eS.apply_symm_apply ⟨i, hi⟩)
            rw [h1]
          · simp [hi]
        right_inv := by
          rintro ⟨u, v⟩
          apply Prod.ext
          · funext a
            have ha : T j a ∈ S := (eS a).2
            simp only [ha, dite_true]
            have h1 : eS.symm ⟨T j a, ha⟩ = a := eS.symm_apply_apply a
            rw [h1]
          · funext l
            have hl : (eSc l).1 ∉ S := Finset.mem_compl.mp (eSc l).2
            simp [hl] }
    have hsum_eq : (∑ w : 𝔽₃ m, X j w) =
        ∑ uv : (Fin 3 → ZMod 3) × 𝔽₃ (m - 3),
          if uv.1 0 ≠ uv.1 1 ∧ uv.1 0 ≠ uv.1 2 ∧ uv.1 1 ≠ uv.1 2 then (1 : ℝ) else 0 :=
      Fintype.sum_equiv bij (fun w => X j w)
        (fun uv => if uv.1 0 ≠ uv.1 1 ∧ uv.1 0 ≠ uv.1 2 ∧ uv.1 1 ≠ uv.1 2 then (1 : ℝ) else 0)
        (fun _ => rfl)
    have hsplit1 :
        (∑ uv : (Fin 3 → ZMod 3) × 𝔽₃ (m - 3),
          if uv.1 0 ≠ uv.1 1 ∧ uv.1 0 ≠ uv.1 2 ∧ uv.1 1 ≠ uv.1 2 then (1 : ℝ) else 0) =
        ∑ u : Fin 3 → ZMod 3, ∑ _v : 𝔽₃ (m - 3),
          if u 0 ≠ u 1 ∧ u 0 ≠ u 2 ∧ u 1 ≠ u 2 then (1 : ℝ) else 0 :=
      Fintype.sum_prod_type _
    rw [hsum_eq, hsplit1, Finset.sum_comm]
    simp only [Finset.sum_const, Finset.card_univ, card_F3, nsmul_eq_mul,
      Nat.cast_pow, Nat.cast_ofNat]
    have hm3 : 3 ≤ m := by
      calc 3 = S.card := hScard.symm
      _ ≤ Fintype.card (Fin m) := Finset.card_le_univ S
      _ = m := Fintype.card_fin m
    rw [hcount6]
    have hpow : (3 : ℝ) ^ m = (3 : ℝ) ^ (m - 3) * 27 := by
      have : (3 : ℝ) ^ m = (3 : ℝ) ^ (m - 3) * (3 : ℝ) ^ 3 := by
        rw [← pow_add, Nat.sub_add_cancel hm3]
      rw [this]; norm_num
    rw [hpow]
    ring
  have hpair : ∀ j₁ j₂ : Fin r, j₁ ≠ j₂ →
      (∑ w : 𝔽₃ m, X j₁ w * X j₂ w) = (4 / 81 : ℝ) * (3 : ℝ) ^ m := by
    intro j₁ j₂ hjne
    let S : Finset (Fin m) := {T j₁ 0, T j₁ 1, T j₁ 2, T j₂ 0, T j₂ 1, T j₂ 2}
    let idx6 : Fin 3 ⊕ Fin 3 → Fin r × Fin 3 := fun k =>
      match k with | Sum.inl a => (j₁, a) | Sum.inr a => (j₂, a)
    have hidx_inj : Function.Injective (fun k : Fin 3 ⊕ Fin 3 => T (idx6 k).1 (idx6 k).2) := by
      intro k₁ k₂ h
      have hpair_eq := hT h
      rcases k₁ with a₁ | a₁ <;> rcases k₂ with a₂ | a₂ <;> simp_all [idx6, hjne.symm]
    have hS_eq : S = Finset.univ.image (fun k : Fin 3 ⊕ Fin 3 => T (idx6 k).1 (idx6 k).2) := by
      ext i
      simp only [S, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
        Finset.mem_univ, true_and]
      constructor
      · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
        · exact ⟨Sum.inl 0, rfl⟩
        · exact ⟨Sum.inl 1, rfl⟩
        · exact ⟨Sum.inl 2, rfl⟩
        · exact ⟨Sum.inr 0, rfl⟩
        · exact ⟨Sum.inr 1, rfl⟩
        · exact ⟨Sum.inr 2, rfl⟩
      · rintro ⟨k, rfl⟩
        rcases k with a | a <;> fin_cases a <;> simp [idx6]
    have hScard : S.card = 6 := by
      rw [hS_eq, Finset.card_image_of_injective _ hidx_inj, Finset.card_univ, Fintype.card_sum,
        Fintype.card_fin]
    let eS : Fin 3 ⊕ Fin 3 ≃ S :=
      Equiv.ofBijective (fun k => ⟨T (idx6 k).1 (idx6 k).2, by
        rw [hS_eq]; exact Finset.mem_image_of_mem _ (Finset.mem_univ k)⟩)
        ⟨fun k₁ k₂ h => hidx_inj (congrArg Subtype.val h), fun ⟨i, hi⟩ => by
          rw [hS_eq, Finset.mem_image] at hi
          rcases hi with ⟨k, _, rfl⟩
          exact ⟨k, rfl⟩⟩
    let Sc : Finset (Fin m) := Sᶜ
    have hScc : Sc.card = m - 6 := by rw [Finset.card_compl, Fintype.card_fin, hScard]
    let eSc : Fin (m - 6) ≃ Sc :=
      (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hScc])).symm
    let bij : 𝔽₃ m ≃ (Fin 3 → ZMod 3) × (Fin 3 → ZMod 3) × 𝔽₃ (m - 6) :=
      { toFun := fun w => (fun a => w (T j₁ a), fun a => w (T j₂ a), fun l => w (eSc l).1)
        invFun := fun uvw i =>
          if hi : i ∈ S then
            match eS.symm ⟨i, hi⟩ with
            | Sum.inl a => uvw.1 a
            | Sum.inr a => uvw.2.1 a
          else uvw.2.2 (eSc.symm ⟨i, Finset.mem_compl.mpr hi⟩)
        left_inv := by
          intro w; funext i
          by_cases hi : i ∈ S
          · simp only [hi, dite_true]
            have hk : T (idx6 (eS.symm ⟨i, hi⟩)).1 (idx6 (eS.symm ⟨i, hi⟩)).2 = i :=
              congrArg Subtype.val (eS.apply_symm_apply ⟨i, hi⟩)
            cases hcase : eS.symm ⟨i, hi⟩ with
            | inl a => simp only [hcase, idx6] at hk; exact congrArg w hk
            | inr a => simp only [hcase, idx6] at hk; exact congrArg w hk
          · simp [hi]
        right_inv := by
          rintro ⟨u, v, rest⟩
          refine Prod.ext ?_ (Prod.ext ?_ ?_)
          · funext a
            have hm : T j₁ a ∈ S := (eS (Sum.inl a)).2
            simp only [hm, dite_true]
            have h0 : eS.symm ⟨T j₁ a, hm⟩ = Sum.inl a := eS.symm_apply_apply (Sum.inl a)
            rw [h0]
          · funext a
            have hm : T j₂ a ∈ S := (eS (Sum.inr a)).2
            simp only [hm, dite_true]
            have h0 : eS.symm ⟨T j₂ a, hm⟩ = Sum.inr a := eS.symm_apply_apply (Sum.inr a)
            rw [h0]
          · funext l
            have hl : (eSc l).1 ∉ S := Finset.mem_compl.mp (eSc l).2
            simp [hl] }
    have hsum_eq : (∑ w : 𝔽₃ m, X j₁ w * X j₂ w) =
        ∑ uvw : (Fin 3 → ZMod 3) × (Fin 3 → ZMod 3) × 𝔽₃ (m - 6),
          (if uvw.1 0 ≠ uvw.1 1 ∧ uvw.1 0 ≠ uvw.1 2 ∧ uvw.1 1 ≠ uvw.1 2 then (1 : ℝ) else 0) *
          (if uvw.2.1 0 ≠ uvw.2.1 1 ∧ uvw.2.1 0 ≠ uvw.2.1 2 ∧ uvw.2.1 1 ≠ uvw.2.1 2 then (1 : ℝ) else 0) :=
      Fintype.sum_equiv bij (fun w => X j₁ w * X j₂ w)
        (fun uvw =>
          (if uvw.1 0 ≠ uvw.1 1 ∧ uvw.1 0 ≠ uvw.1 2 ∧ uvw.1 1 ≠ uvw.1 2 then (1 : ℝ) else 0) *
          (if uvw.2.1 0 ≠ uvw.2.1 1 ∧ uvw.2.1 0 ≠ uvw.2.1 2 ∧ uvw.2.1 1 ≠ uvw.2.1 2 then (1 : ℝ) else 0))
        (fun _ => rfl)
    have hsplit2 :
        (∑ uvw : (Fin 3 → ZMod 3) × (Fin 3 → ZMod 3) × 𝔽₃ (m - 6),
          (if uvw.1 0 ≠ uvw.1 1 ∧ uvw.1 0 ≠ uvw.1 2 ∧ uvw.1 1 ≠ uvw.1 2 then (1 : ℝ) else 0) *
          (if uvw.2.1 0 ≠ uvw.2.1 1 ∧ uvw.2.1 0 ≠ uvw.2.1 2 ∧ uvw.2.1 1 ≠ uvw.2.1 2 then (1 : ℝ) else 0)) =
        ∑ u : Fin 3 → ZMod 3, ∑ v : Fin 3 → ZMod 3, ∑ _rest : 𝔽₃ (m - 6),
          (if u 0 ≠ u 1 ∧ u 0 ≠ u 2 ∧ u 1 ≠ u 2 then (1 : ℝ) else 0) *
          (if v 0 ≠ v 1 ∧ v 0 ≠ v 2 ∧ v 1 ≠ v 2 then (1 : ℝ) else 0) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl; intro u _
      exact Fintype.sum_prod_type _
    rw [hsum_eq, hsplit2]
    have hinner : ∀ u : Fin 3 → ZMod 3,
        (∑ v : Fin 3 → ZMod 3, ∑ _rest : 𝔽₃ (m - 6),
          (if u 0 ≠ u 1 ∧ u 0 ≠ u 2 ∧ u 1 ≠ u 2 then (1 : ℝ) else 0) *
          (if v 0 ≠ v 1 ∧ v 0 ≠ v 2 ∧ v 1 ≠ v 2 then (1 : ℝ) else 0)) =
        (if u 0 ≠ u 1 ∧ u 0 ≠ u 2 ∧ u 1 ≠ u 2 then (1 : ℝ) else 0) * (6 * (3 : ℝ) ^ (m - 6)) := by
      intro u
      simp only [Finset.sum_const, Finset.card_univ, card_F3, nsmul_eq_mul,
        Nat.cast_pow, Nat.cast_ofNat]
      have hpull :
          (∑ v : Fin 3 → ZMod 3, (3 : ℝ) ^ (m - 6) *
            ((if u 0 ≠ u 1 ∧ u 0 ≠ u 2 ∧ u 1 ≠ u 2 then (1 : ℝ) else 0) *
             (if v 0 ≠ v 1 ∧ v 0 ≠ v 2 ∧ v 1 ≠ v 2 then (1 : ℝ) else 0))) =
          (if u 0 ≠ u 1 ∧ u 0 ≠ u 2 ∧ u 1 ≠ u 2 then (1 : ℝ) else 0) * (3 : ℝ) ^ (m - 6) *
            (∑ v : Fin 3 → ZMod 3,
              if v 0 ≠ v 1 ∧ v 0 ≠ v 2 ∧ v 1 ≠ v 2 then (1 : ℝ) else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _
        ring
      rw [hpull, hcount6]
      ring
    simp only [hinner]
    rw [← Finset.sum_mul, hcount6]
    have hm6 : 6 ≤ m := by
      calc 6 = S.card := hScard.symm
      _ ≤ Fintype.card (Fin m) := Finset.card_le_univ S
      _ = m := Fintype.card_fin m
    have hpow : (3 : ℝ) ^ m = (3 : ℝ) ^ (m - 6) * 729 := by
      have : (3 : ℝ) ^ m = (3 : ℝ) ^ (m - 6) * (3 : ℝ) ^ 6 := by
        rw [← pow_add, Nat.sub_add_cancel hm6]
      rw [this]; norm_num
    rw [hpow]
    ring
  have hvar :
      (∑ w : 𝔽₃ m, ((∑ j : Fin r, X j w) - (2 / 9 : ℝ) * (r : ℝ)) ^ 2) =
        (14 / 81 : ℝ) * (r : ℝ) * (3 : ℝ) ^ m := by
    have hcenter : ∀ w : 𝔽₃ m,
        ((∑ j : Fin r, X j w) - (2 / 9 : ℝ) * (r : ℝ)) ^ 2 =
        ∑ j₁ : Fin r, ∑ j₂ : Fin r, (X j₁ w - 2 / 9) * (X j₂ w - 2 / 9) := by
      intro w
      have h1 : (∑ j : Fin r, X j w) - (2 / 9 : ℝ) * (r : ℝ) =
          ∑ j : Fin r, (X j w - 2 / 9) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        ring
      rw [h1, sq, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j₁ _
      rw [Finset.mul_sum]
    simp only [hcenter]
    rw [Finset.sum_comm]
    have hswap : ∀ j₁ : Fin r,
        (∑ w : 𝔽₃ m, ∑ j₂ : Fin r, (X j₁ w - 2 / 9) * (X j₂ w - 2 / 9)) =
        ∑ j₂ : Fin r, ∑ w : 𝔽₃ m, (X j₁ w - 2 / 9) * (X j₂ w - 2 / 9) := fun _ => Finset.sum_comm
    simp only [hswap]
    have hcov : ∀ j₁ j₂ : Fin r,
        (∑ w : 𝔽₃ m, (X j₁ w - 2 / 9) * (X j₂ w - 2 / 9)) =
        if j₁ = j₂ then (14 / 81 : ℝ) * (3 : ℝ) ^ m else 0 := by
      intro j₁ j₂
      have hexp :
          (∑ w : 𝔽₃ m, (X j₁ w - 2 / 9) * (X j₂ w - 2 / 9)) =
          (∑ w : 𝔽₃ m, X j₁ w * X j₂ w) - (2 / 9 : ℝ) * (∑ w : 𝔽₃ m, X j₁ w) -
            (2 / 9 : ℝ) * (∑ w : 𝔽₃ m, X j₂ w) + (4 / 81 : ℝ) * (3 : ℝ) ^ m := by
        have h1 : ∀ w : 𝔽₃ m,
            (X j₁ w - 2 / 9) * (X j₂ w - 2 / 9) =
            X j₁ w * X j₂ w - (2 / 9 : ℝ) * X j₁ w - (2 / 9 : ℝ) * X j₂ w + (4 / 81 : ℝ) := by
          intro w; ring
        simp only [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          Finset.sum_const, Finset.card_univ, card_F3, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
        ring
      rw [hexp, hsingle j₁, hsingle j₂]
      by_cases hjeq : j₁ = j₂
      · subst hjeq
        have hsqX : ∀ w : 𝔽₃ m, X j₁ w * X j₁ w = X j₁ w := by
          intro w; dsimp only [X]; split_ifs <;> ring
        simp only [hsqX, hsingle j₁, ↓reduceIte]
        ring
      · rw [hpair j₁ j₂ hjeq]
        simp only [hjeq, ↓reduceIte]
        ring
    simp only [hcov, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  let Bad := Finset.univ.filter fun w : 𝔽₃ m =>
    (Finset.univ.filter fun j : Fin r =>
      w (T j 0) ≠ w (T j 1) ∧ w (T j 0) ≠ w (T j 2) ∧ w (T j 1) ≠ w (T j 2)).card < r / 9
  have hcheb : ((r : ℝ) / 9) ^ 2 * (Bad.card : ℝ) ≤ (14 / 81 : ℝ) * (r : ℝ) * (3 : ℝ) ^ m := by
    rw [← hvar]
    calc
      ((r : ℝ) / 9) ^ 2 * (Bad.card : ℝ) = ∑ _w ∈ Bad, ((r : ℝ) / 9) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ w ∈ Bad, ((∑ j : Fin r, X j w) - (2 / 9 : ℝ) * (r : ℝ)) ^ 2 := by
        apply Finset.sum_le_sum
        intro w hw
        simp only [Bad, Finset.mem_filter, Finset.mem_univ, true_and] at hw
        have hsumX : (∑ j : Fin r, X j w) =
            ((Finset.univ.filter fun j : Fin r =>
              w (T j 0) ≠ w (T j 1) ∧ w (T j 0) ≠ w (T j 2) ∧ w (T j 1) ≠ w (T j 2)).card : ℝ) := by
          simp [X]
        rw [hsumX]
        have hdiv : ((r / 9 : ℕ) : ℝ) ≤ (r : ℝ) / 9 := by
          have : (r / 9) * 9 ≤ r := Nat.div_mul_le_self r 9
          have hR : ((r / 9 : ℕ) : ℝ) * 9 ≤ (r : ℝ) := by exact_mod_cast this
          linarith
        have hlt : ((Finset.univ.filter fun j : Fin r =>
            w (T j 0) ≠ w (T j 1) ∧ w (T j 0) ≠ w (T j 2) ∧ w (T j 1) ≠ w (T j 2)).card : ℝ) <
            (r : ℝ) / 9 :=
          lt_of_lt_of_le (Nat.cast_lt.mpr hw) hdiv
        nlinarith
      _ ≤ ∑ w : 𝔽₃ m, ((∑ j : Fin r, X j w) - (2 / 9 : ℝ) * (r : ℝ)) ^ 2 :=
        Finset.sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _)
  have hrpos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr (by omega)
  have hmul : (r : ℝ) * (Bad.card : ℝ) ≤ 14 * (3 : ℝ) ^ m := by nlinarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hrpos]
  linarith

/- Replacing coordinate functions inside balanced triples by their triple representative
preserves product correlation up to gamma / 8 and yields total L1 fiber deviation >= 3*gamma/4. -/
lemma balanced_triple_approx_corr {m t r : ℕ} (A' : Finset (𝔽₃ m))
    (Q : Fin m → ZMod 3 → ℂ) {γ η : ℝ} (hηpos : 0 < η)
    (hr_eq : r = 9 * t) (h27η : 27 * (t : ℝ) * η = γ / 8)
    (hQ : ∀ i a, ‖Q i a‖ ≤ 1)
    (hcorr : 7 * γ / 8 ≤ ‖(∑ w : 𝔽₃ m,
      (((if w ∈ A' then (1 : ℝ) else 0) - (A'.card : ℝ) / (3 : ℝ) ^ m : ℝ) : ℂ) *
        ∏ i : Fin m, Q i (w i)) / (3 : ℂ) ^ m‖)
    (T : Fin r → Fin 3 → Fin m)
    (hT_inj : Function.Injective (fun ja : Fin r × Fin 3 => T ja.1 ja.2))
    (hT_close : ∀ (j : Fin r) (a : Fin 3) (c : ZMod 3), ‖Q (T j a) c - Q (T j 0) c‖ ≤ η)
    (tripOf : Fin m → Option (Fin r))
    (htripOf_T : ∀ j a, tripOf (T j a) = some j)
    (htripOf_some : ∀ {i : Fin m} {j : Fin r}, tripOf i = some j → ∃ a : Fin 3, T j a = i) :
    let bal : 𝔽₃ m → Finset (Fin r) := fun w =>
      Finset.univ.filter fun j : Fin r =>
        w (T j 0) ≠ w (T j 1) ∧ w (T j 0) ≠ w (T j 2) ∧ w (T j 1) ≠ w (T j 2)
    let canon : 𝔽₃ m → 𝔽₃ m := fun w i =>
      match tripOf i with
      | some j => if j ∈ bal w then w i - w (T j 0) else w i
      | none => w i
    3 * γ / 4 * (3 : ℝ) ^ m ≤
      ∑ u ∈ Finset.univ.image canon,
        |∑ w ∈ Finset.univ.filter (fun w => canon w = u),
          ((if w ∈ A' then (1 : ℝ) else 0) - (A'.card : ℝ) / (3 : ℝ) ^ m)| := by
  classical
  intro bal canon
  have hbal_canon : ∀ w : 𝔽₃ m, bal (canon w) = bal w := by
    intro w
    ext j
    simp only [bal, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hj : j ∈ bal w
    · have hj' : w (T j 0) ≠ w (T j 1) ∧ w (T j 0) ≠ w (T j 2) ∧ w (T j 1) ≠ w (T j 2) :=
        (Finset.mem_filter.mp hj).2
      simp only [canon, htripOf_T, hj, ↓reduceIte]
      refine ⟨fun _ => hj', fun _ => ⟨?_, ?_, ?_⟩⟩
      · intro h; exact hj'.1 (sub_left_inj.mp h)
      · intro h; exact hj'.2.1 (sub_left_inj.mp h)
      · intro h; exact hj'.2.2 (sub_left_inj.mp h)
    · simp only [canon, htripOf_T, hj, ↓reduceIte]
  let Qfac : 𝔽₃ m → Fin m → ℂ := fun w i =>
    match tripOf i with
    | some j => if j ∈ bal w then Q (T j 0) (w i) else Q i (w i)
    | none => Q i (w i)
  let Qapprox : 𝔽₃ m → ℂ := fun w => ∏ i : Fin m, Qfac w i
  have hQapprox_const : ∀ w : 𝔽₃ m, Qapprox w = Qapprox (canon w) := by
    intro w
    let covBal : Finset (Fin m) := (bal w ×ˢ (Finset.univ : Finset (Fin 3))).image (fun ja => T ja.1 ja.2)
    have hsplit_prod : ∀ (G : Fin m → ℂ),
        (∏ i : Fin m, G i) =
        (∏ i ∈ covBal, G i) * (∏ i ∈ covBalᶜ, G i) := by
      intro G
      rw [← Finset.prod_union disjoint_compl_right, Finset.union_compl]
    dsimp only [Qapprox]
    rw [hsplit_prod (Qfac w), hsplit_prod (Qfac (canon w))]
    congr 1
    · have hcov_inj : Set.InjOn (fun ja : Fin r × Fin 3 => T ja.1 ja.2)
          ((bal w ×ˢ (Finset.univ : Finset (Fin 3)) : Finset (Fin r × Fin 3)) : Set (Fin r × Fin 3)) :=
        fun _ _ _ _ h => hT_inj h
      rw [Finset.prod_image hcov_inj, Finset.prod_image hcov_inj,
        Finset.prod_product, Finset.prod_product]
      apply Finset.prod_congr rfl
      intro j hj
      have hj' : w (T j 0) ≠ w (T j 1) ∧ w (T j 0) ≠ w (T j 2) ∧ w (T j 1) ≠ w (T j 2) :=
        (Finset.mem_filter.mp hj).2
      have hcj : j ∈ bal (canon w) := by rw [hbal_canon]; exact hj
      simp only [Qfac, htripOf_T, hj, hcj, ↓reduceIte, Fin.prod_univ_three]
      have hL := prod_balanced_triple_zmod3 (Q (T j 0)) hj'.1 hj'.2.1 hj'.2.2 0
      simp only [add_zero] at hL
      have hR := prod_balanced_triple_zmod3 (Q (T j 0)) hj'.1 hj'.2.1 hj'.2.2 (-w (T j 0))
      have hcanon_j : ∀ a : Fin 3, canon w (T j a) = w (T j a) + -w (T j 0) := by
        intro a; simp [canon, htripOf_T, hj, sub_eq_add_neg]
      simp only [hcanon_j]
      rw [hL, hR]
    · apply Finset.prod_congr rfl
      intro i hi
      rw [Finset.mem_compl] at hi
      have hnot_bal : ∀ j, tripOf i = some j → j ∉ bal w := by
        intro j hj hjb
        apply hi
        obtain ⟨a, ha⟩ := htripOf_some hj
        rw [Finset.mem_image]
        exact ⟨(j, a), Finset.mem_product.mpr ⟨hjb, Finset.mem_univ a⟩, ha⟩
      cases ht : tripOf i with
      | none => simp [Qfac, canon, ht]
      | some j =>
        have hjb : j ∉ bal w := hnot_bal j ht
        have hjbc : j ∉ bal (canon w) := by rw [hbal_canon]; exact hjb
        simp [Qfac, canon, ht, hjb, hjbc]
  have hQapprox_norm : ∀ w : 𝔽₃ m, ‖Qapprox w‖ ≤ 1 := by
    intro w
    dsimp only [Qapprox]
    rw [norm_prod]
    apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
    intro i _
    dsimp only [Qfac]
    cases tripOf i with
    | none => exact hQ i (w i)
    | some j => dsimp only; split_ifs <;> exact hQ _ _
  have hQ_diff : ∀ w : 𝔽₃ m, ‖(∏ i : Fin m, Q i (w i)) - Qapprox w‖ ≤ γ / 8 := by
    intro w
    let covBal : Finset (Fin m) := (bal w ×ˢ (Finset.univ : Finset (Fin 3))).image (fun ja => T ja.1 ja.2)
    have hsplit : ∀ (G : Fin m → ℂ),
        (∏ i : Fin m, G i) = (∏ i ∈ covBal, G i) * (∏ i ∈ covBalᶜ, G i) := by
      intro G; rw [← Finset.prod_union disjoint_compl_right, Finset.union_compl]
    have hrest_eq : (∏ i ∈ covBalᶜ, Q i (w i)) = ∏ i ∈ covBalᶜ, Qfac w i := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [Finset.mem_compl] at hi
      dsimp only [Qfac]
      cases ht : tripOf i with
      | none => rfl
      | some j =>
        have hjb : j ∉ bal w := by
          intro hjb
          apply hi
          obtain ⟨a, ha⟩ := htripOf_some ht
          rw [Finset.mem_image]
          exact ⟨(j, a), Finset.mem_product.mpr ⟨hjb, Finset.mem_univ a⟩, ha⟩
        simp [hjb]
    dsimp only [Qapprox]
    rw [hsplit (fun i => Q i (w i)), hsplit (Qfac w), ← hrest_eq, ← sub_mul, norm_mul]
    have hrest_norm : ‖∏ i ∈ covBalᶜ, Q i (w i)‖ ≤ 1 := by
      rw [norm_prod]
      exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => hQ i (w i))
    have hcov_diff :
        ‖(∏ i ∈ covBal, Q i (w i)) - (∏ i ∈ covBal, Qfac w i)‖ ≤ (covBal.card : ℝ) * η := by
      apply norm_prod_sub_prod_le covBal _ _
      · intro i _; exact hQ i (w i)
      · intro i _; dsimp only [Qfac]; cases tripOf i with | none => exact hQ i (w i) | some j => dsimp only; split_ifs <;> exact hQ _ _
      · intro i hi
        rw [Finset.mem_image] at hi
        rcases hi with ⟨⟨j, a⟩, hja, rfl⟩
        have hjb : j ∈ bal w := (Finset.mem_product.mp hja).1
        simp only [Qfac, htripOf_T, hjb, ↓reduceIte]
        exact hT_close j a (w (T j a))
    have hcov_card : covBal.card ≤ 3 * r := by
      calc covBal.card ≤ (bal w ×ˢ (Finset.univ : Finset (Fin 3))).card := Finset.card_image_le
      _ = (bal w).card * 3 := by rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
      _ ≤ r * 3 := Nat.mul_le_mul_right 3 (by simpa using Finset.card_le_univ (bal w))
      _ = 3 * r := mul_comm _ _
    have hcard_η : (covBal.card : ℝ) * η ≤ γ / 8 := by
      have h1 : (covBal.card : ℝ) ≤ 27 * (t : ℝ) := by
        have : covBal.card ≤ 27 * t := by omega
        exact_mod_cast this
      nlinarith
    calc
      ‖(∏ i ∈ covBal, Q i (w i)) - (∏ i ∈ covBal, Qfac w i)‖ * ‖∏ i ∈ covBalᶜ, Q i (w i)‖
        ≤ ((covBal.card : ℝ) * η) * 1 :=
          mul_le_mul hcov_diff hrest_norm (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (le_of_lt hηpos))
      _ ≤ γ / 8 := by linarith
  let α' : ℝ := (A'.card : ℝ) / (3 : ℝ) ^ m
  let f' : 𝔽₃ m → ℝ := fun w => (if w ∈ A' then (1 : ℝ) else 0) - α'
  have h3m_pos : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have hf'_bdd : ∀ w : 𝔽₃ m, |f' w| ≤ 1 := by
    intro w
    have hα0 : 0 ≤ α' := by positivity
    have hα1 : α' ≤ 1 := by
      have hc : A'.card ≤ 3 ^ m := by
        calc A'.card ≤ Fintype.card (𝔽₃ m) := Finset.card_le_univ A'
        _ = 3 ^ m := card_F3 m
      have hR : (A'.card : ℝ) ≤ (3 : ℝ) ^ m := by exact_mod_cast hc
      exact (div_le_one h3m_pos).mpr hR
    dsimp only [f']
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  have hQapprox_corr :
      3 * γ / 4 * (3 : ℝ) ^ m ≤ ‖∑ w : 𝔽₃ m, (f' w : ℂ) * Qapprox w‖ := by
    have hnorm3 : ‖(3 : ℂ) ^ m‖ = (3 : ℝ) ^ m := by
      rw [norm_pow, Complex.norm_ofNat]
    have hcorr_sum : 7 * γ / 8 * (3 : ℝ) ^ m ≤ ‖∑ w : 𝔽₃ m, (f' w : ℂ) * ∏ i : Fin m, Q i (w i)‖ := by
      rw [norm_div, hnorm3, le_div_iff₀ h3m_pos] at hcorr
      exact hcorr
    have hdiff_sum :
        ‖(∑ w : 𝔽₃ m, (f' w : ℂ) * ∏ i : Fin m, Q i (w i)) -
          (∑ w : 𝔽₃ m, (f' w : ℂ) * Qapprox w)‖ ≤ γ / 8 * (3 : ℝ) ^ m := by
      rw [← Finset.sum_sub_distrib]
      calc
        ‖∑ w : 𝔽₃ m, ((f' w : ℂ) * ∏ i : Fin m, Q i (w i) - (f' w : ℂ) * Qapprox w)‖
          ≤ ∑ w : 𝔽₃ m, ‖(f' w : ℂ) * ∏ i : Fin m, Q i (w i) - (f' w : ℂ) * Qapprox w‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _w : 𝔽₃ m, (γ / 8) := by
            apply Finset.sum_le_sum
            intro w _
            rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
            calc |f' w| * ‖(∏ i : Fin m, Q i (w i)) - Qapprox w‖ ≤ 1 * (γ / 8) :=
              mul_le_mul (hf'_bdd w) (hQ_diff w) (norm_nonneg _) (by norm_num)
            _ = γ / 8 := one_mul _
        _ = γ / 8 * (3 : ℝ) ^ m := by
            rw [Finset.sum_const, Finset.card_univ, card_F3, nsmul_eq_mul,
              Nat.cast_pow, Nat.cast_ofNat, mul_comm]
    have htri := norm_sub_norm_le (∑ w : 𝔽₃ m, (f' w : ℂ) * ∏ i : Fin m, Q i (w i))
      (∑ w : 𝔽₃ m, (f' w : ℂ) * Qapprox w)
    linarith only [hcorr_sum, hdiff_sum, htri]
  let Im : Finset (𝔽₃ m) := Finset.univ.image canon
  let fib : 𝔽₃ m → Finset (𝔽₃ m) := fun u => Finset.univ.filter fun w => canon w = u
  let s : 𝔽₃ m → ℝ := fun u => ∑ w ∈ fib u, f' w
  have hgroup :
      (∑ w : 𝔽₃ m, (f' w : ℂ) * Qapprox w) =
      ∑ u ∈ Im, (s u : ℂ) * Qapprox u := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := canon) (t := Im)
      (fun w _ => Finset.mem_image_of_mem canon (Finset.mem_univ w))]
    apply Finset.sum_congr rfl
    intro u _
    have hterm : ∀ w ∈ fib u, (f' w : ℂ) * Qapprox w = (f' w : ℂ) * Qapprox u := by
      intro w hw
      have hcw : canon w = u := (Finset.mem_filter.mp hw).2
      rw [hQapprox_const w, hcw]
    calc
      (∑ w ∈ fib u, (f' w : ℂ) * Qapprox w) = ∑ w ∈ fib u, (f' w : ℂ) * Qapprox u :=
        Finset.sum_congr rfl hterm
      _ = (∑ w ∈ fib u, (f' w : ℂ)) * Qapprox u := (Finset.sum_mul _ _ _).symm
      _ = (s u : ℂ) * Qapprox u := by simp [s]
  calc
    3 * γ / 4 * (3 : ℝ) ^ m ≤ ‖∑ u ∈ Im, (s u : ℂ) * Qapprox u‖ := by
      rw [← hgroup]; exact hQapprox_corr
    _ ≤ ∑ u ∈ Im, ‖(s u : ℂ) * Qapprox u‖ := norm_sum_le _ _
    _ ≤ ∑ u ∈ Im, |s u| := by
      apply Finset.sum_le_sum
      intro u _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |s u| * ‖Qapprox u‖ ≤ |s u| * 1 :=
        mul_le_mul_of_nonneg_left (hQapprox_norm u) (abs_nonneg _)
      _ = |s u| := mul_one _

/- Extracting a shifted combinatorial subspace of dimension >= t and density >= alpha' + gamma / 4
from r = 9*t pairwise-disjoint eta-close triples. -/
lemma balanced_triple_density_boost {m t r : ℕ} (A' : Finset (𝔽₃ m))
    (Q : Fin m → ZMod 3 → ℂ) {γ η : ℝ} (hγ0 : 0 < γ) (hηpos : 0 < η)
    (ht1 : 1 ≤ t) (hr_eq : r = 9 * t) (ht_lo : 16 / γ ≤ (t : ℝ))
    (h27η : 27 * (t : ℝ) * η = γ / 8)
    (hQ : ∀ i a, ‖Q i a‖ ≤ 1)
    (hcorr : 7 * γ / 8 ≤ ‖(∑ w : 𝔽₃ m,
      (((if w ∈ A' then (1 : ℝ) else 0) - (A'.card : ℝ) / (3 : ℝ) ^ m : ℝ) : ℂ) *
        ∏ i : Fin m, Q i (w i)) / (3 : ℂ) ^ m‖)
    (T : Fin r → Fin 3 → Fin m)
    (hT_inj : Function.Injective (fun ja : Fin r × Fin 3 => T ja.1 ja.2))
    (hT_close : ∀ (j : Fin r) (a : Fin 3) (c : ZMod 3), ‖Q (T j a) c - Q (T j 0) c‖ ≤ η) :
    ∃ (d : ℕ) (blk : Fin m → Option (Fin d)) (z : 𝔽₃ m),
      t ≤ d ∧
      (∀ l : Fin d, ∃ i : Fin m, blk i = some l) ∧
      (A'.card : ℝ) / (3 : ℝ) ^ m + γ / 4 ≤
        ((Finset.univ.filter fun y : 𝔽₃ d =>
          (fun i : Fin m => match blk i with | some l => z i + y l | none => z i) ∈ A').card : ℝ) /
        (3 : ℝ) ^ d := by
  classical
  have hr1 : 1 ≤ r := by omega
  let bal : 𝔽₃ m → Finset (Fin r) := fun w =>
    Finset.univ.filter fun j : Fin r =>
      w (T j 0) ≠ w (T j 1) ∧ w (T j 0) ≠ w (T j 2) ∧ w (T j 1) ≠ w (T j 2)
  let tripOf : Fin m → Option (Fin r) := fun i =>
    if h : ∃ ja : Fin r × Fin 3, T ja.1 ja.2 = i then some (Classical.choose h).1 else none
  have htripOf_T : ∀ j a, tripOf (T j a) = some j := by
    intro j a
    have hex : ∃ ja : Fin r × Fin 3, T ja.1 ja.2 = T j a := ⟨(j, a), rfl⟩
    simp only [tripOf, hex, dite_true]
    have hspec := Classical.choose_spec hex
    have hpair : Classical.choose hex = (j, a) := hT_inj hspec
    rw [congrArg Prod.fst hpair]
  have htripOf_some : ∀ {i : Fin m} {j : Fin r}, tripOf i = some j → ∃ a : Fin 3, T j a = i := by
    intro i j hij
    have hex : ∃ ja : Fin r × Fin 3, T ja.1 ja.2 = i := by
      by_contra hne
      simp only [tripOf, hne, dite_false] at hij
      simp at hij
    have hspec := Classical.choose_spec hex
    have hj_eq : (Classical.choose hex).1 = j := by
      simp only [tripOf, hex, dite_true, Option.some.injEq] at hij
      exact hij
    refine ⟨(Classical.choose hex).2, ?_⟩
    rw [← hj_eq]
    exact hspec
  let canon : 𝔽₃ m → 𝔽₃ m := fun w i =>
    match tripOf i with
    | some j => if j ∈ bal w then w i - w (T j 0) else w i
    | none => w i
  have hbal_canon : ∀ w : 𝔽₃ m, bal (canon w) = bal w := by
    intro w
    ext j
    simp only [bal, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hj : j ∈ bal w
    · have hj' : w (T j 0) ≠ w (T j 1) ∧ w (T j 0) ≠ w (T j 2) ∧ w (T j 1) ≠ w (T j 2) :=
        (Finset.mem_filter.mp hj).2
      simp only [canon, htripOf_T, hj, ↓reduceIte]
      refine ⟨fun _ => hj', fun _ => ⟨?_, ?_, ?_⟩⟩
      · intro h; exact hj'.1 (sub_left_inj.mp h)
      · intro h; exact hj'.2.1 (sub_left_inj.mp h)
      · intro h; exact hj'.2.2 (sub_left_inj.mp h)
    · simp only [canon, htripOf_T, hj, ↓reduceIte]
  have hcanon_zero : ∀ w j, j ∈ bal w → canon w (T j 0) = 0 := by
    intro w j hj
    simp [canon, htripOf_T, hj]
  let α' : ℝ := (A'.card : ℝ) / (3 : ℝ) ^ m
  let f' : 𝔽₃ m → ℝ := fun w => (if w ∈ A' then (1 : ℝ) else 0) - α'
  have h3m_pos : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have hf'_bdd : ∀ w : 𝔽₃ m, |f' w| ≤ 1 := by
    intro w
    have hα0 : 0 ≤ α' := by positivity
    have hα1 : α' ≤ 1 := by
      have hc : A'.card ≤ 3 ^ m := by
        calc A'.card ≤ Fintype.card (𝔽₃ m) := Finset.card_le_univ A'
        _ = 3 ^ m := card_F3 m
      have hR : (A'.card : ℝ) ≤ (3 : ℝ) ^ m := by exact_mod_cast hc
      exact (div_le_one h3m_pos).mpr hR
    dsimp only [f']
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  let Im : Finset (𝔽₃ m) := Finset.univ.image canon
  let fib : 𝔽₃ m → Finset (𝔽₃ m) := fun u => Finset.univ.filter fun w => canon w = u
  let s : 𝔽₃ m → ℝ := fun u => ∑ w ∈ fib u, f' w
  have habs_sum : 3 * γ / 4 * (3 : ℝ) ^ m ≤ ∑ u ∈ Im, |s u| :=
    balanced_triple_approx_corr A' Q hηpos hr_eq h27η hQ hcorr T hT_inj hT_close
      tripOf htripOf_T htripOf_some
  have hsum_s_zero : (∑ u ∈ Im, s u) = 0 := by
    dsimp only [s]
    rw [Finset.sum_fiberwise_of_maps_to (g := canon) (t := Im)
      (fun w _ => Finset.mem_image_of_mem canon (Finset.mem_univ w))]
    dsimp only [f', α']
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, mul_one,
      Finset.card_univ, card_F3, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    have h3ne : (3 : ℝ) ^ m ≠ 0 := ne_of_gt h3m_pos
    field_simp
    ring
  have hpos_sum : 3 * γ / 8 * (3 : ℝ) ^ m ≤ ∑ u ∈ Im, max (s u) 0 := by
    have hid : (∑ u ∈ Im, |s u|) = 2 * (∑ u ∈ Im, max (s u) 0) - ∑ u ∈ Im, s u := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro u _
      rcases le_total (s u) 0 with h | h
      · rw [abs_of_nonpos h, max_eq_right h]; ring
      · rw [abs_of_nonneg h, max_eq_left h]; ring
    rw [hid, hsum_s_zero, sub_zero] at habs_sum
    linarith
  let ImGood : Finset (𝔽₃ m) := Im.filter fun u => t ≤ (bal u).card
  let ImBad : Finset (𝔽₃ m) := Im.filter fun u => ¬ t ≤ (bal u).card
  have hbad_sum : (∑ u ∈ ImBad, max (s u) 0) ≤ γ / 8 * (3 : ℝ) ^ m := by
    have hcheb := balanced_triple_chebyshev hr1 T hT_inj
    have hrt : r / 9 = t := by omega
    rw [hrt] at hcheb
    have hbad_fib :
        (∑ u ∈ ImBad, (fib u).card) ≤
        (Finset.univ.filter fun w : 𝔽₃ m => (bal w).card < t).card := by
      have hdisj : Set.PairwiseDisjoint (ImBad : Set (𝔽₃ m)) fib := by
        intro u₁ _ u₂ _ hne
        change Disjoint (fib u₁) (fib u₂)
        rw [Finset.disjoint_left]
        intro w hw₁ hw₂
        have h1 : canon w = u₁ := (Finset.mem_filter.mp hw₁).2
        have h2 : canon w = u₂ := (Finset.mem_filter.mp hw₂).2
        exact hne (h1.symm.trans h2)
      rw [← Finset.card_biUnion hdisj]
      apply Finset.card_le_card
      intro w hw
      rw [Finset.mem_biUnion] at hw
      rcases hw with ⟨u, hu, hwu⟩
      have hcw : canon w = u := (Finset.mem_filter.mp hwu).2
      have hlt : (bal u).card < t := by
        have := (Finset.mem_filter.mp hu).2
        omega
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hbal_canon w, hcw]
      exact hlt
    have h1 : (∑ u ∈ ImBad, max (s u) 0) ≤ ∑ u ∈ ImBad, ((fib u).card : ℝ) := by
      apply Finset.sum_le_sum
      intro u _
      apply max_le _ (Nat.cast_nonneg _)
      dsimp only [s]
      calc
        (∑ w ∈ fib u, f' w) ≤ ∑ _w ∈ fib u, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro w _
          exact le_of_abs_le (hf'_bdd w)
        _ = ((fib u).card : ℝ) := by simp
    have h2 : (∑ u ∈ ImBad, ((fib u).card : ℝ)) ≤
        ((Finset.univ.filter fun w : 𝔽₃ m => (bal w).card < t).card : ℝ) := by
      exact_mod_cast hbad_fib
    have h14 : (14 : ℝ) / (r : ℝ) ≤ γ / 8 := by
      have hr_eqR : (r : ℝ) = 9 * (t : ℝ) := by exact_mod_cast hr_eq
      have hrpos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr (by omega)
      rw [div_le_div_iff₀ hrpos (by norm_num : (0 : ℝ) < 8)]
      have h16 : 16 ≤ (t : ℝ) * γ := (div_le_iff₀ hγ0).mp ht_lo
      rw [hr_eqR]
      linarith only [h16]
    calc
      (∑ u ∈ ImBad, max (s u) 0) ≤ (14 : ℝ) / (r : ℝ) * (3 : ℝ) ^ m :=
        le_trans (le_trans h1 h2) hcheb
      _ ≤ γ / 8 * (3 : ℝ) ^ m := mul_le_mul_of_nonneg_right h14 (le_of_lt h3m_pos)
  have hgood_sum : γ / 4 * (3 : ℝ) ^ m ≤ ∑ u ∈ ImGood, max (s u) 0 := by
    have hpart : (∑ u ∈ Im, max (s u) 0) =
        (∑ u ∈ ImGood, max (s u) 0) + (∑ u ∈ ImBad, max (s u) 0) :=
      (Finset.sum_filter_add_sum_filter_not Im (fun u => t ≤ (bal u).card) _).symm
    linarith
  have hgood_fib_sum : (∑ u ∈ ImGood, ((fib u).card : ℝ)) ≤ (3 : ℝ) ^ m := by
    have hdisj : Set.PairwiseDisjoint (ImGood : Set (𝔽₃ m)) fib := by
      intro u₁ _ u₂ _ hne
      change Disjoint (fib u₁) (fib u₂)
      rw [Finset.disjoint_left]
      intro w hw₁ hw₂
      exact hne ((Finset.mem_filter.mp hw₁).2.symm.trans (Finset.mem_filter.mp hw₂).2)
    have hnat : (∑ u ∈ ImGood, (fib u).card) ≤ 3 ^ m := by
      rw [← Finset.card_biUnion hdisj]
      calc ((ImGood.biUnion fib).card) ≤ Fintype.card (𝔽₃ m) := Finset.card_le_univ _
      _ = 3 ^ m := card_F3 m
    exact_mod_cast hnat
  have hex_good : ∃ u ∈ ImGood, γ / 4 * ((fib u).card : ℝ) ≤ s u := by
    by_contra hno
    push Not at hno
    have hlt : (∑ u ∈ ImGood, max (s u) 0) < γ / 4 * (3 : ℝ) ^ m := by
      by_cases hne : ImGood.Nonempty
      · calc
          (∑ u ∈ ImGood, max (s u) 0) < ∑ u ∈ ImGood, γ / 4 * ((fib u).card : ℝ) := by
            apply Finset.sum_lt_sum_of_nonempty hne
            intro u hu
            apply max_lt (hno u hu)
            have huIm : u ∈ Im := (Finset.mem_filter.mp hu).1
            rcases Finset.mem_image.mp huIm with ⟨w₀, _, rfl⟩
            have hpos_fib : 0 < (fib (canon w₀)).card :=
              Finset.card_pos.mpr ⟨w₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
            have hposR : (0 : ℝ) < ((fib (canon w₀)).card : ℝ) := Nat.cast_pos.mpr hpos_fib
            positivity
          _ = γ / 4 * (∑ u ∈ ImGood, ((fib u).card : ℝ)) := (Finset.mul_sum _ _ _).symm
          _ ≤ γ / 4 * (3 : ℝ) ^ m := mul_le_mul_of_nonneg_left hgood_fib_sum (by linarith)
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        rw [hne, Finset.sum_empty]
        positivity
    linarith
  obtain ⟨u, huGood, hus⟩ := hex_good
  have huIm : u ∈ Im := (Finset.mem_filter.mp huGood).1
  have huBal_ge : t ≤ (bal u).card := (Finset.mem_filter.mp huGood).2
  rcases Finset.mem_image.mp huIm with ⟨w₀, _, rfl⟩
  set u₀ := canon w₀
  let d : ℕ := (bal u₀).card
  let eb : Fin d ≃ bal u₀ := (Fintype.equivFinOfCardEq (Fintype.card_coe (bal u₀))).symm
  let blk : Fin m → Option (Fin d) := fun i =>
    match tripOf i with
    | some j => if hj : j ∈ bal u₀ then some (eb.symm ⟨j, hj⟩) else none
    | none => none
  let φ : 𝔽₃ d → 𝔽₃ m := fun y i => match blk i with | some l => u₀ i + y l | none => u₀ i
  have hblk_surj : ∀ l : Fin d, ∃ i : Fin m, blk i = some l := by
    intro l
    refine ⟨T (eb l).1 0, ?_⟩
    have hj : (eb l).1 ∈ bal u₀ := (eb l).2
    simp only [blk, htripOf_T, hj, dite_true, Subtype.coe_eta, Equiv.symm_apply_apply]
  have hφ_inj : Function.Injective φ := combSubspace_injective blk hblk_surj u₀
  have hφ_canon : ∀ y : 𝔽₃ d, canon (φ y) = u₀ := by
    intro y
    have hbal_φ : bal (φ y) = bal u₀ := by
      ext j
      simp only [bal, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hj : j ∈ bal u₀
      · have hj' : u₀ (T j 0) ≠ u₀ (T j 1) ∧ u₀ (T j 0) ≠ u₀ (T j 2) ∧ u₀ (T j 1) ≠ u₀ (T j 2) :=
          (Finset.mem_filter.mp hj).2
        simp only [φ, blk, htripOf_T, hj, dite_true]
        refine ⟨fun _ => hj', fun _ => ⟨?_, ?_, ?_⟩⟩
        · intro h; exact hj'.1 (add_right_cancel h)
        · intro h; exact hj'.2.1 (add_right_cancel h)
        · intro h; exact hj'.2.2 (add_right_cancel h)
      · simp only [φ, blk, htripOf_T, hj, dite_false]
    funext i
    dsimp only [canon]
    rw [hbal_φ]
    cases ht : tripOf i with
    | none => simp [φ, blk, ht]
    | some j =>
      by_cases hj : j ∈ bal u₀
      · have hjw : j ∈ bal w₀ := by rw [← hbal_canon w₀]; exact hj
        have hu0 : u₀ (T j 0) = 0 := hcanon_zero w₀ j hjw
        simp only [hj, ↓reduceIte, φ, blk, ht, htripOf_T, dite_true, hu0, zero_add, add_sub_cancel_right]
      · simp [φ, blk, ht, hj]
  have hφ_surj_fib : ∀ w ∈ fib u₀, ∃ y : 𝔽₃ d, φ y = w := by
    intro w hw
    have hcw : canon w = u₀ := (Finset.mem_filter.mp hw).2
    have hbw : bal w = bal u₀ := by rw [← hbal_canon w, hcw]
    refine ⟨fun l => w (T (eb l).1 0), ?_⟩
    funext i
    dsimp only [φ, blk]
    cases ht : tripOf i with
    | none =>
      have hi := congrFun hcw i
      simp only [canon, ht] at hi
      exact hi.symm
    | some j =>
      by_cases hj : j ∈ bal u₀
      · have hjbw : j ∈ bal w := by rw [hbw]; exact hj
        have hi := congrFun hcw i
        simp only [canon, ht, hjbw, ↓reduceIte] at hi
        simp only [hj, dite_true, Equiv.apply_symm_apply]
        rw [← hi, sub_add_cancel]
      · have hjbw : j ∉ bal w := by rw [hbw]; exact hj
        have hi := congrFun hcw i
        simp only [canon, ht, hjbw, ↓reduceIte] at hi
        simp only [hj, dite_false]
        exact hi.symm
  have hfib_card : (fib u₀).card = 3 ^ d := by
    have hbij : (fib u₀).card = (Finset.univ : Finset (𝔽₃ d)).card := by
      refine (Finset.card_bij (fun y _ => φ y) ?_ ?_ ?_).symm
      · intro y _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hφ_canon y⟩
      · intro y₁ _ y₂ _ h; exact hφ_inj h
      · intro w hw
        obtain ⟨y, hy⟩ := hφ_surj_fib w hw
        exact ⟨y, Finset.mem_univ y, hy⟩
    rw [hbij, Finset.card_univ, card_F3]
  have hpull_card :
      (Finset.univ.filter fun y : 𝔽₃ d => φ y ∈ A').card =
      ((fib u₀).filter fun w => w ∈ A').card := by
    refine Finset.card_bij (fun y _ => φ y) ?_ ?_ ?_
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hφ_canon y⟩, hy⟩
    · intro y₁ _ y₂ _ h; exact hφ_inj h
    · intro w hw
      rcases Finset.mem_filter.mp hw with ⟨hwf, hwA⟩
      obtain ⟨y, hy⟩ := hφ_surj_fib w hwf
      exact ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hy]; exact hwA⟩, hy⟩
  have hs_eval : s u₀ = (((fib u₀).filter fun w => w ∈ A').card : ℝ) - α' * (3 : ℝ) ^ d := by
    dsimp only [s, f']
    rw [Finset.sum_sub_distrib, Finset.sum_const, hfib_card, nsmul_eq_mul,
      Nat.cast_pow, Nat.cast_ofNat]
    have h1 : (∑ w ∈ fib u₀, if w ∈ A' then (1 : ℝ) else 0) =
        (((fib u₀).filter fun w => w ∈ A').card : ℝ) := by
      rw [Finset.sum_boole]
    rw [h1]
    ring
  refine ⟨d, blk, u₀, huBal_ge, hblk_surj, ?_⟩
  rw [hpull_card]
  have h3d_pos : (0 : ℝ) < (3 : ℝ) ^ d := by positivity
  rw [hfib_card, hs_eval] at hus
  have hcast : ((3 ^ d : ℕ) : ℝ) = (3 : ℝ) ^ d := by push_cast; rfl
  rw [hcast] at hus
  rw [le_div_iff₀ h3d_pos]
  linarith

/- Core density increment from 1-bounded product-function correlation to a shifted combinatorial
subspace of dimension d >= t and density >= alpha' + gamma / 4, via complex-disk bucketing
and balanced-triple canonical representatives. -/
lemma product_corr_to_combSubspace_increment {m t : ℕ} (A' : Finset (𝔽₃ m))
    (Q : Fin m → ZMod 3 → ℂ) {γ : ℝ} (hγ0 : 0 < γ) (hγhalf : γ ≤ 1 / 2)
    (hQ : ∀ i a, ‖Q i a‖ ≤ 1)
    (hcorr : 7 * γ / 8 ≤ ‖(∑ w : 𝔽₃ m,
      (((if w ∈ A' then (1 : ℝ) else 0) - (A'.card : ℝ) / (3 : ℝ) ^ m : ℝ) : ℂ) *
        ∏ i : Fin m, Q i (w i)) / (3 : ℂ) ^ m‖)
    (ht_lo : 16 / γ ≤ (t : ℝ))
    (hm_lo : (3000 * (t : ℝ) / γ) ^ 6 ≤ (m : ℝ)) :
    ∃ (d : ℕ) (blk : Fin m → Option (Fin d)) (z : 𝔽₃ m),
      t ≤ d ∧
      (∀ l : Fin d, ∃ i : Fin m, blk i = some l) ∧
      (A'.card : ℝ) / (3 : ℝ) ^ m + γ / 4 ≤
        ((Finset.univ.filter fun y : 𝔽₃ d =>
          (fun i : Fin m => match blk i with | some l => z i + y l | none => z i) ∈ A').card : ℝ) /
        (3 : ℝ) ^ d := by
  classical
  have ht1R : (1 : ℝ) ≤ (t : ℝ) := by
    have : (32 : ℝ) ≤ 16 / γ := by
      rw [le_div_iff₀ hγ0]; linarith
    linarith
  have ht1 : 1 ≤ t := by exact_mod_cast ht1R
  let r : ℕ := 9 * t
  let η : ℝ := γ / (216 * (t : ℝ))
  have hηpos : 0 < η := by positivity
  have h27η : 27 * (t : ℝ) * η = γ / 8 := by
    dsimp only [η]
    have htne : (t : ℝ) ≠ 0 := by linarith
    field_simp
    ring
  let B : ℕ := Nat.ceil (4 / η) + 1
  have hB1 : 1 ≤ B := by omega
  have hB_ge : 4 / η ≤ (B : ℝ) := by
    have h1 := Nat.le_ceil (4 / η)
    have h2 : (Nat.ceil (4 / η) : ℝ) ≤ (B : ℝ) := by exact_mod_cast (Nat.le_succ _)
    linarith
  have hB_le : (B : ℝ) ≤ 2000 * (t : ℝ) / γ := by
    have h1 : (Nat.ceil (4 / η) : ℝ) < 4 / η + 1 := Nat.ceil_lt_add_one (by positivity)
    have h4η : 4 / η = 864 * ((t : ℝ) / γ) := by dsimp only [η]; field_simp; ring
    have hBcast : (B : ℝ) = (Nat.ceil (4 / η) : ℝ) + 1 := by simp [B]
    have ht_over_γ : (1 : ℝ) ≤ (t : ℝ) / γ := by
      rw [le_div_iff₀ hγ0]; linarith only [ht1R, hγhalf]
    have h2000 : 2000 * (t : ℝ) / γ = 2000 * ((t : ℝ) / γ) := mul_div_assoc 2000 (t : ℝ) γ
    linarith only [h1, h4η, hBcast, ht_over_γ, h2000]
  have hm_triples : 2 * Fintype.card (ZMod 3 → Fin B × Fin B) + 3 * r ≤ (Finset.univ : Finset (Fin m)).card := by
    have hcard_key : Fintype.card (ZMod 3 → Fin B × Fin B) = B ^ 6 := by
      rw [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, ZMod.card]
      ring
    rw [hcard_key, Finset.card_univ, Fintype.card_fin]
    have hR : (2 * (B : ℝ) ^ 6 + 3 * (r : ℝ)) ≤ (m : ℝ) := by
      have hB6 : (B : ℝ) ^ 6 ≤ (2000 * (t : ℝ) / γ) ^ 6 :=
        pow_le_pow_left₀ (Nat.cast_nonneg B) hB_le 6
      have ht_over_γ : (1 : ℝ) ≤ (t : ℝ) / γ := by
        rw [le_div_iff₀ hγ0]; linarith only [ht1R, hγhalf]
      have h2000 : 2000 * (t : ℝ) / γ = 2000 * ((t : ℝ) / γ) := mul_div_assoc 2000 (t : ℝ) γ
      have hr_le : 3 * (r : ℝ) ≤ (2000 * (t : ℝ) / γ) ^ 6 := by
        have h1 : 3 * (r : ℝ) = 27 * (t : ℝ) := by
          have : (r : ℝ) = 9 * (t : ℝ) := by exact_mod_cast (rfl : r = 9 * t)
          linarith only [this]
        have h2 : 27 * (t : ℝ) ≤ 2000 * (t : ℝ) / γ := by
          have ht_le : (t : ℝ) ≤ (t : ℝ) / γ := by
            rw [le_div_iff₀ hγ0]; nlinarith only [ht1R, hγhalf]
          linarith only [ht_le, h2000, ht1R]
        have h3 : 2000 * (t : ℝ) / γ ≤ (2000 * (t : ℝ) / γ) ^ 6 := by
          have hge1 : (1 : ℝ) ≤ 2000 * (t : ℝ) / γ := by linarith only [ht_over_γ, h2000]
          calc 2000 * (t : ℝ) / γ = (2000 * (t : ℝ) / γ) ^ 1 := (pow_one _).symm
          _ ≤ (2000 * (t : ℝ) / γ) ^ 6 := pow_le_pow_right₀ hge1 (by norm_num)
        linarith only [h1, h2, h3]
      have h3000 : 3 * (2000 * (t : ℝ) / γ) ^ 6 ≤ (3000 * (t : ℝ) / γ) ^ 6 := by
        have hnonneg : 0 ≤ ((t : ℝ) / γ) ^ 6 := by positivity
        have hfact : (3000 * (t : ℝ) / γ) ^ 6 - 3 * (2000 * (t : ℝ) / γ) ^ 6 =
            (3000 ^ 6 - 3 * 2000 ^ 6) * ((t : ℝ) / γ) ^ 6 := by ring
        nlinarith
      linarith
    exact_mod_cast hR
  obtain ⟨slot, hslot⟩ := exists_unit_interval_bucketing B hB1
  let key : Fin m → (ZMod 3 → Fin B × Fin B) := fun i a =>
    (slot (Q i a).re, slot (Q i a).im)
  obtain ⟨T, _, hT_inj, hT_key⟩ :=
    exists_disjoint_same_fiber_triples key r Finset.univ hm_triples
  have hT_close : ∀ (j : Fin r) (a : Fin 3) (c : ZMod 3), ‖Q (T j a) c - Q (T j 0) c‖ ≤ η := by
    intro j a c
    have hk := congrFun (hT_key j a) c
    have hre_eq : slot (Q (T j a) c).re = slot (Q (T j 0) c).re := congrArg Prod.fst hk
    have him_eq : slot (Q (T j a) c).im = slot (Q (T j 0) c).im := congrArg Prod.snd hk
    have hre1 : |(Q (T j a) c).re| ≤ 1 := le_trans (Complex.abs_re_le_norm _) (hQ _ _)
    have hre0 : |(Q (T j 0) c).re| ≤ 1 := le_trans (Complex.abs_re_le_norm _) (hQ _ _)
    have him1 : |(Q (T j a) c).im| ≤ 1 := le_trans (Complex.abs_im_le_norm _) (hQ _ _)
    have him0 : |(Q (T j 0) c).im| ≤ 1 := le_trans (Complex.abs_im_le_norm _) (hQ _ _)
    have hdre : |(Q (T j a) c).re - (Q (T j 0) c).re| ≤ 2 / (B : ℝ) := hslot _ _ hre1 hre0 hre_eq
    have hdim : |(Q (T j a) c).im - (Q (T j 0) c).im| ≤ 2 / (B : ℝ) := hslot _ _ him1 him0 him_eq
    have hnorm : ‖Q (T j a) c - Q (T j 0) c‖ ≤ 4 / (B : ℝ) := by
      have h1 := complex_norm_le_abs_re_add_abs_im (Q (T j a) c - Q (T j 0) c)
      simp only [Complex.sub_re, Complex.sub_im] at h1
      have h4 : 2 / (B : ℝ) + 2 / (B : ℝ) = 4 / (B : ℝ) := by ring
      linarith
    have h4B : 4 / (B : ℝ) ≤ η := by
      have hBpos : (0 : ℝ) < (B : ℝ) := Nat.cast_pos.mpr (by omega)
      rw [div_le_iff₀ hBpos]
      have := (div_le_iff₀ hηpos).mp hB_ge
      linarith
    exact le_trans hnorm h4B
  exact balanced_triple_density_boost A' Q hγ0 hηpos ht1 rfl ht_lo h27η hQ hcorr T hT_inj hT_close

/- ============================================================================
   Part 5: Single-Step Density Increment from H1 and H2
   ============================================================================ -/

/- Subcube averaging dichotomy (BKLM24 Lemma 8.2): under a delta-random restriction with small-set
tail <= gamma^2 / 64 and L^2-product correlation mass >= delta, either some large subcube already
achieves a gamma^2 / 64 density bump, or some large subcube has density within [alpha - gamma / 16,
alpha + gamma^2 / 64) and exhibits L^2-bounded product correlation >= delta. -/
lemma bernoulli_subcube_dichotomy {n : ℕ} (A : Finset (𝔽₃ n)) {δ γ : ℝ}
    (hδ0 : 0 < δ) (hδ_half : δ ≤ 1 / 2) (hγ0 : 0 < γ) (hγ_le_δ : γ ≤ δ)
    (h1_bound : δ ≤ ∑ J : Finset (Fin n),
      δ ^ J.card * (1 - δ) ^ (n - J.card) *
        (({z : 𝔽₃ n | ∃ P : Fin n → ZMod 3 → ℂ,
            (∀ i, ∑ a : ZMod 3, ‖P i a‖ ^ 2 ≤ 3) ∧
            δ ≤ ‖(∑ w : 𝔽₃ n,
              ((((if (fun i => if i ∈ J then w i else z i) ∈ A then (1 : ℝ) else 0) -
                  (A.card : ℝ) / (3 : ℝ) ^ n : ℝ) : ℂ) *
                ∏ i ∈ J, P i (w i))) / (3 : ℂ) ^ n‖}.ncard : ℝ) / (3 : ℝ) ^ n))
    (hsmall_wt :
      (∑ J ∈ Finset.univ.filter (fun J : Finset (Fin n) => (J.card : ℝ) < δ * (n : ℝ) / 2),
        δ ^ J.card * (1 - δ) ^ (n - J.card)) ≤ γ ^ 2 / 64) :
    (∃ J : Finset (Fin n), δ * (n : ℝ) / 2 ≤ (J.card : ℝ) ∧
      ∃ z : 𝔽₃ n, (A.card : ℝ) / (3 : ℝ) ^ n + γ ^ 2 / 64 ≤
        (∑ w : 𝔽₃ n, if (fun i => if i ∈ J then w i else z i) ∈ A then (1 : ℝ) else 0) / (3 : ℝ) ^ n) ∨
    (∃ J : Finset (Fin n), δ * (n : ℝ) / 2 ≤ (J.card : ℝ) ∧
      ∃ z : 𝔽₃ n,
        (A.card : ℝ) / (3 : ℝ) ^ n - γ / 16 ≤
          (∑ w : 𝔽₃ n, if (fun i => if i ∈ J then w i else z i) ∈ A then (1 : ℝ) else 0) / (3 : ℝ) ^ n ∧
        (∑ w : 𝔽₃ n, if (fun i => if i ∈ J then w i else z i) ∈ A then (1 : ℝ) else 0) / (3 : ℝ) ^ n <
          (A.card : ℝ) / (3 : ℝ) ^ n + γ ^ 2 / 64 ∧
        ∃ P : Fin n → ZMod 3 → ℂ,
          (∀ i, ∑ a : ZMod 3, ‖P i a‖ ^ 2 ≤ 3) ∧
          δ ≤ ‖(∑ w : 𝔽₃ n,
            ((((if (fun i => if i ∈ J then w i else z i) ∈ A then (1 : ℝ) else 0) -
                (A.card : ℝ) / (3 : ℝ) ^ n : ℝ) : ℂ) *
              ∏ i ∈ J, P i (w i))) / (3 : ℂ) ^ n‖) := by
  classical
  let α : ℝ := (A.card : ℝ) / (3 : ℝ) ^ n
  have h3n_pos : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hα_nn : 0 ≤ α := by positivity
  let wt : Finset (Fin n) → ℝ := fun J => δ ^ J.card * (1 - δ) ^ (n - J.card)
  have hwt_nn : ∀ J, 0 ≤ wt J := fun J =>
    mul_nonneg (pow_nonneg (le_of_lt hδ0) _) (pow_nonneg (by linarith) _)
  have hwt_sum : (∑ J : Finset (Fin n), wt J) = 1 := (bernoulli_subset_moments n δ).1
  let BigJ : Finset (Finset (Fin n)) :=
    Finset.univ.filter fun J : Finset (Fin n) => δ * (n : ℝ) / 2 ≤ (J.card : ℝ)
  let SmallJ : Finset (Finset (Fin n)) :=
    Finset.univ.filter fun J : Finset (Fin n) => (J.card : ℝ) < δ * (n : ℝ) / 2
  let densJZ : Finset (Fin n) → 𝔽₃ n → ℝ := fun J z =>
    (∑ w : 𝔽₃ n, if (fun i => if i ∈ J then w i else z i) ∈ A then (1 : ℝ) else 0) / (3 : ℝ) ^ n
  have hdens_avg :
      (∑ J : Finset (Fin n), wt J * ((∑ z : 𝔽₃ n, densJZ J z) / (3 : ℝ) ^ n)) = α := by
    have hinner : ∀ J : Finset (Fin n), (∑ z : 𝔽₃ n, densJZ J z) / (3 : ℝ) ^ n = α := by
      intro J
      dsimp only [densJZ, α]
      rw [← Finset.sum_div, sum_patch_eq J (fun x => if x ∈ A then (1 : ℝ) else 0)]
      have hsumA : (∑ x : 𝔽₃ n, if x ∈ A then (1 : ℝ) else 0) = (A.card : ℝ) := by simp
      rw [hsumA]
      have h3ne : (3 : ℝ) ^ n ≠ 0 := ne_of_gt h3n_pos
      field_simp
    simp only [hinner, ← Finset.sum_mul, hwt_sum, one_mul]
  by_cases hcase1 : ∃ J ∈ BigJ, ∃ z : 𝔽₃ n, α + γ ^ 2 / 64 ≤ densJZ J z
  · obtain ⟨J, hJ, z, hJz⟩ := hcase1
    exact Or.inl ⟨J, (Finset.mem_filter.mp hJ).2, z, hJz⟩
  · right
    push Not at hcase1
    let f : 𝔽₃ n → ℝ := fun x => (if x ∈ A then (1 : ℝ) else 0) - α
    let GoodZ : Finset (Fin n) → Finset (𝔽₃ n) := fun J =>
      Finset.univ.filter fun z : 𝔽₃ n =>
        ∃ P : Fin n → ZMod 3 → ℂ,
          (∀ i, ∑ a : ZMod 3, ‖P i a‖ ^ 2 ≤ 3) ∧
          δ ≤ ‖(∑ w : 𝔽₃ n, ((f (fun i => if i ∈ J then w i else z i) : ℂ) *
            ∏ i ∈ J, P i (w i))) / (3 : ℂ) ^ n‖
    let BadZ : Finset (Fin n) → Finset (𝔽₃ n) := fun J =>
      Finset.univ.filter fun z : 𝔽₃ n => densJZ J z < α - γ / 16
    have hcomp : SmallJ = Finset.univ.filter (fun J : Finset (Fin n) => ¬ δ * (n : ℝ) / 2 ≤ (J.card : ℝ)) := by
      ext J; simp [SmallJ, not_le]
    have hGood_big : 3 * δ / 4 ≤
        ∑ J ∈ BigJ, wt J * ((GoodZ J).card : ℝ) / (3 : ℝ) ^ n := by
      have h1_rew : δ ≤ ∑ J : Finset (Fin n), wt J * (((GoodZ J).card : ℝ) / (3 : ℝ) ^ n) := by
        refine le_trans h1_bound (le_of_eq ?_)
        apply Finset.sum_congr rfl
        intro J _
        dsimp only [wt]
        congr 2
        rw [← Set.ncard_coe_finset (GoodZ J)]
        congr 2
        ext z
        simp [GoodZ, f, α]
      have hpart :
          (∑ J : Finset (Fin n), wt J * (((GoodZ J).card : ℝ) / (3 : ℝ) ^ n)) =
          (∑ J ∈ BigJ, wt J * (((GoodZ J).card : ℝ) / (3 : ℝ) ^ n)) +
          (∑ J ∈ SmallJ, wt J * (((GoodZ J).card : ℝ) / (3 : ℝ) ^ n)) := by
        rw [hcomp]
        exact (Finset.sum_filter_add_sum_filter_not Finset.univ _ _).symm
      have hsmall_good :
          (∑ J ∈ SmallJ, wt J * (((GoodZ J).card : ℝ) / (3 : ℝ) ^ n)) ≤ δ / 4 := by
        calc
          (∑ J ∈ SmallJ, wt J * (((GoodZ J).card : ℝ) / (3 : ℝ) ^ n))
            ≤ ∑ J ∈ SmallJ, wt J * 1 := by
              apply Finset.sum_le_sum
              intro J _
              apply mul_le_mul_of_nonneg_left _ (hwt_nn J)
              have hc : (GoodZ J).card ≤ 3 ^ n := by
                calc (GoodZ J).card ≤ Fintype.card (𝔽₃ n) := Finset.card_le_univ _
                _ = 3 ^ n := card_F3 n
              exact (div_le_one h3n_pos).mpr (by exact_mod_cast hc)
          _ = ∑ J ∈ SmallJ, wt J := by simp
          _ ≤ γ ^ 2 / 64 := hsmall_wt
          _ ≤ δ / 4 := by
              have : γ ^ 2 ≤ δ := by nlinarith only [hγ0, hγ_le_δ, hδ_half]
              linarith only [this, hδ0]
      have hrew : (∑ J ∈ BigJ, wt J * (((GoodZ J).card : ℝ) / (3 : ℝ) ^ n)) =
          ∑ J ∈ BigJ, wt J * ((GoodZ J).card : ℝ) / (3 : ℝ) ^ n := by
        apply Finset.sum_congr rfl; intro J _; ring
      linarith only [h1_rew, hpart, hsmall_good, hrew]
    have hBad_big :
        (∑ J ∈ BigJ, wt J * ((BadZ J).card : ℝ) / (3 : ℝ) ^ n) ≤ γ / 2 := by
      have hzero :
          (∑ J : Finset (Fin n), wt J * ((∑ z : 𝔽₃ n, (densJZ J z - α)) / (3 : ℝ) ^ n)) = 0 := by
        have hstep : ∀ J : Finset (Fin n),
            (∑ z : 𝔽₃ n, (densJZ J z - α)) / (3 : ℝ) ^ n =
            (∑ z : 𝔽₃ n, densJZ J z) / (3 : ℝ) ^ n - α := by
          intro J
          rw [Finset.sum_sub_distrib, sub_div, Finset.sum_const, Finset.card_univ, card_F3,
            nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
          have h3ne : (3 : ℝ) ^ n ≠ 0 := ne_of_gt h3n_pos
          field_simp
        rw [Finset.sum_congr rfl (fun J _ => congrArg (wt J * ·) (hstep J))]
        simp only [mul_sub, Finset.sum_sub_distrib, hdens_avg, ← Finset.sum_mul, hwt_sum,
          one_mul, sub_self]
      have hpart :
          (∑ J : Finset (Fin n), wt J * ((∑ z : 𝔽₃ n, (densJZ J z - α)) / (3 : ℝ) ^ n)) =
          (∑ J ∈ BigJ, wt J * ((∑ z : 𝔽₃ n, (densJZ J z - α)) / (3 : ℝ) ^ n)) +
          (∑ J ∈ SmallJ, wt J * ((∑ z : 𝔽₃ n, (densJZ J z - α)) / (3 : ℝ) ^ n)) := by
        rw [hcomp]
        exact (Finset.sum_filter_add_sum_filter_not Finset.univ _ _).symm
      have hsmall_up :
          (∑ J ∈ SmallJ, wt J * ((∑ z : 𝔽₃ n, (densJZ J z - α)) / (3 : ℝ) ^ n)) ≤ γ ^ 2 / 64 := by
        calc
          (∑ J ∈ SmallJ, wt J * ((∑ z : 𝔽₃ n, (densJZ J z - α)) / (3 : ℝ) ^ n))
            ≤ ∑ J ∈ SmallJ, wt J * 1 := by
              apply Finset.sum_le_sum
              intro J _
              apply mul_le_mul_of_nonneg_left _ (hwt_nn J)
              rw [div_le_one h3n_pos]
              calc
                (∑ z : 𝔽₃ n, (densJZ J z - α)) ≤ ∑ _z : 𝔽₃ n, (1 : ℝ) := by
                  apply Finset.sum_le_sum
                  intro z _
                  have hd1 : densJZ J z ≤ 1 := by
                    dsimp only [densJZ]
                    rw [div_le_one h3n_pos]
                    calc
                      (∑ w : 𝔽₃ n, if (fun i => if i ∈ J then w i else z i) ∈ A then (1 : ℝ) else 0)
                        ≤ ∑ _w : 𝔽₃ n, (1 : ℝ) := Finset.sum_le_sum (fun w _ => by split_ifs <;> norm_num)
                      _ = (3 : ℝ) ^ n := by simp
                  linarith only [hd1, hα_nn]
                _ = (3 : ℝ) ^ n := by simp
          _ = ∑ J ∈ SmallJ, wt J := by simp
          _ ≤ γ ^ 2 / 64 := hsmall_wt
      have hbig_up :
          (∑ J ∈ BigJ, wt J * ((∑ z : 𝔽₃ n, (densJZ J z - α)) / (3 : ℝ) ^ n)) ≤
          γ ^ 2 / 64 - (γ / 16) * (∑ J ∈ BigJ, wt J * ((BadZ J).card : ℝ) / (3 : ℝ) ^ n) := by
        have hJ_bound : ∀ J ∈ BigJ,
            (∑ z : 𝔽₃ n, (densJZ J z - α)) / (3 : ℝ) ^ n ≤
            γ ^ 2 / 64 - (γ / 16) * (((BadZ J).card : ℝ) / (3 : ℝ) ^ n) := by
          intro J hJ
          have hpartz :
              (∑ z : 𝔽₃ n, (densJZ J z - α)) =
              (∑ z ∈ BadZ J, (densJZ J z - α)) +
              (∑ z ∈ Finset.univ.filter (fun z : 𝔽₃ n => ¬ densJZ J z < α - γ / 16), (densJZ J z - α)) :=
            (Finset.sum_filter_add_sum_filter_not Finset.univ _ _).symm
          have hbadz : (∑ z ∈ BadZ J, (densJZ J z - α)) ≤ -(γ / 16) * ((BadZ J).card : ℝ) := by
            calc
              (∑ z ∈ BadZ J, (densJZ J z - α)) ≤ ∑ _z ∈ BadZ J, -(γ / 16) := by
                apply Finset.sum_le_sum
                intro z hz
                have hlt := (Finset.mem_filter.mp hz).2
                linarith only [hlt]
              _ = -(γ / 16) * ((BadZ J).card : ℝ) := by
                rw [Finset.sum_const, nsmul_eq_mul]; ring
          have hgoodz :
              (∑ z ∈ Finset.univ.filter (fun z : 𝔽₃ n => ¬ densJZ J z < α - γ / 16),
                (densJZ J z - α)) ≤ (γ ^ 2 / 64) * (3 : ℝ) ^ n := by
            calc
              (∑ z ∈ Finset.univ.filter (fun z : 𝔽₃ n => ¬ densJZ J z < α - γ / 16),
                (densJZ J z - α))
                ≤ ∑ _z ∈ Finset.univ.filter (fun z : 𝔽₃ n => ¬ densJZ J z < α - γ / 16),
                    (γ ^ 2 / 64) := by
                  apply Finset.sum_le_sum
                  intro z _
                  have hlt := hcase1 J hJ z
                  linarith only [hlt]
              _ ≤ ∑ _z : 𝔽₃ n, (γ ^ 2 / 64) :=
                  Finset.sum_le_univ_sum_of_nonneg (fun _ => by positivity)
              _ = (γ ^ 2 / 64) * (3 : ℝ) ^ n := by
                  rw [Finset.sum_const, Finset.card_univ, card_F3, nsmul_eq_mul,
                    Nat.cast_pow, Nat.cast_ofNat, mul_comm]
          rw [hpartz, add_div]
          have h1' : (∑ z ∈ BadZ J, (densJZ J z - α)) / (3 : ℝ) ^ n ≤
              -(γ / 16) * (((BadZ J).card : ℝ) / (3 : ℝ) ^ n) := by
            rw [← mul_div_assoc]
            exact div_le_div_of_nonneg_right hbadz (le_of_lt h3n_pos)
          have h2' : (∑ z ∈ Finset.univ.filter (fun z : 𝔽₃ n => ¬ densJZ J z < α - γ / 16),
              (densJZ J z - α)) / (3 : ℝ) ^ n ≤ γ ^ 2 / 64 := by
            rw [div_le_iff₀ h3n_pos]
            exact hgoodz
          linarith only [h1', h2']
        calc
          (∑ J ∈ BigJ, wt J * ((∑ z : 𝔽₃ n, (densJZ J z - α)) / (3 : ℝ) ^ n))
            ≤ ∑ J ∈ BigJ, wt J * (γ ^ 2 / 64 - (γ / 16) * (((BadZ J).card : ℝ) / (3 : ℝ) ^ n)) :=
              Finset.sum_le_sum (fun J hJ => mul_le_mul_of_nonneg_left (hJ_bound J hJ) (hwt_nn J))
          _ = (γ ^ 2 / 64) * (∑ J ∈ BigJ, wt J) -
              (γ / 16) * (∑ J ∈ BigJ, wt J * ((BadZ J).card : ℝ) / (3 : ℝ) ^ n) := by
              rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro J _; ring
          _ ≤ γ ^ 2 / 64 - (γ / 16) * (∑ J ∈ BigJ, wt J * ((BadZ J).card : ℝ) / (3 : ℝ) ^ n) := by
              have hBig_le1 : (∑ J ∈ BigJ, wt J) ≤ 1 := by
                rw [← hwt_sum]
                exact Finset.sum_le_univ_sum_of_nonneg hwt_nn
              have hpos64 : 0 ≤ γ ^ 2 / 64 := by positivity
              nlinarith only [hBig_le1, hpos64]
      nlinarith only [hzero, hpart, hsmall_up, hbig_up, hγ0]
    have hex_good_not_bad : ∃ J ∈ BigJ, ∃ z : 𝔽₃ n, z ∈ GoodZ J ∧ z ∉ BadZ J := by
      by_contra hno_ex
      push Not at hno_ex
      have hle :
          (∑ J ∈ BigJ, wt J * ((GoodZ J).card : ℝ) / (3 : ℝ) ^ n) ≤
          (∑ J ∈ BigJ, wt J * ((BadZ J).card : ℝ) / (3 : ℝ) ^ n) := by
        apply Finset.sum_le_sum
        intro J hJ
        have hsub : GoodZ J ⊆ BadZ J := fun z hz => hno_ex J hJ z hz
        have hc : ((GoodZ J).card : ℝ) ≤ ((BadZ J).card : ℝ) :=
          Nat.cast_le.mpr (Finset.card_le_card hsub)
        apply div_le_div_of_nonneg_right _ (le_of_lt h3n_pos)
        exact mul_le_mul_of_nonneg_left hc (hwt_nn J)
      linarith only [hGood_big, hBad_big, hle, hγ_le_δ, hδ0]
    obtain ⟨J, hJ, z, hzGood, hzNotBad⟩ := hex_good_not_bad
    have hdens_lo : α - γ / 16 ≤ densJZ J z := by
      simp only [BadZ, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hzNotBad
      exact hzNotBad
    have hdens_hi : densJZ J z < α + γ ^ 2 / 64 := hcase1 J hJ z
    obtain ⟨P, hP_l2, hP_corr⟩ := (Finset.mem_filter.mp hzGood).2
    exact ⟨J, (Finset.mem_filter.mp hJ).2, z, hdens_lo, hdens_hi, P, hP_l2, hP_corr⟩

/- Combining H1, H2, 3-AP deviation, Bernoulli Chebyshev, subcube dichotomy, and balanced-triple
combinatorial subspace increment into a single clean density-increment step. -/
lemma single_step_density_increment (hH1 : H1) (hH2 : H2) :
    ∃ K : ℝ, 4 ≤ K ∧ ∀ (α₀ : ℝ), 0 < α₀ → α₀ ≤ 1 →
      let γ₀ : ℝ := Real.exp (-(K * α₀ ^ (-K)))
      let η₀ : ℝ := γ₀ ^ 2 / 64
      let D₀ : ℝ := (3000 / γ₀) ^ 6 * (2 / γ₀)
      ∀ (t n : ℕ) (A : Finset (𝔽₃ n)),
        (16 / γ₀ ≤ (t : ℝ)) →
        (2 / α₀ ^ 2 ≤ (2 : ℝ) ^ n) →
        (D₀ * (t : ℝ) ^ 6 + 256 / γ₀ ^ 3 + 2 ≤ (n : ℝ)) →
        α₀ ≤ (A.card : ℝ) / (3 : ℝ) ^ n →
        ¬ Green17.HasRestrictedAP A →
        ∃ (d : ℕ) (B : Finset (𝔽₃ d)),
          t ≤ d ∧ ¬ Green17.HasRestrictedAP B ∧
          (A.card : ℝ) / (3 : ℝ) ^ n + η₀ ≤ (B.card : ℝ) / (3 : ℝ) ^ d := by
  classical
  obtain ⟨C₁, hC₁, h1⟩ := hH1
  obtain ⟨C₂, hC₂, h2⟩ := hH2
  let K : ℝ := max 4 (C₁ * C₂ * (4 : ℝ) ^ C₁ + 3 * C₁ + 1)
  have hK4 : 4 ≤ K := le_max_left _ _
  refine ⟨K, hK4, ?_⟩
  intro α₀ hα₀ hα₀1 γ₀ η₀ D₀ t n A ht_lo h2n hn_lo hdens hno
  let α : ℝ := (A.card : ℝ) / (3 : ℝ) ^ n
  have h3n_pos : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hα_pos : 0 < α := lt_of_lt_of_le hα₀ hdens
  have hα_le1 : α ≤ 1 := by
    have hc : A.card ≤ 3 ^ n := by
      calc A.card ≤ Fintype.card (𝔽₃ n) := Finset.card_le_univ A
      _ = 3 ^ n := card_F3 n
    exact (div_le_one h3n_pos).mpr (by exact_mod_cast hc)
  have h2n_α : 2 / α ^ 2 ≤ (2 : ℝ) ^ n := by
    have hsq : α₀ ^ 2 ≤ α ^ 2 := by nlinarith
    have hdiv : 2 / α ^ 2 ≤ 2 / α₀ ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq
    exact le_trans hdiv h2n
  obtain ⟨g, h, hg, hh, hcorr⟩ := three_ap_correlation_of_not_hasRestrictedAP A hno hα_pos h2n_α
  let ε : ℝ := α ^ 3 / 4
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by
    have : α ^ 3 ≤ 1 := by nlinarith
    dsimp only [ε]; linarith
  obtain ⟨δ, hδ_exp, hδ_half, h1_apply⟩ := h1 ε hε0 hε1
  have hδ0 : 0 < δ := lt_of_lt_of_le (Real.exp_pos _) hδ_exp
  let f : 𝔽₃ n → ℝ := fun x => (if x ∈ A then (1 : ℝ) else 0) - α
  have hf_bdd : ∀ x : 𝔽₃ n, |f x| ≤ 1 := by
    intro x; dsimp only [f]; split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  have h1_bound := h1_apply n f g h hf_bdd hg hh hcorr
  let γ : ℝ := δ ^ C₂
  have hγ0 : 0 < γ := Real.rpow_pos_of_pos hδ0 C₂
  have hγ_le_δ : γ ≤ δ := by
    have h1' : δ ^ C₂ ≤ δ ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hδ0 (by linarith) hC₂
    simpa only [Real.rpow_one] using h1'
  have hγ_half : γ ≤ 1 / 2 := le_trans hγ_le_δ hδ_half
  have hγ₀_le_γ : γ₀ ≤ γ := by
    have hpow : δ ^ C₂ ≥ (Real.exp (-(C₁ * ε ^ (-C₁)))) ^ C₂ :=
      Real.rpow_le_rpow (le_of_lt (Real.exp_pos _)) hδ_exp (by linarith)
    rw [← Real.exp_mul] at hpow
    refine le_trans ?_ hpow
    rw [Real.exp_le_exp]
    have hε_ge : α₀ ^ 3 / 4 ≤ ε := by
      have : α₀ ^ 3 ≤ α ^ 3 := pow_le_pow_left₀ (le_of_lt hα₀) hdens 3
      dsimp only [ε]; linarith
    have hε_rpow : ε ^ (-C₁) ≤ (α₀ ^ 3 / 4) ^ (-C₁) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hε_ge (by linarith)
    have h4eq : (α₀ ^ 3 / 4) ^ (-C₁) = (4 : ℝ) ^ C₁ * α₀ ^ (-(3 * C₁)) := by
      rw [div_eq_mul_inv, Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_natCast α₀ 3, ← Real.rpow_mul (le_of_lt hα₀),
        Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 4), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4),
        inv_inv]
      ring_nf
    have hα_rpow : α₀ ^ (-(3 * C₁)) ≤ α₀ ^ (-K) := by
      apply Real.rpow_le_rpow_of_exponent_ge hα₀ hα₀1
      have hK_ge : 3 * C₁ ≤ K := by
        have h1' : C₁ * C₂ * (4 : ℝ) ^ C₁ + 3 * C₁ + 1 ≤ K := le_max_right _ _
        have hpos1 : 0 ≤ C₁ * C₂ * (4 : ℝ) ^ C₁ := by positivity
        linarith
      linarith
    have hcoef_le : C₁ * (4 : ℝ) ^ C₁ * C₂ ≤ K := by
      have h1' : C₁ * C₂ * (4 : ℝ) ^ C₁ + 3 * C₁ + 1 ≤ K := le_max_right _ _
      linarith
    have hcomb : C₁ * ε ^ (-C₁) * C₂ ≤ K * α₀ ^ (-K) := by
      calc
        C₁ * ε ^ (-C₁) * C₂ ≤ C₁ * ((4 : ℝ) ^ C₁ * α₀ ^ (-(3 * C₁))) * C₂ := by
          have : ε ^ (-C₁) ≤ (4 : ℝ) ^ C₁ * α₀ ^ (-(3 * C₁)) := by rw [← h4eq]; exact hε_rpow
          have hC12 : 0 ≤ C₁ * C₂ := by positivity
          nlinarith
        _ = (C₁ * (4 : ℝ) ^ C₁ * C₂) * α₀ ^ (-(3 * C₁)) := by ring
        _ ≤ K * α₀ ^ (-K) :=
          mul_le_mul hcoef_le hα_rpow (by positivity) (by linarith)
    linarith
  have hγ₀_pos : 0 < γ₀ := Real.exp_pos _
  have hη₀_le : η₀ ≤ γ ^ 2 / 64 := by
    dsimp only [η₀]
    have hsq : γ₀ ^ 2 ≤ γ ^ 2 := pow_le_pow_left₀ (le_of_lt hγ₀_pos) hγ₀_le_γ 2
    linarith only [hsq]
  have hn_pos : 0 < n := by
    have hD0_nn : 0 ≤ D₀ * (t : ℝ) ^ 6 := by positivity
    have h256_nn : 0 ≤ 256 / γ₀ ^ 3 := by positivity
    have h1 : (0 : ℝ) < (n : ℝ) := by linarith only [hn_lo, hD0_nn, h256_nn]
    exact_mod_cast h1
  have hsmall_wt :
      (∑ J ∈ Finset.univ.filter (fun J : Finset (Fin n) => (J.card : ℝ) < δ * (n : ℝ) / 2),
        δ ^ J.card * (1 - δ) ^ (n - J.card)) ≤ γ ^ 2 / 64 := by
    have hcheb := bernoulli_subset_tail_bound hn_pos hδ0 (by linarith only [hδ_half])
    have h4 : 4 / (δ * (n : ℝ)) ≤ γ ^ 2 / 64 := by
      have hδn_pos : 0 < δ * (n : ℝ) := mul_pos hδ0 (Nat.cast_pos.mpr hn_pos)
      rw [div_le_div_iff₀ hδn_pos (by norm_num : (0 : ℝ) < 64)]
      have h256 : 256 / γ₀ ^ 3 ≤ (n : ℝ) := by
        have hD0_nn : 0 ≤ D₀ * (t : ℝ) ^ 6 := by positivity
        linarith only [hn_lo, hD0_nn]
      have hγ3 : γ₀ ^ 3 ≤ δ * γ ^ 2 := by
        have h1' : γ₀ ^ 2 ≤ γ ^ 2 := pow_le_pow_left₀ (le_of_lt hγ₀_pos) hγ₀_le_γ 2
        have h2' : γ₀ ≤ δ := le_trans hγ₀_le_γ hγ_le_δ
        calc γ₀ ^ 3 = γ₀ * γ₀ ^ 2 := by ring
        _ ≤ δ * γ ^ 2 := mul_le_mul h2' h1' (sq_nonneg γ₀) (le_of_lt hδ0)
      have hstep : 256 ≤ (n : ℝ) * γ₀ ^ 3 := (div_le_iff₀ (by positivity)).mp h256
      have hstep2 : (n : ℝ) * γ₀ ^ 3 ≤ (n : ℝ) * (δ * γ ^ 2) :=
        mul_le_mul_of_nonneg_left hγ3 (Nat.cast_nonneg n)
      linarith only [hstep, hstep2]
    exact le_trans hcheb h4
  rcases bernoulli_subcube_dichotomy A hδ0 hδ_half hγ0 hγ_le_δ h1_bound hsmall_wt with
      ⟨J, hJge, z, hJz⟩ | ⟨J, hJge, z, hdens_lo, hdens_hi, P, hP_l2, hP_corr⟩
  · obtain ⟨blk, z₀, _, hblk_surj, _, hdens_eq⟩ := subcube_to_combSubspace J z A
    let B : Finset (𝔽₃ J.card) := Finset.univ.filter fun y : 𝔽₃ J.card =>
      (fun i : Fin n => match blk i with | some l => z₀ i + y l | none => z₀ i) ∈ A
    have hB_no : ¬ Green17.HasRestrictedAP B := by
      intro hAP
      apply hno
      refine hasRestrictedAP_of_combSubspace blk hblk_surj z₀ A B ?_ hAP
      intro y hy
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      refine Eq.mpr (congrArg (· ∈ A) ?_) hy
      funext i
      cases blk i <;> rfl
    have hJ_ge_t : t ≤ J.card := by
      have hD0_ge : (2 / γ₀) * (t : ℝ) ≤ (n : ℝ) := by
        have hγ₀_half : γ₀ ≤ 1 / 2 := le_trans hγ₀_le_γ hγ_half
        have ht1 : (1 : ℝ) ≤ (t : ℝ) := by
          have : (32 : ℝ) ≤ 16 / γ₀ := by
            rw [le_div_iff₀ hγ₀_pos]; linarith only [hγ₀_half]
          linarith only [this, ht_lo]
        have h3000 : (1 : ℝ) ≤ (3000 / γ₀) ^ 6 := by
          have : (1 : ℝ) ≤ 3000 / γ₀ := by
            rw [le_div_iff₀ hγ₀_pos]; linarith only [hγ₀_half]
          exact one_le_pow₀ this
        have ht6 : (t : ℝ) ≤ (t : ℝ) ^ 6 := by
          calc (t : ℝ) = (t : ℝ) ^ 1 := (pow_one _).symm
          _ ≤ (t : ℝ) ^ 6 := pow_le_pow_right₀ ht1 (by norm_num)
        have hstep : (2 / γ₀) * (t : ℝ) ≤ D₀ * (t : ℝ) ^ 6 := by
          dsimp only [D₀]
          have h2g : 0 ≤ 2 / γ₀ := by positivity
          have h1' : 2 / γ₀ ≤ (3000 / γ₀) ^ 6 * (2 / γ₀) := by nlinarith only [h3000, h2g]
          exact mul_le_mul h1' ht6 (by positivity) (by positivity)
        have h256_nn : 0 ≤ 256 / γ₀ ^ 3 := by positivity
        linarith only [hstep, h256_nn, hn_lo]
      have hR : (t : ℝ) ≤ (J.card : ℝ) := by
        have h1' : (t : ℝ) ≤ γ₀ * (n : ℝ) / 2 := by
          have hmul := mul_le_mul_of_nonneg_left hD0_ge (le_of_lt hγ₀_pos)
          have hc : γ₀ * (2 / γ₀ * (t : ℝ)) = 2 * (t : ℝ) := by field_simp
          linarith only [hmul, hc]
        have h2' : γ₀ * (n : ℝ) / 2 ≤ δ * (n : ℝ) / 2 := by
          have hγδ : γ₀ ≤ δ := le_trans hγ₀_le_γ hγ_le_δ
          have hmul := mul_le_mul_of_nonneg_right hγδ (Nat.cast_nonneg n)
          linarith only [hmul]
        linarith only [h1', h2', hJge]
      exact_mod_cast hR
    refine ⟨J.card, B, hJ_ge_t, hB_no, ?_⟩
    rw [← hdens_eq]
    have hJz' : α + γ ^ 2 / 64 ≤
        (∑ w : 𝔽₃ n, if (fun i => if i ∈ J then w i else z i) ∈ A then (1 : ℝ) else 0) / (3 : ℝ) ^ n := hJz
    linarith only [hη₀_le, hJz']
  · obtain ⟨blk₁, z₁, e, hblk₁_surj, hφ₁_eq, hdens_eq⟩ := subcube_to_combSubspace J z A
    let m : ℕ := J.card
    let A' : Finset (𝔽₃ m) := Finset.univ.filter fun y : 𝔽₃ m =>
      (fun i : Fin n => match blk₁ i with | some l => z₁ i + y l | none => z₁ i) ∈ A
    have hα'_eq : (A'.card : ℝ) / (3 : ℝ) ^ m =
        (∑ w : 𝔽₃ n, if (fun i => if i ∈ J then w i else z i) ∈ A then (1 : ℝ) else 0) / (3 : ℝ) ^ n :=
      hdens_eq.symm
    let fJ : 𝔽₃ m → ℝ := fun y => (if y ∈ A' then (1 : ℝ) else 0) - α
    have hfJ_eq : ∀ y : 𝔽₃ m,
        f (fun i => if hi : i ∈ J then y (e.symm ⟨i, hi⟩) else z i) = fJ y := by
      intro y
      dsimp only [f, fJ, A']
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hvec : (fun i : Fin n => if hi : i ∈ J then y (e.symm ⟨i, hi⟩) else z i) =
          (fun i : Fin n => match blk₁ i with | some l => z₁ i + y l | none => z₁ i) :=
        funext (fun i => (hφ₁_eq y i).symm)
      rw [hvec]
    have hPJ_corr : δ ≤ ‖(∑ y : 𝔽₃ m, (fJ y : ℂ) * ∏ j : Fin m, P (e j).1 (y j)) / (3 : ℂ) ^ m‖ := by
      have htrans := sum_patch_prod_eq J z e f P
      simp only [hfJ_eq] at htrans
      rw [← htrans]
      exact hP_corr
    have hfJ_bdd : ∀ y : 𝔽₃ m, |fJ y| ≤ 1 := by
      intro y; rw [← hfJ_eq y]; exact hf_bdd _
    obtain ⟨Q, hQ_bdd, hQ_corr⟩ :=
      h2 m fJ (fun j => P (e j).1) δ hδ0 hδ_half hfJ_bdd (fun j => hP_l2 (e j).1) hPJ_corr
    have hQ_recentered :
        7 * γ / 8 ≤ ‖(∑ y : 𝔽₃ m,
          (((if y ∈ A' then (1 : ℝ) else 0) - (A'.card : ℝ) / (3 : ℝ) ^ m : ℝ) : ℂ) *
            ∏ j : Fin m, Q j (y j)) / (3 : ℂ) ^ m‖ := by
      have h3m_pos : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
      have hnorm3m : ‖(3 : ℂ) ^ m‖ = (3 : ℝ) ^ m := by
        rw [norm_pow, Complex.norm_ofNat]
      have hdiff_α : |(A'.card : ℝ) / (3 : ℝ) ^ m - α| ≤ γ / 16 := by
        rw [hα'_eq, abs_le]
        have hsq : γ ^ 2 / 64 ≤ γ / 16 := by nlinarith only [hγ0, hγ_half]
        constructor <;> linarith only [hdens_lo, hdens_hi, hsq]
      have hsplit_sum :
          (∑ y : 𝔽₃ m, (fJ y : ℂ) * ∏ j : Fin m, Q j (y j)) / (3 : ℂ) ^ m -
          (∑ y : 𝔽₃ m,
            (((if y ∈ A' then (1 : ℝ) else 0) - (A'.card : ℝ) / (3 : ℝ) ^ m : ℝ) : ℂ) *
              ∏ j : Fin m, Q j (y j)) / (3 : ℂ) ^ m =
          (((A'.card : ℝ) / (3 : ℝ) ^ m - α : ℝ) : ℂ) *
            ((∑ y : 𝔽₃ m, ∏ j : Fin m, Q j (y j)) / (3 : ℂ) ^ m) := by
        rw [← sub_div, ← Finset.sum_sub_distrib, ← mul_div_assoc, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro y _
        dsimp only [fJ]
        push_cast
        ring
      have hnorm_diff :
          ‖(((A'.card : ℝ) / (3 : ℝ) ^ m - α : ℝ) : ℂ) *
            ((∑ y : 𝔽₃ m, ∏ j : Fin m, Q j (y j)) / (3 : ℂ) ^ m)‖ ≤ γ / 16 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_div, hnorm3m]
        have havgQ : ‖∑ y : 𝔽₃ m, ∏ j : Fin m, Q j (y j)‖ / (3 : ℝ) ^ m ≤ 1 := by
          rw [div_le_one h3m_pos]
          calc
            ‖∑ y : 𝔽₃ m, ∏ j : Fin m, Q j (y j)‖ ≤ ∑ y : 𝔽₃ m, ‖∏ j : Fin m, Q j (y j)‖ :=
              norm_sum_le _ _
            _ ≤ ∑ _y : 𝔽₃ m, (1 : ℝ) := by
              apply Finset.sum_le_sum
              intro y _
              rw [norm_prod]
              exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun j _ => hQ_bdd j (y j))
            _ = (3 : ℝ) ^ m := by simp
        calc
          |(A'.card : ℝ) / (3 : ℝ) ^ m - α| * (‖∑ y : 𝔽₃ m, ∏ j : Fin m, Q j (y j)‖ / (3 : ℝ) ^ m)
            ≤ (γ / 16) * 1 :=
              mul_le_mul hdiff_α havgQ (div_nonneg (norm_nonneg _) (le_of_lt h3m_pos)) (by linarith only [hγ0])
          _ = γ / 16 := mul_one _
      have htri := norm_sub_norm_le
        ((∑ y : 𝔽₃ m, (fJ y : ℂ) * ∏ j : Fin m, Q j (y j)) / (3 : ℂ) ^ m)
        ((∑ y : 𝔽₃ m,
          (((if y ∈ A' then (1 : ℝ) else 0) - (A'.card : ℝ) / (3 : ℝ) ^ m : ℝ) : ℂ) *
            ∏ j : Fin m, Q j (y j)) / (3 : ℂ) ^ m)
      rw [hsplit_sum] at htri
      have hQ_corr' : γ ≤ ‖(∑ y : 𝔽₃ m, (fJ y : ℂ) * ∏ j : Fin m, Q j (y j)) / (3 : ℂ) ^ m‖ := hQ_corr
      linarith only [hQ_corr', htri, hnorm_diff, hγ0]
    have ht_lo_γ : 16 / γ ≤ (t : ℝ) :=
      le_trans (div_le_div_of_nonneg_left (by norm_num) hγ₀_pos hγ₀_le_γ) ht_lo
    have hm_lo_γ : (3000 * (t : ℝ) / γ) ^ 6 ≤ (m : ℝ) := by
      have h3000_le : (3000 * (t : ℝ) / γ) ^ 6 ≤ (3000 * (t : ℝ) / γ₀) ^ 6 := by
        apply pow_le_pow_left₀ (by positivity)
        exact div_le_div_of_nonneg_left (by positivity) hγ₀_pos hγ₀_le_γ
      have hD0_le_n : (3000 / γ₀) ^ 6 * (2 / γ₀) * (t : ℝ) ^ 6 ≤ (n : ℝ) := by
        have h256_nn : 0 ≤ 256 / γ₀ ^ 3 := by positivity
        dsimp only [D₀] at hn_lo
        linarith only [h256_nn, hn_lo]
      have hstep : (3000 * (t : ℝ) / γ₀) ^ 6 ≤ γ₀ * (n : ℝ) / 2 := by
        have hmul := mul_le_mul_of_nonneg_left hD0_le_n (le_of_lt hγ₀_pos)
        have hcancel : γ₀ * ((3000 / γ₀) ^ 6 * (2 / γ₀) * (t : ℝ) ^ 6) =
            2 * (3000 * (t : ℝ) / γ₀) ^ 6 := by
          have hne : γ₀ ≠ 0 := ne_of_gt hγ₀_pos
          field_simp
        linarith only [hmul, hcancel]
      have hγδ : γ₀ * (n : ℝ) / 2 ≤ δ * (n : ℝ) / 2 := by
        have hle' : γ₀ ≤ δ := le_trans hγ₀_le_γ hγ_le_δ
        have hmul := mul_le_mul_of_nonneg_right hle' (Nat.cast_nonneg n)
        linarith only [hmul]
      linarith only [h3000_le, hstep, hγδ, hJge]
    obtain ⟨d, blk₂, z₂, hd_ge, hblk₂_surj, hdens_boost⟩ :=
      product_corr_to_combSubspace_increment A' Q hγ0 hγ_half hQ_bdd hQ_recentered ht_lo_γ hm_lo_γ
    obtain ⟨blk, z₀, hblk_surj, hcomp_eq⟩ :=
      combSubspace_comp blk₂ hblk₂_surj z₂ blk₁ hblk₁_surj z₁
    let B : Finset (𝔽₃ d) := Finset.univ.filter fun w : 𝔽₃ d =>
      (fun i : Fin n => match blk i with | some l => z₀ i + w l | none => z₀ i) ∈ A
    have hB_eq : B = Finset.univ.filter fun w : 𝔽₃ d =>
        (fun j : Fin m => match blk₂ j with | some l => z₂ j + w l | none => z₂ j) ∈ A' := by
      ext w
      simp only [B, A', Finset.mem_filter, Finset.mem_univ, true_and]
      have hvec : (fun i : Fin n => match blk i with | some l => z₀ i + w l | none => z₀ i) =
          (fun i : Fin n => match blk₁ i with
            | some j => z₁ i + (match blk₂ j with | some l => z₂ j + w l | none => z₂ j)
            | none => z₁ i) := by
        funext i
        have hc := hcomp_eq w i
        cases h1 : blk i <;> cases h2 : blk₁ i
        · simpa only [h1, h2] using hc
        · rename_i j; cases h3 : blk₂ j <;> simpa only [h1, h2, h3] using hc
        · simpa only [h1, h2] using hc
        · rename_i j; cases h3 : blk₂ j <;> simpa only [h1, h2, h3] using hc
      rw [hvec]
    have hB_no : ¬ Green17.HasRestrictedAP B := by
      intro hAP
      apply hno
      refine hasRestrictedAP_of_combSubspace blk hblk_surj z₀ A B ?_ hAP
      intro y hy
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      refine Eq.mpr (congrArg (· ∈ A) ?_) hy
      funext i
      cases blk i <;> rfl
    refine ⟨d, B, hd_ge, hB_no, ?_⟩
    rw [hB_eq]
    have hboost2 : α + η₀ ≤ (A'.card : ℝ) / (3 : ℝ) ^ m + γ / 4 := by
      rw [hα'_eq]
      have hsq : γ ^ 2 / 64 ≤ 3 * γ / 16 := by nlinarith only [hγ0, hγ_half]
      linarith only [hdens_lo, hη₀_le, hsq]
    exact le_trans hboost2 hdens_boost

/- ============================================================================
   Part 6: Multi-Step Density Increment & Triple-Logarithmic Asymptotics
   ============================================================================ -/

/- Elementary exponential dominance: 1 + x <= exp x and x <= exp x for all x in R. -/
lemma real_le_exp (x : ℝ) : x ≤ Real.exp x := by
  have := Real.add_one_le_exp x
  linarith

/- Iterated power recurrence: if a 0 <= R and a (s + 1) <= R * (a s)^6 with 1 <= R,
then a s <= R ^ (7 ^ s). -/
lemma iterated_pow6_le {R : ℝ} (hR : 1 ≤ R) (a : ℕ → ℝ) (h0 : a 0 ≤ R)
    (hstep : ∀ s, 0 ≤ a s ∧ a (s + 1) ≤ R * (a s) ^ 6) :
    ∀ s : ℕ, a s ≤ R ^ (7 ^ s) := by
  intro s
  induction s with
  | zero => simpa using h0
  | succ s ih =>
    have hpow6 : (a s) ^ 6 ≤ (R ^ (7 ^ s)) ^ 6 :=
      pow_le_pow_left₀ (hstep s).1 ih 6
    have hexp : 6 * 7 ^ s + 1 ≤ 7 ^ (s + 1) := by
      have : 7 ^ (s + 1) = 7 * 7 ^ s := by rw [pow_succ, mul_comm]
      have hpos : 1 ≤ 7 ^ s := Nat.one_le_pow s 7 (by omega)
      omega
    calc
      a (s + 1) ≤ R * (a s) ^ 6 := (hstep s).2
      _ ≤ R * (R ^ (7 ^ s)) ^ 6 := mul_le_mul_of_nonneg_left hpow6 (by linarith)
      _ = R ^ (6 * 7 ^ s + 1) := by rw [← pow_mul, mul_comm (7 ^ s) 6, pow_succ']
      _ ≤ R ^ (7 ^ (s + 1)) := pow_le_pow_right₀ hR hexp

/- Quantitative triple-logarithmic dimension inversion: iterating the 6th-power dimension
recurrence S = ceil(1/eta0) + 1 times stays below n when alpha0 = (400*K / log log log n)^(1/K). -/
lemma triple_log_dim_bound {K α₀ L n : ℝ} {t₀ S : ℕ} {dimReq : ℕ → ℕ}
    (hK4 : 4 ≤ K) (hα₀_pos : 0 < α₀) (hα₀_le1 : α₀ ≤ 1)
    (hα₀_powK : 4 * (100 * K) * α₀ ^ (-K) = L)
    (hn_big : Real.exp (Real.exp (Real.exp (4 * (100 * K)))) < n)
    (hlog1 : Real.exp (Real.exp (4 * (100 * K))) < Real.log n)
    (hlog2 : Real.exp (4 * (100 * K)) < Real.log (Real.log n))
    (hL_eq : L = Real.log (Real.log (Real.log n)))
    (ht₀_eq : t₀ = Nat.ceil (16 / Real.exp (-(K * α₀ ^ (-K)))) + Nat.ceil (2 / α₀ ^ 2) + 10)
    (hS_eq : S = Nat.ceil (1 / (Real.exp (-(K * α₀ ^ (-K))) ^ 2 / 64)) + 1)
    (hdim0 : dimReq 0 = t₀)
    (hdim_succ : ∀ s, dimReq (s + 1) =
      Nat.ceil (((3000 / Real.exp (-(K * α₀ ^ (-K)))) ^ 6 *
        (2 / Real.exp (-(K * α₀ ^ (-K))))) * (dimReq s : ℝ) ^ 6 +
        256 / Real.exp (-(K * α₀ ^ (-K))) ^ 3 + 2) + 1)
    (hdim_mono : ∀ s, t₀ ≤ dimReq s) :
    (dimReq S : ℝ) ≤ n := by
  let A_const : ℝ := 100 * K
  let γ₀ : ℝ := Real.exp (-(K * α₀ ^ (-K)))
  let η₀ : ℝ := γ₀ ^ 2 / 64
  let D₀ : ℝ := (3000 / γ₀) ^ 6 * (2 / γ₀)
  let E : ℝ := A_const * α₀ ^ (-K)
  let R : ℝ := Real.exp E
  have hKpos : 0 < K := by linarith only [hK4]
  have hγ₀_pos : 0 < γ₀ := Real.exp_pos _
  have hη₀_pos : 0 < η₀ := by positivity
  have hαK_ge1 : (1 : ℝ) ≤ α₀ ^ (-K) := by
    rw [Real.rpow_neg (le_of_lt hα₀_pos)]
    exact (one_le_inv₀ (Real.rpow_pos_of_pos hα₀_pos K)).mpr
      (Real.rpow_le_one (le_of_lt hα₀_pos) hα₀_le1 (le_of_lt hKpos))
  have hE_ge : 400 ≤ E := by
    dsimp only [E, A_const]
    nlinarith only [hK4, hαK_ge1]
  have hR1 : 1 ≤ R := Real.one_le_exp (by linarith only [hE_ge])
  have hγ₀_inv : 1 / γ₀ = Real.exp (K * α₀ ^ (-K)) := by
    dsimp only [γ₀]
    rw [one_div, ← Real.exp_neg, neg_neg]
  have ht₀_eq' : t₀ = Nat.ceil (16 / γ₀) + Nat.ceil (2 / α₀ ^ 2) + 10 := ht₀_eq
  have hS_eq' : S = Nat.ceil (1 / η₀) + 1 := hS_eq
  have hdim_succ' : ∀ s, dimReq (s + 1) =
      Nat.ceil (D₀ * (dimReq s : ℝ) ^ 6 + 256 / γ₀ ^ 3 + 2) + 1 := hdim_succ
  have hS_le : (S : ℝ) ≤ Real.exp E := by
    have h1 : (S : ℝ) ≤ 1 / η₀ + 2 := by
      rw [hS_eq']
      have hc : (Nat.ceil (1 / η₀) : ℝ) < 1 / η₀ + 1 := Nat.ceil_lt_add_one (by positivity)
      have hcast : ((Nat.ceil (1 / η₀) + 1 : ℕ) : ℝ) = (Nat.ceil (1 / η₀) : ℝ) + 1 := by
        push_cast; rfl
      linarith only [hc, hcast]
    have h2 : 1 / η₀ = 64 * Real.exp (2 * (K * α₀ ^ (-K))) := by
      dsimp only [η₀]
      have hsq : γ₀ ^ 2 = Real.exp (-(2 * (K * α₀ ^ (-K)))) := by
        dsimp only [γ₀]
        rw [sq, ← Real.exp_add]
        congr 1; ring
      rw [hsq, one_div, inv_div, div_eq_mul_inv, ← Real.exp_neg, neg_neg]
    have h3 : 1 / η₀ + 2 ≤ 66 * Real.exp (2 * (K * α₀ ^ (-K))) := by
      have hexp1 : (1 : ℝ) ≤ Real.exp (2 * (K * α₀ ^ (-K))) :=
        Real.one_le_exp (by positivity)
      linarith only [h2, hexp1]
    have h66 : (66 : ℝ) ≤ Real.exp 5 := by
      have he1 : (5 / 2 : ℝ) ≤ Real.exp 1 := by
        have := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) 4
        simp [Finset.sum_range_succ, Nat.factorial] at this
        linarith only [this]
      calc (66 : ℝ) ≤ (5 / 2 : ℝ) ^ 5 := by norm_num
      _ ≤ (Real.exp 1) ^ 5 := pow_le_pow_left₀ (by norm_num) he1 5
      _ = Real.exp 5 := by rw [← Real.exp_nat_mul]; norm_num
    have hcomb : 66 * Real.exp (2 * (K * α₀ ^ (-K))) ≤ Real.exp E := by
      calc
        66 * Real.exp (2 * (K * α₀ ^ (-K)))
          ≤ Real.exp 5 * Real.exp (2 * (K * α₀ ^ (-K))) :=
            mul_le_mul_of_nonneg_right h66 (le_of_lt (Real.exp_pos _))
        _ = Real.exp (5 + 2 * (K * α₀ ^ (-K))) := (Real.exp_add _ _).symm
        _ ≤ Real.exp E := by
            rw [Real.exp_le_exp]
            dsimp only [E, A_const]
            nlinarith only [hK4, hαK_ge1]
    linarith only [h1, h3, hcomb]
  have ht0_le_R : (t₀ : ℝ) ≤ R := by
    have hα2 : 2 / α₀ ^ 2 ≤ 2 * α₀ ^ (-K) := by
      have h1' : α₀ ^ (-2 : ℝ) ≤ α₀ ^ (-K) :=
        Real.rpow_le_rpow_of_exponent_ge hα₀_pos hα₀_le1 (by linarith only [hK4])
      have h2' : α₀ ^ (-2 : ℝ) = (α₀ ^ 2)⁻¹ := by
        rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num,
          Real.rpow_neg (le_of_lt hα₀_pos), Real.rpow_natCast]
      rw [div_eq_mul_inv, ← h2']
      linarith only [h1']
    have hα_exp : 2 * α₀ ^ (-K) ≤ 2 * Real.exp (K * α₀ ^ (-K)) := by
      have hex := real_le_exp (K * α₀ ^ (-K))
      have h1' : α₀ ^ (-K) ≤ K * α₀ ^ (-K) := by nlinarith only [hK4, hαK_ge1]
      linarith only [hex, h1']
    have ht0_est : (t₀ : ℝ) ≤ 18 * Real.exp (K * α₀ ^ (-K)) + 12 := by
      rw [ht₀_eq']
      have h1' : (Nat.ceil (16 / γ₀) : ℝ) < 16 / γ₀ + 1 := Nat.ceil_lt_add_one (by positivity)
      have h2' : (Nat.ceil (2 / α₀ ^ 2) : ℝ) < 2 / α₀ ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
      have h16 : 16 / γ₀ = 16 * Real.exp (K * α₀ ^ (-K)) := by
        rw [div_eq_mul_inv, ← one_div, hγ₀_inv]
      have hcast : ((Nat.ceil (16 / γ₀) + Nat.ceil (2 / α₀ ^ 2) + 10 : ℕ) : ℝ) =
          (Nat.ceil (16 / γ₀) : ℝ) + (Nat.ceil (2 / α₀ ^ 2) : ℝ) + 10 := by push_cast; rfl
      linarith only [h1', h2', h16, hcast, hα2, hα_exp]
    have h30 : (30 : ℝ) ≤ Real.exp 5 := by
      have he1 : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ); linarith only [this]
      calc (30 : ℝ) ≤ (2 : ℝ) ^ 5 := by norm_num
      _ ≤ (Real.exp 1) ^ 5 := pow_le_pow_left₀ (by norm_num) he1 5
      _ = Real.exp 5 := by rw [← Real.exp_nat_mul]; norm_num
    have hexp1 : (1 : ℝ) ≤ Real.exp (K * α₀ ^ (-K)) := Real.one_le_exp (by positivity)
    calc
      (t₀ : ℝ) ≤ 30 * Real.exp (K * α₀ ^ (-K)) := by linarith only [ht0_est, hexp1]
      _ ≤ Real.exp 5 * Real.exp (K * α₀ ^ (-K)) :=
        mul_le_mul_of_nonneg_right h30 (le_of_lt (Real.exp_pos _))
      _ = Real.exp (5 + K * α₀ ^ (-K)) := (Real.exp_add _ _).symm
      _ ≤ Real.exp E := by
        rw [Real.exp_le_exp]
        dsimp only [E, A_const]; nlinarith only [hK4, hαK_ge1]
  have hD0_eq : D₀ = 2 * (3000 : ℝ) ^ 6 * Real.exp (7 * (K * α₀ ^ (-K))) := by
    dsimp only [D₀]
    have h6 : (3000 / γ₀) ^ 6 = (3000 : ℝ) ^ 6 * (1 / γ₀) ^ 6 := by
      rw [div_eq_mul_inv, mul_pow, one_div]
    have h1 : 2 / γ₀ = 2 * (1 / γ₀) := by rw [div_eq_mul_inv, one_div]
    rw [h6, h1, hγ₀_inv, ← Real.exp_nat_mul]
    have hmul : Real.exp (6 * (K * α₀ ^ (-K))) * Real.exp (K * α₀ ^ (-K)) =
        Real.exp (7 * (K * α₀ ^ (-K))) := by
      rw [← Real.exp_add]; congr 1; ring
    calc
      (3000 : ℝ) ^ 6 * Real.exp (↑6 * (K * α₀ ^ (-K))) * (2 * Real.exp (K * α₀ ^ (-K)))
        = 2 * (3000 : ℝ) ^ 6 * (Real.exp (6 * (K * α₀ ^ (-K))) * Real.exp (K * α₀ ^ (-K))) := by
          ring
      _ = 2 * (3000 : ℝ) ^ 6 * Real.exp (7 * (K * α₀ ^ (-K))) := by rw [hmul]
  have hcoef_le_R : D₀ + 256 / γ₀ ^ 3 + 4 ≤ R := by
    have h256 : 256 / γ₀ ^ 3 ≤ 256 * Real.exp (7 * (K * α₀ ^ (-K))) := by
      have h3 : 256 / γ₀ ^ 3 = 256 * Real.exp (3 * (K * α₀ ^ (-K))) := by
        rw [div_eq_mul_inv, ← inv_pow, ← one_div, hγ₀_inv, ← Real.exp_nat_mul]
        push_cast; rfl
      rw [h3]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [Real.exp_le_exp]
      have hnn : 0 ≤ K * α₀ ^ (-K) := by positivity
      linarith only [hnn]
    have h4 : (4 : ℝ) ≤ 4 * Real.exp (7 * (K * α₀ ^ (-K))) := by
      have h1' := Real.one_le_exp (by positivity : 0 ≤ 7 * (K * α₀ ^ (-K)))
      linarith only [h1']
    have hC_num : 2 * (3000 : ℝ) ^ 6 + 260 ≤ Real.exp 80 := by
      have he2 : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ); linarith only [this]
      calc
        2 * (3000 : ℝ) ^ 6 + 260 ≤ (2 : ℝ) ^ 80 := by norm_num
        _ ≤ (Real.exp 1) ^ 80 := pow_le_pow_left₀ (by norm_num) he2 80
        _ = Real.exp 80 := by rw [← Real.exp_nat_mul]; norm_num
    calc
      D₀ + 256 / γ₀ ^ 3 + 4
        ≤ (2 * (3000 : ℝ) ^ 6 + 260) * Real.exp (7 * (K * α₀ ^ (-K))) := by
          rw [hD0_eq]; linarith only [h256, h4]
      _ ≤ Real.exp 80 * Real.exp (7 * (K * α₀ ^ (-K))) :=
          mul_le_mul_of_nonneg_right hC_num (le_of_lt (Real.exp_pos _))
      _ = Real.exp (80 + 7 * (K * α₀ ^ (-K))) := (Real.exp_add _ _).symm
      _ ≤ Real.exp E := by
          rw [Real.exp_le_exp]
          dsimp only [E, A_const]; nlinarith only [hK4, hαK_ge1]
  have hstep_R : ∀ s : ℕ, 0 ≤ (dimReq s : ℝ) ∧ (dimReq (s + 1) : ℝ) ≤ R * (dimReq s : ℝ) ^ 6 := by
    intro s
    refine ⟨Nat.cast_nonneg _, ?_⟩
    have hprev1 : (1 : ℝ) ≤ (dimReq s : ℝ) := by
      have ht1 : 1 ≤ t₀ := by rw [ht₀_eq']; omega
      exact_mod_cast le_trans ht1 (hdim_mono s)
    have hnext_le : (dimReq (s + 1) : ℝ) ≤ D₀ * (dimReq s : ℝ) ^ 6 + 256 / γ₀ ^ 3 + 4 := by
      rw [hdim_succ' s]
      have hc : (Nat.ceil (D₀ * (dimReq s : ℝ) ^ 6 + 256 / γ₀ ^ 3 + 2) : ℝ) <
          D₀ * (dimReq s : ℝ) ^ 6 + 256 / γ₀ ^ 3 + 2 + 1 :=
        Nat.ceil_lt_add_one (by positivity)
      have hcast : ((Nat.ceil (D₀ * (dimReq s : ℝ) ^ 6 + 256 / γ₀ ^ 3 + 2) + 1 : ℕ) : ℝ) =
          (Nat.ceil (D₀ * (dimReq s : ℝ) ^ 6 + 256 / γ₀ ^ 3 + 2) : ℝ) + 1 := by
        push_cast; rfl
      linarith only [hc, hcast]
    have hpow6_ge1 : (1 : ℝ) ≤ (dimReq s : ℝ) ^ 6 := one_le_pow₀ hprev1
    have h256_nn : 0 ≤ 256 / γ₀ ^ 3 + 4 := by positivity
    calc
      (dimReq (s + 1) : ℝ) ≤ D₀ * (dimReq s : ℝ) ^ 6 + (256 / γ₀ ^ 3 + 4) * (dimReq s : ℝ) ^ 6 := by
        nlinarith only [hnext_le, hpow6_ge1, h256_nn]
      _ = (D₀ + 256 / γ₀ ^ 3 + 4) * (dimReq s : ℝ) ^ 6 := by ring
      _ ≤ R * (dimReq s : ℝ) ^ 6 := mul_le_mul_of_nonneg_right hcoef_le_R (by positivity)
  have hdimS : (dimReq S : ℝ) ≤ R ^ (7 ^ S) :=
    iterated_pow6_le hR1 (fun s => (dimReq s : ℝ)) (by rw [hdim0]; exact ht0_le_R) hstep_R S
  have hR7S : R ^ (7 ^ S) ≤ Real.exp (Real.exp (Real.exp (4 * E))) := by
    have h7S : ((7 ^ S : ℕ) : ℝ) ≤ Real.exp (2 * Real.exp E) := by
      have h7_le : (7 : ℝ) ≤ Real.exp 2 := by
        have he1 : (8 / 3 : ℝ) ≤ Real.exp 1 := by
          have := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) 4
          simp [Finset.sum_range_succ, Nat.factorial] at this
          linarith only [this]
        calc (7 : ℝ) ≤ (8 / 3 : ℝ) ^ 2 := by norm_num
        _ ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ (by norm_num) he1 2
        _ = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
      calc
        ((7 ^ S : ℕ) : ℝ) = (7 : ℝ) ^ S := by push_cast; rfl
        _ ≤ (Real.exp 2) ^ S := pow_le_pow_left₀ (by norm_num) h7_le S
        _ = Real.exp ((S : ℝ) * 2) := by rw [← Real.exp_nat_mul]
        _ ≤ Real.exp (2 * Real.exp E) := by
          rw [Real.exp_le_exp]; linarith only [hS_le]
    have hE_mul : E * ((7 ^ S : ℕ) : ℝ) ≤ Real.exp (Real.exp (4 * E)) := by
      have hE_le : E ≤ Real.exp E := real_le_exp E
      have hprod : E * ((7 ^ S : ℕ) : ℝ) ≤ Real.exp (E + 2 * Real.exp E) := by
        calc
          E * ((7 ^ S : ℕ) : ℝ) ≤ Real.exp E * Real.exp (2 * Real.exp E) :=
            mul_le_mul hE_le h7S (by positivity) (le_of_lt (Real.exp_pos _))
          _ = Real.exp (E + 2 * Real.exp E) := (Real.exp_add _ _).symm
      refine le_trans hprod ?_
      rw [Real.exp_le_exp]
      have h3 : E + 2 * Real.exp E ≤ 3 * Real.exp E := by linarith only [hE_le]
      have h3_le : (3 : ℝ) ≤ Real.exp (3 * E) := by
        have h1' := Real.add_one_le_exp (3 * E); linarith only [h1', hE_ge]
      calc
        E + 2 * Real.exp E ≤ 3 * Real.exp E := h3
        _ ≤ Real.exp (3 * E) * Real.exp E :=
          mul_le_mul_of_nonneg_right h3_le (le_of_lt (Real.exp_pos _))
        _ = Real.exp (4 * E) := by rw [← Real.exp_add]; congr 1; ring
    dsimp only [R]
    rw [← Real.exp_nat_mul, mul_comm, Real.exp_le_exp]
    exact hE_mul
  have h4E_eq : 4 * E = L := by
    dsimp only [E, A_const]
    have : 4 * (100 * K * α₀ ^ (-K)) = 4 * (100 * K) * α₀ ^ (-K) := by ring
    rw [this, hα₀_powK]
  have hexp3_eq : Real.exp (Real.exp (Real.exp (4 * E))) = n := by
    rw [h4E_eq, hL_eq]
    rw [Real.exp_log (lt_trans (Real.exp_pos _) hlog2),
      Real.exp_log (lt_trans (Real.exp_pos _) hlog1),
      Real.exp_log (lt_trans (Real.exp_pos _) hn_big)]
  linarith only [hdimS, hR7S, hexp3_eq]

/- Full BKLM Theorem 3 deduction from H1 and H2 via iterated density increment and
triple-logarithmic threshold inversion. -/
theorem main : H1 → H2 → type_of% @Green17.green_17.variants.bklm := by
  intro hH1 hH2
  obtain ⟨K, hK4, hstep_all⟩ := single_step_density_increment hH1 hH2
  let A_const : ℝ := 100 * K
  let c : ℝ := 1 / K
  let C : ℝ := (4 * A_const) ^ c
  have hKpos : 0 < K := by linarith only [hK4]
  have hc0 : 0 < c := by positivity
  have hApos : 0 < A_const := by positivity
  have hC0 : 0 < C := Real.rpow_pos_of_pos (by positivity) c
  refine ⟨c, C, hc0, hC0, ?_⟩
  let N₀ : ℕ := Nat.ceil (Real.exp (Real.exp (Real.exp (4 * A_const)))) + 100
  rw [Filter.eventually_atTop]
  refine ⟨N₀, ?_⟩
  intro n hn A hA_card
  have hn_big : Real.exp (Real.exp (Real.exp (4 * A_const))) < (n : ℝ) := by
    have h1 : Real.exp (Real.exp (Real.exp (4 * A_const))) ≤ (Nat.ceil (Real.exp (Real.exp (Real.exp (4 * A_const)))) : ℝ) :=
      Nat.le_ceil _
    have h2 : (Nat.ceil (Real.exp (Real.exp (Real.exp (4 * A_const)))) : ℝ) < (n : ℝ) := by
      have : Nat.ceil (Real.exp (Real.exp (Real.exp (4 * A_const)))) < n := by omega
      exact_mod_cast this
    linarith only [h1, h2]
  have hlog1 : Real.exp (Real.exp (4 * A_const)) < Real.log (n : ℝ) := by
    rw [Real.lt_log_iff_exp_lt (lt_trans (Real.exp_pos _) hn_big)]
    exact hn_big
  have hlog2 : Real.exp (4 * A_const) < Real.log (Real.log (n : ℝ)) := by
    rw [Real.lt_log_iff_exp_lt (lt_trans (Real.exp_pos _) hlog1)]
    exact hlog1
  have hlog3 : 4 * A_const < Real.log (Real.log (Real.log (n : ℝ))) := by
    rw [Real.lt_log_iff_exp_lt (lt_trans (Real.exp_pos _) hlog2)]
    exact hlog2
  let L : ℝ := Real.log (Real.log (Real.log (n : ℝ)))
  have hL_pos : 0 < L := lt_trans (by positivity) hlog3
  let α₀ : ℝ := C / L ^ c
  have hα₀_pos : 0 < α₀ := by
    have : 0 < L ^ c := Real.rpow_pos_of_pos hL_pos c
    positivity
  have hα₀_le1 : α₀ ≤ 1 := by
    dsimp only [α₀, C]
    have h1 : (4 * A_const) ^ c ≤ L ^ c :=
      Real.rpow_le_rpow (by positivity) (le_of_lt hlog3) (le_of_lt hc0)
    exact (div_le_one (Real.rpow_pos_of_pos hL_pos c)).mpr h1
  have hα₀_powK : 4 * A_const * α₀ ^ (-K) = L := by
    dsimp only [α₀, C]
    rw [div_eq_mul_inv, Real.mul_rpow (by positivity) (by positivity),
      Real.inv_rpow (le_of_lt (Real.rpow_pos_of_pos hL_pos c)),
      ← Real.rpow_mul (by positivity), ← Real.rpow_mul (le_of_lt hL_pos)]
    have hcK : c * (-K) = -1 := by dsimp only [c]; field_simp
    rw [hcK, Real.rpow_neg_one, Real.rpow_neg_one, inv_inv]
    have h4ne : 4 * A_const ≠ 0 := by positivity
    field_simp
  let γ₀ : ℝ := Real.exp (-(K * α₀ ^ (-K)))
  let η₀ : ℝ := γ₀ ^ 2 / 64
  let D₀ : ℝ := (3000 / γ₀) ^ 6 * (2 / γ₀)
  have hγ₀_pos : 0 < γ₀ := Real.exp_pos _
  have hγ₀_le1 : γ₀ ≤ 1 := by
    dsimp only [γ₀]
    rw [Real.exp_le_one_iff]
    have hnn : 0 ≤ K * α₀ ^ (-K) := by positivity
    linarith only [hnn]
  have hη₀_pos : 0 < η₀ := by positivity
  let t₀ : ℕ := Nat.ceil (16 / γ₀) + Nat.ceil (2 / α₀ ^ 2) + 10
  let nextDim : ℕ → ℕ := fun t => Nat.ceil (D₀ * (t : ℝ) ^ 6 + 256 / γ₀ ^ 3 + 2) + 1
  have hdim_ex : ∃ dimReq : ℕ → ℕ, dimReq 0 = t₀ ∧ ∀ s, dimReq (s + 1) = nextDim (dimReq s) :=
    ⟨Nat.rec t₀ (fun _ prev => nextDim prev), rfl, fun _ => rfl⟩
  obtain ⟨dimReq, hdim0, hdim_succ⟩ := hdim_ex
  have hdim_mono : ∀ s : ℕ, t₀ ≤ dimReq s := by
    intro s
    induction s with
    | zero => rw [hdim0]
    | succ s ih =>
      have hD0_ge1 : (1 : ℝ) ≤ D₀ := by
        dsimp only [D₀]
        have h1 : (1 : ℝ) ≤ 3000 / γ₀ := by rw [le_div_iff₀ hγ₀_pos]; linarith only [hγ₀_le1]
        have h2 : (1 : ℝ) ≤ 2 / γ₀ := by rw [le_div_iff₀ hγ₀_pos]; linarith only [hγ₀_le1]
        have h3 : (1 : ℝ) ≤ (3000 / γ₀) ^ 6 := one_le_pow₀ h1
        nlinarith only [h2, h3]
      have hprev1 : (1 : ℝ) ≤ (dimReq s : ℝ) := by
        have ht1 : 1 ≤ t₀ := by dsimp only [t₀]; omega
        have : 1 ≤ dimReq s := le_trans ht1 ih
        exact_mod_cast this
      have hge : (dimReq s : ℝ) ≤ (nextDim (dimReq s) : ℝ) := by
        have hp6 : (dimReq s : ℝ) ≤ (dimReq s : ℝ) ^ 6 := by
          calc (dimReq s : ℝ) = (dimReq s : ℝ) ^ 1 := (pow_one _).symm
          _ ≤ (dimReq s : ℝ) ^ 6 := pow_le_pow_right₀ hprev1 (by norm_num)
        have h1 : (dimReq s : ℝ) ≤ D₀ * (dimReq s : ℝ) ^ 6 + 256 / γ₀ ^ 3 + 2 := by
          have h256 : 0 ≤ 256 / γ₀ ^ 3 := by positivity
          nlinarith only [hD0_ge1, hp6, hprev1, h256]
        have h2 : D₀ * (dimReq s : ℝ) ^ 6 + 256 / γ₀ ^ 3 + 2 ≤ (nextDim (dimReq s) : ℝ) := by
          dsimp only [nextDim]
          have hc := Nat.le_ceil (D₀ * (dimReq s : ℝ) ^ 6 + 256 / γ₀ ^ 3 + 2)
          have hcast : (Nat.ceil (D₀ * (dimReq s : ℝ) ^ 6 + 256 / γ₀ ^ 3 + 2) : ℝ) ≤
              ((Nat.ceil (D₀ * (dimReq s : ℝ) ^ 6 + 256 / γ₀ ^ 3 + 2) + 1 : ℕ) : ℝ) := by
            exact_mod_cast Nat.le_succ _
          linarith only [hc, hcast]
        linarith only [h1, h2]
      have hnat : dimReq s ≤ nextDim (dimReq s) := by exact_mod_cast hge
      rw [hdim_succ s]
      exact le_trans ih hnat
  let S : ℕ := Nat.ceil (1 / η₀) + 1
  have hR_bound : (dimReq S : ℝ) ≤ (n : ℝ) :=
    triple_log_dim_bound hK4 hα₀_pos hα₀_le1 hα₀_powK hn_big hlog1 hlog2 rfl rfl rfl
      hdim0 hdim_succ hdim_mono
  have hn_ge_dimS : dimReq S ≤ n := by exact_mod_cast hR_bound
  have hiter : ∀ (s : ℕ) (m : ℕ) (B : Finset (𝔽₃ m)),
      dimReq s ≤ m → α₀ ≤ (B.card : ℝ) / (3 : ℝ) ^ m → ¬ Green17.HasRestrictedAP B →
      ∃ (d : ℕ) (B' : Finset (𝔽₃ d)),
        t₀ ≤ d ∧ ¬ Green17.HasRestrictedAP B' ∧
        (B.card : ℝ) / (3 : ℝ) ^ m + (s : ℝ) * η₀ ≤ (B'.card : ℝ) / (3 : ℝ) ^ d := by
    intro s
    induction s with
    | zero =>
      intro m B hm _ hnoB
      rw [hdim0] at hm
      exact ⟨m, B, hm, hnoB, by simp⟩
    | succ s ih =>
      intro m B hm hdensB hnoB
      have ht_lo : 16 / γ₀ ≤ (dimReq s : ℝ) := by
        have h1' : 16 / γ₀ ≤ (t₀ : ℝ) := by
          dsimp only [t₀]
          have hc := Nat.le_ceil (16 / γ₀)
          have hcast : (Nat.ceil (16 / γ₀) : ℝ) ≤
              ((Nat.ceil (16 / γ₀) + Nat.ceil (2 / α₀ ^ 2) + 10 : ℕ) : ℝ) := by
            exact_mod_cast (by omega : Nat.ceil (16 / γ₀) ≤ Nat.ceil (16 / γ₀) + Nat.ceil (2 / α₀ ^ 2) + 10)
          linarith only [hc, hcast]
        have h2' : (t₀ : ℝ) ≤ (dimReq s : ℝ) := Nat.cast_le.mpr (hdim_mono s)
        linarith only [h1', h2']
      have h2m : 2 / α₀ ^ 2 ≤ (2 : ℝ) ^ m := by
        have hm_t0 : t₀ ≤ m := le_trans (hdim_mono (s + 1)) hm
        have h1' : 2 / α₀ ^ 2 ≤ (t₀ : ℝ) := by
          dsimp only [t₀]
          have hc := Nat.le_ceil (2 / α₀ ^ 2)
          have hcast : (Nat.ceil (2 / α₀ ^ 2) : ℝ) ≤
              ((Nat.ceil (16 / γ₀) + Nat.ceil (2 / α₀ ^ 2) + 10 : ℕ) : ℝ) := by
            exact_mod_cast (by omega : Nat.ceil (2 / α₀ ^ 2) ≤ Nat.ceil (16 / γ₀) + Nat.ceil (2 / α₀ ^ 2) + 10)
          linarith only [hc, hcast]
        have h2' : (t₀ : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hm_t0
        have hm_le_2m : (m : ℝ) ≤ (2 : ℝ) ^ m := by
          have hnat : m ≤ 2 ^ m := Nat.le_of_lt Nat.lt_two_pow_self
          exact_mod_cast hnat
        linarith only [h1', h2', hm_le_2m]
      have hm_next : D₀ * (dimReq s : ℝ) ^ 6 + 256 / γ₀ ^ 3 + 2 ≤ (m : ℝ) := by
        have h1' : D₀ * (dimReq s : ℝ) ^ 6 + 256 / γ₀ ^ 3 + 2 ≤ (dimReq (s + 1) : ℝ) := by
          rw [hdim_succ s]
          dsimp only [nextDim]
          have hc := Nat.le_ceil (D₀ * (dimReq s : ℝ) ^ 6 + 256 / γ₀ ^ 3 + 2)
          have hcast : (Nat.ceil (D₀ * (dimReq s : ℝ) ^ 6 + 256 / γ₀ ^ 3 + 2) : ℝ) ≤
              ((Nat.ceil (D₀ * (dimReq s : ℝ) ^ 6 + 256 / γ₀ ^ 3 + 2) + 1 : ℕ) : ℝ) := by
            exact_mod_cast Nat.le_succ _
          linarith only [hc, hcast]
        have h2' : (dimReq (s + 1) : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hm
        linarith only [h1', h2']
      obtain ⟨d₁, B₁, hd₁, hnoB₁, hdensB₁⟩ :=
        hstep_all α₀ hα₀_pos hα₀_le1 (dimReq s) m B ht_lo h2m hm_next hdensB hnoB
      have hdensB₁' : (B.card : ℝ) / (3 : ℝ) ^ m + η₀ ≤ (B₁.card : ℝ) / (3 : ℝ) ^ d₁ := hdensB₁
      have hdensB₁_α₀ : α₀ ≤ (B₁.card : ℝ) / (3 : ℝ) ^ d₁ := by linarith only [hdensB, hdensB₁', hη₀_pos]
      obtain ⟨d₂, B₂, hd₂, hnoB₂, hdensB₂⟩ := ih d₁ B₁ hd₁ hdensB₁_α₀ hnoB₁
      refine ⟨d₂, B₂, hd₂, hnoB₂, ?_⟩
      rw [Nat.cast_add, Nat.cast_one]
      linarith only [hdensB₁', hdensB₂]
  by_contra hnoA
  have hA_dens : α₀ ≤ (A.card : ℝ) / (3 : ℝ) ^ n := by
    have h3pos : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
    rw [le_div_iff₀ h3pos]
    exact hA_card
  obtain ⟨d, B, _, _, hB_dens⟩ := hiter S n A hn_ge_dimS hA_dens hnoA
  have hB_le1 : (B.card : ℝ) / (3 : ℝ) ^ d ≤ 1 := by
    have h3pos : (0 : ℝ) < (3 : ℝ) ^ d := by positivity
    have hc : B.card ≤ 3 ^ d := by
      calc B.card ≤ Fintype.card (𝔽₃ d) := Finset.card_le_univ B
      _ = 3 ^ d := card_F3 d
    exact (div_le_one h3pos).mpr (by exact_mod_cast hc)
  have hS_η : 1 < (S : ℝ) * η₀ := by
    dsimp only [S]
    have hc : 1 / η₀ ≤ (Nat.ceil (1 / η₀) : ℝ) := Nat.le_ceil (1 / η₀)
    have hcast : ((Nat.ceil (1 / η₀) + 1 : ℕ) : ℝ) = (Nat.ceil (1 / η₀) : ℝ) + 1 := by
      push_cast; rfl
    have hmul : 1 = (1 / η₀) * η₀ := by field_simp
    have hgt : 1 / η₀ < ((Nat.ceil (1 / η₀) + 1 : ℕ) : ℝ) := by linarith only [hc, hcast]
    have hprod := mul_lt_mul_of_pos_right hgt hη₀_pos
    linarith only [hmul, hprod]
  linarith only [hA_dens, hα₀_pos, hB_dens, hB_le1, hS_η]

end OMA.R_Green17_green_17_variants_bklm_R1
