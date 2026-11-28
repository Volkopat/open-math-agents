import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3

-- Reduction Erdos142.erdos_142.variants.lower.R1.H2.R3.H1.R2 of step Erdos142.erdos_142.variants.lower.R1.H2.R3.H1
-- Credit: @Pixelstorm44

/-!
Translate covering converts a multicolor van der Waerden bound to a density
bound. A single popular shift removes a fixed fraction of the remaining
points. Iteration gives an interval coloring, with the logarithmic covering
loss absorbed into half of the stretched-exponential exponent. The extremizer
and positive-step lemmas are adapted from the parent Erdős 142 reductions.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R2

open Erdos142 Real

/-- A multicolor van der Waerden bound. Every coloring of an interval without
a monochromatic nonconstant k-AP needs many colors. -/
def H1 : Prop :=
  ∀ k : ℕ, 4 ≤ k → ∃ B c ε : ℝ, 0 < B ∧ 0 < c ∧ 0 < ε ∧
    ∀ N q : ℕ, 2 ≤ N → ∀ f : ℕ → ℕ, (∀ x ∈ Finset.Icc 1 N, f x < q) →
      (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k,
        a + i*d ∈ Finset.Icc 1 N ∧ f (a+i*d) = f a) →
      exp (c * log (N : ℝ) ^ ε) ≤ B * q

/-- One averaging step for arbitrary subsets of an interval. The two natural
offsets encode a signed shift. Summing the number of pairs (x,y) in U × A by
their difference gives the expected coverage using at most 2N shifts. -/
def H2 : Prop :=
  ∀ N : ℕ, 2 ≤ N → ∀ A U : Finset ℕ, A ⊆ Finset.Icc 1 N → U ⊆ Finset.Icc 1 N →
    ∃ s t : ℕ, ∃ V ⊆ U, (V.card : ℝ) ≤ (1 - (A.card : ℝ)/(2*N)) * U.card ∧
      ∀ x ∈ U, x ∉ V → ∃ y ∈ A, x+s = y+t

/-- The finite averaging hypothesis follows by grouping U × A by the difference. -/
theorem popularShift : H2 := by
  classical
  intro N hN A U hA hU
  let P := U ×ˢ A
  let D := Finset.range (2*N)
  let diff (z : ℕ × ℕ) := z.1 + N - z.2
  let fiber (j : ℕ) := P.filter fun z => diff z = j
  have hxy {z : ℕ × ℕ} (hz : z ∈ P) :
      (1 ≤ z.1 ∧ z.1 ≤ N) ∧ 1 ≤ z.2 ∧ z.2 ≤ N :=
    ⟨Finset.mem_Icc.mp (hU (Finset.mem_product.mp hz).1),
     Finset.mem_Icc.mp (hA (Finset.mem_product.mp hz).2)⟩
  have hmap : (P : Set (ℕ × ℕ)).MapsTo diff D := by
    intro z hz
    have hh := hxy hz
    apply Finset.mem_range.mpr
    dsimp [diff]
    omega
  obtain ⟨j,hj,hmax⟩ := D.exists_max_image (fun i => (fiber i).card)
    (show D.Nonempty from ⟨0, Finset.mem_range.mpr (by omega)⟩)
  have hmass : U.card*A.card ≤ (2*N)*(fiber j).card := by
    calc
      U.card*A.card = P.card := (Finset.card_product U A).symm
      _ = ∑ i ∈ D, (fiber i).card := Finset.card_eq_sum_card_fiberwise hmap
      _ ≤ ∑ _i ∈ D, (fiber j).card := Finset.sum_le_sum hmax
      _ = _ := by simp [D]
  let E := (fiber j).image Prod.fst
  have heq {z : ℕ × ℕ} (hz : z ∈ fiber j) : z.1+N = z.2+j := by
    obtain ⟨hzP,hj'⟩ := Finset.mem_filter.mp hz
    have hh := hxy hzP
    change z.1+N-z.2 = j at hj'
    omega
  have hcard : E.card = (fiber j).card := by
    apply Finset.card_image_of_injOn
    intro z hz w hw h
    apply Prod.ext h
    have h1 := heq hz
    have h2 := heq hw
    change z.1 = w.1 at h
    omega
  have hEU : E ⊆ U := by
    intro x hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hz).1).1
  refine ⟨N,j,U \ E,Finset.sdiff_subset,?_,?_⟩
  · have hNpos : 0 < (2*(N:ℝ)) := by exact_mod_cast (show 0 < 2*N by omega)
    have hm : (U.card:ℝ)*A.card ≤ (2*(N:ℝ))*E.card := by rw [hcard]; exact_mod_cast hmass
    have hfrac : (A.card:ℝ)/(2*N)*U.card ≤ E.card := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hNpos]
      nlinarith only [hm]
    rw [Finset.card_sdiff_of_subset hEU, Nat.cast_sub (Finset.card_mono hEU)]
    linarith
  · intro x hx hn
    have hxE : x ∈ E := by by_contra h; exact hn (Finset.mem_sdiff.mpr ⟨hx,h⟩)
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hxE
    exact ⟨z.2,(Finset.mem_product.mp (Finset.mem_filter.mp hz).1).2,heq hz⟩

/-- After m shifts, the uncovered portion decreases exponentially. -/
private theorem iterateCover (step : H2) {N : ℕ} (hN : 2 ≤ N)
    {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (m : ℕ) :
    ∃ U ⊆ Finset.Icc 1 N, ∃ s t : ℕ → ℕ,
      (U.card : ℝ) ≤ N * exp (-((A.card : ℝ)/(2*N)) * m) ∧
      ∀ x ∈ Finset.Icc 1 N, x ∉ U → ∃ i < m, ∃ y ∈ A, x+s i = y+t i := by
  let p : ℝ := (A.card : ℝ)/(2*N)
  change ∃ U ⊆ Finset.Icc 1 N, ∃ s t : ℕ → ℕ, (U.card : ℝ) ≤ N * exp (-p * m) ∧ _
  induction m with
  | zero =>
    refine ⟨_, Finset.Subset.rfl, fun _ => 0, fun _ => 0, ?_, ?_⟩
    · simp [Nat.card_Icc]
    · intro x hx hn
      exact (hn hx).elim
  | succ m ih =>
    obtain ⟨U, hU, s, t, hcount, hcovered⟩ := ih
    obtain ⟨u, v, V, hVU, hV, hnew⟩ := step N hN A U hA hU
    refine ⟨V, hVU.trans hU, Function.update s m u, Function.update t m v, ?_, ?_⟩
    · calc
        (V.card : ℝ) ≤ (1-p) * U.card := hV
        _ ≤ exp (-p) * U.card := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith [Real.add_one_le_exp (-p)]
        _ ≤ exp (-p) * (N * exp (-p * m)) :=
          mul_le_mul_of_nonneg_left hcount (exp_pos _).le
        _ = N * exp (-p * (m+1 : ℕ)) := by
          rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one, exp_add]
          ring
    · intro x hx hxV
      by_cases hxU : x ∈ U
      · obtain ⟨y, hy, hxy⟩ := hnew x hxU hxV
        exact ⟨m, by omega, y, hy, by simpa using hxy⟩
      · obtain ⟨i, hi, y, hy, hxy⟩ := hcovered x hx hxU
        exact ⟨i, by omega, y, hy, by simpa [Function.update_of_ne (Nat.ne_of_lt hi)] using hxy⟩

/-- An extremal set supplies a cover of cost at most 3N(1+log N)/|A|. -/
private theorem cover (step : H2) {N : ℕ} (hN : 2 ≤ N) {A : Finset ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (ha : 0 < A.card) :
    ∃ q : ℕ, ∃ s t : ℕ → ℕ,
      (q : ℝ)*A.card ≤ 3*N*(1+log N) ∧
      ∀ x ∈ Finset.Icc 1 N, ∃ i < q, ∃ y ∈ A, x+s i = y+t i := by
  have hNr : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hAr : (0:ℝ) < A.card := by exact_mod_cast ha
  have hAN : (A.card : ℝ) ≤ N := by exact_mod_cast (Finset.card_mono hA).trans_eq (Nat.card_Icc 1 N)
  have hlog : 0 ≤ log (N:ℝ) := log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  let p : ℝ := A.card/(2*(N:ℝ))
  have hp : 0 < p := by dsimp [p]; positivity
  let z : ℝ := (1+log N)/p
  let q := ⌈z⌉₊
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hlo : 1+log N ≤ (q:ℝ)*p := (div_le_iff₀ hp).mp (Nat.le_ceil z)
  have hhi : (q:ℝ) < z+1 := Nat.ceil_lt_add_one hz
  obtain ⟨U, _, s, t, hcnt, hc⟩ := iterateCover step hN hA q
  have hlt : (U.card : ℝ) < 1 := by
    calc
      (U.card : ℝ) ≤ N * exp (-p*q) := hcnt
      _ < N * exp (-log N) := by
        apply mul_lt_mul_of_pos_left _ hNr
        apply exp_lt_exp.mpr
        linarith [mul_comm (q:ℝ) p]
      _ = 1 := by rw [exp_neg, exp_log hNr]; exact mul_inv_cancel₀ hNr.ne'
  have hzero : U.card = 0 := by
    have : U.card < 1 := by exact_mod_cast hlt
    omega
  refine ⟨q, s, t, ?_, fun x hx => hc x hx (by simp [Finset.card_eq_zero.mp hzero])⟩
  have heq : z*(A.card:ℝ) = (1+log N)*(2*N) := by dsimp [z,p]; field_simp
  have h := mul_le_mul_of_nonneg_right hhi.le hAr.le
  rw [add_mul, heq, one_mul] at h
  nlinarith [mul_nonneg hNr.le hlog]

lemma no_positive_step {A : Set ℕ} {k : ℕ} (hk : 1 < k) (hfree : A.IsAPOfLengthFree k) :
    ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A := by
  rintro ⟨a, d, hd, hmem⟩
  let T := (Finset.range k).image fun i => a + i * d
  have hcard : T.card = k := by
    have hinj : Function.Injective (fun i : ℕ => a + i * d) := by
      intro x y h
      exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel h)
    simp [T, Finset.card_image_of_injective _ hinj]
  have hsub : (T : Set ℕ) ⊆ A := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact hmem i (Finset.mem_range.mp hi)
  have hap' : (T : Set ℕ).IsAPOfLength k := by
    refine ⟨a, d, by simp [hcard], ?_⟩
    ext x
    simp [T]
  have hle := hfree (T : Set ℕ) hsub hap'
  exact (not_le_of_gt hk) (by exact_mod_cast hle)

/-- The natural-number supremum defining the extremal cardinality is attained. -/
lemma extremizer {k : ℕ} (hk : 1 < k) (N : ℕ) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 N ∧ (S : Set ℕ).IsAPOfLengthFree k ∧
      S.card = r k N := by
  let c : Set ℕ := {Finset.card S | (S) (_ : S ⊆ Finset.Icc 1 N)
    (_ : (S : Set ℕ).IsAPOfLengthFree k)}
  have hnon : c.Nonempty := by
    refine ⟨0, ∅, by simp, ?_, by simp⟩
    intro t ht hprogression
    have ht' : t = ∅ := Set.subset_empty_iff.mp (by simpa using ht)
    have hpos : 0 < (k : ℕ∞) := by exact_mod_cast (show 0 < k by omega)
    exact (Set.not_isAPOfLength_empty hpos (ht' ▸ hprogression)).elim
  have hbound : BddAbove c := by
    refine ⟨N, ?_⟩
    rintro _ ⟨S, hs, _, rfl⟩
    exact (Finset.card_mono hs).trans_eq (Nat.card_Icc 1 N)
  obtain ⟨S, hS, hfree, hcard⟩ := Nat.sSup_mem hnon hbound
  exact ⟨S, hS, hfree, hcard⟩

/-- Scaling the elementary inequality log z ≤ z^ε/ε absorbs the cost of
covering into half the Ramsey exponent, uniformly over all interval lengths. -/
private theorem absorb {c ε : ℝ} (hc : 0 < c) (he : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 0 < x → 1+x ≤ K * exp (c/2*x^ε) := by
  let a : ℝ := (c/2*ε)^(ε⁻¹)
  have hb : 0 < c/2*ε := by positivity
  have ha : 0 < a := rpow_pos_of_pos hb _
  have hpow : a^ε = c/2*ε := by
    dsimp [a]
    rw [← rpow_mul hb.le, inv_mul_cancel₀ he.ne', rpow_one]
  refine ⟨1+a⁻¹, by positivity, ?_⟩
  intro x hx
  have hh := log_le_rpow_div (mul_pos ha hx).le he
  rw [mul_rpow ha.le hx.le, hpow] at hh
  have hlog : log (a*x) ≤ c/2*x^ε := by
    apply hh.trans
    apply (div_le_iff₀ he).mpr
    ring_nf
    rfl
  have hax : a*x ≤ exp (c/2*x^ε) := by simpa [exp_log (mul_pos ha hx)] using exp_le_exp.mpr hlog
  have h1 : 1 ≤ exp (c/2*x^ε) := one_le_exp (by positivity)
  have hinv := mul_le_mul_of_nonneg_left hax (inv_pos.mpr ha).le
  rw [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul] at hinv
  linarith

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3.H1 := by
  classical
  intro ramsey step k hk
  obtain ⟨B,c,ε,hB,hc,he,hram⟩ := ramsey k hk
  obtain ⟨K,hK,habs⟩ := absorb hc he
  refine ⟨3*B*K,c/2,ε,by positivity,by positivity,he,?_⟩
  intro N hN
  obtain ⟨A,hA,hfree,hcard⟩ := extremizer (by omega : 1 < k) N
  rw [← hcard]
  by_cases ha : A.card = 0
  · rw [ha, Nat.cast_zero]
    positivity
  obtain ⟨q,s,t,hcost,hcover⟩ := cover step hN hA (Nat.pos_of_ne_zero ha)
  let f (x : ℕ) := if hx : x ∈ Finset.Icc 1 N then (hcover x hx).choose else 0
  have hcol x (hx : x ∈ Finset.Icc 1 N) :
      f x < q ∧ ∃ y ∈ A, x+s (f x) = y+t (f x) := by
    simpa only [f, dif_pos hx] using (hcover x hx).choose_spec
  have hproper : ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k,
      a+i*d ∈ Finset.Icc 1 N ∧ f (a+i*d) = f a := by
    rintro ⟨a,d,hd,hm⟩
    have haI : a ∈ Finset.Icc 1 N := by simpa using (hm 0 (by omega)).1
    obtain ⟨b,_,hb⟩ := (hcol a haI).2
    apply no_positive_step (by omega : 1 < k) hfree
    refine ⟨b,d,hd,?_⟩
    intro i hi
    obtain ⟨y,hy,hyEq⟩ := (hcol _ (hm i hi).1).2
    rw [(hm i hi).2] at hyEq
    have : b+i*d = y := by omega
    simpa [this] using hy
  let x := log (N:ℝ)
  have hx : 0 < x := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hram' := hram N q hN f (fun n hn => (hcol n hn).1) hproper
  have hbound : (A.card:ℝ) * exp (c*x^ε) ≤ (3*B*K*N) * exp (c/2*x^ε) := by
    calc
      (A.card:ℝ)*exp (c*x^ε) ≤ A.card*(B*q) :=
        mul_le_mul_of_nonneg_left hram' (Nat.cast_nonneg _)
      _ = B*((q:ℝ)*A.card) := by ring
      _ ≤ B*(3*N*(1+x)) := mul_le_mul_of_nonneg_left hcost hB.le
      _ ≤ B*(3*N*(K*exp (c/2*x^ε))) := by gcongr; exact habs x hx
      _ = _ := by ring
  calc
    (A.card:ℝ) = (A.card*exp (c*x^ε))*exp (-(c*x^ε)) := by rw [mul_assoc, ← exp_add]; simp
    _ ≤ ((3*B*K*N)*exp (c/2*x^ε))*exp (-(c*x^ε)) :=
      mul_le_mul_of_nonneg_right hbound (exp_pos _).le
    _ = _ := by rw [mul_assoc, ← exp_add]; congr 2 <;> dsimp [x] <;> ring

end OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R2
