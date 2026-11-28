import OMAReductions.R_Erdos5_erdos_5_variants_banks_freiberg_maynard_measure_R1

-- Reduction Erdos5.erdos_5.variants.banks_freiberg_maynard_measure.R1.H1.R1 of step
-- Erdos5.erdos_5.variants.banks_freiberg_maynard_measure.R1.H1
-- Source: W. D. Banks, T. Freiberg, J. Maynard, On limit points of the sequence of
-- normalized prime gaps, Proc. London Math. Soc. 113 (2016) 515-539, arXiv:1404.5094.
-- Credit: @LordMike

/-!
The target is Theorem 1.1 of the paper: for nine nonnegative increasing reals some difference
is a limit point of the normalised prime gaps. The paper deduces it in Section 6 from two
results, and this file formalises exactly that deduction.

* `H1` is Theorem 4.3 (i) of the paper with m = 1: the Maynard-Tao sieve with the modified
  Bombieri-Vinogradov theorem 4.2, for tuples whose shifts may be as large as N and for n in a
  fixed residue class modulo W. This is the deep sieve input.
* `H2` is Lemma 5.2 of the paper: the Erdos-Rankin type construction, which sieves the interval
  (0, z] by the primes up to y and leaves exactly an admissible tuple with prescribed positions.
  This is the deep covering input (it rests on smooth-number bounds, Mertens and the prime
  number theorem in progressions).

In the paper both statements refer to the exceptional modulus Z of Lemma 4.1 (a possible Siegel
zero). Only two facts about Z are used: it is 1 or a prime, and it is at least a constant times
log log N (bound (4.7)). Both hypotheses quantify over such a Z instead of defining it through
zeros of L-functions; for `H2` this is condition (5.6) for a set with at most one element. In `H2`
the residue classes are written g + a p = 0 mod p, which is the paper's g = a p mod p with the
sign of a p changed. `main` is the gluing argument of Section 6: choice of the parameters, the
Chinese remainder theorem, the fact that the sieved interval contains no further primes, the
search for two consecutive primes in different blocks, and a pigeonhole over the pairs of blocks.
-/

open Filter Real
open scoped Topology

namespace OMA.R_Erdos5_erdos_5_variants_banks_freiberg_maynard_measure_R1_H1_R1

-- Banks-Freiberg-Maynard, Theorem 4.3 (i) with m = 1 (Maynard-Tao sieve in a residue class).
def H1 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → 144 ∣ k →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∃ Z : ℕ, (Z = 1 ∨ (Z.Prime ∧ c * log (log (N : ℝ)) ≤ (Z : ℝ))) ∧
          ∀ (h : Fin k → ℕ) (col : Fin k → Fin 9) (b : ℕ),
            Function.Injective h → (∀ i, h i ≤ N) →
            (∀ p : ℕ, p.Prime → ∃ r : ℕ, ∀ i, ¬ p ∣ h i + r) →
            (∀ i j, i < j → ∀ p : ℕ, p.Prime → (p : ℤ) ∣ (h j : ℤ) - (h i : ℤ) →
              (p : ℝ) ≤ ε * log (N : ℝ)) →
            (∀ a : Fin 9, 9 * (Finset.univ.filter fun i => col i = a).card = k) →
            (∀ p : ℕ, p.Prime → (p : ℝ) ≤ ε * log (N : ℝ) → p ≠ Z → ∀ i, ¬ p ∣ b + h i) →
            ∃ n : ℕ, N < n ∧ n ≤ 2 * N ∧
              (∀ p : ℕ, p.Prime → (p : ℝ) ≤ ε * log (N : ℝ) → p ≠ Z → n ≡ b [MOD p]) ∧
              ∃ i j, col i ≠ col j ∧ (n + h i).Prime ∧ (n + h j).Prime

-- Banks-Freiberg-Maynard, Lemma 5.2 (Erdos-Rankin type construction).
def H2 : Prop :=
  ∀ c : ℝ, 0 < c → ∀ k : ℕ, 1 ≤ k → ∀ β : Fin k → ℝ, Monotone β → (∀ i, 0 ≤ β i) →
    ∀ x : ℝ, 1 ≤ x → ∃ y₀ C : ℝ, ∀ (y z : ℝ) (Z : ℕ), y₀ ≤ y →
      (∀ i, 2 * y * (1 + (1 + β i) * x) ≤ 2 * z) →
      2 * z ≤ y * log (log y) / log (log (log y)) →
      (Z = 1 ∨ (Z.Prime ∧ c * log z ≤ (Z : ℝ))) →
      ∃ (a : ℕ → ℕ) (h : Fin k → ℕ), Function.Injective h ∧
        (∀ p : ℕ, p.Prime → ∃ r : ℕ, ∀ i, ¬ p ∣ h i + r) ∧
        (∀ g : ℕ, 0 < g → (g : ℝ) ≤ z →
          ((∃ i, h i = g) ↔ ∀ p : ℕ, p.Prime → (p : ℝ) ≤ y → p ≠ Z → ¬ p ∣ g + a p)) ∧
        (∀ i, 0 < h i ∧ (h i : ℝ) ≤ z) ∧
        (∀ i j, i < j → ∀ p : ℕ, p.Prime → (p : ℤ) ∣ (h j : ℤ) - (h i : ℤ) → (p : ℝ) ≤ y) ∧
        ∀ i, |(h i : ℝ) - (β i * x * y + y)| ≤ C * y * exp (-(log y) ^ ((1 : ℝ) / 4))

lemma exists_step {Q : ℕ → Prop} {a b : ℕ} (hab : a ≤ b) (ha : Q a) (hb : ¬ Q b) :
    ∃ r, a ≤ r ∧ r < b ∧ Q r ∧ ¬ Q (r + 1) := by
  induction b, hab using Nat.le_induction with
  | base => exact absurd ha hb
  | succ m hm ih =>
    by_cases hQ : Q m
    · exact ⟨m, hm, Nat.lt_succ_self m, hQ, hb⟩
    · obtain ⟨r, h1, h2, h3, h4⟩ := ih hQ
      exact ⟨r, h1, by omega, h3, h4⟩

lemma finish (β : Fin 9 → ℝ) (hβ : StrictMono β)
    (core : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, ∃ a b : Fin 9, a ≠ b ∧ ∃ r : ℕ,
      N < Nat.nth Nat.Prime r ∧
      |(primeGap r : ℝ) / log (Nat.nth Nat.Prime r) - (β b - β a)| < δ) :
    ∃ i j, i < j ∧ ∃ n : ℕ → ℕ, StrictMono n ∧
      Tendsto (fun k => (primeGap (n k) : ℝ) / log (Nat.nth Nat.Prime (n k)))
        atTop (𝓝 (β j - β i)) := by
  set u : ℕ → ℝ := fun r => (primeGap r : ℝ) / log (Nat.nth Nat.Prime r) with hu
  have hu0 : ∀ r, 0 ≤ u r := fun r =>
    div_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  have hex : ∃ a b : Fin 9, a ≠ b ∧ MapClusterPt (β b - β a) atTop u := by
    by_contra hno
    push Not at hno
    have h1 : ∀ p : Fin 9 × Fin 9, ∃ η : ℝ, 0 < η ∧
        (p.1 ≠ p.2 → ∀ᶠ r in atTop, η ≤ |u r - (β p.2 - β p.1)|) := by
      rintro ⟨a, b⟩
      by_cases hab : a = b
      · exact ⟨1, one_pos, fun h => absurd hab h⟩
      · have hnc := hno a b hab
        rw [mapClusterPt_iff_frequently] at hnc
        simp only [not_forall, not_frequently] at hnc
        obtain ⟨s, hs, hev⟩ := hnc
        obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.mp hs
        refine ⟨η, hη, fun _ => ?_⟩
        filter_upwards [hev] with r hr
        by_contra hlt
        exact hr (hball (by rw [Metric.mem_ball, Real.dist_eq]; exact not_le.mp hlt))
    choose η hη hev using h1
    obtain ⟨η0, hη0, hmin⟩ : ∃ η0 : ℝ, 0 < η0 ∧ ∀ p, η0 ≤ η p := by
      refine ⟨Finset.univ.inf' Finset.univ_nonempty η, ?_,
        fun p => Finset.inf'_le _ (Finset.mem_univ p)⟩
      rw [Finset.lt_inf'_iff]
      exact fun p _ => hη p
    have hall : ∀ᶠ r in atTop, ∀ p : Fin 9 × Fin 9, p.1 ≠ p.2 →
        η p ≤ |u r - (β p.2 - β p.1)| := by
      rw [eventually_all]
      intro p
      by_cases hp : p.1 = p.2
      · exact Eventually.of_forall fun r h => absurd hp h
      · filter_upwards [hev p hp] with r hr _ using hr
    obtain ⟨R, hR⟩ := eventually_atTop.mp hall
    obtain ⟨M, hM⟩ := eventually_atTop.mp (core η0 hη0)
    obtain ⟨a, b, hab, r, hNr, hlt⟩ := hM (max M (Nat.nth Nat.Prime R)) (le_max_left _ _)
    have hRr : R < r := (Nat.nth_lt_nth Nat.infinite_setOfPred_prime).mp
      (lt_of_le_of_lt (le_max_right _ _) hNr)
    have h3 := hR r hRr.le (a, b) hab
    have h4 := hmin (a, b)
    simp only at h3
    linarith
  obtain ⟨a, b, hab, hcl⟩ := hex
  obtain ⟨ψ, hψ, hlim⟩ := hcl.tendsto_subseq
  have hnn : 0 ≤ β b - β a := ge_of_tendsto' hlim fun k => hu0 _
  have hlt : a < b := by
    rcases lt_or_gt_of_ne hab with h | h
    · exact h
    · have := hβ h
      linarith
  exact ⟨a, b, hlt, ψ, hψ, hlim⟩

set_option maxHeartbeats 1600000 in
lemma core (h1 : H1) (h2 : H2) (β : Fin 9 → ℝ) (hβ0 : ∀ i, 0 ≤ β i) (hβ : StrictMono β) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, ∃ a b : Fin 9, a ≠ b ∧ ∃ r : ℕ,
      N < Nat.nth Nat.Prime r ∧
      |(primeGap r : ℝ) / log (Nat.nth Nat.Prime r) - (β b - β a)| < δ := by
  classical
  obtain ⟨c, hc, k₀, h1⟩ := h1
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = 16 * (k₀ + 1) := ⟨_, rfl⟩
  let e : Fin 9 × Fin q ≃ Fin (9 * q) := finProdFinEquiv
  let col : Fin (9 * q) → Fin 9 := fun i => (e.symm i).1
  have hcolmono : Monotone col := by
    intro i j hij
    simp only [col, e, finProdFinEquiv_symm_apply]
    rw [Fin.le_def] at hij ⊢
    exact Nat.div_le_div_right hij
  have hfib : ∀ a : Fin 9, 9 * (Finset.univ.filter fun i => col i = a).card = 9 * q := by
    intro a
    congr 1
    have h3 : (Finset.univ.filter fun i => col i = a).card
        = (Finset.univ.filter fun p : Fin 9 × Fin q => p.1 = a).card :=
      Finset.card_bijective e.symm e.symm.bijective (by simp [col])
    have h4 : (Finset.univ.filter fun p : Fin 9 × Fin q => p.1 = a)
        = ({a} : Finset (Fin 9)) ×ˢ (Finset.univ : Finset (Fin q)) := by
      ext ⟨p1, p2⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
        Finset.mem_singleton, and_true]
    rw [h3, h4, Finset.card_product]
    simp
  obtain ⟨ε₀, hε₀, h1⟩ := h1 (9 * q) (by omega) (by subst hq; omega)
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = min ε₀ 1 / 2 := ⟨_, rfl⟩
  have hεpos : 0 < ε := by rw [hε]; exact half_pos (lt_min hε₀ one_pos)
  have hεlt : ε < ε₀ := by
    have h3 := min_le_left ε₀ 1
    have h4 : 0 < min ε₀ 1 := lt_min hε₀ one_pos
    linarith
  have hε1 : ε ≤ 1 := by
    have h3 := min_le_right ε₀ 1
    have h4 : 0 < min ε₀ 1 := lt_min hε₀ one_pos
    linarith
  obtain ⟨N₀, h1⟩ := h1 ε hεpos hεlt
  obtain ⟨y₀, C, h2⟩ := h2 (c / 2) (by positivity) (9 * q) (by omega)
    (fun i => β (col i)) (hβ.monotone.comp hcolmono) (fun i => hβ0 _)
    (1 / ε) (by rw [le_div_iff₀ hεpos]; linarith)
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = β (Fin.last 8) := ⟨_, rfl⟩
  have hBle : ∀ a, β a ≤ B := fun a => hB ▸ hβ.monotone (Fin.le_last a)
  have hB0 : 0 ≤ B := hB ▸ hβ0 _
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 1 + (1 + B) / ε := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := by
    have : 0 ≤ (1 + B) / ε := by positivity
    linarith
  have hK0 : 0 < K := by linarith
  intro δ hδ
  have tL : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ty : Tendsto (fun N : ℕ => ε * log (N : ℝ)) atTop atTop := tL.const_mul_atTop hεpos
  have tly : Tendsto (fun N : ℕ => log (ε * log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp ty
  have tlly : Tendsto (fun N : ℕ => log (log (ε * log (N : ℝ)))) atTop atTop :=
    Real.tendsto_log_atTop.comp tly
  have tLL : Tendsto (fun N : ℕ => log (log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp tL
  have E3 : ∀ᶠ N : ℕ in atTop,
      2 * K ≤ log (log (ε * log (N : ℝ))) / log (log (log (ε * log (N : ℝ)))) := by
    have hlo := Real.isLittleO_log_id_atTop.def (show (0 : ℝ) < 1 / (2 * K) by positivity)
    filter_upwards [tlly.eventually hlo, tlly.eventually (eventually_gt_atTop (1 : ℝ))]
      with N h3 h4
    have hlpos : 0 < log (log (log (ε * log (N : ℝ)))) := Real.log_pos h4
    rw [le_div_iff₀ hlpos]
    simp only [id, Real.norm_eq_abs] at h3
    rw [abs_of_pos hlpos, abs_of_pos (by linarith)] at h3
    calc 2 * K * log (log (log (ε * log (N : ℝ))))
        ≤ 2 * K * (1 / (2 * K) * log (log (ε * log (N : ℝ)))) := by gcongr
      _ = log (log (ε * log (N : ℝ))) := by field_simp
  have E4 : ∀ᶠ N : ℕ in atTop, log (ε * K) ≤ log (log (N : ℝ)) := tLL.eventually_ge_atTop _
  have E5 : ∀ᶠ N : ℕ in atTop, ε * K * log (N : ℝ) ≤ N := by
    have hlo := Real.isLittleO_log_id_atTop.def (show (0 : ℝ) < 1 / (ε * K) by positivity)
    filter_upwards [tendsto_natCast_atTop_atTop.eventually hlo, eventually_ge_atTop 1]
      with N h3 h4
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast h4
    simp only [id, Real.norm_eq_abs] at h3
    rw [abs_of_nonneg (Real.log_nonneg hN1), abs_of_nonneg (by linarith)] at h3
    calc ε * K * log (N : ℝ) ≤ ε * K * (1 / (ε * K) * N) := by gcongr
      _ = N := by field_simp
  have E6a : ∀ᶠ N : ℕ in atTop,
      2 * C * ε * exp (-(log (ε * log (N : ℝ))) ^ ((1 : ℝ) / 4)) < δ / 2 := by
    have t : Tendsto (fun N : ℕ => exp (-(log (ε * log (N : ℝ))) ^ ((1 : ℝ) / 4)))
        atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
        ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp tly))
    have t2 := t.const_mul (2 * C * ε)
    rw [mul_zero] at t2
    exact t2.eventually_lt_const (half_pos hδ)
  have E6b : ∀ᶠ N : ℕ in atTop, B * log 3 < δ / 2 * log (N : ℝ) :=
    (tL.const_mul_atTop (half_pos hδ)).eventually_gt_atTop _
  filter_upwards [eventually_ge_atTop N₀, eventually_ge_atTop 3, ty.eventually_ge_atTop y₀,
    E3, E4, E5, E6a, E6b] with N hN0 hN3 E2 E3 E4 E5 E6a E6b
  have hN3r : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = log (N : ℝ) := ⟨_, rfl⟩
  rw [← hLdef] at E2 E3 E4 E5 E6a E6b
  have hL : 0 < L := hLdef ▸ Real.log_pos (by linarith)
  obtain ⟨y, hydef⟩ : ∃ y : ℝ, y = ε * L := ⟨_, rfl⟩
  rw [← hydef] at E2 E3 E6a
  have hy0 : 0 < y := hydef ▸ mul_pos hεpos hL
  obtain ⟨z, hzdef⟩ : ∃ z : ℝ, z = y * K := ⟨_, rfl⟩
  obtain ⟨Z, hZ, h1⟩ := h1 N hN0
  rw [← hLdef, ← hydef] at h1
  rw [← hLdef] at hZ
  have hyN : y ≤ N := by
    have h3 : log (N : ℝ) ≤ N - 1 := Real.log_le_sub_one_of_pos (by linarith)
    rw [← hLdef] at h3
    have h4 : ε * L ≤ 1 * L := mul_le_mul_of_nonneg_right hε1 hL.le
    linarith
  have hzN : z ≤ N := by
    calc z = ε * K * L := by rw [hzdef, hydef]; ring
      _ ≤ N := E5
  have hlogz : log z = log (ε * K) + log L := by
    rw [show z = ε * K * L by rw [hzdef, hydef]; ring, Real.log_mul (by positivity) hL.ne']
  have hZ' : Z = 1 ∨ (Z.Prime ∧ c / 2 * log z ≤ (Z : ℝ)) := by
    rcases hZ with h | ⟨hp, hle⟩
    · exact Or.inl h
    · refine Or.inr ⟨hp, ?_⟩
      rw [hlogz]
      have h3 := mul_le_mul_of_nonneg_left E4 hc.le
      linarith
  have c3 : ∀ i, 2 * y * (1 + (1 + β (col i)) * (1 / ε)) ≤ 2 * z := by
    intro i
    have h3 : (1 + β (col i)) * (1 / ε) ≤ (1 + B) / ε := by
      rw [mul_one_div]
      have := hBle (col i)
      gcongr
    have h4 : y * (1 + (1 + β (col i)) * (1 / ε)) ≤ y * K := by
      rw [hK]
      gcongr
    rw [hzdef]
    linarith
  have c4 : 2 * z ≤ y * log (log y) / log (log (log y)) := by
    rw [mul_div_assoc]
    calc 2 * z = y * (2 * K) := by rw [hzdef]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left E3 hy0.le
  obtain ⟨a, h, hinj, hadm, hset, hpos, hdiff, hloc⟩ :=
    h2 y z Z E2 c3 c4 hZ'
  let t : Finset ℕ := (Finset.range (N + 1)).filter fun p => p.Prime ∧ (p : ℝ) ≤ y ∧ p ≠ Z
  obtain ⟨b, hb⟩ := Nat.chineseRemainderOfFinset a id t
    (fun p hp => (Finset.mem_filter.mp hp).2.1.ne_zero)
    (fun p hp p' hp' hne => (Nat.coprime_primes (Finset.mem_filter.mp hp).2.1
      (Finset.mem_filter.mp hp').2.1).mpr hne)
  have hb' : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ y → p ≠ Z → b ≡ a p [MOD p] := by
    intro p hp hpy hpZ
    refine hb p (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hp, hpy, hpZ⟩)
    have h3 : (p : ℝ) ≤ N := hpy.trans hyN
    exact Nat.lt_succ_of_le (by exact_mod_cast h3)
  have hdv : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ y → p ≠ Z → ∀ m g : ℕ, m ≡ b [MOD p] →
      (p ∣ m + g ↔ p ∣ g + a p) := by
    intro p hp hpy hpZ m g hm
    rw [add_comm g (a p)]
    exact ((hm.trans (hb' p hp hpy hpZ)).add_right g).dvd_iff dvd_rfl
  have hhN : ∀ i, h i ≤ N := fun i => by
    have h3 := (hpos i).2.trans hzN
    exact_mod_cast h3
  obtain ⟨n, hnN, hn2N, hncong, i, j, hcol, hpi, hpj⟩ := h1 h col b hinj hhN hadm hdiff hfib
    (fun p hp hpy hpZ i hdvd =>
      (hset (h i) (hpos i).1 (hpos i).2).mp ⟨i, rfl⟩ p hp hpy hpZ
        ((hdv p hp hpy hpZ b (h i) (Nat.ModEq.refl b)).mp hdvd))
  have star : ∀ P : ℕ, P.Prime → n < P → (P : ℝ) ≤ n + z → ∃ l, P = n + h l := by
    intro P hP hnP hPz
    obtain ⟨g, rfl⟩ : ∃ g, P = n + g := ⟨P - n, by omega⟩
    have hg0 : 0 < g := by omega
    have hgz : (g : ℝ) ≤ z := by
      push_cast at hPz
      linarith
    by_contra hno
    have hno' : ¬ ∃ i, h i = g := fun ⟨l, hl⟩ => hno ⟨l, by rw [hl]⟩
    rw [hset g hg0 hgz] at hno'
    push Not at hno'
    obtain ⟨p, hp, hpy, hpZ, hdvd⟩ := hno'
    have hdvd' : p ∣ n + g := (hdv p hp hpy hpZ n g (hncong p hp hpy hpZ)).mpr hdvd
    have hpeq := (Nat.prime_dvd_prime_iff_eq hp hP).mp hdvd'
    have h3 : (p : ℝ) ≤ N := hpy.trans hyN
    have h4 : p ≤ N := by exact_mod_cast h3
    omega
  have key : ∀ i j, col i ≠ col j → h i < h j → (n + h i).Prime → (n + h j).Prime →
      ∃ a b : Fin 9, a ≠ b ∧ ∃ r : ℕ, N < Nat.nth Nat.Prime r ∧
        |(primeGap r : ℝ) / log (Nat.nth Nat.Prime r) - (β b - β a)| < δ := by
    intro i j hcol hlt hpi hpj
    have hinf := Nat.infinite_setOfPred_prime
    have hri : Nat.nth Nat.Prime (Nat.count Nat.Prime (n + h i)) = n + h i := Nat.nth_count hpi
    have hrj : Nat.nth Nat.Prime (Nat.count Nat.Prime (n + h j)) = n + h j := Nat.nth_count hpj
    have hrij : Nat.count Nat.Prime (n + h i) ≤ Nat.count Nat.Prime (n + h j) :=
      Nat.count_monotone _ (by omega)
    obtain ⟨r, hr1, hr2, ⟨l, hl, hcl⟩, hnQ⟩ := exists_step
      (Q := fun r => ∃ l, Nat.nth Nat.Prime r = n + h l ∧ col l = col i) hrij ⟨i, hri, rfl⟩
      (by
        rintro ⟨l, hl, hcl⟩
        rw [hrj] at hl
        have h3 : j = l := hinj (Nat.add_left_cancel hl)
        exact hcol (by rw [← hcl, h3]))
    have hlt1 : Nat.nth Nat.Prime r < Nat.nth Nat.Prime (r + 1) :=
      (Nat.nth_lt_nth hinf).mpr (Nat.lt_succ_self r)
    have hle2 : Nat.nth Nat.Prime (r + 1) ≤ n + h j := by
      rw [← hrj]
      exact (Nat.nth_strictMono hinf).monotone (by omega)
    obtain ⟨l', hl'⟩ := star _ (Nat.prime_nth_prime (r + 1)) (by omega) (by
      have h3 : ((Nat.nth Nat.Prime (r + 1) : ℕ) : ℝ) ≤ ((n + h j : ℕ) : ℝ) := by
        exact_mod_cast hle2
      push_cast at h3
      linarith [(hpos j).2])
    have hcl' : col l' ≠ col l := fun hh => hnQ ⟨l', hl', hh.trans hcl⟩
    refine ⟨col l, col l', hcl'.symm, r, by omega, ?_⟩
    have hgap : (primeGap r : ℝ) = (h l' : ℝ) - h l := by
      have h3 : primeGap r = h l' - h l := by
        unfold primeGap
        rw [hl', hl]
        omega
      rw [h3, Nat.cast_sub (by omega)]
    obtain ⟨p, hpdef⟩ : ∃ p : ℝ, p = (Nat.nth Nat.Prime r : ℝ) := ⟨_, rfl⟩
    rw [hgap, ← hpdef]
    have hpN : (N : ℝ) < p := by
      rw [hpdef]
      exact_mod_cast (by omega : N < Nat.nth Nat.Prime r)
    have hp3 : p ≤ 3 * N := by
      have h3 := hhN j
      rw [hpdef]
      exact_mod_cast (by omega : Nat.nth Nat.Prime r ≤ 3 * N)
    have hlogp1 : L ≤ log p := hLdef ▸ Real.log_le_log (by linarith) hpN.le
    have hlogp2 : log p ≤ L + log 3 := by
      have h3 := Real.log_le_log (by linarith : 0 < p) hp3
      rw [Real.log_mul (by norm_num) (by linarith), ← hLdef] at h3
      linarith
    have hxy : 1 / ε * y = L := by
      rw [hydef]
      field_simp
    obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = C * y * exp (-(log y) ^ ((1 : ℝ) / 4)) := ⟨_, rfl⟩
    have hE : 2 * E < δ / 2 * L := by
      have h3 : 2 * E = (2 * C * ε * exp (-(log y) ^ ((1 : ℝ) / 4))) * L := by
        rw [hEdef, hydef]
        ring
      rw [h3]
      exact mul_lt_mul_of_pos_right E6a hL
    have e1 : |(h l : ℝ) - (β (col l) * L + y)| ≤ E := by
      have h3 := hloc l
      rwa [mul_assoc, hxy, ← hEdef] at h3
    have e2 : |(h l' : ℝ) - (β (col l') * L + y)| ≤ E := by
      have h3 := hloc l'
      rwa [mul_assoc, hxy, ← hEdef] at h3
    obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = β (col l') - β (col l) := ⟨_, rfl⟩
    rw [← hDdef]
    have hD : |D| ≤ B := by
      rw [hDdef]
      exact abs_le.mpr ⟨by linarith [hβ0 (col l'), hBle (col l)],
        by linarith [hβ0 (col l), hBle (col l')]⟩
    have hDL : D * L = β (col l') * L - β (col l) * L := by
      rw [hDdef]
      ring
    have hGD : |(h l' : ℝ) - h l - D * L| ≤ 2 * E := by
      rw [abs_le] at e1 e2 ⊢
      constructor <;> linarith
    have hlp : 0 < log p := lt_of_lt_of_le hL hlogp1
    rw [show ((h l' : ℝ) - h l) / log p - D = ((h l' : ℝ) - h l - D * log p) / log p by
      field_simp, abs_div, abs_of_pos hlp, div_lt_iff₀ hlp]
    calc |(h l' : ℝ) - h l - D * log p|
        = |((h l' : ℝ) - h l - D * L) - D * (log p - L)| := by ring_nf
      _ ≤ |(h l' : ℝ) - h l - D * L| + |D * (log p - L)| := abs_sub _ _
      _ ≤ 2 * E + B * log 3 := by
          rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ log p - L)]
          exact add_le_add hGD (mul_le_mul hD (by linarith) (by linarith) hB0)
      _ < δ * L := by linarith
      _ ≤ δ * log p := mul_le_mul_of_nonneg_left hlogp1 hδ.le
  have hij : i ≠ j := fun hh => hcol (by rw [hh])
  rcases lt_or_gt_of_ne (fun hh => hij (hinj hh)) with hlt | hlt
  · exact key i j hcol hlt hpi hpj
  · exact key j i hcol.symm hlt hpj hpi

theorem main : H1 → H2 → OMA.R_Erdos5_erdos_5_variants_banks_freiberg_maynard_measure_R1.H1 := by
  intro h1 h2 β hβ0 hβ
  exact finish β hβ (core h1 h2 β hβ0 hβ)

end OMA.R_Erdos5_erdos_5_variants_banks_freiberg_maynard_measure_R1_H1_R1
