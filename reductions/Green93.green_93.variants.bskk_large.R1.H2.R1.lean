import OMAReductions.R_Green93_green_93_variants_bskk_large_R1

/-!
Reduction of `Green93.green_93.variants.bskk_large.R1.H2` (the intermediate-degree divisor
bound for random monic polynomials in `Z[X]` with coefficients uniform on `{0, ..., M}`,
`34 <= M`, `(log M)^3 <= n`) to two independent, unconditional theorems:

- `H1`: Single-prime finite-field polynomial divisor-of-degree-`d` bound (Ford 2008;
  Eberhard-Ford-Green 2016; Pemantle-Peres-Rivin 2016; Bary-Soroker-Kozma 2020; BSKK23):
  there exists an absolute exponent `delta > 0` such that for every prime `p`, the proportion
  of monic degree-`n` polynomials over `ZMod p` having a monic divisor of exact degree `d`
  (`1 <= d <= n / 2`) is `O_p(d^(-delta))`.
- `H2`: BSKK23 Theorem 1(a) intermediate-degree bound restricted to linear-height boxes
  `34 <= M <= K * n` (with monic divisors).

Inside `main`, we prove completely from scratch in Lean 4:
1. Exact sample cardinality `eligible.card = M * (M + 1)^(n - 1)` for `1 <= n`, giving
   `(M + 1)^n <= (35 / 34) * eligible.card` for `34 <= M`.
2. Monic normalization in `Z[X]`: every divisor `g` of a monic integer polynomial has
   `g.leadingCoeff = 1` or `-1`, yielding a monic associate `g'` of the same degree.
3. Multi-prime CRT fiber reduction for ALL large heights `Q * n <= M` (eliminating the entire
   super-linear / stretched-exponential regime `K * n < M <= exp(n^(1/3))` without even needing
   `(log M)^3 <= n`): given `delta > 0` from `H1`, select `r = ceil(11 / delta)` distinct primes
   `p_1 < ... < p_r` via `Nat.nth Nat.Prime`, set `Q = prod p_j`, prove every coordinate fiber
   mod `(p_1, ..., p_r)` in `{0, ..., M}` has size at most `M / Q + 1` via pairwise coprimality
   and Euclidean division, deduce the exact product bound over `ZMod (p_j)` for each divisor
   degree `d`, cancel `Q^n` with fiber distortion `((M + Q) / (M + 1))^n <= exp 1 <= 3`, and
   union-bound over all `d` in `[n^(1/10), n/2]` to obtain `n^(-1/20) / 2` decay.
4. Regime assembly uniting `M <= Q * n` (`H2 Q` plus monic normalization) with `Q * n < M`.
-/

namespace OMA.R_Green93_green_93_variants_bskk_large_R1_H2_R1

open Polynomial

/-- Single-prime finite-field divisor-of-degree-`d` bound (Ford 2008; Eberhard-Ford-Green 2016;
Pemantle-Peres-Rivin 2016; Bary-Soroker-Kozma 2020; BSKK23): there exists an absolute exponent
`δ > 0` such that for every prime `p`, the proportion of monic degree-`n` polynomials over
`ZMod p` admitting a monic divisor of exact degree `d` (`1 ≤ d ≤ n / 2`) is `O_p(d ^ (-δ))`. -/
def H1 : Prop := by
  classical
  exact ∃ δ : ℝ, 0 < δ ∧ ∀ (p : ℕ) [Fact p.Prime], ∃ C : ℝ, 0 < C ∧ ∀ n d : ℕ,
    1 ≤ d → 2 * d ≤ n →
    (((Finset.univ : Finset (Fin n → ZMod p)).filter fun b =>
      ∃ g : Polynomial (ZMod p), g.Monic ∧ g.natDegree = d ∧
        g ∣ (Polynomial.X ^ n +
          ∑ i : Fin n, Polynomial.C (b i) * Polynomial.X ^ (i : ℕ))).card : ℝ) ≤
      C * (d : ℝ) ^ (-δ) * (p : ℝ) ^ n

/-- Intermediate-degree monic divisor bound restricted to linear-height boxes `34 ≤ M ≤ K * n`
(Bary-Soroker-Koukoulopoulos-Kozma 2023, Theorem 1(a), Section 3.1). -/
def H2 : Prop := by
  classical
  exact ∀ K : ℕ, ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ M n : ℕ,
    34 ≤ M → M ≤ K * n → n₀ ≤ n →
    let eligible := (Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
      (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0
    ((eligible.filter fun a => ∃ g : ℤ[X], g.Monic ∧
      g ∣ Green93.monicPoly (fun j => (a j : ℕ)) ∧
      (n : ℝ) ^ (1 / 10 : ℝ) ≤ (g.natDegree : ℝ) ∧ 2 * g.natDegree ≤ n).card : ℝ) ≤
      ((n : ℝ) ^ (-c) / 2) * eligible.card

section Helpers

open scoped Classical

private lemma eligible_card_eq (M n : ℕ) (hn : 1 ≤ n) :
    ((Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
      (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0).card =
      M * (M + 1) ^ (n - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [Nat.add_sub_cancel]
  let S := (Finset.univ : Finset (Fin (k + 1) → Fin (M + 1))).filter fun a =>
    (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0
  let nz : Finset (Fin (M + 1)) := Finset.univ.filter fun x => x.val ≠ 0
  let T : Finset (Fin (M + 1) × (Fin k → Fin (M + 1))) := nz ×ˢ Finset.univ
  have hS_eq_T : S.card = T.card := by
    refine Finset.card_bij
      (fun a _ => (a 0, fun i : Fin k => a i.succ)) ?_ ?_ ?_
    · intro a ha
      rw [Finset.mem_filter] at ha
      have h0 : (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 = (a 0 : ℤ) :=
        OMA.R_Green93_green_93_variants_bskk_large_R1.green93_coeff_below
          (fun j => (a j : ℕ)) 0
      rw [h0] at ha
      have ha0 : (a 0).val ≠ 0 := by
        intro hzero
        exact ha.2 (by exact_mod_cast hzero)
      exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha0⟩,
        Finset.mem_univ _⟩
    · intro a₁ _ a₂ _ h
      have h0 : a₁ 0 = a₂ 0 := congrArg Prod.fst h
      have htail : (fun i : Fin k => a₁ i.succ) = (fun i : Fin k => a₂ i.succ) :=
        congrArg Prod.snd h
      funext i
      refine Fin.cases h0 (fun j => congrFun htail j) i
    · intro p hp
      rcases Finset.mem_product.mp hp with ⟨hp1, _⟩
      have hp1_ne : p.1.val ≠ 0 := (Finset.mem_filter.mp hp1).2
      let c : Fin (k + 1) → Fin (M + 1) := Fin.cons p.1 p.2
      refine ⟨c, ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        have h0 : (Green93.monicPoly fun j => (c j : ℕ)).coeff 0 = (p.1 : ℤ) := by
          simpa [c] using
            OMA.R_Green93_green_93_variants_bskk_large_R1.green93_coeff_below
              (fun j => (c j : ℕ)) 0
        rw [h0]
        exact_mod_cast hp1_ne
      · ext
        · simp [c]
        · simp [c]
  have hnz_eq : nz = Finset.univ.erase ⟨0, Nat.succ_pos M⟩ := by
    ext x
    simp only [nz, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true,
      ne_eq, Fin.ext_iff]
  have hnz_card : nz.card = M := by
    rw [hnz_eq, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin]
    omega
  rw [hS_eq_T, Finset.card_product, hnz_card, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin]

private lemma eligible_card_lower (M n : ℕ) (hM : 34 ≤ M) (hn : 1 ≤ n) :
    ((M + 1 : ℝ) ^ n) ≤
      (35 / 34 : ℝ) * (((Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
        (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0).card : ℝ) := by
  rw [eligible_card_eq M n hn]
  have hpow : ((M + 1 : ℝ) ^ n) = (M + 1 : ℝ) * ((M + 1 : ℝ) ^ (n - 1)) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
    simp [pow_succ']
  rw [hpow]
  push_cast
  have hnonneg : (0 : ℝ) ≤ ((M : ℝ) + 1) ^ (n - 1) := by positivity
  have hMreal : (34 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hcoef : (M : ℝ) + 1 ≤ (35 / 34 : ℝ) * (M : ℝ) := by linarith
  calc
    ((M : ℝ) + 1) * ((M : ℝ) + 1) ^ (n - 1)
      ≤ ((35 / 34 : ℝ) * (M : ℝ)) * ((M : ℝ) + 1) ^ (n - 1) :=
        mul_le_mul_of_nonneg_right hcoef hnonneg
    _ = (35 / 34 : ℝ) * ((M : ℝ) * ((M : ℝ) + 1) ^ (n - 1)) := by ring

private lemma exists_monic_dvd_of_dvd_monic {f g : ℤ[X]} (hf : f.Monic) (hdvd : g ∣ f) :
    ∃ g' : ℤ[X], g'.Monic ∧ g'.natDegree = g.natDegree ∧ g' ∣ f := by
  obtain ⟨h, hfh⟩ := hdvd
  have hlc : g.leadingCoeff * h.leadingCoeff = 1 := by
    rw [← Polynomial.leadingCoeff_mul, ← hfh, hf.leadingCoeff]
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hlc with ⟨h1, _⟩ | ⟨hm1, _⟩
  · exact ⟨g, h1, rfl, ⟨h, hfh⟩⟩
  · refine ⟨-g, ?_, Polynomial.natDegree_neg g, ⟨-h, by rw [neg_mul_neg]; exact hfh⟩⟩
    show (-g).leadingCoeff = 1
    rw [Polynomial.leadingCoeff_neg, hm1]
    norm_num

private lemma monicPoly_map_intCast {M n p : ℕ} (a : Fin n → Fin (M + 1)) :
    (Green93.monicPoly fun j => (a j : ℕ)).map (Int.castRingHom (ZMod p)) =
      Polynomial.X ^ n +
        ∑ i : Fin n, Polynomial.C (((a i : ℕ) : ZMod p)) * Polynomial.X ^ (i : ℕ) := by
  unfold Green93.monicPoly
  simp [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum,
    Polynomial.map_mul]

private lemma exists_mod_prime_divisor {M n p : ℕ} (hp : p.Prime)
    (a : Fin n → Fin (M + 1)) {g : ℤ[X]} (hg : g.Monic)
    (hdvd : g ∣ Green93.monicPoly (fun j => (a j : ℕ))) :
    ∃ gp : Polynomial (ZMod p), gp.Monic ∧ gp.natDegree = g.natDegree ∧
      gp ∣ (Polynomial.X ^ n +
        ∑ i : Fin n, Polynomial.C (((a i : ℕ) : ZMod p)) * Polynomial.X ^ (i : ℕ)) := by
  let _ : Fact p.Prime := ⟨hp⟩
  refine ⟨g.map (Int.castRingHom (ZMod p)), hg.map _, hg.natDegree_map _, ?_⟩
  rw [← monicPoly_map_intCast]
  exact map_dvd (Polynomial.mapRingHom (Int.castRingHom (ZMod p))) hdvd

private lemma prod_dvd_of_prime_strictMono {r : ℕ} (p : Fin r → ℕ)
    (hmono : StrictMono p) (hprime : ∀ j, (p j).Prime) {d : ℕ}
    (hd : ∀ j : Fin r, p j ∣ d) :
    (∏ j : Fin r, p j) ∣ d := by
  suffices ∀ s : Finset (Fin r), (∏ j ∈ s, p j) ∣ d from this Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hcop : Nat.Coprime (p a) (∏ j ∈ s, p j) :=
      Nat.Coprime.prod_right fun j hj =>
        (Nat.coprime_primes (hprime a) (hprime j)).mpr
          (hmono.injective.ne (fun h => ha (h ▸ hj)))
    exact hcop.mul_dvd_of_dvd_of_dvd (hd a) ih

private lemma coord_fiber_card_le {M r : ℕ} (p : Fin r → ℕ)
    (hmono : StrictMono p) (hprime : ∀ j, (p j).Prime)
    (v : ∀ j : Fin r, ZMod (p j)) :
    ((Finset.univ : Finset (Fin (M + 1))).filter fun x : Fin (M + 1) =>
      ∀ j : Fin r, (x.val : ZMod (p j)) = v j).card ≤
      M / (∏ j : Fin r, p j) + 1 := by
  let Q := ∏ j : Fin r, p j
  have hQpos : 0 < Q := Finset.prod_pos (fun j _ => (hprime j).pos)
  let S : Finset (Fin (M + 1)) :=
    (Finset.univ : Finset (Fin (M + 1))).filter fun x : Fin (M + 1) =>
      ∀ j : Fin r, (x.val : ZMod (p j)) = v j
  let f : Fin (M + 1) → Fin (M / Q + 1) := fun x =>
    ⟨x.val / Q, Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt_succ x.isLt))⟩
  have haux : ∀ x₁ x₂ : Fin (M + 1), x₁ ∈ S → x₂ ∈ S →
      x₁.val ≤ x₂.val → x₁.val / Q = x₂.val / Q → x₁ = x₂ := by
    intro x₁ x₂ hx₁ hx₂ hle hdiv
    have hv₁ := (Finset.mem_filter.mp hx₁).2
    have hv₂ := (Finset.mem_filter.mp hx₂).2
    have hdvd_all : ∀ j : Fin r, p j ∣ x₂.val - x₁.val := by
      intro j
      rw [← ZMod.natCast_eq_zero_iff]
      rw [Nat.cast_sub hle, hv₂ j, hv₁ j, sub_self]
    have hQdvd : Q ∣ x₂.val - x₁.val :=
      prod_dvd_of_prime_strictMono p hmono hprime hdvd_all
    obtain ⟨k, hk⟩ := hQdvd
    have hsum : x₂.val = x₁.val + Q * k := by omega
    have hdiv2 : x₂.val / Q = x₁.val / Q + k := by
      rw [hsum, Nat.add_mul_div_left _ _ hQpos]
    have hk0 : k = 0 := by omega
    rw [hk0, mul_zero, add_zero] at hsum
    exact Fin.ext hsum.symm
  have hinj : Set.InjOn f ↑S := by
    intro x₁ hx₁ x₂ hx₂ hf
    have hdiv : x₁.val / Q = x₂.val / Q := congrArg Fin.val hf
    rcases le_total x₁.val x₂.val with hle | hle
    · exact haux x₁ x₂ hx₁ hx₂ hle hdiv
    · exact (haux x₂ x₁ hx₂ hx₁ hle hdiv.symm).symm
  have hle_card := Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _) hinj
  simpa [S] using hle_card

private lemma vec_fiber_card_le {M n r : ℕ} (p : Fin r → ℕ)
    (hmono : StrictMono p) (hprime : ∀ j, (p j).Prime)
    (w : ∀ j : Fin r, Fin n → ZMod (p j)) :
    ((Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
      ∀ (j : Fin r) (i : Fin n), ((a i).val : ZMod (p j)) = w j i).card ≤
      (M / (∏ j : Fin r, p j) + 1) ^ n := by
  let F : Fin n → Finset (Fin (M + 1)) := fun i =>
    (Finset.univ : Finset (Fin (M + 1))).filter fun x : Fin (M + 1) =>
      ∀ j : Fin r, (x.val : ZMod (p j)) = w j i
  have heq :
      ((Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
        ∀ (j : Fin r) (i : Fin n), ((a i).val : ZMod (p j)) = w j i) =
      Fintype.piFinset F := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, F]
    exact ⟨fun h i j => h j i, fun h j i => h i j⟩
  rw [heq, Fintype.card_piFinset]
  calc
    ∏ i : Fin n, (F i).card
      ≤ ∏ _i : Fin n, (M / (∏ j : Fin r, p j) + 1) := by
        refine Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => ?_)
        exact coord_fiber_card_le p hmono hprime (fun j => w j i)
    _ = (M / (∏ j : Fin r, p j) + 1) ^ n := by
        simp [Finset.prod_const, Finset.card_univ]

private lemma bad_degree_d_card_le {M n d r : ℕ} (p : Fin r → ℕ)
    (hmono : StrictMono p) [hprime_fact : ∀ j, Fact (p j).Prime] :
    ((Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
      ∃ g : ℤ[X], g.Monic ∧ g.natDegree = d ∧
        g ∣ Green93.monicPoly (fun j => (a j : ℕ))).card ≤
      (M / (∏ j : Fin r, p j) + 1) ^ n *
        ∏ j : Fin r, ((Finset.univ : Finset (Fin n → ZMod (p j))).filter fun b =>
          ∃ gp : Polynomial (ZMod (p j)), gp.Monic ∧ gp.natDegree = d ∧
            gp ∣ (Polynomial.X ^ n +
              ∑ i : Fin n, Polynomial.C (b i) * Polynomial.X ^ (i : ℕ))).card := by
  have hprime : ∀ j, (p j).Prime := fun j => (hprime_fact j).out
  let S := (Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
    ∃ g : ℤ[X], g.Monic ∧ g.natDegree = d ∧
      g ∣ Green93.monicPoly (fun j => (a j : ℕ))
  let BadP : ∀ j : Fin r, Finset (Fin n → ZMod (p j)) := fun j =>
    (Finset.univ : Finset (Fin n → ZMod (p j))).filter fun b =>
      ∃ gp : Polynomial (ZMod (p j)), gp.Monic ∧ gp.natDegree = d ∧
        gp ∣ (Polynomial.X ^ n +
          ∑ i : Fin n, Polynomial.C (b i) * Polynomial.X ^ (i : ℕ))
  let T : Finset (∀ j : Fin r, Fin n → ZMod (p j)) := Fintype.piFinset BadP
  let π : (Fin n → Fin (M + 1)) → (∀ j : Fin r, Fin n → ZMod (p j)) :=
    fun a j i => ((a i).val : ZMod (p j))
  have hmaps : ∀ a ∈ S, π a ∈ T := by
    intro a ha
    rcases (Finset.mem_filter.mp ha).2 with ⟨g, hg, hdeg, hdvd⟩
    refine Fintype.mem_piFinset.mpr (fun j => ?_)
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    obtain ⟨gp, hgp_monic, hgp_deg, hgp_dvd⟩ :=
      exists_mod_prime_divisor (hprime j) a hg hdvd
    exact ⟨gp, hgp_monic, hgp_deg.trans hdeg, hgp_dvd⟩
  have hfib := Finset.card_eq_sum_card_fiberwise hmaps
  calc
    S.card = ∑ w ∈ T, (S.filter fun a => π a = w).card := hfib
    _ ≤ ∑ _w ∈ T, (M / (∏ j : Fin r, p j) + 1) ^ n := by
      refine Finset.sum_le_sum (fun w _ => ?_)
      refine le_trans (Finset.card_le_card ?_) (vec_fiber_card_le p hmono hprime w)
      intro a ha
      rw [Finset.mem_filter] at ha ⊢
      refine ⟨Finset.mem_univ _, fun j i => ?_⟩
      exact congrFun (congrFun ha.2 j) i
    _ = T.card * (M / (∏ j : Fin r, p j) + 1) ^ n := by
      rw [Finset.sum_const, smul_eq_mul]
    _ = (M / (∏ j : Fin r, p j) + 1) ^ n * ∏ j : Fin r, (BadP j).card := by
      rw [mul_comm, Fintype.card_piFinset]

private lemma fiber_distortion_bound {M n Q : ℕ} (hQ : 1 ≤ Q) (hn : 1 ≤ n) (hMn : Q * n ≤ M) :
    (((M / Q + 1 : ℕ) : ℝ) * (Q : ℝ)) ^ n ≤ 3 * ((M + 1 : ℝ) ^ n) := by
  have hnat : (M / Q + 1) * Q ≤ M + Q := by
    have hmul : M / Q * Q ≤ M := Nat.div_mul_le_self M Q
    nlinarith
  have hreal : ((M / Q + 1 : ℕ) : ℝ) * (Q : ℝ) ≤ (M : ℝ) + (Q : ℝ) := by
    exact_mod_cast hnat
  have hstep1 : (((M / Q + 1 : ℕ) : ℝ) * (Q : ℝ)) ^ n ≤ ((M : ℝ) + (Q : ℝ)) ^ n :=
    pow_le_pow_left₀ (by positivity) hreal n
  have hM1pos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hQreal : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hMnreal : (Q : ℝ) * (n : ℝ) ≤ (M : ℝ) := by exact_mod_cast hMn
  have hfrac : ((M : ℝ) + (Q : ℝ)) / ((M : ℝ) + 1) ≤ Real.exp (1 / (n : ℝ)) := by
    have hsplit : ((M : ℝ) + (Q : ℝ)) / ((M : ℝ) + 1) =
        ((Q : ℝ) - 1) / ((M : ℝ) + 1) + 1 := by
      field_simp [hM1pos.ne']
      ring
    rw [hsplit]
    have hle_inv : ((Q : ℝ) - 1) / ((M : ℝ) + 1) ≤ 1 / (n : ℝ) := by
      rw [div_le_div_iff₀ hM1pos hnpos]
      nlinarith
    linarith [Real.add_one_le_exp (1 / (n : ℝ))]
  have hpow_div : (((M : ℝ) + (Q : ℝ)) / ((M : ℝ) + 1)) ^ n ≤ 3 := by
    calc
      (((M : ℝ) + (Q : ℝ)) / ((M : ℝ) + 1)) ^ n
        ≤ (Real.exp (1 / (n : ℝ))) ^ n :=
          pow_le_pow_left₀ (by positivity) hfrac n
      _ = Real.exp ((n : ℝ) * (1 / (n : ℝ))) := (Real.exp_nat_mul _ n).symm
      _ = Real.exp 1 := by
          congr 1
          field_simp [hnpos.ne']
      _ ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have hstep2 : ((M : ℝ) + (Q : ℝ)) ^ n ≤ 3 * ((M : ℝ) + 1) ^ n := by
    have hpow_pos : (0 : ℝ) < ((M : ℝ) + 1) ^ n := pow_pos hM1pos n
    rw [div_pow, div_le_iff₀ hpow_pos] at hpow_div
    exact hpow_div
  exact hstep1.trans hstep2

private lemma large_M_bound (hH1 : H1) :
    ∃ Q n₁ : ℕ, ∀ M n : ℕ, 34 ≤ M → n₁ ≤ n → Q * n ≤ M →
      let eligible := (Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
        (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0
      ((eligible.filter fun a => ∃ g : ℤ[X], g ∣ Green93.monicPoly (fun j => (a j : ℕ)) ∧
        (n : ℝ) ^ (1 / 10 : ℝ) ≤ (g.natDegree : ℝ) ∧ 2 * g.natDegree ≤ n).card : ℝ) ≤
        ((n : ℝ) ^ (-(1 / 20 : ℝ)) / 2) * eligible.card := by
  obtain ⟨δ, hδ, hprime_bound⟩ := hH1
  let r : ℕ := Nat.ceil (11 / δ)
  have hr_ge : (11 : ℝ) ≤ (r : ℝ) * δ := by
    have h1 : 11 / δ ≤ (r : ℝ) := Nat.le_ceil (11 / δ)
    exact (div_le_iff₀ hδ).mp h1
  let p : Fin r → ℕ := fun j => Nat.nth Nat.Prime j.val
  have hmono : StrictMono p :=
    (Nat.nth_strictMono Nat.infinite_setOfPred_prime).comp Fin.val_strictMono
  have hprime : ∀ j : Fin r, (p j).Prime :=
    fun j => Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime j.val
  have : ∀ j : Fin r, Fact (p j).Prime := fun j => ⟨hprime j⟩
  let Q : ℕ := ∏ j : Fin r, p j
  have hQpos : 1 ≤ Q := Nat.succ_le_of_lt (Finset.prod_pos (fun j _ => (hprime j).pos))
  choose C hCpos hCbound using fun j : Fin r => hprime_bound (p j)
  let C_tot : ℝ := ∏ j : Fin r, C j
  have hC_tot_pos : 0 < C_tot := Finset.prod_pos (fun j _ => hCpos j)
  let A : ℝ := 2 * (105 / 34 : ℝ) * C_tot
  have hApos : 0 < A := by positivity
  let n₁ : ℕ := max 1 (Nat.ceil (A ^ (20 : ℕ)))
  refine ⟨Q, n₁, ?_⟩
  intro M n hM hn hMn
  have hn1 : 1 ≤ n := (le_max_left 1 _).trans hn
  have hn_ceil : Nat.ceil (A ^ (20 : ℕ)) ≤ n := (le_max_right 1 _).trans hn
  have hn_real1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  let eligible := (Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
    (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0
  let bad := eligible.filter fun a => ∃ g : ℤ[X], g ∣ Green93.monicPoly (fun j => (a j : ℕ)) ∧
    (n : ℝ) ^ (1 / 10 : ℝ) ≤ (g.natDegree : ℝ) ∧ 2 * g.natDegree ≤ n
  let D : Finset ℕ := (Finset.Icc 1 (n / 2)).filter fun d => (n : ℝ) ^ (1 / 10 : ℝ) ≤ (d : ℝ)
  let S : ℕ → Finset (Fin n → Fin (M + 1)) := fun d =>
    (Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
      ∃ g : ℤ[X], g.Monic ∧ g.natDegree = d ∧
        g ∣ Green93.monicPoly (fun j => (a j : ℕ))
  have hbad_sub : bad ⊆ D.biUnion S := by
    intro a ha
    rcases (Finset.mem_filter.mp ha).2 with ⟨g, hdvd, hdeg_lo, hdeg_hi⟩
    have hf_monic : (Green93.monicPoly fun j => (a j : ℕ)).Monic :=
      (OMA.R_Green93_green_93_variants_bskk_large_R1.green93_monic_of_degree _).monic
    obtain ⟨g', hg'_monic, hg'_deg, hg'_dvd⟩ := exists_monic_dvd_of_dvd_monic hf_monic hdvd
    refine Finset.mem_biUnion.mpr ⟨g.natDegree, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, by omega⟩, hdeg_lo⟩
      have h1_le_pow : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 10 : ℝ) :=
        Real.one_le_rpow hn_real1 (by norm_num)
      have h1_le_deg : (1 : ℝ) ≤ (g.natDegree : ℝ) := h1_le_pow.trans hdeg_lo
      exact_mod_cast h1_le_deg
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨g', hg'_monic, hg'_deg, hg'_dvd⟩⟩
  have hS_bound : ∀ d ∈ D,
      ((S d).card : ℝ) ≤
        (105 / 34 : ℝ) * C_tot * (n : ℝ) ^ (-(11 / 10 : ℝ)) * (eligible.card : ℝ) := by
    intro d hd
    rcases Finset.mem_filter.mp hd with ⟨hdIcc, hd_lo⟩
    rcases Finset.mem_Icc.mp hdIcc with ⟨hd1, hd_half⟩
    have hd2 : 2 * d ≤ n := by omega
    have hcard_d : ((S d).card : ℝ) ≤
        (((M / Q + 1 : ℕ) : ℝ) ^ n) *
          ∏ j : Fin r, (((Finset.univ : Finset (Fin n → ZMod (p j))).filter fun b =>
            ∃ gp : Polynomial (ZMod (p j)), gp.Monic ∧ gp.natDegree = d ∧
              gp ∣ (Polynomial.X ^ n +
                ∑ i : Fin n, Polynomial.C (b i) * Polynomial.X ^ (i : ℕ))).card : ℝ) := by
      exact_mod_cast bad_degree_d_card_le (M := M) (n := n) (d := d) p hmono
    have hprod_le :
        ∏ j : Fin r, (((Finset.univ : Finset (Fin n → ZMod (p j))).filter fun b =>
          ∃ gp : Polynomial (ZMod (p j)), gp.Monic ∧ gp.natDegree = d ∧
            gp ∣ (Polynomial.X ^ n +
              ∑ i : Fin n, Polynomial.C (b i) * Polynomial.X ^ (i : ℕ))).card : ℝ) ≤
          ∏ j : Fin r, (C j * (d : ℝ) ^ (-δ) * (p j : ℝ) ^ n) := by
      refine Finset.prod_le_prod (fun _ _ => by positivity) (fun j _ => ?_)
      exact hCbound j n d hd1 hd2
    have hprod_eq :
        ∏ j : Fin r, (C j * (d : ℝ) ^ (-δ) * (p j : ℝ) ^ n) =
          C_tot * ((d : ℝ) ^ (-δ)) ^ r * (Q : ℝ) ^ n := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]
      have hQp : (∏ j : Fin r, (p j : ℝ) ^ n) = (Q : ℝ) ^ n := by
        simp only [Q, Nat.cast_prod, Finset.prod_pow]
      rw [hQp]
    have hd_pow_le : ((d : ℝ) ^ (-δ)) ^ r ≤ (n : ℝ) ^ (-(11 / 10 : ℝ)) := by
      have hpow_pos : (0 : ℝ) < (n : ℝ) ^ (1 / 10 : ℝ) := Real.rpow_pos_of_pos hn_pos _
      have hstep_d : (d : ℝ) ^ (-δ) ≤ ((n : ℝ) ^ (1 / 10 : ℝ)) ^ (-δ) :=
        Real.rpow_le_rpow_of_nonpos hpow_pos hd_lo (by linarith)
      have hstep_r : ((d : ℝ) ^ (-δ)) ^ r ≤ (((n : ℝ) ^ (1 / 10 : ℝ)) ^ (-δ)) ^ r :=
        pow_le_pow_left₀ (by positivity) hstep_d r
      have hrw : (((n : ℝ) ^ (1 / 10 : ℝ)) ^ (-δ)) ^ r =
          (n : ℝ) ^ (-((r : ℝ) * δ / 10)) := by
        rw [← Real.rpow_mul hn_pos.le, ← Real.rpow_natCast, ← Real.rpow_mul hn_pos.le]
        congr 1
        ring
      rw [hrw] at hstep_r
      refine hstep_r.trans (Real.rpow_le_rpow_of_exponent_le hn_real1 ?_)
      linarith
    have hdist : (((M / Q + 1 : ℕ) : ℝ) * (Q : ℝ)) ^ n ≤ 3 * ((M + 1 : ℝ) ^ n) :=
      fiber_distortion_bound hQpos hn1 hMn
    have helig : ((M + 1 : ℝ) ^ n) ≤ (35 / 34 : ℝ) * (eligible.card : ℝ) :=
      eligible_card_lower M n hM hn1
    calc
      ((S d).card : ℝ)
        ≤ (((M / Q + 1 : ℕ) : ℝ) ^ n) * (C_tot * ((d : ℝ) ^ (-δ)) ^ r * (Q : ℝ) ^ n) :=
          hcard_d.trans (mul_le_mul_of_nonneg_left (hprod_le.trans_eq hprod_eq) (by positivity))
      _ = C_tot * ((d : ℝ) ^ (-δ)) ^ r * ((((M / Q + 1 : ℕ) : ℝ) * (Q : ℝ)) ^ n) := by
          rw [mul_pow]
          ring
      _ ≤ C_tot * (n : ℝ) ^ (-(11 / 10 : ℝ)) * (3 * ((35 / 34 : ℝ) * (eligible.card : ℝ))) := by
          refine mul_le_mul ?_ (hdist.trans (mul_le_mul_of_nonneg_left helig (by norm_num)))
            (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left hd_pow_le hC_tot_pos.le
      _ = (105 / 34 : ℝ) * C_tot * (n : ℝ) ^ (-(11 / 10 : ℝ)) * (eligible.card : ℝ) := by
          ring
  have hD_card : (D.card : ℝ) ≤ (n : ℝ) := by
    have hD_nat : D.card ≤ n := by
      calc
        D.card ≤ (Finset.Icc 1 (n / 2)).card := Finset.card_filter_le _ _
        _ = n / 2 := by simp
        _ ≤ n := Nat.div_le_self n 2
    exact_mod_cast hD_nat
  have hbad_le : (bad.card : ℝ) ≤
      (n : ℝ) * ((105 / 34 : ℝ) * C_tot * (n : ℝ) ^ (-(11 / 10 : ℝ)) * (eligible.card : ℝ)) := by
    have h1 : (bad.card : ℝ) ≤ ∑ d ∈ D, ((S d).card : ℝ) := by
      exact_mod_cast (Finset.card_le_card hbad_sub).trans Finset.card_biUnion_le
    calc
      (bad.card : ℝ) ≤ ∑ d ∈ D, ((S d).card : ℝ) := h1
      _ ≤ ∑ _d ∈ D, ((105 / 34 : ℝ) * C_tot * (n : ℝ) ^ (-(11 / 10 : ℝ)) * (eligible.card : ℝ)) :=
          Finset.sum_le_sum hS_bound
      _ = (D.card : ℝ) *
            ((105 / 34 : ℝ) * C_tot * (n : ℝ) ^ (-(11 / 10 : ℝ)) * (eligible.card : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (n : ℝ) * ((105 / 34 : ℝ) * C_tot * (n : ℝ) ^ (-(11 / 10 : ℝ)) * (eligible.card : ℝ)) :=
          mul_le_mul_of_nonneg_right hD_card (by positivity)
  have hA_le_n : A ≤ (n : ℝ) ^ (1 / 20 : ℝ) := by
    have hA20 : A ^ (20 : ℕ) ≤ (n : ℝ) :=
      (Nat.le_ceil (A ^ (20 : ℕ))).trans (by exact_mod_cast hn_ceil)
    have hstep : (A ^ (20 : ℝ)) ^ (1 / 20 : ℝ) ≤ (n : ℝ) ^ (1 / 20 : ℝ) := by
      refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
      simpa [Real.rpow_natCast] using hA20
    have hsimp : (A ^ (20 : ℝ)) ^ (1 / 20 : ℝ) = A := by
      rw [← Real.rpow_mul hApos.le]
      norm_num
    rwa [hsimp] at hstep
  have hconst_le : (105 / 34 : ℝ) * C_tot * (n : ℝ) ^ (-(1 / 20 : ℝ)) ≤ 1 / 2 := by
    have hmul : A * (n : ℝ) ^ (-(1 / 20 : ℝ)) ≤ 1 := by
      calc
        A * (n : ℝ) ^ (-(1 / 20 : ℝ))
          ≤ (n : ℝ) ^ (1 / 20 : ℝ) * (n : ℝ) ^ (-(1 / 20 : ℝ)) :=
            mul_le_mul_of_nonneg_right hA_le_n (by positivity)
        _ = (n : ℝ) ^ ((1 / 20 : ℝ) + -(1 / 20 : ℝ)) := (Real.rpow_add hn_pos _ _).symm
        _ = 1 := by norm_num
    dsimp [A] at hmul
    linarith
  have hpow_split : (n : ℝ) * (n : ℝ) ^ (-(11 / 10 : ℝ)) =
      (n : ℝ) ^ (-(1 / 20 : ℝ)) * (n : ℝ) ^ (-(1 / 20 : ℝ)) := by
    calc
      (n : ℝ) * (n : ℝ) ^ (-(11 / 10 : ℝ))
        = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(11 / 10 : ℝ)) := by rw [Real.rpow_one]
      _ = (n : ℝ) ^ ((1 : ℝ) + -(11 / 10 : ℝ)) := (Real.rpow_add hn_pos _ _).symm
      _ = (n : ℝ) ^ (-(1 / 20 : ℝ) + -(1 / 20 : ℝ)) := by norm_num
      _ = (n : ℝ) ^ (-(1 / 20 : ℝ)) * (n : ℝ) ^ (-(1 / 20 : ℝ)) := Real.rpow_add hn_pos _ _
  calc
    (bad.card : ℝ)
      ≤ (n : ℝ) * ((105 / 34 : ℝ) * C_tot * (n : ℝ) ^ (-(11 / 10 : ℝ)) * (eligible.card : ℝ)) :=
        hbad_le
    _ = ((105 / 34 : ℝ) * C_tot * (n : ℝ) ^ (-(1 / 20 : ℝ))) *
          ((n : ℝ) ^ (-(1 / 20 : ℝ)) * (eligible.card : ℝ)) := by
        calc
          (n : ℝ) * ((105 / 34 : ℝ) * C_tot * (n : ℝ) ^ (-(11 / 10 : ℝ)) * (eligible.card : ℝ))
            = (105 / 34 : ℝ) * C_tot * ((n : ℝ) * (n : ℝ) ^ (-(11 / 10 : ℝ))) *
                (eligible.card : ℝ) := by ring
          _ = (105 / 34 : ℝ) * C_tot *
                ((n : ℝ) ^ (-(1 / 20 : ℝ)) * (n : ℝ) ^ (-(1 / 20 : ℝ))) *
                (eligible.card : ℝ) := by rw [hpow_split]
          _ = ((105 / 34 : ℝ) * C_tot * (n : ℝ) ^ (-(1 / 20 : ℝ))) *
                ((n : ℝ) ^ (-(1 / 20 : ℝ)) * (eligible.card : ℝ)) := by ring
    _ ≤ (1 / 2 : ℝ) * ((n : ℝ) ^ (-(1 / 20 : ℝ)) * (eligible.card : ℝ)) :=
        mul_le_mul_of_nonneg_right hconst_le (by positivity)
    _ = ((n : ℝ) ^ (-(1 / 20 : ℝ)) / 2) * (eligible.card : ℝ) := by ring

end Helpers

theorem main : H1 → H2 → OMA.R_Green93_green_93_variants_bskk_large_R1.H2 := by
  classical
  intro hH1 hH2
  obtain ⟨Q, n₁, hlarge⟩ := large_M_bound hH1
  obtain ⟨c₂, hc₂, n₂, hsmall⟩ := hH2 Q
  refine ⟨min (1 / 20 : ℝ) c₂, lt_min (by norm_num) hc₂, max 1 (max n₁ n₂), ?_⟩
  intro M n hM hn _hlog
  have hn1 : 1 ≤ n := (le_max_left 1 _).trans hn
  have hmax : max n₁ n₂ ≤ n := (le_max_right 1 _).trans hn
  have hn_real1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  let eligible := (Finset.univ : Finset (Fin n → Fin (M + 1))).filter fun a =>
    (Green93.monicPoly fun j => (a j : ℕ)).coeff 0 ≠ 0
  let bad := eligible.filter fun a => ∃ g : ℤ[X], g ∣ Green93.monicPoly (fun j => (a j : ℕ)) ∧
    (n : ℝ) ^ (1 / 10 : ℝ) ≤ (g.natDegree : ℝ) ∧ 2 * g.natDegree ≤ n
  change (bad.card : ℝ) ≤ ((n : ℝ) ^ (-min (1 / 20 : ℝ) c₂) / 2) * (eligible.card : ℝ)
  by_cases hMQ : M ≤ Q * n
  · have hmonic_sub :
        bad ⊆ eligible.filter fun a => ∃ g : ℤ[X], g.Monic ∧
          g ∣ Green93.monicPoly (fun j => (a j : ℕ)) ∧
          (n : ℝ) ^ (1 / 10 : ℝ) ≤ (g.natDegree : ℝ) ∧ 2 * g.natDegree ≤ n := by
      intro a ha
      rcases Finset.mem_filter.mp ha with ⟨helig, g, hdvd, hlo, hhi⟩
      have hf_monic : (Green93.monicPoly fun j => (a j : ℕ)).Monic :=
        (OMA.R_Green93_green_93_variants_bskk_large_R1.green93_monic_of_degree _).monic
      obtain ⟨g', hg'_monic, hg'_deg, hg'_dvd⟩ := exists_monic_dvd_of_dvd_monic hf_monic hdvd
      exact Finset.mem_filter.mpr
        ⟨helig, g', hg'_monic, hg'_dvd, by rwa [hg'_deg], by rwa [hg'_deg]⟩
    have hcard_le : (bad.card : ℝ) ≤
        ((eligible.filter fun a => ∃ g : ℤ[X], g.Monic ∧
          g ∣ Green93.monicPoly (fun j => (a j : ℕ)) ∧
          (n : ℝ) ^ (1 / 10 : ℝ) ≤ (g.natDegree : ℝ) ∧ 2 * g.natDegree ≤ n).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hmonic_sub
    have h2 := hsmall M n hM hMQ ((le_max_right n₁ n₂).trans hmax)
    have hpow : (n : ℝ) ^ (-c₂) ≤ (n : ℝ) ^ (-min (1 / 20 : ℝ) c₂) :=
      Real.rpow_le_rpow_of_exponent_le hn_real1 (neg_le_neg (min_le_right _ _))
    have hscale : ((n : ℝ) ^ (-c₂) / 2) * (eligible.card : ℝ) ≤
        ((n : ℝ) ^ (-min (1 / 20 : ℝ) c₂) / 2) * (eligible.card : ℝ) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hpow (by norm_num)) (by positivity)
    exact (hcard_le.trans h2).trans hscale
  · have hQnM : Q * n ≤ M := Nat.le_of_not_ge hMQ
    have h1 := hlarge M n hM ((le_max_left n₁ n₂).trans hmax) hQnM
    have hpow : (n : ℝ) ^ (-(1 / 20 : ℝ)) ≤ (n : ℝ) ^ (-min (1 / 20 : ℝ) c₂) :=
      Real.rpow_le_rpow_of_exponent_le hn_real1 (neg_le_neg (min_le_left _ _))
    have hscale : ((n : ℝ) ^ (-(1 / 20 : ℝ)) / 2) * (eligible.card : ℝ) ≤
        ((n : ℝ) ^ (-min (1 / 20 : ℝ) c₂) / 2) * (eligible.card : ℝ) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hpow (by norm_num)) (by positivity)
    exact h1.trans hscale

end OMA.R_Green93_green_93_variants_bskk_large_R1_H2_R1
