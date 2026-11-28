import OMAReductions.R_Green46_green_46_variants_lower_R1_H1_R1

-- Reduction Green46.green_46.variants.lower.R1.H1.R1.H2.R1 of step Green46.green_46.variants.lower.R1.H1.R1.H2
-- Credit: @Abubakar2105

/-!
# Rounding by rounds: the covering theorem and a random partition

Ford, Green, Konyagin, Maynard and Tao, *Long gaps between primes*,
JAMS 31 (2018), Theorem 3 and the proof of Corollary 4.
The first hypothesis is Theorem 3 (probabilistic covering) in a finite,
derandomized form: for disjoint rounds of sparse random edges with small
codegrees and controlled degrees, some selection leaves at most
(1+δ^(1/10^(m+1))) Σ_v P_m(v) vertices uncovered, where P_j is the
recursion P_(j+1)(v) = P_j(v) exp(-d_(I_(j+1))(v)/P_j(v)).
The second is the random partition step of Corollary 4: the primes can be
split into disjoint rounds whose degree shares are prescribed fractions of
the full degree, up to 1/U², by Hoeffding and a union bound.
The main proof takes shares 5^(1-j) log 5 / C for m = ⌊log U / log 5⌋
rounds, shows by induction that P_j(v) = 5^(-j) e^(λ) with |λ| ≤ 2·4^j·(2/U),
checks the smallness condition with δ = X^(-1/10), r = √(log X), D = 4,
κ = 1/(2·5^m), and concludes with at most 12 |V| / U uncovered vertices.
-/

namespace OMA.R_Green46_green_46_variants_lower_R1_H1_R1_H2_R1

open Finset Filter Real
open scoped Classical

private lemma log5_le : log 5 ≤ 33/20 := by
  have h : log 5 = 2 * log 2 + log (5/4) := by
    rw [show (5:ℝ) = 2*2*(5/4) by norm_num, log_mul (by norm_num) (by norm_num),
      log_mul (by norm_num) (by norm_num)]; norm_num; ring
  have h1 := Real.log_two_lt_d9
  have h2 : log (5/4:ℝ) ≤ 5/4 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  linarith

private lemma one_le_log5 : 1 ≤ log 5 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have := Real.exp_one_lt_d9; linarith

private lemma step_bound {l ν μ : ℝ} (hl : |l| ≤ 1/10) (hν : |ν| ≤ μ) :
    |log 5 + l - log 5*(1+ν)*exp (-l)| ≤ 3*|l| + 2*μ := by
  set L := log 5 with hLdef
  have hL1 := one_le_log5; have hL2 := log5_le
  set r := exp (-l) - 1 - (-l) with hr
  have hr1 : |r| ≤ (-l)^2 := Real.abs_exp_sub_one_sub_id_le (by rw [abs_neg]; linarith)
  have hl2 : (-l)^2 ≤ |l|/10 := by
    rw [neg_sq, ← sq_abs]; nlinarith [abs_nonneg l]
  have he : exp (-l) = 1 - l + r := by rw [hr]; ring
  have hE : exp (-l) ≤ 6/5 := by
    rw [he]; have := (abs_le.mp hl).1; have := (abs_le.mp hr1).2; linarith
  have hνe : |ν * exp (-l)| ≤ μ * (6/5) := by
    rw [abs_mul, abs_of_pos (exp_pos _)]
    exact mul_le_mul hν hE (exp_pos _).le ((abs_nonneg _).trans hν)
  have hexp : log 5 + l - log 5*(1+ν)*exp (-l) = (1+L)*l - L*r - L*(ν*exp (-l)) := by
    rw [he]; ring
  rw [hexp]
  have a1 : |(1+L)*l| = (1+L)*|l| := by rw [abs_mul, abs_of_pos (by linarith)]
  have a2 : |L*r| = L*|r| := by rw [abs_mul, abs_of_pos (by linarith)]
  have a3 : |L*(ν*exp (-l))| = L*|ν*exp (-l)| := by rw [abs_mul, abs_of_pos (by linarith)]
  have t1 := abs_sub ((1+L)*l - L*r) (L*(ν*exp (-l)))
  have t2 := abs_sub ((1+L)*l) (L*r)
  have b1 : (1+L)*|l| ≤ (53/20)*|l| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
  have b2 : L*|r| ≤ (33/20)*(|l|/10) := mul_le_mul hL2 (hr1.trans hl2) (abs_nonneg _) (by norm_num)
  have b3 : L*|ν*exp (-l)| ≤ (33/20)*(μ*(6/5)) := mul_le_mul hL2 hνe (abs_nonneg _) (by norm_num)
  have := (abs_nonneg ν).trans hν
  have := abs_nonneg l
  linarith

private lemma rec_bound (dd Pr : ℕ → ℝ) (m : ℕ) (μ : ℝ) (hμ : 0 ≤ μ) (hsmall : 2*4^m*μ ≤ 1/10)
    (h0 : Pr 0 = 1) (hrec : ∀ j < m, Pr (j+1) = Pr j * exp (-dd (j+1) / Pr j))
    (hd : ∀ j < m, |dd (j+1) - (1/5)^j*log 5| ≤ μ*((1/5)^j*log 5)) :
    ∀ j ≤ m, ∃ l, |l| ≤ 2*4^j*μ ∧ Pr j = (1/5)^j * exp l := by
  intro j
  induction j with
  | zero => intro _; exact ⟨0, by simp; positivity, by simp [h0]⟩
  | succ j ih =>
    intro hj
    obtain ⟨l, hl, hP⟩ := ih (by omega)
    have hjm : j < m := by omega
    set a := (1/5:ℝ)^j*log 5 with ha
    have hL1 := one_le_log5
    have hapos : 0 < a := by positivity
    set ν := (dd (j+1) - a)/a with hν
    have hdd : dd (j+1) = a*(1+ν) := by rw [hν]; field_simp; ring
    have hνb : |ν| ≤ μ := by
      rw [hν, abs_div, abs_of_pos hapos, div_le_iff₀ hapos]; exact hd j hjm
    have h4 : (4:ℝ)^j ≤ 4^m := pow_le_pow_right₀ (by norm_num) hjm.le
    have hl' : |l| ≤ 1/10 := by nlinarith
    refine ⟨log 5 + l - log 5*(1+ν)*exp (-l), ?_, ?_⟩
    · have := step_bound hl' hνb
      have h1 : (1:ℝ) ≤ 4^j := one_le_pow₀ (by norm_num)
      rw [pow_succ]; nlinarith
    · rw [hrec j hjm, hP, hdd, ha]
      have hel := exp_pos l
      have h5 : (0:ℝ) < (1/5)^j := by positivity
      have key : -((1/5)^j*log 5*(1+ν)) / ((1/5)^j*exp l) = -(log 5*(1+ν)*exp (-l)) := by
        rw [exp_neg]; field_simp
      rw [key, show log 5 + l - log 5*(1+ν)*exp (-l) = (log 5 + l) + -(log 5*(1+ν)*exp (-l)) by ring,
        exp_add, exp_add, exp_log (by norm_num)]
      ring

private lemma ev (C₀ : ℝ) (hC : 1 ≤ C₀) : ∀ᶠ x : ℕ in atTop,
    (5:ℝ)^18 ≤ log (log (x:ℝ)) ∧ 1000*(21+C₀)*log (log (x:ℝ))^4 ≤ √(log (x:ℝ)) ∧
    1 ≤ log (x:ℝ) := by
  have hX : Tendsto (fun x : ℕ => (x:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hL : Tendsto (fun x : ℕ => log (x:ℝ)) atTop atTop := tendsto_log_atTop.comp hX
  have hU : Tendsto (fun x : ℕ => log (log (x:ℝ))) atTop atTop := tendsto_log_atTop.comp hL
  have hc : (0:ℝ) < 1/(1000*(21+C₀)) := by positivity
  have hb := (isLittleO_log_rpow_rpow_atTop (4:ℝ) (by norm_num : (0:ℝ) < 1/2)).bound hc
  have hb' : ∀ᶠ L : ℝ in atTop, 1000*(21+C₀)*log L^4 ≤ √L := by
    filter_upwards [hb, eventually_ge_atTop 1] with L h1 h2
    have hl : 0 ≤ log L := log_nonneg h2
    rw [norm_of_nonneg (rpow_nonneg hl _), norm_of_nonneg (rpow_nonneg (by linarith) _),
      show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, rpow_natCast, ← sqrt_eq_rpow] at h1
    calc 1000*(21+C₀)*log L^4 = (1000*(21+C₀)) * log L^4 := rfl
      _ ≤ (1000*(21+C₀)) * (1/(1000*(21+C₀))*√L) := by gcongr
      _ = √L := by field_simp
  filter_upwards [hU.eventually_ge_atTop ((5:ℝ)^18), hL.eventually hb',
    hL.eventually_ge_atTop 1] with x h1 h2 h3
  exact ⟨h1, h2, h3⟩

private lemma sum_geom_eq (m : ℕ) : (∑ j ∈ Icc 1 m, (1/5:ℝ)^(j-1)) = 5/4*(1-(1/5)^m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Nat.add_sub_cancel, pow_succ]; ring

private lemma sum_geom (m : ℕ) : (∑ j ∈ Icc 1 m, (1/5:ℝ)^(j-1)) ≤ 5/4 := by
  rw [sum_geom_eq]; have : (0:ℝ) ≤ (1/5)^m := by positivity
  linarith

private lemma pow_cmp (m : ℕ) (hm : 17 ≤ m) : 40*(4:ℝ)^m ≤ 5^m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ n _ ih => rw [pow_succ, pow_succ]; nlinarith [pow_pos (by norm_num : (0:ℝ) < 4) n]

private lemma small (C₀ L U X : ℝ) (m : ℕ) (hC : 1 ≤ C₀) (hU : 1 ≤ U) (hL : 1 ≤ L) (hX : 0 < X)
    (hLX : log X = L) (hmU : (m:ℝ) ≤ U) (h5 : (5:ℝ)^m ≤ U)
    (hs : 1000*(21+C₀)*U^4 ≤ √L) :
    X^(-1/10:ℝ) ≤ ((1/(2*5^m))^(2*√L*m+1)/(C₀*exp ((2*√L*m+1)*4)))^(10^(m+2)) := by
  set A := 2*√L*m+1 with hA
  set κ : ℝ := 1/(2*5^m) with hκ
  have hκ0 : 0 < κ := by positivity
  have hC0 : 0 < C₀ := by linarith
  have hB : κ^A/(C₀*exp (A*4)) = exp (A*log κ - log C₀ - A*4) := by
    rw [rpow_def_of_pos hκ0, exp_sub, exp_sub, exp_log hC0]; ring_nf
  rw [hB, ← Real.exp_nat_mul, rpow_def_of_pos hX, hLX, exp_le_exp]
  have hlogκ : -log κ ≤ 2*U+1 := by
    have : log κ = -(log 2 + m*log 5) := by
      rw [hκ, log_div (by norm_num) (by positivity), log_one, log_mul (by norm_num) (by positivity),
        log_pow]; ring
    rw [this]
    have := log5_le; have := Real.log_two_lt_d9
    nlinarith
  have hsL : 1 ≤ √L := by rw [show (1:ℝ) = √1 by simp]; exact sqrt_le_sqrt hL
  have hA1 : A ≤ 3*√L*U := by rw [hA]; nlinarith
  have hA0 : 0 ≤ A := by positivity
  have hlogC : log C₀ ≤ C₀ := (log_le_sub_one_of_pos hC0).trans (by linarith)
  have hn : ((10^(m+2) : ℕ):ℝ) ≤ 100*U^2 := by
    push_cast
    have : (10:ℝ)^m ≤ ((5:ℝ)^m)^2 := by
      rw [← pow_mul, mul_comm, pow_mul]; exact pow_le_pow_left₀ (by norm_num) (by norm_num) m
    have h52 : ((5:ℝ)^m)^2 ≤ U^2 := pow_le_pow_left₀ (by positivity) h5 2
    rw [pow_add]; nlinarith
  have hinner : A*(-log κ) + log C₀ + A*4 ≤ (21+C₀)*√L*U^2 := by
    have e1 : A*(-log κ) + A*4 ≤ (3*√L*U)*(2*U+5) := by
      have : A*(-log κ + 4) ≤ (3*√L*U)*(2*U+5) := mul_le_mul hA1 (by linarith)
        (by nlinarith [log_le_sub_one_of_pos hκ0, show κ ≤ 1 by rw [hκ]; rw [div_le_one (by positivity)]; nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 5) (n := m)]])
        (by positivity)
      linarith
    have e2 : (3*√L*U)*(2*U+5) ≤ 21*√L*U^2 := by nlinarith
    have e3 : C₀ ≤ C₀*√L*U^2 := by
      have : 1 ≤ √L*U^2 := by nlinarith
      nlinarith
    nlinarith
  have hinner0 : 0 ≤ A*(-log κ) + log C₀ + A*4 := by
    have : 0 ≤ -log κ := by
      rw [neg_nonneg]; apply log_nonpos hκ0.le
      rw [hκ, div_le_one (by positivity)]; nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 5) (n := m)]
    have := log_nonneg hC; positivity
  have hsq : √L*√L = L := mul_self_sqrt (by linarith)
  have key : ((10^(m+2) : ℕ):ℝ) * (A*(-log κ) + log C₀ + A*4) ≤ L/10 := by
    calc ((10^(m+2) : ℕ):ℝ) * (A*(-log κ) + log C₀ + A*4)
        ≤ (100*U^2) * ((21+C₀)*√L*U^2) := mul_le_mul hn hinner hinner0 (by positivity)
      _ = (1000*(21+C₀)*U^4) * √L / 10 := by ring
      _ ≤ √L * √L / 10 := by gcongr
      _ = L/10 := by rw [hsq]
  have : ((10^(m+2) : ℕ):ℝ) * (A*log κ - log C₀ - A*4) = -(((10^(m+2) : ℕ):ℝ) * (A*(-log κ) + log C₀ + A*4)) := by ring
  rw [this]; linarith

private lemma err_bound (a s C deg dd U : ℝ) (hU1 : 1 ≤ U) (hC3 : 3 ≤ C) (hs0 : 0 ≤ s)
    (hsa : s*C = a) (haU : 1/U ≤ a) (h1 : |dd - s*deg| ≤ 1/U^2) (h2 : |deg - C| ≤ 1/U^2) :
    |dd - a| ≤ (2/U)*a := by
  have hU0 : 0 < U := by linarith
  have hC0 : 0 < C := by linarith
  have ha0 : 0 ≤ a := le_trans (by positivity) haU
  have hsplit : dd - a = (dd - s * deg) + s * (deg - C) := by rw [← hsa]; ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_nonneg hs0]
  have haU' : 1 ≤ a*U := by rwa [div_le_iff₀ hU0] at haU
  have e1 : 1/U^2 ≤ a/U := by
    rw [div_le_div_iff₀ (by positivity) hU0]
    nlinarith [mul_le_mul_of_nonneg_right haU' hU0.le]
  have hsj : s = a / C := by rw [← hsa]; field_simp
  have e2 : s * |deg - C| ≤ a/U := by
    rw [hsj]
    calc a / C * |deg - C| ≤ a / C * (1/U^2) := by gcongr
      _ ≤ a / U := by
        rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) hU0]
        have hUC : U ≤ C*U^2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hUC ha0]
  have : a/U + a/U = 2/U*a := by ring
  linarith

private lemma final_arith (N S δ' q U : ℝ) (hU0 : 0 < U) (hN : 0 ≤ N) (hS0 : 0 ≤ S)
    (hS : S ≤ N*((6/5)*q)) (hδ0 : 0 ≤ δ') (hδ : δ' ≤ 1) (hq : q ≤ 5/U) :
    (1+δ')*S ≤ 12*N/U := by
  have h2 : (1+δ')*S ≤ 2*(N*((6/5)*q)) := by nlinarith
  have h3 : 2*(N*((6/5)*q)) ≤ 12*N/U := by
    have := mul_le_mul_of_nonneg_left hq hN
    have h5 : N*(5/U) = 5*N/U := by ring
    have : 12*N/U = (12/5)*(5*N/U) := by ring
    nlinarith
  linarith

private lemma deg_arith (d q el μ : ℝ) (h1 : d - q*log 5 ≤ μ*(q*log 5)) (hq : 0 < q)
    (hel : 9/10 ≤ el) (hμ0 : 0 ≤ μ) (hμ : μ ≤ 1/10) : d ≤ 4*(q*el) := by
  have hl5 := log5_le
  have hl1 := one_le_log5
  have hql : 0 ≤ q*log 5 := by positivity
  have e1 : μ*(q*log 5) ≤ (1/10)*(q*log 5) := mul_le_mul_of_nonneg_right hμ hql
  have e2 : q*log 5 ≤ q*(33/20) := mul_le_mul_of_nonneg_left hl5 hq.le
  have e3 : q*(9/10) ≤ q*el := mul_le_mul_of_nonneg_left hel hq.le
  linarith

/-- Theorem 3 of FGKMT (probabilistic covering), derandomized and summed over single vertices. -/
def H1 : Prop :=
  ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ (D r A κ δ : ℝ) (m : ℕ), 1 ≤ D → 1 ≤ r → 2*r*m+1 ≤ A →
    0 < κ → κ ≤ 1/2 → 0 < δ → δ ≤ (κ^A/(C₀*exp (A*D)))^(10^(m+2)) →
    ∀ (I : ℕ → Finset ℕ) (V : Finset ℕ) (E : ℕ → Finset (Finset ℕ))
      (w : ℕ → Finset ℕ → ℝ) (Pr : ℕ → ℕ → ℝ),
    (∀ j ∈ Icc 1 m, ∀ k ∈ Icc 1 m, j ≠ k → Disjoint (I j) (I k)) →
    (∀ j ∈ Icc 1 m, (I j).Nonempty) →
    (∀ j ∈ Icc 1 m, ∀ p ∈ I j, (∑ e ∈ E p, w p e) = 1 ∧
      ∀ e ∈ E p, 0 ≤ w p e ∧ e ⊆ V ∧ (e.card:ℝ) ≤ r) →
    (∀ j ∈ Icc 1 m, ∀ p ∈ I j, ∀ v ∈ V,
      (∑ e ∈ (E p).filter (v ∈ ·), w p e) ≤ δ/√((I j).card)) →
    (∀ j ∈ Icc 1 m, ∀ u ∈ V, ∀ v ∈ V, u ≠ v →
      (∑ p ∈ I j, ∑ e ∈ (E p).filter (fun e => u ∈ e ∧ v ∈ e), w p e) ≤ δ) →
    (∀ v, Pr 0 v = 1) →
    (∀ j < m, ∀ v, Pr (j+1) v =
      Pr j v * exp (-(∑ p ∈ I (j+1), ∑ e ∈ (E p).filter (v ∈ ·), w p e) / Pr j v)) →
    (∀ j ∈ Icc 1 m, ∀ v ∈ V,
      (∑ p ∈ I j, ∑ e ∈ (E p).filter (v ∈ ·), w p e) ≤ D*Pr (j-1) v) →
    (∀ j ≤ m, ∀ v ∈ V, κ ≤ Pr j v) →
    ∃ f : ℕ → Finset ℕ, (∀ j ∈ Icc 1 m, ∀ p ∈ I j, f p = ∅ ∨ f p ∈ E p) ∧
      ((V \ ((Icc 1 m).biUnion I).biUnion f).card : ℝ) ≤
        (1+δ^((1:ℝ)/10^(m+1))) * ∑ v ∈ V, Pr m v

/-- Random partition of the primes into rounds with prescribed degree shares. -/
def H2 : Prop :=
  ∀ K : ℝ, 3≤K → ∀ᶠ x : ℕ in atTop,
    let X : ℝ := x
    let U := log (log X)
    ∀ (P V : Finset ℕ) (E : ℕ → Finset (Finset ℕ)) (w : ℕ → Finset ℕ → ℝ) (C : ℝ)
      (m : ℕ) (s : ℕ → ℝ),
      P.card ≤ x → 3≤C → C≤K →
      (∀ p ∈ P, ∀ e ∈ E p, e ⊆ V ∧ (e.card:ℝ) ≤ √(log X)) →
      (∀ p ∈ P, (∑ e ∈ E p, w p e)=1 ∧ ∀ e ∈ E p, 0≤w p e) →
      (∀ p ∈ P, ∀ q ∈ V, (∑ e ∈ (E p).filter (q ∈ ·), w p e) ≤ X^(-3/5:ℝ)) →
      (∀ q ∈ V, |(∑ p ∈ P, ∑ e ∈ (E p).filter (q ∈ ·), w p e)-C| ≤ 1/U^2) →
      (m:ℝ) ≤ U → (∀ j, 0 ≤ s j) → (∑ j ∈ Icc 1 m, s j) ≤ 1 →
      ∃ I : ℕ → Finset ℕ, (∀ j ∈ Icc 1 m, I j ⊆ P) ∧
        (∀ j ∈ Icc 1 m, ∀ k ∈ Icc 1 m, j ≠ k → Disjoint (I j) (I k)) ∧
        ∀ j ∈ Icc 1 m, ∀ q ∈ V,
          |(∑ p ∈ I j, ∑ e ∈ (E p).filter (q ∈ ·), w p e) -
            s j * ∑ p ∈ P, ∑ e ∈ (E p).filter (q ∈ ·), w p e| ≤ 1/U^2

set_option maxHeartbeats 1600000 in
theorem main : H1 → H2 → OMA.R_Green46_green_46_variants_lower_R1_H1_R1.H2 := by
  classical
  rintro ⟨C₀, hC₀, cover⟩ part K hK
  refine ⟨12, by norm_num, ?_⟩
  filter_upwards [part K hK, ev C₀ hC₀, eventually_gt_atTop 1] with x hpart hev hx1
  dsimp only at hpart ⊢
  have hX1 : (1:ℝ) < x := by exact_mod_cast hx1
  have hX0 : (0:ℝ) < x := by linarith
  set L := log (x:ℝ) with hLdef
  set U := log L with hUdef
  obtain ⟨hU18, hsm, hL1⟩ := hev
  intro P V E w C hP hV hC3 hCK hE hw hmass hdeg hcod
  have hU1 : (1:ℝ) ≤ U := le_trans (by norm_num) hU18
  have hU0 : (0:ℝ) < U := by linarith
  have hl5 := one_le_log5
  have hl5' := log5_le
  set m : ℕ := ⌊log U / log 5⌋₊ with hm
  have hmle : (m:ℝ) ≤ log U / log 5 := Nat.floor_le (div_nonneg (log_nonneg hU1) (by linarith))
  have hmlt : log U / log 5 < m + 1 := Nat.lt_floor_add_one _
  have h5m : (5:ℝ)^m ≤ U := by
    have : (m:ℝ)*log 5 ≤ log U := by rwa [le_div_iff₀ (by linarith)] at hmle
    rw [← log_le_log_iff (by positivity) hU0, log_pow]; exact this
  have h5m1 : U < (5:ℝ)^(m+1) := by
    have : log U < ((m+1:ℕ):ℝ)*log 5 := by push_cast; rwa [div_lt_iff₀ (by linarith)] at hmlt
    rw [← log_lt_log_iff hU0 (by positivity), log_pow]; exact this
  have hmU : (m:ℝ) ≤ U := hmle.trans ((div_le_self (log_nonneg hU1) hl5).trans
    ((log_le_sub_one_of_pos hU0).trans (by linarith)))
  have hm17 : 17 ≤ m := by
    have : (17:ℝ) ≤ log U / log 5 := by
      rw [le_div_iff₀ (by linarith)]
      have : log ((5:ℝ)^18) ≤ log U := log_le_log (by positivity) hU18
      rw [log_pow] at this; push_cast at this; linarith
    exact Nat.le_floor (by exact_mod_cast this)
  have h4m : 40*(4:ℝ)^m ≤ U := (pow_cmp m hm17).trans h5m
  have hinv : (1/5:ℝ)^m ≤ 5/U := by
    rw [one_div_pow, div_le_div_iff₀ (by positivity) hU0]; rw [pow_succ] at h5m1; linarith
  have hinv2 : 1/U ≤ (1/5:ℝ)^m := by
    rw [one_div_pow]; exact one_div_le_one_div_of_le (by positivity) h5m
  have hC0 : (0:ℝ) < C := by linarith
  -- shares
  set s : ℕ → ℝ := fun j => (1/5:ℝ)^(j-1)*log 5/C with hs
  have hs0 : ∀ j, 0 ≤ s j := fun j => by simp only [hs]; positivity
  have hssum : (∑ j ∈ Icc 1 m, s j) ≤ 1 := by
    simp only [hs]
    rw [← Finset.sum_div, ← Finset.sum_mul, div_le_one hC0]
    have := sum_geom m
    nlinarith
  obtain ⟨I, hIP, hdisj, hdev⟩ := hpart P V E w C m s hP hC3 hCK hE hw hmass hdeg hmU hs0 hssum
  obtain ⟨dd, hdd⟩ : ∃ dd : ℕ → ℕ → ℝ, ∀ j v,
      dd j v = ∑ p ∈ I j, ∑ e ∈ (E p).filter (v ∈ ·), w p e := ⟨_, fun _ _ => rfl⟩
  have herr : ∀ j ∈ Icc 1 m, ∀ v ∈ V,
      |dd j v - (1/5:ℝ)^(j-1)*log 5| ≤ (2/U)*((1/5:ℝ)^(j-1)*log 5) := by
    intro j hj v hv
    obtain ⟨hj1, hjm⟩ := Finset.mem_Icc.mp hj
    have hsa : s j * C = (1/5:ℝ)^(j-1)*log 5 := by
      show (1/5:ℝ)^(j-1)*log 5/C*C = _
      field_simp
    have h1 := hdev j hj v hv
    rw [← hdd] at h1
    have hapow : (1/5:ℝ)^m ≤ (1/5)^(j-1) := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    exact err_bound _ _ _ _ _ _ hU1 hC3 (hs0 j) hsa (by nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/5) (j-1)]) h1 (hdeg v hv)
  obtain ⟨Pr, hPr0, hPrrec⟩ : ∃ Pr : ℕ → ℕ → ℝ, (∀ v, Pr 0 v = 1) ∧
      ∀ j v, Pr (j+1) v = Pr j v * exp (-dd (j+1) v / Pr j v) :=
    ⟨fun j v => Nat.rec (motive := fun _ => ℝ) 1 (fun j pj => pj * exp (-dd (j+1) v / pj)) j,
      fun _ => rfl, fun _ _ => rfl⟩
  have hμ : 2*4^m*(2/U) ≤ 1/10 := by
    rw [show 2*4^m*(2/U) = 4*4^m/U by ring, div_le_iff₀ hU0]; linarith
  have hbound : ∀ v ∈ V, ∀ j ≤ m, ∃ l : ℝ, |l| ≤ 1/10 ∧ Pr j v = (1/5)^j * exp l := by
    intro v hv j hj
    obtain ⟨l, hl, hPl⟩ := rec_bound (fun j => dd j v) (fun j => Pr j v) m (2/U) (by positivity)
      hμ (hPr0 v) (fun j _ => hPrrec j v)
      (fun j hj => by
        have := herr (j+1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) v hv
        simpa using this) j hj
    refine ⟨l, ?_, hPl⟩
    have h4 : (4:ℝ)^j ≤ 4^m := pow_le_pow_right₀ (by norm_num) hj
    calc |l| ≤ 2*4^j*(2/U) := hl
      _ ≤ 2*4^m*(2/U) := by gcongr
      _ ≤ 1/10 := hμ
  have hexp_lo : ∀ l : ℝ, |l| ≤ 1/10 → 9/10 ≤ exp l := fun l hl => by
    have := add_one_le_exp l; have := (abs_le.mp hl).1; linarith
  have hexp_hi : ∀ l : ℝ, |l| ≤ 1/10 → exp l ≤ 6/5 := fun l hl => by
    have := Real.abs_exp_sub_one_le (show |l| ≤ 1 by linarith)
    have := (abs_le.mp this).2; linarith
  have hVne : V.Nonempty := by
    rw [← Finset.card_pos]; have : (0:ℝ) < U^3 := by positivity
    exact_mod_cast this.trans_le hV
  have hsL : 1 ≤ √L := by rw [show (1:ℝ) = √1 by simp]; exact sqrt_le_sqrt hL1
  have hδ0 : (0:ℝ) < (x:ℝ)^(-1/10:ℝ) := rpow_pos_of_pos hX0 _
  have hδ1 : (x:ℝ)^(-1/10:ℝ) ≤ 1 := rpow_le_one_of_one_le_of_nonpos hX1.le (by norm_num)
  have hmono : (x:ℝ)^(-3/5:ℝ) ≤ (x:ℝ)^(-1/10:ℝ) :=
    rpow_le_rpow_of_exponent_le hX1.le (by norm_num)
  have hinner0 : ∀ p ∈ P, ∀ (S : Finset (Finset ℕ)), S ⊆ E p → 0 ≤ ∑ e ∈ S, w p e :=
    fun p hp S hS => Finset.sum_nonneg (fun e he => (hw p hp).2 e (hS he))
  obtain ⟨f, hf, hcount⟩ := cover 4 (√L) (2*√L*m+1) (1/(2*5^m)) ((x:ℝ)^(-1/10:ℝ)) m
    (by norm_num) hsL le_rfl (by positivity)
    (by rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 5) (n := m)])
    hδ0 (small C₀ L U (x:ℝ) m hC₀ hU1 hL1 hX0 rfl hmU h5m hsm) I V E w Pr hdisj
    (by
      intro j hj
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      obtain ⟨v, hv⟩ := hVne
      have := herr j hj v hv
      rw [hdd, hne, Finset.sum_empty, zero_sub, abs_neg] at this
      have ha : 0 < (1/5:ℝ)^(j-1)*log 5 := by positivity
      rw [abs_of_pos ha] at this
      have : 2/U < 1 := by rw [div_lt_one hU0]; linarith
      nlinarith)
    (fun j hj p hp => by
      have hp' := hIP j hj hp
      exact ⟨(hw p hp').1, fun e he => ⟨(hw p hp').2 e he, (hE p hp' e he).1, (hE p hp' e he).2⟩⟩)
    (by
      intro j hj p hp v hv
      have hp' := hIP j hj hp
      have hc0 : (0:ℝ) < ((I j).card : ℝ) := by exact_mod_cast Finset.card_pos.mpr ⟨p, hp⟩
      have hcx : ((I j).card : ℝ) ≤ x := by
        exact_mod_cast (Finset.card_le_card (hIP j hj)).trans hP
      rw [le_div_iff₀ (sqrt_pos.mpr hc0)]
      have hsq : √((I j).card : ℝ) ≤ √(x:ℝ) := sqrt_le_sqrt hcx
      have hid : (x:ℝ)^(-3/5:ℝ) * √(x:ℝ) = (x:ℝ)^(-1/10:ℝ) := by
        rw [sqrt_eq_rpow, ← rpow_add hX0]; norm_num
      rw [← hid]
      exact mul_le_mul (hmass p hp' v hv) hsq (sqrt_nonneg _) (by positivity))
    (by
      intro j hj u hu v hv huv
      have hsub : ∀ a b : ℕ, (∑ p ∈ I j, ∑ e ∈ (E p).filter (fun e => a ∈ e ∧ b ∈ e), w p e) ≤
          ∑ p ∈ P, ∑ e ∈ (E p).filter (fun e => a ∈ e ∧ b ∈ e), w p e :=
        fun a b => Finset.sum_le_sum_of_subset_of_nonneg (hIP j hj)
          (fun p hp _ => hinner0 p hp _ (Finset.filter_subset _ _))
      rcases lt_or_gt_of_ne huv with h | h
      · exact (hsub u v).trans ((hcod u hu v hv h).trans hmono)
      · have hsw : (∑ p ∈ I j, ∑ e ∈ (E p).filter (fun e => u ∈ e ∧ v ∈ e), w p e) =
            ∑ p ∈ I j, ∑ e ∈ (E p).filter (fun e => v ∈ e ∧ u ∈ e), w p e :=
          Finset.sum_congr rfl (fun p _ => by
            rw [Finset.filter_congr (fun e _ => and_comm)])
        rw [hsw]; exact (hsub v u).trans ((hcod v hv u hu h).trans hmono))
    hPr0
    (fun j _ v => by rw [hPrrec, hdd])
    (by
      intro j hj v hv
      obtain ⟨hj1, hjm⟩ := Finset.mem_Icc.mp hj
      rw [← hdd]
      have h1 := (abs_le.mp (herr j hj v hv)).2
      obtain ⟨l, hl, hPl⟩ := hbound v hv (j-1) (by omega)
      rw [hPl]
      have : 2/U ≤ 1/10 := by rw [div_le_iff₀ hU0]; linarith
      exact deg_arith _ _ _ _ h1 (by positivity) (hexp_lo l hl) (by positivity) this)
    (by
      intro j hj v hv
      obtain ⟨l, hl, hPl⟩ := hbound v hv j hj
      rw [hPl]
      have := hexp_lo l hl
      have hpj : (1/5:ℝ)^m ≤ (1/5)^j := pow_le_pow_of_le_one (by norm_num) (by norm_num) hj
      have : 1/(2*(5:ℝ)^m) = (1/2)*(1/5)^m := by rw [one_div_pow]; field_simp
      rw [this]
      have : (0:ℝ) ≤ (1/5)^m := by positivity
      nlinarith)
  refine ⟨fun p => if p ∈ (Icc 1 m).biUnion I then f p else ∅, ?_, ?_⟩
  · intro p hp
    dsimp only
    split_ifs with h
    · obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp h
      exact hf j hj p hpj
    · left; rfl
  · have hsub : V \ P.biUnion (fun p => if p ∈ (Icc 1 m).biUnion I then f p else ∅) ⊆
        V \ ((Icc 1 m).biUnion I).biUnion f := by
      intro q hq
      rw [Finset.mem_sdiff] at hq ⊢
      refine ⟨hq.1, fun hq2 => hq.2 ?_⟩
      obtain ⟨p, hp, hqp⟩ := Finset.mem_biUnion.mp hq2
      obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hp
      exact Finset.mem_biUnion.mpr ⟨p, hIP j hj hpj, by rw [if_pos hp]; exact hqp⟩
    have hc1 : ((V \ P.biUnion (fun p => if p ∈ (Icc 1 m).biUnion I then f p else ∅)).card : ℝ) ≤
        ((V \ ((Icc 1 m).biUnion I).biUnion f).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hPrm : ∀ v ∈ V, 0 ≤ Pr m v ∧ Pr m v ≤ (6/5)*(1/5:ℝ)^m := by
      intro v hv
      obtain ⟨l, hl, hPl⟩ := hbound v hv m le_rfl
      rw [hPl]
      have := hexp_hi l hl
      have : (0:ℝ) < (1/5)^m := by positivity
      constructor
      · positivity
      · nlinarith
    have hsum0 : 0 ≤ ∑ v ∈ V, Pr m v := Finset.sum_nonneg (fun v hv => (hPrm v hv).1)
    have hsum1 : (∑ v ∈ V, Pr m v) ≤ V.card * ((6/5)*(1/5:ℝ)^m) := by
      have := Finset.sum_le_sum (fun v hv => (hPrm v hv).2)
      rwa [Finset.sum_const, nsmul_eq_mul] at this
    have hδ' : ((x:ℝ)^(-1/10:ℝ))^((1:ℝ)/10^(m+1)) ≤ 1 :=
      rpow_le_one hδ0.le hδ1 (by positivity)
    have hVc : (0:ℝ) ≤ V.card := by positivity
    exact hc1.trans (hcount.trans (final_arith _ _ _ _ _ hU0 hVc hsum0 hsum1 (by positivity) hδ' hinv))

end OMA.R_Green46_green_46_variants_lower_R1_H1_R1_H2_R1
