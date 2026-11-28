import FormalConjectures.ErdosProblems.«1101»

-- Credit: @MrSeizy
/-!
The prime-pool construction follows the argument recorded in the selection notes for the
Erdős Problem 1101 discussion at https://www.erdosproblems.com/forum/thread/1101.

One prime is sampled independently from each ordered pool. At scale n, a fully covered
interval would require more than n distinct large selected primes. Bounding that event by
finite cylinders over all possible starts gives a summable probability. The deterministic
sieve uses the limiting product density to recover the constant in the required gap bound.
-/

open Filter Finset Asymptotics
open scoped Topology

namespace OMA.Erdos1101PartII

namespace GoodPools

private theorem real_sqrt_lt (n : ℕ) : Real.sqrt n < (n.sqrt : ℝ) + 1 := by
  apply (Real.sqrt_lt (by positivity) (by positivity)).2
  rw [← Nat.cast_one, ← Nat.cast_add, pow_two]
  exact_mod_cast Nat.lt_succ_sqrt n

private theorem sqrt_tendsto : Tendsto (fun n : ℕ => (n.sqrt : ℝ)) atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
    ((max b 0 + 1)^2)] with n hn
  have h := real_sqrt_lt n
  have h' := Real.le_sqrt_of_sq_le hn
  linarith [le_max_left b 0]

private theorem log_add_le_sqrt (c : ℝ) (d : ℝ) (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, Real.log (n + c) ≤ d * (n.sqrt : ℝ) := by
  have hl := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    ((isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).bound
      (show 0 < d / 4 by positivity))
  filter_upwards [hl, (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (max (|c| + 1) 1),
    sqrt_tendsto.eventually_ge_atTop (max 1 (4 * Real.log 2 / d))] with n hl hn hs
  have hn1 : (1 : ℝ) ≤ n := (le_max_right _ _).trans hn
  have habs : |c| + 1 ≤ (n : ℝ) := (le_max_left _ _).trans hn
  have hnc : c ≤ n := by linarith [le_abs_self c]
  have hs1 : (1 : ℝ) ≤ n.sqrt := (le_max_left _ _).trans hs
  have hs2 : 4 * Real.log 2 ≤ d * (n.sqrt : ℝ) := by
    have h := (le_max_right (1 : ℝ) _).trans hs
    have := (div_le_iff₀ hd).mp h
    linarith
  change |Real.log (n : ℝ)| ≤ d / 4 * |(n : ℝ) ^ (1 / 2 : ℝ)| at hl
  rw [abs_of_nonneg (Real.log_nonneg hn1), abs_of_nonneg (Real.rpow_nonneg (by positivity) _),
    ← Real.sqrt_eq_rpow] at hl
  calc
    Real.log (n + c) ≤ Real.log (2 * (n : ℝ)) :=
      Real.log_le_log (by linarith [neg_abs_le c]) (by linarith)
    _ = Real.log 2 + Real.log n := Real.log_mul (by norm_num) (by positivity)
    _ ≤ d * (n.sqrt : ℝ) := by
      have := mul_le_mul_of_nonneg_left (real_sqrt_lt n).le (show 0 ≤ d / 4 by positivity)
      nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hs1)]

private theorem theta_half :
    ∀ᶠ x : ℝ in atTop, x * (Real.log 2 / 2) ≤ Chebyshev.theta x := by
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl := (isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).bound
      (show 0 < Real.log 2 / 8 by positivity)
  filter_upwards [hl, eventually_ge_atTop (32 : ℝ)] with x hl h32
  have h16 : 16 ≤ x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hxp : 0 < x := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1),
    abs_of_nonneg (Real.rpow_nonneg hxp.le _), ← Real.sqrt_eq_rpow] at hl
  have hs : Real.sqrt x ≤ x / 4 := by
    have hs4 : 4 ≤ Real.sqrt x := by
      apply Real.le_sqrt_of_sq_le
      norm_num
      exact h16
    nlinarith [Real.sq_sqrt hxp.le, mul_nonneg (Real.sqrt_nonneg x) (sub_nonneg.mpr hs4)]
  have hmul : 2 * Real.sqrt x * Real.log x ≤ x * (Real.log 2 / 4) := by
    have := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2 * Real.sqrt x by positivity)
    nlinarith [Real.sq_sqrt hxp.le]
  have hlog : Real.log (x + 2) ≤ x * (Real.log 2 / 16) := by
    have he : Real.log (x + 2) ≤ Real.log 2 + Real.log x := by
      rw [← Real.log_mul (by norm_num) hxp.ne']
      exact Real.log_le_log (by positivity) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hs (show 0 ≤ Real.log 2 / 8 by positivity),
      mul_nonneg hp.le (sub_nonneg.mpr h32)]
  nlinarith [Chebyshev.theta_ge' hx1, mul_nonneg hp.le (sub_nonneg.mpr h16)]

private def primeBand (j : ℕ) : Finset ℕ :=
  Nat.primesLE (8 ^ (j+1)) \ Nat.primesLE (8 ^ j)

private theorem mem_primeBand {j p : ℕ} :
    p ∈ primeBand j ↔ 8 ^ j < p ∧ p ≤ 8 ^ (j+1) ∧ p.Prime := by
  rw [primeBand, Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hu, hp⟩, hl⟩
    exact ⟨lt_of_not_ge fun h => hl ⟨h, hp⟩, hu, hp⟩
  · rintro ⟨hl, hu, hp⟩
    exact ⟨⟨hu, hp⟩, fun h => hl.not_ge h.1⟩

private theorem band_card :
    ∀ᶠ j : ℕ in atTop, (8 : ℝ)^j ≤ 2 * (j + 1) * (primeBand j).card := by
  have he : Tendsto (fun j : ℕ => (((8 : ℕ) ^ (j+1) : ℕ) : ℝ)) atTop atTop := by
    push_cast
    exact (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 8 by norm_num)).comp
      (tendsto_add_atTop_nat 1)
  filter_upwards [he.eventually theta_half] with j hj
  have hp : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hsub := Nat.primesLE_mono (show (8 : ℕ)^j ≤ 8^(j+1) by gcongr <;> omega)
  have hsum : Chebyshev.theta (((8 : ℕ)^(j+1) : ℕ) : ℝ) - Chebyshev.theta (((8 : ℕ)^j : ℕ) : ℝ) =
      ∑ p ∈ primeBand j, Real.log (p : ℝ) := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log,
      primeBand]
    have h := sum_sdiff (f := fun p : ℕ => Real.log (p : ℝ)) hsub
    linarith
  have hupper := Chebyshev.theta_le_log4_mul_x (x := (((8 : ℕ)^j : ℕ) : ℝ)) (by positivity)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2^3 by norm_num, Real.log_pow]
    norm_num
  have hbound : (∑ p ∈ primeBand j, Real.log (p : ℝ)) ≤
      (primeBand j).card * ((j + 1) * (3 * Real.log 2)) := by
    rw [← nsmul_eq_mul]
    apply sum_le_card_nsmul
    intro p hp'
    have hm := mem_primeBand.mp hp'
    calc
      Real.log (p : ℝ) ≤ Real.log ((8 : ℝ)^(j+1)) :=
        Real.log_le_log (by exact_mod_cast hm.2.2.pos) (by exact_mod_cast hm.2.1)
      _ = (j+1) * (3 * Real.log 2) := by rw [Real.log_pow, hlog8]; push_cast; rfl
  rw [hlog4] at hupper
  push_cast at hj hupper hsum
  rw [pow_succ] at hj hsum
  apply le_of_lt
  have hex : (0 : ℝ) < (8 : ℝ)^j * Real.log 2 := by positivity
  by_contra! hh
  have hmul := mul_le_mul_of_nonneg_right hh hp.le
  nlinarith [hbound]

def size (j : ℕ) : ℕ := 8^j / (8 * (j+1)^2)

theorem log_size (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1) :
    ∀ᶠ j : ℕ in atTop, Real.exp ((1-δ) * j * Real.log 8) ≤ (size j : ℝ) := by
  have hp : 0 < Real.log 8 := Real.log_pos (by norm_num)
  let c := δ * Real.log 8
  have hc : 0 < c := mul_pos hδ hp
  filter_upwards [log_add_le_sqrt 1 (c/4) (by positivity),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (2 * Real.log 16 / c)] with j hj hj'
  have hj_s : (j.sqrt : ℝ) ≤ j := by exact_mod_cast Nat.sqrt_le_self j
  have hlog : Real.log (16 * ((j : ℝ)+1)^2) ≤ c * j := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    have h₁ := mul_le_mul_of_nonneg_left hj_s (show 0 ≤ c/4 by positivity)
    have h₂ := (div_le_iff₀ hc).mp hj'
    norm_num at *
    nlinarith only [hj, h₁, h₂]
  let D : ℕ := 8 * (j+1)^2
  have hD : 0 < D := by dsimp [D]; positivity
  have hDexp : (2 : ℝ) * D ≤ Real.exp (c * j) := by
    have h := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log (by positivity)] at h
    push_cast [D]
    linarith
  have hpow : Real.exp ((j : ℝ) * Real.log 8) = (8 : ℝ)^j := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  have hDj : 2 * D ≤ (8 : ℕ)^j := by
    have h := hDexp.trans (Real.exp_le_exp.mpr (show c * j ≤ j * Real.log 8 by
      dsimp [c]
      have h := mul_le_mul_of_nonneg_right hδ' (show 0 ≤ (j : ℝ) * Real.log 8 by positivity)
      nlinarith))
    rw [hpow] at h
    exact_mod_cast h
  have hq : 1 ≤ size j := Nat.le_div_iff_mul_le hD |>.2 (by simpa using (Nat.le_mul_of_pos_left D (by decide : 0 < 2)).trans hDj)
  have hprod : (8 : ℕ)^j ≤ 2 * D * size j := by
    have hm := Nat.mod_lt ((8 : ℕ)^j) hD
    have h := Nat.mod_add_div ((8 : ℕ)^j) D
    change (8 : ℕ)^j % D + D * size j = 8^j at h
    have h' : D ≤ D * size j := by simpa using Nat.mul_le_mul_left D hq
    calc
      _ ≤ D + D * size j := by omega
      _ ≤ D * size j + D * size j := Nat.add_le_add_right h' _
      _ = _ := by ring
  have hproduct : Real.exp ((1-δ) * j * Real.log 8) * Real.exp (c*j) ≤
      (size j : ℝ) * Real.exp (c*j) := by
    rw [← Real.exp_add, show (1-δ) * j * Real.log 8 + c*j = j * Real.log 8 by dsimp [c]; ring, hpow]
    have h := mul_le_mul_of_nonneg_left hDexp (show 0 ≤ (size j : ℝ) by positivity)
    have h' : (8 : ℝ)^j ≤ 2 * (D : ℝ) * (size j : ℝ) := by exact_mod_cast hprod
    linarith
  exact le_of_mul_le_mul_right hproduct (Real.exp_pos _)

private theorem band_enough :
    ∀ᶠ j : ℕ in atTop, (2*j+1)*size j ≤ (primeBand j).card := by
  filter_upwards [band_card] with j hj
  have hcard : (8 : ℕ)^j ≤ 2 * (j+1) * (primeBand j).card := by exact_mod_cast hj
  have hd : 2*(j+1)*(2*j+1) ≤ 8*(j+1)^2 := by nlinarith
  have hs := Nat.mul_div_le ((8 : ℕ)^j) (8*(j+1)^2)
  change (8*(j+1)^2) * size j ≤ 8^j at hs
  have hc : 2*(j+1)*((2*j+1)*size j) ≤ 2*(j+1)*(primeBand j).card := by
    rw [← Nat.mul_assoc]
    exact (Nat.mul_le_mul_right _ hd).trans (hs.trans hcard)
  exact Nat.le_of_mul_le_mul_left hc (by positivity)

def weight (J i : ℕ) : ℕ := J + i.sqrt

private theorem offsets (i : ℕ) :
    i - i.sqrt^2 < 2*i.sqrt+1 := by
  have h₁ := Nat.sqrt_le i
  have h₂ := Nat.lt_succ_sqrt i
  have h₃ : (i.sqrt+1)*(i.sqrt+1) = i.sqrt^2+2*i.sqrt+1 := by ring
  rw [Nat.succ_eq_add_one, h₃] at h₂
  omega

private theorem band_rank_lt {x y a b : ℕ} (h : x = y) (hab : a < b)
    (ha : a < (primeBand x).card) (hb : b < (primeBand y).card) :
    (primeBand x).orderEmbOfFin rfl ⟨a, ha⟩ < (primeBand y).orderEmbOfFin rfl ⟨b, hb⟩ := by
  subst y
  exact ((primeBand x).orderEmbOfFin rfl).strictMono hab

theorem pools_exist :
    ∀ᶠ J : ℕ in atTop, ∃ P : ℕ → Finset ℕ,
      (∀ i, (P i).Nonempty ∧ (P i).card = size (weight J i)) ∧
      (∀ i p, p ∈ P i → 8 ^ weight J i < p ∧ p ≤ 8 ^ (weight J i + 1) ∧ p.Prime) ∧
      (∀ i j p q, i < j → p ∈ P i → q ∈ P j → p < q) := by
  classical
  have hpositive := log_size (1/2) (by norm_num) (by norm_num)
  obtain ⟨J₀, hJ₀⟩ := eventually_atTop.1 (band_enough.and hpositive)
  filter_upwards [eventually_ge_atTop J₀] with J hJ
  let w := weight J
  let o : ℕ → ℕ := fun i => i - i.sqrt^2
  have hJw : ∀ i, J₀ ≤ w i := fun i => hJ.trans (Nat.le_add_right J _)
  have hc : ∀ i, (2*w i+1)*size (w i) ≤ (primeBand (w i)).card :=
    fun i => (hJ₀ _ (hJw i)).1
  have hs : ∀ i, 0 < size (w i) := by
    intro i
    have h := (Real.exp_pos ((1-1/2)*(w i : ℝ)*Real.log 8)).trans_le (hJ₀ _ (hJw i)).2
    exact_mod_cast h
  have hr : ∀ i (b : Fin (size (w i))), o i * size (w i) + b < (primeBand (w i)).card := by
    intro i b
    apply lt_of_lt_of_le _ (hc i)
    have hb := b.isLt
    have ho : o i + 1 ≤ 2*w i+1 := by
      have := offsets i
      dsimp [o, w, weight]
      omega
    calc
      _ < (o i + 1) * size (w i) := by rw [Nat.add_mul, Nat.one_mul]; omega
      _ ≤ _ := Nat.mul_le_mul_right _ ho
  let f : ∀ i, Fin (size (w i)) → ℕ := fun i b =>
    (primeBand (w i)).orderEmbOfFin rfl ⟨o i * size (w i) + b, hr i b⟩
  let P : ℕ → Finset ℕ := fun i => univ.image (f i)
  have hinj : ∀ i, Function.Injective (f i) := by
    intro i b c h
    have e := ((primeBand (w i)).orderEmbOfFin rfl).injective h
    apply Fin.ext
    have he := congrArg Fin.val e
    dsimp at he
    omega
  have hp : ∀ i p, p ∈ P i → p ∈ primeBand (w i) := by
    intro i p hp
    obtain ⟨b, _, rfl⟩ := mem_image.1 hp
    exact orderEmbOfFin_mem _ _ _
  refine ⟨P, fun i => ?_, fun i p hi => mem_primeBand.1 (hp i p hi), ?_⟩
  · have hcard : (P i).card = size (w i) := by
      simp [P, card_image_of_injective _ (hinj i)]
    exact ⟨card_pos.1 (hcard ▸ hs i), hcard⟩
  · intro i j p q hij hp' hq'
    have hwi : w i ≤ w j := by
      dsimp [w, weight]
      exact Nat.add_le_add_left (Nat.sqrt_le_sqrt hij.le) _
    rcases lt_or_eq_of_le hwi with hw | hw
    · have hpi := mem_primeBand.1 (hp _ _ hp')
      have hqj := mem_primeBand.1 (hp _ _ hq')
      apply hpi.2.1.trans_lt (_ : _ < q)
      exact (Nat.pow_le_pow_right (by decide : 0 < (8 : ℕ)) hw).trans_lt hqj.1
    · obtain ⟨b, _, rfl⟩ := mem_image.1 hp'
      obtain ⟨c, _, rfl⟩ := mem_image.1 hq'
      have hsqrt : i.sqrt = j.sqrt := by
        dsimp [w, weight] at hw
        omega
      have hi := Nat.sqrt_le i
      have hj := Nat.sqrt_le j
      have ho : o i < o j := by
        dsimp [o]
        rw [hsqrt] at hi ⊢
        simp only [pow_two]
        omega
      have hf : ∀ l (z : Fin (size (w l))), f l z =
          (primeBand (w l)).orderEmbOfFin rfl ⟨o l * size (w l) + z, hr l z⟩ := fun _ _ => rfl
      rw [hf, hf]
      apply band_rank_lt hw
      have h := Nat.mul_le_mul_right (size (w i)) (Nat.succ_le_of_lt ho)
      have hsize : size (w i) = size (w j) := congrArg size hw
      have hh : o i * size (w i) + size (w i) ≤ o j * size (w j) := by
        rw [← hsize, ← Nat.succ_mul]
        exact h
      have hb := b.isLt
      omega

end GoodPools

/- A product probability bound for many hits in an interval. -/

open Filter Finset MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GoodCount

noncomputable def law (P : ℕ → Finset ℕ) (_hP : ∀ i, (P i).Nonempty) :
    Measure (ℕ → ℕ) :=
  letI : ∀ i, IsProbabilityMeasure (uniformOn (P i : Set ℕ)) := fun i =>
    isProbabilityMeasure_uniformOn (P i).finite_toSet (by simpa using _hP i)
  Measure.infinitePi (fun i => uniformOn (P i : Set ℕ))

instance (P : ℕ → Finset ℕ) (hP : ∀ i, (P i).Nonempty) :
    IsProbabilityMeasure (law P hP) := by
  let : ∀ i, IsProbabilityMeasure (uniformOn (P i : Set ℕ)) := fun i =>
    isProbabilityMeasure_uniformOn (P i).finite_toSet (by simpa using hP i)
  unfold law
  infer_instance

private theorem law_pi (P : ℕ → Finset ℕ) (hP : ∀ i, (P i).Nonempty)
    (I : Finset ℕ) (D : ℕ → Finset ℕ) :
    law P hP ((I : Set ℕ).pi fun i => (D i : Set ℕ)) =
      ∏ i ∈ I, (↑((P i ∩ D i).card) : ℝ≥0∞) / ↑(P i).card := by
  let : ∀ i, IsProbabilityMeasure (uniformOn (P i : Set ℕ)) := fun i =>
    isProbabilityMeasure_uniformOn (P i).finite_toSet (by simpa using hP i)
  unfold law
  rw [Measure.infinitePi_pi _ (fun i _ => (D i).measurableSet)]
  exact prod_congr rfl fun i _ => uniformOn_apply_finset

theorem ae_in_pools (P : ℕ → Finset ℕ) (hP : ∀ i, (P i).Nonempty) :
    ∀ᵐ u ∂law P hP, ∀ i, u i ∈ P i := by
  rw [ae_all_iff]
  intro i
  apply (mem_ae_iff_prob_eq_one (s := {u : ℕ → ℕ | u i ∈ P i})
    ((P i).measurableSet.preimage (measurable_pi_apply i))).2
  change law P hP (Function.eval i ⁻¹' (P i : Set ℕ)) = 1
  have h := law_pi P hP {i} P
  have hi : ((P i).card : ℝ≥0∞) ≠ 0 := by exact_mod_cast (hP i).card_ne_zero
  simpa [ENNReal.div_self hi (by simp)] using h

private theorem law_pi_le (P : ℕ → Finset ℕ) (hP : ∀ i, (P i).Nonempty)
    (I D : Finset ℕ) (B : ℕ) (hD : D.card ≤ B) :
    law P hP ((I : Set ℕ).pi fun _ => (D : Set ℕ)) ≤
      (B : ℝ≥0∞)^I.card / ↑(∏ i ∈ I, (P i).card) := by
  rw [law_pi, Nat.cast_prod, div_eq_mul_inv, ENNReal.prod_inv_distrib]
  · simp_rw [div_eq_mul_inv, prod_mul_distrib]
    gcongr
    rw [← prod_const]
    gcongr with i hi
    exact_mod_cast (card_le_card inter_subset_right).trans hD
  · exact fun i hi j hj hij => Or.inr (by simp)

theorem law_many_hits (P : ℕ → Finset ℕ) (hP : ∀ i, (P i).Nonempty)
    (H N m B : ℕ) (Q : ℝ≥0∞) (A : Finset ℕ) (D : ℕ → Finset ℕ)
    (hD : ∀ a ∈ A, (D a).card ≤ B)
    (hprod : ∀ I ⊆ Ico H N, I.card = m → Q ≤ ↑(∏ i ∈ I, (P i).card)) :
    law P hP {u | ∃ a ∈ A, m ≤ ((Ico H N).filter fun i => u i ∈ D a).card} ≤
      (A.card : ℝ≥0∞) * ((N : ℝ≥0∞) * B)^m / Q := by
  classical
  let E : ℕ → Finset ℕ → Set (ℕ → ℕ) := fun a I =>
    (I : Set ℕ).pi (fun _ => (D a : Set ℕ))
  have inc : {u : ℕ → ℕ | ∃ a ∈ A, m ≤ ((Ico H N).filter fun i => u i ∈ D a).card} ⊆
      ⋃ a ∈ A, ⋃ I ∈ (Ico H N).powersetCard m, E a I := by
    rintro u ⟨a, ha, hu⟩
    obtain ⟨I, hI, hc⟩ := exists_subset_card_eq hu
    refine Set.mem_iUnion₂.2 ⟨a, ha, Set.mem_iUnion₂.2 ⟨I, ?_, ?_⟩⟩
    · exact mem_powersetCard.2 ⟨hI.trans (filter_subset _ _), hc⟩
    · exact fun i hi => (mem_filter.1 (hI hi)).2
  calc
    _ ≤ law P hP (⋃ a ∈ A, ⋃ I ∈ (Ico H N).powersetCard m, E a I) := measure_mono inc
    _ ≤ ∑ a ∈ A, ∑ I ∈ (Ico H N).powersetCard m, law P hP (E a I) := by
      refine (measure_biUnion_finset_le _ _).trans (sum_le_sum fun a ha => ?_)
      exact measure_biUnion_finset_le _ _
    _ ≤ ∑ a ∈ A, ∑ I ∈ (Ico H N).powersetCard m, (B : ℝ≥0∞)^m / Q := by
      refine sum_le_sum fun a ha => sum_le_sum fun I hI => ?_
      obtain ⟨hIs, hIc⟩ := mem_powersetCard.1 hI
      refine (law_pi_le P hP I (D a) B (hD a ha)).trans ?_
      rw [hIc]
      gcongr
      exact hprod I hIs hIc
    _ ≤ _ := by
      simp only [sum_const, nsmul_eq_mul, card_powersetCard, Nat.card_Ico]
      simp only [mul_pow, div_eq_mul_inv, mul_assoc]
      gcongr
      exact_mod_cast (Nat.choose_le_pow (N-H) m).trans (Nat.pow_le_pow_left (Nat.sub_le _ _) _)

theorem primeFactors_card_le {x b : ℕ} (hx : x ≠ 0) (hb : x ≤ 2^b) :
    x.primeFactors.card ≤ b := by
  have h := Nat.le_of_dvd (Nat.pos_of_ne_zero hx) (Nat.prod_primeFactors_dvd x)
  have hp : (2 : ℕ)^x.primeFactors.card ≤ ∏ p ∈ x.primeFactors, p := by
    rw [← prod_const]
    exact prod_le_prod' fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  exact (pow_le_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).1 (hp.trans (h.trans hb))

theorem intervalFactors_card_le {a L b : ℕ} (hb : a + L ≤ 2^b) :
    ((Ioc a (a + L)).biUnion Nat.primeFactors).card ≤ L * b := by
  refine card_biUnion_le.trans ?_
  calc
    _ ≤ ∑ z ∈ Ioc a (a + L), b := sum_le_sum fun z hz => by
      have hz' := mem_Ioc.1 hz
      exact primeFactors_card_le (by omega) (hz'.2.trans hb)
    _ = L * b := by simp

end GoodCount

/- Deterministic interval bounds for a sequence of distinct primes. -/

open Filter Finset Asymptotics
open scoped Topology

namespace GoodSieve

private theorem coprime_blocks (d a k : ℕ) :
    #{b ∈ Ico a (a + d * k) | d.Coprime b} = k * d.totient := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc]
    rw [← Ico_union_Ico_eq_Ico (Nat.le_add_right a (d*k)) (Nat.le_add_right _ d),
      filter_union, card_union_of_disjoint]
    · rw [ih, Nat.filter_coprime_Ico_eq_totient, Nat.succ_mul]
    · exact (Ico_disjoint_Ico_consecutive _ _ _).mono (filter_subset _ _) (filter_subset _ _)

private theorem card_prefix (d a L : ℕ) (hd : 0 < d) :
    (d.totient : ℝ) / d * L - d ≤
      (#{b ∈ Ioc a (a+L) | d.Coprime b} : ℝ) := by
  have hI : Ico (a+1) (a+1+d*(L/d)) ⊆ Ioc a (a+L) := by
    intro b hb
    have hh := mem_Ico.mp hb
    have ha := Nat.mul_div_le L d
    exact mem_Ioc.mpr ⟨by omega, by omega⟩
  have h := card_le_card (filter_subset_filter (fun b => d.Coprime b) hI)
  rw [coprime_blocks] at h
  have hR : (L : ℝ) - d ≤ (d : ℝ) * (L/d : ℕ) := by
    have hdv := Nat.mod_add_div L d
    have hr := Nat.mod_lt L hd
    have hh : L ≤ d * (L/d) + d := by omega
    exact sub_le_iff_le_add.2 (by exact_mod_cast hh)
  have hp : (0 : ℝ) < d := by positivity
  have ht : (d.totient : ℝ) ≤ d := by exact_mod_cast Nat.totient_le d
  have hm := mul_le_mul_of_nonneg_left hR (show (0 : ℝ) ≤ (d.totient : ℝ) / d by positivity)
  have hc : ((L / d * d.totient : ℕ) : ℝ) ≤
      (#{b ∈ Ioc a (a + L) | d.Coprime b} : ℝ) := by exact_mod_cast h
  push_cast at hc
  rw [mul_sub, div_mul_cancel₀ _ hp.ne', ← mul_assoc, div_mul_cancel₀ _ hp.ne'] at hm
  nlinarith

-- The quotient-map count also appears in the Erdős 208 log-bound reduction
-- step Erdos208.erdos_208.variants.log_bound.R1.H1 by @caa1982.
private theorem card_multiples (p a L : ℕ) (hp : 0 < p) :
    (#{b ∈ Ioc a (a+L) | p ∣ b} : ℝ) ≤ (L : ℝ) / p + 1 := by
  let s := (Ioc a (a+L)).filter fun b => p ∣ b
  let t := Ioc (a/p) ((a+L)/p)
  have h : s.card ≤ t.card := by
    apply card_le_card_of_injOn (fun b => b/p)
    · intro b hb
      obtain ⟨hb, hpb⟩ := mem_filter.mp hb
      obtain ⟨hab, hbl⟩ := mem_Ioc.mp hb
      apply mem_Ioc.mpr
      refine ⟨?_, Nat.div_le_div_right hbl⟩
      apply lt_of_not_ge
      intro hh
      have := Nat.mul_le_mul_left p hh
      rw [Nat.mul_div_cancel' hpb] at this
      exact (not_le_of_gt hab) (this.trans (Nat.mul_div_le _ _))
    · intro b hb c hc hbc
      have hpb := (mem_filter.mp hb).2
      have hpc := (mem_filter.mp hc).2
      change b/p = c/p at hbc
      calc
        b = p * (b/p) := (Nat.mul_div_cancel' hpb).symm
        _ = p * (c/p) := by rw [hbc]
        _ = c := Nat.mul_div_cancel' hpc
  have hR : (s.card : ℝ) ≤ (((a+L)/p : ℕ) : ℝ) - ((a/p : ℕ) : ℝ) := by
    have hh : (s.card : ℝ) ≤ (t.card : ℝ) := by exact_mod_cast h
    simpa [t, Nat.card_Ioc, Nat.cast_sub (Nat.div_le_div_right (Nat.le_add_right a L))] using hh
  have hupper : (p : ℝ) * ((a+L)/p : ℕ) ≤ (a : ℝ) + L := by
    exact_mod_cast Nat.mul_div_le (a+L) p
  have hlower : (a : ℝ) ≤ p * (a/p : ℕ) + p := by
    exact_mod_cast (show a ≤ p * (a/p) + p by
      have := Nat.mod_add_div a p
      have := Nat.mod_lt a hp
      omega)
  apply le_trans hR
  have hp' : (0 : ℝ) < p := by positivity
  calc
    _ ≤ ((L : ℝ) + p) / p := (le_div_iff₀ hp').2 (by nlinarith)
    _ = _ := by rw [add_div, div_self hp'.ne']

private theorem totient_prod {u : ℕ → ℕ} (hu : ∀ i, (u i).Prime)
    (hc : Function.Injective u) (K : ℕ) :
    (↑(∏ i ∈ range K, u i).totient : ℝ) / (↑(∏ i ∈ range K, u i) : ℝ) =
      ∏ i ∈ range K, (1 - 1 / (u i : ℝ)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hp : (∏ i ∈ range K, u i).Coprime (u K) := by
      apply Nat.Coprime.prod_left
      intro i hi
      exact (Nat.coprime_primes (hu i) (hu K)).2
        (fun e => (mem_range.1 hi).ne (hc e))
    rw [prod_range_succ, Nat.totient_mul hp, Nat.totient_prime (hu K), prod_range_succ,
      Nat.cast_mul, Nat.cast_mul, mul_div_mul_comm, ih,
      Nat.cast_sub (hu K).one_lt.le, Nat.cast_one, sub_div]
    rw [div_self (by exact_mod_cast (hu K).ne_zero)]

private theorem prefixes_coprime {u : ℕ → ℕ} (hu : ∀ i, (u i).Prime) (K b : ℕ) :
    (∏ i ∈ range K, u i).Coprime b ↔ ∀ i < K, ¬ u i ∣ b := by
  rw [Nat.coprime_prod_left_iff]
  simp only [mem_range, Nat.Prime.coprime_iff_not_dvd (hu _)]

theorem survivors {u : ℕ → ℕ} (hu : ∀ i, (u i).Prime)
    (hc : Function.Injective u) {K H a L : ℕ} (hKH : K ≤ H) :
    (∏ i ∈ range K, (1 - 1 / (u i : ℝ))) * L -
      (∏ i ∈ range K, (u i : ℝ)) -
      ((L : ℝ) * (∑ i ∈ Ico K H, 1 / (u i : ℝ)) + H)
      ≤ (#{b ∈ Ioc a (a+L) | ∀ i ∈ range H, ¬ u i ∣ b} : ℝ) := by
  classical
  let d := ∏ i ∈ range K, u i
  let pre := (Ioc a (a+L)).filter (fun b => d.Coprime b)
  let bad := (Ico K H).biUnion (fun i => (Ioc a (a+L)).filter (fun b => u i ∣ b))
  have hD : 0 < d := prod_pos fun i _ => (hu i).pos
  have hpre := card_prefix d a L hD
  rw [totient_prod hu hc K] at hpre
  have hbad : (bad.card : ℝ) ≤ ((L : ℝ) * (∑ i ∈ Ico K H, 1 / (u i : ℝ)) + H) := by
    calc
      _ ≤ ∑ i ∈ Ico K H, (#{b ∈ Ioc a (a+L) | u i ∣ b} : ℝ) := by
        norm_cast
        exact card_biUnion_le
      _ ≤ ∑ i ∈ Ico K H, ((L : ℝ) / (u i : ℝ) + 1) :=
        sum_le_sum fun i _ => card_multiples (u i) a L (hu i).pos
      _ ≤ _ := by
        simp only [sum_add_distrib, sum_const, nsmul_eq_mul, mul_one, Nat.card_Ico, mul_sum,
          mul_one_div]
        gcongr
        exact Nat.sub_le _ _
  have hsurv : pre \ bad = (Ioc a (a+L)).filter (fun b => ∀ i ∈ range H, ¬ u i ∣ b) := by
    ext b
    rw [Finset.mem_sdiff]
    rw [show b ∈ bad ↔ ∃ i ∈ Ico K H, b ∈ (Ioc a (a+L)).filter (fun b => u i ∣ b)
      from Finset.mem_biUnion]
    simp only [pre, mem_filter, mem_Ico, mem_range]
    dsimp [d]
    rw [prefixes_coprime hu K b]
    constructor
    · rintro ⟨⟨hb, hp⟩, hbad⟩
      refine ⟨hb, fun i hi hd => ?_⟩
      by_cases hk : i < K
      · exact hp i hk hd
      · exact hbad ⟨i, ⟨by omega, hi⟩, hb, hd⟩
    · rintro ⟨hb, hp⟩
      exact ⟨⟨hb, fun i hi => hp i (hi.trans_le hKH)⟩, fun ⟨i, hi, _, hd⟩ => hp i hi.2 hd⟩
  have hcard := card_le_card (show pre ⊆ (pre \ bad) ∪ bad by
    intro b hb
    apply mem_union.2
    by_cases h : b ∈ bad
    · exact Or.inr h
    · exact Or.inl (Finset.mem_sdiff.2 ⟨hb, h⟩))
  have hh := hcard.trans (card_union_le (pre \ bad) bad)
  rw [hsurv] at hh
  have hh' : (pre.card : ℝ) ≤
      (#{b ∈ Ioc a (a+L) | ∀ i ∈ range H, ¬u i ∣ b} : ℝ) + (bad.card : ℝ) := by
    exact_mod_cast hh
  rw [← Nat.cast_prod]
  change _ - (d : ℝ) - _ ≤ _
  change _ - (d : ℝ) ≤ (pre.card : ℝ) at hpre
  linarith

theorem many_hits_of_covered {u : ℕ → ℕ} (hu : ∀ i, (u i).Prime)
    {H N a L W m : ℕ} (hLW : L ≤ W) (hsize : ∀ i, H ≤ i → W < u i)
    (hN : ∀ i, N ≤ i → a + W < u i)
    (hs : m ≤ #{b ∈ Ioc a (a+L) | ∀ i ∈ range H, ¬u i ∣ b})
    (hcov : ∀ b ∈ Ioc a (a+L), ∃ i, u i ∣ b) :
    m ≤ #{i ∈ Ico H N | u i ∈ (Ioc a (a+W)).biUnion Nat.primeFactors} := by
  classical
  let S := (Ioc a (a+L)).filter (fun b => ∀ i ∈ range H, ¬u i ∣ b)
  choose f hf using fun b (hb : b ∈ S) => hcov b (mem_filter.1 hb).1
  let g : ℕ → ℕ := fun b => if hb : b ∈ S then f b hb else 0
  have hg : ∀ b ∈ S, u (g b) ∣ b := fun b hb => by simpa [g, hb] using hf b hb
  have hH : ∀ b ∈ S, H ≤ g b := by
    intro b hb
    by_contra! h
    exact (mem_filter.1 hb).2 _ (mem_range.2 h) (hg b hb)
  refine hs.trans (card_le_card_of_injOn g ?_ ?_)
  · intro b hb
    have hbl := mem_Ioc.1 (mem_filter.1 hb).1
    have hbp : 0 < b := by omega
    refine mem_filter.2 ⟨mem_Ico.2 ⟨hH b hb, ?_⟩, mem_biUnion.2 ⟨b, mem_Ioc.2 ⟨hbl.1, by omega⟩,
      Nat.mem_primeFactors.2 ⟨hu _, hg b hb, hbp.ne'⟩⟩⟩
    by_contra! h
    have := hN _ h
    have := Nat.le_of_dvd hbp (hg b hb)
    omega
  · intro b hb c hc h
    have hab := mem_Ioc.1 (mem_filter.1 hb).1
    have hac := mem_Ioc.1 (mem_filter.1 hc).1
    have huW := hsize _ (hH b hb)
    have hb' := hg b hb
    have hc'' := hg c hc
    rw [← h] at hc''
    rcases lt_trichotomy b c with hbc | he | hcb
    · have hd := Nat.dvd_sub hc'' hb'
      have := Nat.le_of_dvd (by omega : 0 < c-b) hd
      omega
    · exact he
    · have hd := Nat.dvd_sub hb' hc''
      have := Nat.le_of_dvd (by omega : 0 < b-c) hd
      omega

end GoodSieve
/- Growth estimates for the prime pools and the interval scales. -/

open Filter Finset Asymptotics MeasureTheory
open scoped ENNReal Topology

namespace GoodScale

open GoodPools

private theorem weight_mono (J : ℕ) : Monotone (weight J) :=
  fun _ _ h => Nat.add_le_add_left (Nat.sqrt_le_sqrt h) _

private theorem sqrt_nat_tendsto : Tendsto Nat.sqrt atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [eventually_ge_atTop (b*b)] with n hn
  exact Nat.le_sqrt.2 hn

private theorem weight_tendsto (J : ℕ) : Tendsto (weight J) atTop atTop := by
  refine tendsto_atTop.2 fun b => (sqrt_nat_tendsto.eventually_ge_atTop b).mono ?_
  intro n hn
  exact hn.trans (Nat.le_add_left _ _)

private theorem exp_log_base (b : ℝ) (hb : 0 < b) (n : ℕ) :
    Real.exp (n * Real.log b) = b ^ n := by
  rw [← Real.log_pow, Real.exp_log (by positivity)]

private theorem sqrt_superlog (C : ℝ) (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) * C < (8 : ℝ)^(n.sqrt.sqrt) := by
  have hlog := (sqrt_nat_tendsto.eventually (GoodPools.log_add_le_sqrt 1 (Real.log 8 / 4)
    (by positivity : 0 < Real.log 8 / 4)))
  have hcut := (GoodPools.sqrt_tendsto.comp sqrt_nat_tendsto).eventually_gt_atTop
    (2 * Real.log C / Real.log 8)
  filter_upwards [hlog, hcut, eventually_ge_atTop (1 : ℕ)] with n hl hc hn
  have hp : (0 : ℝ) < Real.log 8 := Real.log_pos (by norm_num)
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsq : (n : ℝ) ≤ ((n.sqrt : ℝ)+1)^2 := by
    have hh := (GoodPools.real_sqrt_lt n).le
    have hh' := pow_le_pow_left₀ (Real.sqrt_nonneg (n : ℝ)) hh 2
    rwa [Real.sq_sqrt hn'.le] at hh'
  have ha : Real.log (n : ℝ) ≤ 2 * Real.log ((n.sqrt : ℝ)+1) := by
    have h := Real.log_le_log hn' hsq
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hc' := (div_lt_iff₀ hp).mp hc
  change 2 * Real.log C < (n.sqrt.sqrt : ℝ) * Real.log 8 at hc'
  rw [← exp_log_base 8 (by norm_num), ← Real.exp_log (mul_pos hn' hC), Real.exp_lt_exp,
    Real.log_mul hn'.ne' hC.ne']
  nlinarith only [ha, hl, hc']

private theorem base_recip_summable : Summable (fun i : ℕ => 1 / (8 : ℝ)^i.sqrt) := by
  have hp : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have he := GoodPools.log_add_le_sqrt 1 (Real.log 8 / 2) (by positivity)
  obtain ⟨K, hK⟩ := eventually_atTop.1 he
  have hs : Summable (fun i : ℕ => 1 / (i : ℝ)^2) :=
    Real.summable_one_div_nat_pow.2 (by decide)
  apply (summable_nat_add_iff K).1
  have hs' := (summable_nat_add_iff (K+1)).2 hs
  refine hs'.of_nonneg_of_le (fun i => by positivity) fun i => ?_
  have h := hK (i+K) (Nat.le_add_left _ _)
  have hh : ((i+K+1 : ℕ) : ℝ)^2 ≤ (8 : ℝ)^((i+K).sqrt) := by
    rw [← exp_log_base 8 (by norm_num)]
    rw [← Real.exp_log (show 0 < ((i+K+1 : ℕ) : ℝ)^2 by positivity)]
    apply Real.exp_le_exp.2
    rw [Real.log_pow]
    push_cast at h ⊢
    linarith
  simpa only [Nat.add_assoc] using
    one_div_le_one_div_of_le (by positivity : 0 < ((i+K+1 : ℕ) : ℝ)^2) hh

theorem small_recip :
    ∀ᶠ J : ℕ in atTop, ∀ u : ℕ → ℕ, (∀ i, 8 ^ weight J i < u i) →
      Summable (fun i => 1 / (u i : ℝ)) ∧ (∑' i, 1 / (u i : ℝ)) ≤ (1/2 : ℝ) := by
  let T := ∑' i : ℕ, 1 / (8 : ℝ)^i.sqrt
  have hT : 0 ≤ T := tsum_nonneg fun _ => by positivity
  filter_upwards [(tendsto_pow_atTop_atTop_of_one_lt
    (show (1 : ℝ) < 8 by norm_num)).eventually_ge_atTop (2*T)] with J hJ
  intro u hu
  have hs : Summable (fun i : ℕ => ((8 : ℝ)^J)⁻¹ * (1 / 8^i.sqrt)) :=
    base_recip_summable.mul_left _
  have hp : ∀ i, 1 / (u i : ℝ) ≤ ((8 : ℝ)^J)⁻¹ * (1 / 8^i.sqrt) := by
    intro i
    have hh : (8 : ℝ)^(J+i.sqrt) ≤ u i := by exact_mod_cast (hu i).le
    have hm := one_div_le_one_div_of_le (by positivity : 0 < (8 : ℝ)^(J+i.sqrt)) hh
    simpa [pow_add, one_div, mul_comm] using hm
  have hsum := hs.of_nonneg_of_le (fun i => by positivity) hp
  refine ⟨hsum, (hsum.tsum_le_tsum hp hs).trans ?_⟩
  rw [tsum_mul_left, ← div_eq_inv_mul]
  exact (div_le_iff₀ (by positivity)).2 (by linarith)

theorem subexp {J : ℕ} {u : ℕ → ℕ} (hlo : ∀ i, 8 ^ weight J i < u i)
    (hhi : ∀ i, u i ≤ 8 ^ (weight J i + 1)) :
    (fun i => Real.log (u i : ℝ)) =o[atTop] (fun i => (i : ℝ)) := by
  apply Asymptotics.isLittleO_iff.2
  intro c hc
  let p := Real.log 8
  have hp : 0 < p := Real.log_pos (by norm_num)
  filter_upwards [GoodPools.sqrt_tendsto.eventually_ge_atTop (max 1 (((J : ℝ)+2)*p/c))] with i hi
  have hi1 : (1 : ℝ) ≤ i.sqrt := (le_max_left _ _).trans hi
  have hcoef : ((J : ℝ)+2)*p ≤ c * (i.sqrt : ℝ) := by
    have := (div_le_iff₀ hc).1 ((le_max_right (1 : ℝ) _).trans hi)
    linarith
  have hs : (i.sqrt : ℝ) * i.sqrt ≤ i := by exact_mod_cast Nat.sqrt_le i
  have hlog : Real.log (u i : ℝ) ≤ ((J : ℝ) + i.sqrt + 1)*p := by
    have hu : (1 : ℝ) ≤ u i := by exact_mod_cast (show 1 ≤ u i from (Nat.zero_lt_of_lt (hlo i)))
    have h := Real.log_le_log (lt_of_lt_of_le zero_lt_one hu)
      (show (u i : ℝ) ≤ (8 : ℝ)^(weight J i + 1) by exact_mod_cast hhi i)
    simpa [Real.log_pow, weight, p] using h
  have hu : (1 : ℝ) ≤ u i := by exact_mod_cast Nat.zero_lt_of_lt (hlo i)
  rw [Real.norm_of_nonneg (Real.log_nonneg hu), Real.norm_of_nonneg (by positivity : 0 ≤ (i : ℝ))]
  have hm := mul_le_mul_of_nonneg_right hcoef (show (0 : ℝ) ≤ i.sqrt by positivity)
  have ht := mul_le_mul_of_nonneg_left hs hc.le
  have hz := mul_nonneg (show 0 ≤ ((J : ℝ)+1)*p by positivity)
    (sub_nonneg.mpr hi1)
  nlinarith

def weightSum (J n : ℕ) : ℕ := ∑ i ∈ range n, weight J i

def scale (J n : ℕ) : ℕ := (8 : ℕ)^(weightSum J n + n)

private theorem weightSum_le (J n : ℕ) :
    weightSum J n ≤ n * weight J n := by
  unfold weightSum
  simpa using (sum_le_card_nsmul (range n) (weight J) (weight J n)
    (fun i hi => weight_mono J (mem_range.1 hi).le))

private theorem weightSum_add (J n t : ℕ) :
    weightSum J n + t * weight J n ≤ weightSum J (n+t) := by
  unfold weightSum
  rw [sum_range_add]
  apply Nat.add_le_add_left
  simpa using (sum_le_sum (s := range t) (f := fun _ => weight J n)
    (g := fun i => weight J (n+i)) fun i _ => weight_mono J (Nat.le_add_right _ _))

private theorem weightSum_le_sum (J : ℕ) {I : Finset ℕ} {m : ℕ} (hI : I.card = m) :
    weightSum J m ≤ ∑ i ∈ I, weight J i := by
  let e := I.orderEmbOfFin hI
  have h : ∀ k (hk : k < m), k ≤ e ⟨k,hk⟩ := by
    intro k
    induction k with
    | zero => exact fun _ => Nat.zero_le _
    | succ k ih =>
      intro hk
      have hlt := e.strictMono (show (⟨k, by omega⟩ : Fin m) < ⟨k+1,hk⟩ from Nat.lt_succ_self _)
      have hle := ih (by omega)
      omega
  calc
    _ = ∑ i : Fin m, weight J i := (Fin.sum_univ_eq_sum_range (weight J) m).symm
    _ ≤ ∑ i : Fin m, weight J (e i) := sum_le_sum fun i _ => weight_mono J (h i i.isLt)
    _ = _ := by
      have hsum := Fintype.sum_equiv (I.orderIsoOfFin hI).toEquiv
        (fun i : Fin m => weight J (e i)) (fun i : I => weight J i) (fun _ => rfl)
      simpa only [Finset.sum_coe_sort] using hsum

def bits (J n : ℕ) : ℕ := 3 * (weightSum J (n+1) + (n+1) + 1)

def cutoff (J n : ℕ) : ℕ := (bits J n + 1)^2

def window (n : ℕ) : ℕ := 4*n

noncomputable def slack (r : ℕ) : ℝ := 1 / ((r : ℝ) + 4)

noncomputable def hits (r n : ℕ) : ℕ := n + ⌈slack r * (n : ℝ)⌉₊

private theorem slack_pos (r : ℕ) : 0 < slack r := by unfold slack; positivity

private theorem slack_le (r : ℕ) : slack r ≤ 1/4 := by
  apply one_div_le_one_div_of_le (by norm_num)
  exact le_add_of_nonneg_left (Nat.cast_nonneg r)

private theorem hits_bounds (r n : ℕ) :
    (1 + slack r) * (n : ℝ) ≤ (hits r n : ℝ) ∧ hits r n ≤ 2*n := by
  have h₁ := Nat.le_ceil (slack r * (n : ℝ))
  have h₂ : ⌈slack r * (n : ℝ)⌉₊ ≤ n := Nat.ceil_le.2
    (by nlinarith [mul_le_mul_of_nonneg_right (slack_le r) (Nat.cast_nonneg n)])
  constructor
  · unfold hits
    push_cast
    nlinarith
  · unfold hits
    omega

private theorem scale_succ (J n : ℕ) : scale J n < scale J (n+1) := by
  unfold scale
  rw [weightSum, weightSum, sum_range_succ]
  apply Nat.pow_lt_pow_right (by decide)
  omega

private theorem scale_tendsto (J : ℕ) : Tendsto (scale J) atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [eventually_ge_atTop b] with n hn
  unfold scale
  exact hn.trans (le_trans (Nat.le_add_left n _) (Nat.le_of_lt (Nat.lt_pow_self (by decide : 1 < (8 : ℕ)))))

private theorem scale_window_le (J n : ℕ) : window n ≤ scale J (n+1) := by
  have h : ∀ k : ℕ, 4*k ≤ 8^(k+1) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      rw [show k+1+1 = (k+1)+1 by omega, pow_succ]
      have h8 : 1 ≤ (8 : ℕ)^(k+1) := Nat.pos_of_ne_zero (pow_ne_zero _ (by decide))
      omega
  exact (h n).trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _))

theorem start_bits (J n a : ℕ) (ha : a ≤ scale J (n+1)) :
    a + window n ≤ 2^(bits J n) := by
  have he : (2 : ℕ)^(bits J n) = 8 * scale J (n+1) := by
    unfold bits scale
    rw [pow_mul, show (2 : ℕ)^3 = 8 by decide, pow_succ, Nat.mul_comm]
  rw [he]
  have hw := scale_window_le J n
  omega

theorem above_cutoff {J n : ℕ} {u : ℕ → ℕ} (hu : ∀ i, 8 ^ weight J i < u i)
    (a : ℕ) (ha : a ≤ scale J (n+1)) (i : ℕ) (hi : cutoff J n ≤ i) :
    a + window n < u i := by
  have hs : bits J n + 1 ≤ i.sqrt := Nat.le_sqrt.2 (by simpa [cutoff, pow_two] using hi)
  have he : bits J n ≤ weight J i := by unfold weight; omega
  have h₂ : (2 : ℕ)^(bits J n) ≤ 8^(bits J n) := Nat.pow_le_pow_left (by decide) _
  exact (start_bits J n a ha).trans_lt ((h₂.trans
    (Nat.pow_le_pow_right (by decide) he)).trans_lt (hu i))

theorem above_window {J : ℕ} :
    ∀ᶠ n : ℕ in atTop, ∀ i, n.sqrt ≤ i → window n ≤ 8^weight J i := by
  filter_upwards [sqrt_superlog 4 (by norm_num)] with n hn i hi
  have h : window n < 8^n.sqrt.sqrt := by
    unfold window
    exact_mod_cast (show (4 : ℝ)*n < (8 : ℝ)^n.sqrt.sqrt by linarith)
  exact h.le.trans (Nat.pow_le_pow_right (by decide)
    ((Nat.sqrt_le_sqrt hi).trans (Nat.le_add_left _ _)))

private theorem log_overhead (J : ℕ) (c : ℝ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      Real.log ((cutoff J n : ℝ) * (window n * bits J n : ℕ)) ≤ c * (n.sqrt : ℝ) := by
  filter_upwards [GoodPools.log_add_le_sqrt (J+10) (c/12) (by positivity),
    eventually_ge_atTop (1 : ℕ)] with n hn hn1
  let z : ℕ := J+n+10
  have hs := weightSum_le J (n+1)
  have hsq := Nat.sqrt_le_self (n+1)
  have hsup : weightSum J (n+1) ≤ (n+1)*(J+n+1) := by
    apply hs.trans
    apply Nat.mul_le_mul_left
    unfold weight
    omega
  have hz2 : 1 ≤ z := by dsimp [z]; omega
  have hb : bits J n + 1 ≤ z^3 := by
    have h₁ : weightSum J (n+1) ≤ (z-2)*(z-2) := by
      apply hsup.trans
      apply Nat.mul_le_mul <;> dsimp [z] <;> omega
    have h₂ : (n+1)+1 ≤ z-2 := by dsimp [z]; omega
    have h₃ : 5 ≤ z := by dsimp [z]; omega
    have h₄ : (z-2)*(z-2) + (z-2) ≤ z*z := by
      have e : z-2+2 = z := by omega
      nlinarith
    have h₅ : 3*(z*z)+1 ≤ z^3 := by
      have := Nat.mul_le_mul_left (z*z) (show 4 ≤ z by omega)
      nlinarith
    unfold bits
    omega
  have hN : cutoff J n ≤ z^6 := by
    unfold cutoff
    rw [show 6 = 3*2 by decide, pow_mul]
    exact Nat.pow_le_pow_left hb _
  have hw : window n ≤ z^2 := by
    unfold window
    have h₁ : n ≤ z := by dsimp [z]; omega
    have h₂ : 4 ≤ z := by dsimp [z]; omega
    simpa only [pow_two] using Nat.mul_le_mul h₂ h₁
  have hB : window n * bits J n ≤ z^5 := by
    rw [show 5 = 2+3 by decide, pow_add]
    exact Nat.mul_le_mul hw ((Nat.le_succ _).trans hb)
  have hNB : cutoff J n * (window n * bits J n) ≤ z^12 := by
    refine (Nat.mul_le_mul hN hB).trans ?_
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by omega) (by decide)
  have hp : 0 < (cutoff J n : ℝ) * (window n * bits J n : ℕ) := by
    unfold cutoff window bits
    positivity
  calc
    _ ≤ Real.log ((z : ℝ)^12) := Real.log_le_log hp (by exact_mod_cast hNB)
    _ ≤ c * (n.sqrt : ℝ) := by
      rw [Real.log_pow]
      show (12 : ℝ) * Real.log (z : ℝ) ≤ _
      dsimp [z]
      push_cast
      rw [add_comm (J : ℝ) (n : ℝ), add_assoc]
      linarith

end GoodScale
/- Summable exceptional-event probabilities. -/

open Filter Finset MeasureTheory
open scoped Topology ENNReal

namespace GoodScale

open GoodPools GoodCount

private def divisorsInWindow (n a : ℕ) : Finset ℕ :=
  (Ioc a (a+window n)).biUnion Nat.primeFactors

private def badEvent (J r n : ℕ) : Set (ℕ → ℕ) :=
  {u | ∃ a ≤ scale J (n+1),
    hits r n ≤ ((Ico n.sqrt (cutoff J n)).filter fun i => u i ∈ divisorsInWindow n a).card}

private theorem aggregate_size (J r : ℕ) (P : ℕ → Finset ℕ)
    (hP : ∀ i, (P i).card = size (weight J i)) :
    ∀ᶠ n : ℕ in atTop, ∀ I ⊆ Ico n.sqrt (cutoff J n), I.card = hits r n →
      ENNReal.ofReal (Real.exp ((1-slack r/8) * (weightSum J (hits r n) : ℝ) * Real.log 8)) ≤
        ↑(∏ i ∈ I, (P i).card) := by
  let δ := slack r / 8
  have hd : 0 < δ := by dsimp [δ]; linarith [slack_pos r]
  have hd1 : δ ≤ 1 := by dsimp [δ]; linarith [slack_le r]
  obtain ⟨K, hK⟩ := eventually_atTop.1 (log_size δ hd hd1)
  filter_upwards [(sqrt_nat_tendsto.eventually_ge_atTop (K*K))] with n hn I hI hc
  rw [← ENNReal.ofReal_natCast]
  apply ENNReal.ofReal_le_ofReal
  push_cast
  have h₁ : (weightSum J (hits r n) : ℝ) ≤ ∑ i ∈ I, (weight J i : ℝ) := by
    exact_mod_cast weightSum_le_sum J hc
  calc
    _ ≤ Real.exp (∑ i ∈ I, ((1-δ) * (weight J i : ℝ) * Real.log 8)) := by
      apply Real.exp_le_exp.2
      rw [← sum_mul, ← mul_sum]
      have hδ : 0 ≤ 1 - slack r/8 := by linarith [slack_le r]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h₁ hδ) (by positivity)
    _ ≤ _ := by
      rw [Real.exp_sum]
      refine prod_le_prod (fun _ _ => (Real.exp_pos _).le) fun i hi => ?_
      rw [hP i]
      have hs := Nat.le_sqrt.2 (hn.trans (mem_Ico.1 (hI hi)).1)
      exact hK _ (hs.trans (Nat.le_add_left _ _))

private theorem gain (J r n : ℕ) :
    (weightSum J n : ℝ) + slack r / 2 * (n : ℝ) * (weight J n : ℝ) ≤
      (1-slack r/8) * (weightSum J (hits r n) : ℝ) := by
  let δ := slack r
  have hd : 0 < δ := slack_pos r
  have hd' : δ ≤ 1 := (slack_le r).trans (by norm_num)
  let t := ⌈δ * (n : ℝ)⌉₊
  have ht : δ * (n : ℝ) ≤ (t : ℝ) := Nat.le_ceil _
  have h₁ : (weightSum J n : ℝ) + (t : ℝ) * (weight J n : ℝ) ≤
      (weightSum J (hits r n) : ℝ) := by exact_mod_cast weightSum_add J n t
  have h₂ : (weightSum J n : ℝ) ≤ (n : ℝ) * (weight J n : ℝ) := by
    exact_mod_cast weightSum_le J n
  have hp : 0 ≤ (weight J n : ℝ) := Nat.cast_nonneg _
  have h₃ := mul_le_mul_of_nonneg_right ht hp
  have h₄ : (weightSum J n : ℝ) + δ * (n : ℝ) * (weight J n : ℝ) ≤
      (weightSum J (hits r n) : ℝ) := by linarith only [h₁, h₃]
  have h₅ := mul_le_mul_of_nonneg_left h₄ (show 0 ≤ 1-δ/8 by linarith)
  have h₆ := mul_le_mul_of_nonneg_left h₂ (show 0 ≤ δ/8 by positivity)
  have h₇ := mul_le_mul_of_nonneg_right hd'
    (show 0 ≤ δ/8 * (n : ℝ) * (weight J n : ℝ) by positivity)
  change _ + δ / 2 * _ * _ ≤ (1-δ/8) * _
  nlinarith only [h₅, h₆, h₇, show 0 ≤ δ * (n : ℝ) * (weight J n : ℝ) by positivity]

private theorem probability_arithmetic (J r : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ((scale J (n+1)+1 : ℕ) : ℝ) *
        ((cutoff J n : ℝ) * (window n * bits J n : ℕ))^(hits r n) /
        Real.exp ((1-slack r/8) * (weightSum J (hits r n) : ℝ) * Real.log 8) ≤
      (2 : ℝ)⁻¹ ^ n := by
  let δ := slack r
  let p := Real.log 8
  have hδ : 0 < δ := slack_pos r
  have hp : 0 < p := Real.log_pos (by norm_num)
  have hlog2 : Real.log 2 ≤ p := Real.log_le_log (by norm_num) (by norm_num)
  have hw := (GoodPools.sqrt_tendsto).eventually_ge_atTop (64 / δ)
  filter_upwards [log_overhead J (δ*p/16) (by positivity), eventually_ge_atTop (max 1 J), hw]
    with n hlog hn hw
  let G := (cutoff J n : ℝ) * (window n * bits J n : ℕ)
  have hG : 0 < G := by
    have : 0 < n := lt_of_lt_of_le Nat.zero_lt_one ((le_max_left _ _).trans hn)
    dsimp [G, cutoff, window, bits]
    positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_max_left 1 J).trans hn
  have hw1 : (weight J n : ℝ) ≤ 2*n := by
    have hj : J ≤ n := (le_max_right 1 J).trans hn
    have h : weight J n ≤ 2*n := by
      have hn_s := Nat.sqrt_le_self n
      unfold weight
      omega
    exact_mod_cast h
  have hw2 : (64 : ℝ) ≤ δ * (weight J n : ℝ) := by
    have h := (div_le_iff₀ hδ).1 hw
    have hx : (n.sqrt : ℝ) ≤ weight J n := by exact_mod_cast Nat.le_add_left n.sqrt J
    have hm := mul_le_mul_of_nonneg_left hx hδ.le
    linarith
  have h₁ : ((weight J n : ℝ) + n + 1) * p + (n+1) * Real.log 2 ≤
      8 * (n : ℝ) * p := by
    have h₁ := mul_le_mul_of_nonneg_right (show (weight J n : ℝ) + n + 1 ≤ 4*n by linarith) hp.le
    have h₂ := mul_le_mul_of_nonneg_left hlog2 (show (0 : ℝ) ≤ n+1 by positivity)
    have h₃ := mul_le_mul_of_nonneg_right (show (n+1 : ℝ) ≤ 2*n by linarith) hp.le
    nlinarith only [h₁, h₂, h₃, show 0 ≤ (n : ℝ)*p by positivity]
  have h₂ : 8 * (n : ℝ) * p ≤ δ / 8 * (n : ℝ) * (weight J n : ℝ) * p := by
    have := mul_le_mul_of_nonneg_right hw2 (show 0 ≤ (n : ℝ)*p by positivity)
    nlinarith only [this]
  have h₃ : (hits r n : ℝ) * Real.log G ≤
      δ / 8 * (n : ℝ) * (weight J n : ℝ) * p := by
    have hbound : (hits r n : ℝ) ≤ 2*n := by exact_mod_cast (hits_bounds r n).2
    have hx : (n.sqrt : ℝ) ≤ weight J n := by exact_mod_cast Nat.le_add_left n.sqrt J
    have hlog' : Real.log G ≤ δ*p/16 * (weight J n : ℝ) :=
      hlog.trans (mul_le_mul_of_nonneg_left hx (by positivity))
    have hh := mul_le_mul_of_nonneg_left hlog' (show 0 ≤ (hits r n : ℝ) by positivity)
    have hh' := mul_le_mul_of_nonneg_right hbound
      (show 0 ≤ δ*p/16 * (weight J n : ℝ) by positivity)
    nlinarith only [hh, hh']
  have h₄ := mul_le_mul_of_nonneg_right (gain J r n) hp.le
  have h₅ : (weightSum J (n+1) : ℝ) = (weightSum J n : ℝ) + (weight J n : ℝ) := by
    unfold weightSum
    rw [sum_range_succ, Nat.cast_add]
  have hExp : Real.log 2 + ((weightSum J (n+1) : ℝ)+(n+1))*p +
        (hits r n : ℝ)*Real.log G -
        ((1-δ/8) * (weightSum J (hits r n) : ℝ) * p) ≤ -(n : ℝ) * Real.log 2 := by
    rw [h₅]
    nlinarith only [h₁, h₂, h₃, h₄,
      show 0 ≤ δ/4 * (n : ℝ) * (weight J n : ℝ) * p by positivity]
  have hs : (1 : ℝ) ≤ scale J (n+1) := by
    exact_mod_cast (show 0 < scale J (n+1) by unfold scale; positivity)
  calc
    _ ≤ 2 * (scale J (n+1) : ℝ) * G^(hits r n) /
          Real.exp ((1-δ/8) * (weightSum J (hits r n) : ℝ) * p) := by
      gcongr
      push_cast
      linarith
    _ = Real.exp (Real.log 2 + ((weightSum J (n+1) : ℝ)+(n+1))*p +
          (hits r n : ℝ)*Real.log G -
          ((1-δ/8)*(weightSum J (hits r n) : ℝ)*p)) := by
      rw [Real.exp_sub, Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2),
        exp_log_base G hG]
      have he : Real.exp (((weightSum J (n+1) : ℝ)+(n+1))*p) = (scale J (n+1) : ℝ) := by
        simpa only [scale, p, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] using
          exp_log_base 8 (by norm_num) (weightSum J (n+1)+(n+1))
      rw [he]
    _ ≤ Real.exp (-(n : ℝ) * Real.log 2) := Real.exp_le_exp.2 hExp
    _ = _ := by rw [neg_mul, Real.exp_neg, exp_log_base 2 (by norm_num), inv_pow]

private theorem summable_bad (J r : ℕ) (P : ℕ → Finset ℕ) (hP : ∀ i, (P i).Nonempty)
    (hc : ∀ i, (P i).card = size (weight J i)) :
    (∑' n, law P hP (badEvent J r n)) ≠ ∞ := by
  have hE : ∀ᶠ n in atTop, law P hP (badEvent J r n) ≤ (2 : ℝ≥0∞)⁻¹ ^ n := by
    filter_upwards [aggregate_size J r P hc, probability_arithmetic J r] with n hs ha
    have h := law_many_hits P hP n.sqrt (cutoff J n) (hits r n) (window n * bits J n)
      (ENNReal.ofReal (Real.exp ((1-slack r/8) * (weightSum J (hits r n) : ℝ) * Real.log 8)))
      (range (scale J (n+1)+1)) (divisorsInWindow n)
      (fun a ha => intervalFactors_card_le (start_bits J n a (by simpa using ha))) hs
    simp only [card_range] at h
    have hnorm : {u | ∃ a ∈ range (scale J (n+1)+1),
      hits r n ≤ ((Ico n.sqrt (cutoff J n)).filter fun i => u i ∈ divisorsInWindow n a).card} =
      badEvent J r n := by ext u; simp [badEvent]
    rw [hnorm] at h
    refine h.trans ?_
    have he := ENNReal.ofReal_le_ofReal ha
    rwa [ENNReal.ofReal_div_of_pos (Real.exp_pos _), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2),
      ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
      ENNReal.ofReal_natCast] at he
  obtain ⟨K, hK⟩ := eventually_atTop.1 hE
  let b : ℕ → ℝ≥0∞ := fun n => if n < K then 1 else 0
  have hb : (∑' n, b n) = K := by
    rw [tsum_eq_sum (s := range K)]
    · rw [sum_congr rfl (g := fun _ => (1 : ℝ≥0∞)) (fun n hn => if_pos (mem_range.1 hn))]
      simp
    · intro n hn
      exact if_neg (by simpa using hn)
  apply ne_top_of_le_ne_top (b := (K : ℝ≥0∞) + 2) (by simp)
  rw [← hb, ← ENNReal.tsum_geometric_two, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro n
  by_cases hn : n < K
  · simp only [b, if_pos hn]
    exact prob_le_one.trans (le_add_of_nonneg_right bot_le)
  · simpa [b, hn] using hK n (Nat.le_of_not_gt hn)

theorem exists_sparse (J : ℕ) (P : ℕ → Finset ℕ) (hP : ∀ i, (P i).Nonempty)
    (hc : ∀ i, (P i).card = size (weight J i)) :
    ∃ u : ℕ → ℕ, (∀ i, u i ∈ P i) ∧
      ∀ r : ℕ, ∀ᶠ n : ℕ in atTop, ∀ a ≤ scale J (n+1),
        ((Ico n.sqrt (cutoff J n)).filter fun i =>
          u i ∈ divisorsInWindow n a).card < hits r n := by
  have h : ∀ᵐ u ∂law P hP, ∀ r, ∀ᶠ n in atTop, u ∉ badEvent J r n :=
    ae_all_iff.2 fun r => ae_eventually_notMem (summable_bad J r P hP hc)
  obtain ⟨u, hu, h⟩ := ((ae_in_pools P hP).and h).exists
  refine ⟨u, hu, fun r => (h r).mono fun n hn a ha => ?_⟩
  exact lt_of_not_ge fun hm => hn ⟨a, ha, hm⟩

end GoodScale
/- Convert the interval survivor property into the exact gap bound. -/

open Filter Finset Asymptotics
open scoped Topology

namespace GoodScale

open GoodPools GoodSieve Erdos1101

private noncomputable def density (u : ℕ → ℕ) : ℝ :=
  ∏' i, (1 - 1 / (u i : ℝ))

private theorem density_bounds {u : ℕ → ℕ} (hu : ∀ i, 1 < u i)
    (hs : Summable (fun i : ℕ => 1 / (u i : ℝ)))
    (hs' : (∑' i : ℕ, 1 / (u i : ℝ)) ≤ (1/2 : ℝ)) :
    (1/2 : ℝ) ≤ density u ∧
      ∀ K : ℕ, density u ≤ ∏ i ∈ range K, (1 - 1 / (u i : ℝ)) := by
  let a : ℕ → ℝ := fun i => 1 / (u i : ℝ)
  have ha : ∀ i, 0 ≤ a i := fun _ => by dsimp [a]; positivity
  have hA : ∀ i, a i ≤ 1 := by
    intro i
    have hi : (1 : ℝ) ≤ u i := by exact_mod_cast (hu i).le
    dsimp [a]
    exact div_le_one_of_le₀ hi (by positivity)
  have hp : ∀ n, 1 - ∑ i ∈ range n, a i ≤ ∏ i ∈ range n, (1 - a i) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, prod_range_succ]
      have h₁ := mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr (hA n))
      have h₂ := mul_nonneg (sum_nonneg (s := range n) fun i _ => ha i) (ha n)
      nlinarith only [h₁, h₂]
  have hm : Multipliable (fun i => 1 - a i) := by
    simpa only [sub_eq_add_neg] using Real.multipliable_one_add_of_summable hs.neg
  have ht := hm.hasProd.tendsto_prod_nat
  constructor
  · refine ge_of_tendsto ht (Eventually.of_forall fun n => ?_)
    have h := (hs.sum_le_tsum (range n) (fun i _ => ha i)).trans hs'
    have h' := hp n
    linarith only [h, h']
  · intro K
    refine le_of_tendsto ht ?_
    filter_upwards [eventually_ge_atTop K] with n hn
    exact prod_le_prod_of_subset_of_le_one (range_mono hn)
      (fun i _ => sub_nonneg.mpr (hA i)) (fun i _ _ => sub_le_self _ (ha i))

private theorem tail_bound {f : ℕ → ℝ} (hn : ∀ i, 0 ≤ f i) (hf : Summable f)
    {η : ℝ} (hη : 0 < η) :
    ∃ K, ∀ H ≥ K, ∑ i ∈ Ico K H, f i ≤ η := by
  have he : ∀ᶠ K : ℕ in atTop, (∑' i, f i) - η < ∑ i ∈ range K, f i :=
    hf.hasSum.tendsto_sum_nat.eventually (lt_mem_nhds (sub_lt_self _ hη))
  obtain ⟨K, hK⟩ := he.exists
  refine ⟨K, fun H hH => ?_⟩
  have hp := hf.sum_le_tsum (range H) (fun i _ => hn i)
  rw [← sum_range_add_sum_Ico _ hH] at hp
  linarith

private theorem offset_small (C η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, C + (n.sqrt : ℝ) + 1 ≤ η * n := by
  filter_upwards [GoodPools.sqrt_tendsto.eventually_ge_atTop (max 1 ((|C|+2)/η))]
    with n hn
  have hs : (1 : ℝ) ≤ n.sqrt := (le_max_left _ _).trans hn
  have h₁ := (div_le_iff₀ hη).1 ((le_max_right (1 : ℝ) _).trans hn)
  have h₂ := mul_le_mul_of_nonneg_right h₁ (show (0 : ℝ) ≤ n.sqrt by positivity)
  have hsq : (n.sqrt : ℝ) * n.sqrt ≤ n := by exact_mod_cast Nat.sqrt_le n
  have h₃ := mul_le_mul_of_nonneg_left hsq hη.le
  have h₄ := mul_nonneg (show 0 ≤ |C|+1 by positivity) (sub_nonneg.mpr hs)
  nlinarith only [h₂, h₃, h₄, le_abs_self C]

private theorem surviving_interval {u : ℕ → ℕ} {J : ℕ} (r : ℕ)
    (hu : ∀ i, (u i).Prime) (hinj : Function.Injective u)
    (hlo : ∀ i, 8 ^ weight J i < u i)
    (hs : Summable (fun i => 1 / (u i : ℝ))) (hs' : (∑' i, 1 / (u i : ℝ)) ≤ (1/2 : ℝ))
    (hSparse : ∀ᶠ n : ℕ in atTop, ∀ a ≤ scale J (n+1),
      ((Ico n.sqrt (cutoff J n)).filter fun i => u i ∈ divisorsInWindow n a).card < hits r n) :
    ∀ᶠ n : ℕ in atTop, ∀ a ≤ scale J (n+1), ∃ b ∈ ASet u,
      a < b ∧ (b : ℝ) - a < (1 + 3 * slack r) * n / density u := by
  classical
  let δ := slack r
  let d := density u
  have hδ : 0 < δ := slack_pos r
  have hδ' : δ ≤ 1/4 := slack_le r
  obtain ⟨hd, hdK⟩ := density_bounds (fun i => (hu i).one_lt) hs hs'
  have hdp : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hd₁ : d ≤ 1 := by simpa using hdK 0
  obtain ⟨K, hK⟩ := tail_bound (fun i => by positivity : ∀ i, 0 ≤ 1 / (u i : ℝ)) hs
    (show 0 < δ/8 by positivity)
  let D := ∏ i ∈ range K, (u i : ℝ)
  have hδn := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (1/δ)
  filter_upwards [hSparse, above_window (J := J), sqrt_nat_tendsto.eventually_ge_atTop K,
    offset_small D (δ/2) (by positivity), hδn] with n hS hW hKn herr hn a ha
  let V := (1+2*δ)*(n : ℝ)/d
  let L := ⌈V⌉₊
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hVL : V ≤ (L : ℝ) := Nat.le_ceil _
  have hLV : (L : ℝ) < V+1 := Nat.ceil_lt_add_one hV
  have hL : L ≤ window n := by
    apply Nat.ceil_le.2
    change V ≤ (window n : ℝ)
    dsimp [V, window]
    push_cast
    apply (div_le_iff₀ hdp).2
    have h := mul_le_mul_of_nonneg_right hδ' (Nat.cast_nonneg n)
    have hd' := mul_le_mul_of_nonneg_left hd (show (0 : ℝ) ≤ 4*(n : ℝ) by positivity)
    nlinarith only [h, hd', (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hH : ∀ i, n.sqrt ≤ i → window n < u i :=
    fun i hi => (hW i hi).trans_lt (hlo i)
  have hpref : (1+2*δ)*(n : ℝ) ≤
      (∏ i ∈ range K, (1-1/(u i : ℝ))) * (L : ℝ) := by
    have h := (div_le_iff₀ hdp).1 hVL
    have he := mul_le_mul_of_nonneg_right (hdK K) (Nat.cast_nonneg L)
    linarith only [h, he]
  have htail : (L : ℝ) * (∑ i ∈ Ico K n.sqrt, 1 / (u i : ℝ)) ≤ δ/2*n := by
    have h := mul_le_mul_of_nonneg_left (hK n.sqrt hKn) (Nat.cast_nonneg L)
    have hL' : (L : ℝ) ≤ 4*(n : ℝ) := by exact_mod_cast hL
    have h' := mul_le_mul_of_nonneg_right hL' (show 0 ≤ δ/8 by positivity)
    nlinarith only [h, h']
  have hsurv := GoodSieve.survivors hu hinj (a := a) (L := L) hKn
  have hcount : hits r n ≤ #{b ∈ Ioc a (a+L) | ∀ i ∈ range n.sqrt, ¬u i ∣ b} := by
    have hceil := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ δ*n by positivity)
    have hhit : (hits r n : ℝ) ≤ (1+δ)*(n : ℝ)+1 := by
      unfold hits
      push_cast
      nlinarith only [hceil]
    have h := (show (hits r n : ℝ) ≤
         (#{b ∈ Ioc a (a+L) | ∀ i ∈ range n.sqrt, ¬u i ∣ b} : ℝ) from by
       change D + (n.sqrt : ℝ) + 1 ≤ _ at herr
       change _ - D - _ ≤ _ at hsurv
       nlinarith only [hsurv, hpref, htail, herr, hhit])
    exact_mod_cast h
  have hg : ∃ b ∈ Ioc a (a+L), b ∈ ASet u := by
    by_contra! h
    have hcov : ∀ b ∈ Ioc a (a+L), ∃ i, u i ∣ b := by
      intro b hb
      specialize h b hb
      simp only [ASet, Set.mem_ofPred_eq, not_forall, not_not] at h
      exact h
    have he := many_hits_of_covered hu hL hH (above_cutoff hlo a ha) hcount hcov
    exact (hS a ha).not_ge he
  obtain ⟨b, hb, hbu⟩ := hg
  obtain ⟨hab, hbl⟩ := mem_Ioc.1 hb
  have hbl' : (b : ℝ)-a ≤ L := by
    have h : (b : ℝ) ≤ a+L := by exact_mod_cast hbl
    linarith
  refine ⟨b, hbu, hab, hbl'.trans_lt (hLV.trans_le ?_)⟩
  have hdN := (div_le_iff₀ hδ).1 hn
  apply (le_div_iff₀ hdp).2
  have hVd : V*d = (1+2*δ)*(n : ℝ) := div_mul_cancel₀ _ hdp.ne'
  nlinarith only [hVd, hdN, hd₁]

private theorem product_le_scale {J : ℕ} {u : ℕ → ℕ}
    (hhi : ∀ i, u i ≤ 8^(weight J i+1)) (n : ℕ) :
    ∏ i ∈ range n, u i ≤ scale J n := by
  unfold scale
  have hsum : (∑ i ∈ range n, (weight J i+1)) = weightSum J n+n := by
    unfold weightSum
    simp [sum_add_distrib]
  rw [← hsum, ← prod_pow_eq_pow_sum]
  exact prod_le_prod' fun i _ => hhi i

private theorem le_t_of_prod_le {u : ℕ → ℕ} (hu : ∀ i, 2 ≤ u i) {x n : ℕ}
    (hn : ∏ i ∈ range n, u i ≤ x) : n ≤ t u x := by
  apply le_csSup (a := n) (s := {k : ℕ | ∏ i ∈ range k, u i ≤ x}) _ hn
  refine ⟨x, fun k hk => ?_⟩
  have h₂ : (2 : ℕ)^k ≤ ∏ i ∈ range k, u i := by
    simpa using (prod_le_prod' (s := range k) (f := fun _ => (2 : ℕ)) (g := u) (fun i _ => hu i))
  exact (Nat.le_of_lt (Nat.lt_pow_self (by decide : 1 < (2 : ℕ)))).trans (h₂.trans hk)

private theorem scale_index (J K x : ℕ) (hx : scale J K ≤ x) :
    ∃ n ≥ K, scale J n ≤ x ∧ x < scale J (n+1) := by
  have h : ∃ n, x < scale J (n+1) := by
    obtain ⟨n, hn⟩ := ((scale_tendsto J).eventually_gt_atTop x).exists
    exact ⟨n, hn.trans (scale_succ J n)⟩
  let n := Nat.find h
  have hn : x < scale J (n+1) := Nat.find_spec h
  have hmono : Monotone (scale J) := (strictMono_nat_of_lt_succ (scale_succ J)).monotone
  have hle : K ≤ n := by
    by_contra! hlt
    exact hn.not_ge ((hmono (Nat.succ_le_of_lt hlt)).trans hx)
  refine ⟨n, hle, ?_, hn⟩
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0]
    have hk : K = 0 := by omega
    simpa [hk] using hx
  · have hm := Nat.find_min h (show n-1 < Nat.find h by change n-1 < n; omega)
    have he : n-1+1 = n := by omega
    exact le_of_not_gt (by simpa only [he] using hm)

private theorem good_of_sparse {J : ℕ} {u : ℕ → ℕ} (hmono : StrictMono u)
    (hp : ∀ i, (u i).Prime) (hlo : ∀ i, 8^weight J i < u i)
    (hhi : ∀ i, u i ≤ 8^(weight J i+1))
    (hs : Summable (fun i => 1 / (u i : ℝ))) (hs' : (∑' i, 1 / (u i : ℝ)) ≤ (1/2 : ℝ))
    (hSparse : ∀ r, ∀ᶠ n : ℕ in atTop, ∀ a ≤ scale J (n+1),
      ((Ico n.sqrt (cutoff J n)).filter fun i => u i ∈ divisorsInWindow n a).card < hits r n) :
    IsGood u := by
  refine ⟨hmono, fun i j hij => (Nat.coprime_primes (hp i) (hp j)).2
      (fun h => hij (hmono.injective h)), hs, ?_⟩
  intro ε hε
  obtain ⟨r, hr⟩ := exists_nat_ge (3/ε)
  have hr' : 3 * slack r ≤ ε := by
    have h := (div_le_iff₀ hε).1 hr
    unfold slack
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < r+4)).2
    nlinarith only [h, hε]
  obtain ⟨K, hK⟩ := eventually_atTop.1
    (surviving_interval r hp hmono.injective hlo hs hs' (hSparse r))
  filter_upwards [eventually_ge_atTop (scale J K)] with x hx k hk
  obtain ⟨n, hn, hnx, hxn⟩ := scale_index J K x hx
  have ht : n ≤ t u x := le_t_of_prod_le (fun i => (hp i).two_le)
    ((product_le_scale hhi n).trans hnx)
  let a := A u k
  obtain ⟨b, hb, hab, hbg⟩ := hK n hn a (le_of_lt (hk.trans hxn))
  have hnext : A u (k+1) ≤ b := by
    by_contra! hh
    exact hab.not_ge (Nat.le_nth_of_lt_nth_succ (p := fun z => z ∈ ASet u) hh hb)
  have hgap : (A u (k+1) : ℝ) - A u k ≤ (b : ℝ) - a := by
    have h : (A u (k+1) : ℝ) ≤ b := by exact_mod_cast hnext
    exact sub_le_sub_right h _
  have hdp : 0 < density u := lt_of_lt_of_le (by norm_num)
    (density_bounds (fun i => (hp i).one_lt) hs hs').1
  apply hgap.trans_lt
  apply hbg.trans_le
  rw [div_eq_mul_inv]
  change _ ≤ (1+ε)*(t u x : ℝ)*(density u)⁻¹
  gcongr

end GoodScale

end OMA.Erdos1101PartII

theorem OMA.solution : type_of% @Erdos1101.erdos_1101.parts.ii := by
  open OMA.Erdos1101PartII.GoodPools OMA.Erdos1101PartII.GoodScale in
  obtain ⟨J, ⟨P, hP, hB, hO⟩, hJ⟩ := (pools_exist.and small_recip).exists
  obtain ⟨u, hu, hS⟩ := exists_sparse J P (fun i => (hP i).1) (fun i => (hP i).2)
  have h := fun i => hB i (u i) (hu i)
  have hlo : ∀ i, 8^weight J i < u i := fun i => (h i).1
  have hhi : ∀ i, u i ≤ 8^(weight J i+1) := fun i => (h i).2.1
  have hprime : ∀ i, (u i).Prime := fun i => (h i).2.2
  have hmono : StrictMono u := fun i j hij => hO i j (u i) (u j) hij (hu i) (hu j)
  have hR := hJ u hlo
  exact ⟨u, good_of_sparse hmono hprime hlo hhi hR.1 hR.2 hS, subexp hlo hhi⟩
