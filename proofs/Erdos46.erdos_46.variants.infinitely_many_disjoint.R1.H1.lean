import OMAReductions.R_Erdos46_erdos_46_variants_infinitely_many_disjoint_R1
import Mathlib

/-!
# Regular pools of squarefree denominators

Choose one prime from each of a collection of disjoint blocks. Sixteen
fixed power bands control the product size. A growing number of small
blocks supplies the reciprocal mass and the prime-factor count.

The lower reciprocal estimates use the finite Euler product for the
harmonic sum and bounds on the logarithmically weighted sum of primes.
Every denominator produced is squarefree.
-/

open Finset

namespace RegularReciprocalPool

private theorem small_block {α : Type} [DecidableEq α] (U : Finset α) (w : α → ℝ)
    {cap target : ℝ} (target_pos : 0 < target)
    (weights : ∀ x ∈ U, 0 ≤ w x ∧ w x ≤ cap) (total : target ≤ ∑ x ∈ U, w x) :
    ∃ S ⊆ U, target ≤ (∑ x ∈ S, w x) ∧ (∑ x ∈ S, w x) ≤ target + cap := by
  let wins := U.powerset.filter fun S => target ≤ ∑ x ∈ S, w x
  have win : wins.Nonempty := ⟨U, mem_filter.mpr ⟨mem_powerset.mpr Subset.rfl, total⟩⟩
  obtain ⟨S, hS, minimal⟩ := Finset.exists_min_image wins Finset.card win
  obtain ⟨sub, enough⟩ := mem_filter.mp hS
  have sub := mem_powerset.mp sub
  refine ⟨S, sub, enough, ?_⟩
  by_contra! large
  have nonempty : S.Nonempty := by
    by_contra! blank
    simp [blank, target_pos.not_ge] at enough
  obtain ⟨x, hx⟩ := nonempty
  have erase_sub := (erase_subset x S).trans sub
  have split := sum_erase_add S w hx
  have hxcap := (weights x (sub hx)).2
  have smaller_win : S.erase x ∈ wins := mem_filter.mpr
    ⟨mem_powerset.mpr erase_sub, by linarith⟩
  exact (not_lt_of_ge (minimal _ smaller_win)) (card_erase_lt_of_mem hx)

theorem split_into_blocks {α : Type} [DecidableEq α] (U : Finset α) (w : α → ℝ)
    {cap target : ℝ} (cap_nonneg : 0 ≤ cap) (target_pos : 0 < target)
    (weights : ∀ x ∈ U, 0 ≤ w x ∧ w x ≤ cap)
    (k : ℕ) (total : (k : ℝ) * (target + cap) ≤ ∑ x ∈ U, w x) :
    ∃ S : Fin k → Finset α, (Pairwise fun i j => Disjoint (S i) (S j)) ∧
      ∀ i, S i ⊆ U ∧ target ≤ ∑ x ∈ S i, w x := by
  induction k generalizing U with
  | zero => exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ k ih =>
    have enough : target ≤ ∑ x ∈ U, w x := by
      have hx : (0 : ℝ) ≤ k * (target + cap) := mul_nonneg (Nat.cast_nonneg _) (by positivity)
      push_cast at total
      nlinarith
    obtain ⟨B, sub, lo, hi⟩ := small_block U w target_pos weights enough
    have remainder : (k : ℝ) * (target + cap) ≤ ∑ x ∈ U \ B, w x := by
      have split := sum_sdiff (f := w) sub
      push_cast at total
      linarith
    obtain ⟨S, sep, within⟩ := ih (U \ B) (fun x hx => weights x (mem_sdiff.mp hx).1) remainder
    refine ⟨Fin.cons B S, ?_, ?_⟩
    · intro i j hne
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact (hne rfl).elim
        | succ j =>
          simpa using (disjoint_left.mpr fun x hx hS => (mem_sdiff.mp ((within j).1 hS)).2 hx :
            Disjoint B (S j))
      | succ i =>
        cases j using Fin.cases with
        | zero =>
          simpa using (disjoint_left.mpr fun x hx hS => (mem_sdiff.mp ((within i).1 hS)).2 hx :
            Disjoint B (S i)).symm
        | succ j =>
          simpa using sep (fun he => hne (congrArg Fin.succ he))
    · intro i
      cases i using Fin.cases with
      | zero => simpa using And.intro sub lo
      | succ j => simpa using And.intro ((within j).1.trans sdiff_subset) (within j).2

theorem pool_from_primes {ι : Type} [Fintype ι] [DecidableEq ι] (blocks : ι → Finset ℕ)
    (sep : Pairwise fun i j => Disjoint (blocks i) (blocks j))
    (prime : ∀ i p, p ∈ blocks i → Nat.Prime p) :
    ∃ P : Finset ℕ,
      (∀ n ∈ P, Squarefree n ∧ n.primeFactors.card = Fintype.card ι ∧
        ∃ x : ι → ℕ, (∀ i, x i ∈ blocks i) ∧ n = ∏ i, x i) ∧
      (∑ n ∈ P, (n : ℝ)⁻¹) = ∏ i, ∑ p ∈ blocks i, (p : ℝ)⁻¹ := by
  classical
  let Choice := ∀ i, {p // p ∈ blocks i}
  let value (u : Choice) (i : ι) : ℕ := (u i).val
  let picks (u : Choice) := univ.image (value u)
  let number (u : Choice) := ∏ i, value u i
  have disjoint_choice (u v : Choice) {i j : ι} (same : value u i = value v j) :
      i = j := by
    by_contra apart
    have hv : value v j ∈ blocks j := (v j).property
    rw [← same] at hv
    exact Finset.disjoint_left.mp (sep apart) (u i).property hv
  have val_inj (u : Choice) : Function.Injective (value u) := fun _ _ h => disjoint_choice u u h
  have factors (u : Choice) : (number u).primeFactors = picks u := by
    rw [show number u = ∏ p ∈ picks u, p by
      symm
      exact Finset.prod_image (val_inj u).injOn]
    apply Nat.primeFactors_prod
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact prime i _ (u i).property
  have num_inj : Function.Injective number := by
    intro u v h
    have eq : picks u = picks v := by rw [← factors u, ← factors v, h]
    funext i
    have hit : value u i ∈ picks v := eq ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    obtain ⟨j, _, same⟩ := Finset.mem_image.mp hit
    obtain rfl := disjoint_choice v u same
    exact Subtype.ext same.symm
  refine ⟨univ.image number, ?_, ?_⟩
  · intro n hn
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hn
    have product : number u = ∏ p ∈ picks u, p := by
      symm
      exact Finset.prod_image (val_inj u).injOn
    have pprime (p : ℕ) (hp : p ∈ picks u) : p.Prime := by
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
      exact prime i _ (u i).property
    refine ⟨?_, ?_, value u, fun i => (u i).property, rfl⟩
    · rw [product]
      refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ (fun p hp => (pprime p hp).squarefree)
      intro p hp q hq pq
      simpa only [← Nat.coprime_iff_isRelPrime] using (Nat.coprime_primes (pprime p hp) (pprime q hq)).mpr pq
    · rw [factors, show picks u = univ.image (value u) from rfl,
        Finset.card_image_of_injective _ (val_inj u), Finset.card_univ]
  · rw [Finset.sum_image num_inj.injOn]
    calc
      ∑ u : Choice, (number u : ℝ)⁻¹ = ∑ u : Choice, ∏ i, (value u i : ℝ)⁻¹ := by
        simp only [number, Nat.cast_prod, Finset.prod_inv_distrib]
      _ = ∏ i, ∑ p : {p // p ∈ blocks i}, (p.val : ℝ)⁻¹ := by
        symm
        exact Fintype.prod_sum fun i (p : {p // p ∈ blocks i}) => (p.val : ℝ)⁻¹
      _ = ∏ i, ∑ p ∈ blocks i, (p : ℝ)⁻¹ := by
        apply Finset.prod_congr rfl
        intro i _
        exact Finset.sum_coe_sort (blocks i) (fun p : ℕ => (p : ℝ)⁻¹)

end RegularReciprocalPool

open Finset

namespace RegularReciprocalPool

private theorem harmonic_le_euler (N : ℕ) :
    (harmonic N : ℝ) ≤ ∏ p ∈ Nat.primesLE N, (1 - (p : ℝ)⁻¹)⁻¹ := by
  let P := range (N + 1)
  let invNat : ℕ → ℝ := fun n => (n : ℝ)⁻¹
  have normgeo {p : ℕ} (hp : p.Prime) :
      (fun j : ℕ => ‖invNat (p ^ j)‖) = fun j => ((p : ℝ)⁻¹) ^ j := by
    funext j
    simp [invNat, Nat.cast_pow, inv_pow]
  have geoBound {p : ℕ} (hp : p.Prime) : (p : ℝ)⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have geo {p : ℕ} (hp : p.Prime) : Summable (fun j : ℕ => ‖invNat (p ^ j)‖) := by
    rw [normgeo hp]
    exact summable_geometric_of_lt_one (by positivity) (geoBound hp)
  obtain ⟨hsum, hfac⟩ := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := invNat) (by simp [invNat]) (fun _ => by simp [invNat, Nat.cast_mul, mul_inv_rev, mul_comm]) geo P
  have factored {n : ℕ} (hn : n ∈ Icc 1 N) : n ∈ Nat.factoredNumbers P := by
    obtain ⟨hlo, hhi⟩ := mem_Icc.mp hn
    refine Nat.mem_factoredNumbers_of_primeFactors_subset (by omega) ?_
    intro p hp
    have hpn := Nat.le_of_dvd (by omega : 0 < n) (Nat.dvd_of_mem_primeFactors hp)
    exact mem_range.mpr (by omega)
  let emb : {n // n ∈ Icc 1 N} ↪ Nat.factoredNumbers P :=
    ⟨fun n => ⟨n, factored n.property⟩, fun _ _ eq => Subtype.ext (congrArg (fun z : Nat.factoredNumbers P => (z : ℕ)) eq)⟩
  calc
    (harmonic N : ℝ) = ∑ n ∈ ((Icc 1 N).attach.map emb), invNat n := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, sum_map]
      exact (sum_attach (Icc 1 N) invNat).symm
    _ ≤ ∑' n : Nat.factoredNumbers P, invNat n :=
      hsum.of_norm.sum_le_tsum _ (fun _ _ => by dsimp [invNat]; positivity)
    _ = ∏ p ∈ Nat.primesLE N, (1 - (p : ℝ)⁻¹)⁻¹ := by
      rw [hfac.tsum_eq, Nat.primesLE_eq_filter_range]
      apply prod_congr rfl
      intro p hp
      have prime := (mem_filter.mp hp).2
      simp only [invNat, Nat.cast_pow, ← inv_pow]
      exact tsum_geometric_of_lt_one (by positivity) (geoBound prime)

private theorem log_eulerFactor_le {x : ℝ} (hx : 2 ≤ x) :
    Real.log (1 - x⁻¹)⁻¹ ≤ x⁻¹ + 2 * (x ^ 2)⁻¹ := by
  have x0 : 0 < x := by linarith
  have x1 : 0 < x - 1 := by linarith
  have denom : 0 < 1 - x⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ (by linarith))
  have change_factor : (1 - x⁻¹)⁻¹ - 1 = (x - 1)⁻¹ := by
    field_simp
    ring
  have gap : (x - 1)⁻¹ - x⁻¹ = (x * (x - 1))⁻¹ := by
    field_simp
    ring
  have small : (x * (x - 1))⁻¹ ≤ 2 * (x ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv, ← one_div]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith
  have bound := Real.log_le_sub_one_of_pos (inv_pos.mpr denom)
  rw [change_factor] at bound
  linarith

theorem prime_recip_lower :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      Real.log (Real.log ((N : ℝ) + 1)) - C ≤ ∑ p ∈ Nat.primesLE N, (p : ℝ)⁻¹ := by
  let C := 2 * ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹
  refine ⟨C, fun N hN => ?_⟩
  have n1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have log_pos : 0 < Real.log ((N : ℝ) + 1) := Real.log_pos (by linarith)
  have harm := log_add_one_le_harmonic N
  push_cast at harm
  have log_le := Real.log_le_log log_pos (harm.trans (harmonic_le_euler N))
  rw [Real.log_prod] at log_le
  · have point (p : ℕ) (hp : p ∈ Nat.primesLE N) :
        Real.log (1 - (p : ℝ)⁻¹)⁻¹ ≤ (p : ℝ)⁻¹ + 2 * ((p : ℝ) ^ 2)⁻¹ :=
      log_eulerFactor_le (by exact_mod_cast Nat.two_le_of_mem_primesLE hp)
    have hsum := sum_le_sum point
    rw [sum_add_distrib, ← mul_sum] at hsum
    have tail : (∑ p ∈ Nat.primesLE N, ((p : ℝ) ^ 2)⁻¹) ≤ ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹ :=
      (Real.summable_nat_pow_inv.mpr (by decide : 1 < 2)).sum_le_tsum _ (fun _ _ => by positivity)
    dsimp [C]
    linarith
  · intro p hp
    have pos : 0 < 1 - (p : ℝ)⁻¹ :=
      sub_pos.mpr (inv_lt_one_of_one_lt₀ (by exact_mod_cast Nat.one_lt_of_mem_primesLE hp))
    exact inv_ne_zero pos.ne'

end RegularReciprocalPool

open Filter Finset
open scoped Topology

namespace RegularReciprocalPool

noncomputable def primeBand (a b : ℝ) : Finset ℕ :=
  Nat.primesLE ⌊b⌋₊ \ Nat.primesLE ⌊a⌋₊

theorem mem_primeBand {a b : ℝ} {p : ℕ} :
    p ∈ primeBand a b ↔ p.Prime ∧ a < (p : ℝ) ∧ (p : ℝ) ≤ b := by
  constructor
  · intro h
    obtain ⟨hi, lo⟩ := mem_sdiff.mp h
    obtain ⟨hle, hp⟩ := Nat.mem_primesLE.mp hi
    exact ⟨hp, Nat.lt_of_floor_lt (lt_of_not_ge fun hh => lo (Nat.mem_primesLE.mpr ⟨hh, hp⟩)),
      (Nat.le_floor_iff' hp.ne_zero).1 hle⟩
  · rintro ⟨hp, lo, hi⟩
    refine mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨Nat.le_floor hi, hp⟩, ?_⟩
    intro h
    exact lo.not_ge ((Nat.le_floor_iff' hp.ne_zero).1 (Nat.le_of_mem_primesLE h))

noncomputable def bandMass (a b : ℝ) : ℝ :=
  ∑ p ∈ primeBand a b, (p : ℝ)⁻¹

private theorem bandMass_eq_sub {a b : ℝ} (hab : a ≤ b) :
    bandMass a b =
      (∑ p ∈ Nat.primesLE ⌊b⌋₊, (p : ℝ)⁻¹) - ∑ p ∈ Nat.primesLE ⌊a⌋₊, (p : ℝ)⁻¹ := by
  have h := sum_sdiff (f := fun p : ℕ => (p : ℝ)⁻¹)
    (Nat.primesLE_mono (Nat.floor_mono hab))
  unfold bandMass primeBand
  linarith

theorem bandMass_add {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    bandMass a b + bandMass b c = bandMass a c := by
  rw [bandMass_eq_sub hab, bandMass_eq_sub hbc, bandMass_eq_sub (hab.trans hbc)]
  ring

theorem bandMass_mono {a b c : ℝ} (hbc : b ≤ c) :
    bandMass a b ≤ bandMass a c := by
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    rcases mem_primeBand.mp hp with ⟨pprime, ha, hb⟩
    exact mem_primeBand.mpr ⟨pprime, ha, hb.trans hbc⟩
  · intro p _ _
    positivity

private theorem theta_eventually_lower :
    ∀ᶠ x : ℝ in atTop, (Real.log 2 / 2) * x ≤ Chebyshev.theta x := by
  have log_two : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have scale := (isLittleO_log_rpow_atTop (by norm_num : 0 < (1/2 : ℝ))).def
    (div_pos log_two (by norm_num : (0 : ℝ) < 16))
  filter_upwards [scale, eventually_ge_atTop (8 : ℝ)] with x hlog hx
  have x0 : 0 ≤ x := by linarith
  have x1 : 1 ≤ x := by linarith
  have hlog' : Real.log x ≤ Real.log 2 / 16 * √x := by
    rw [← Real.sqrt_eq_rpow] at hlog
    simpa only [Real.norm_of_nonneg (Real.log_nonneg x1),
      Real.norm_of_nonneg (Real.sqrt_nonneg x)] using hlog
  have sq := Real.sq_sqrt x0
  have root_le : √x ≤ x := by nlinarith [Real.sqrt_nonneg x]
  have a := hlog'.trans (mul_le_mul_of_nonneg_left root_le (by positivity : 0 ≤ Real.log 2 / 16))
  have b := mul_le_mul_of_nonneg_left hlog' (Real.sqrt_nonneg x)
  rw [show √x * (Real.log 2 / 16 * √x) = Real.log 2 / 16 * (√x)^2 by ring, sq] at b
  have c : Real.log (x + 2) ≤ Real.log 2 + Real.log x := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : x ≠ 0)]
    exact Real.log_le_log (by linarith) (by linarith)
  have d := Chebyshev.theta_ge' x1
  have e := mul_le_mul_of_nonneg_right hx (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  nlinarith only [a, b, c, d, e, log_two]

private theorem one_band {X : ℝ}
    (lower : ∀ t ≥ X, (Real.log 2 / 2) * t ≤ Chebyshev.theta t)
    {x : ℝ} (hx : X ≤ x) (hx1 : 1 < x) :
    Real.log 2 / (4 * Real.log (8 * x)) ≤ bandMass x (8 * x) := by
  have x0 : 0 < x := by linarith
  have hx8 : x ≤ 8 * x := by linarith
  have log_pos : 0 < Real.log (8 * x) := Real.log_pos (by linarith)
  have theta_gap : 2 * Real.log 2 * x ≤
      Chebyshev.theta (8 * x) - Chebyshev.theta x := by
    have hlo := lower _ (hx.trans hx8)
    have hhi := Chebyshev.theta_le_log4_mul_x x0.le
    have eq : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rw [eq] at hhi
    linarith
  have thetaEq : (∑ p ∈ primeBand x (8 * x), Real.log (p : ℝ)) =
      Chebyshev.theta (8 * x) - Chebyshev.theta x := by
    rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE]
    have h := sum_sdiff (f := fun p : ℕ => Real.log (p : ℝ))
      (Nat.primesLE_mono (Nat.floor_mono hx8))
    unfold primeBand
    linarith
  have compare : (∑ p ∈ primeBand x (8 * x), Real.log (p : ℝ)) ≤
      (8 * x * Real.log (8 * x)) * bandMass x (8 * x) := by
    unfold bandMass
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    have ⟨pprime, _, hp8⟩ := mem_primeBand.mp hp
    have ppos : 0 < (p : ℝ) := by exact_mod_cast pprime.pos
    rw [← div_eq_mul_inv, le_div_iff₀ ppos]
    have log_le := Real.log_le_log ppos hp8
    have log_nonneg : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast pprime.one_le)
    calc
      Real.log (p : ℝ) * p ≤ Real.log (8 * x) * (8 * x) :=
        mul_le_mul log_le hp8 (by positivity) log_pos.le
      _ = _ := mul_comm _ _
  rw [thetaEq] at compare
  apply (div_le_iff₀ (by positivity : 0 < 4 * Real.log (8 * x))).2
  have h := theta_gap.trans compare
  apply (mul_le_mul_iff_right₀ (show 0 < 2 * x by positivity)).1
  rw [show 2 * x * (bandMass x (8 * x) * (4 * Real.log (8 * x))) =
      (8 * x * Real.log (8 * x)) * bandMass x (8 * x) by ring]
  linarith

private theorem repeat_band {X : ℝ}
    (lower : ∀ t ≥ X, (Real.log 2 / 2) * t ≤ Chebyshev.theta t)
    {x y : ℝ} (hx : X ≤ x) (hx1 : 1 < x) (m : ℕ)
    (hEnd : x * 8 ^ m ≤ y) :
    (m : ℝ) * (Real.log 2 / (4 * Real.log y)) ≤ bandMass x (x * 8 ^ m) := by
  induction m with
  | zero => simp [bandMass, primeBand]
  | succ m ih =>
    let z := x * (8 : ℝ) ^ m
    have xz : x ≤ z := le_mul_of_one_le_right (by linarith)
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 8))
    have z1 : 1 < z := hx1.trans_le xz
    have z8 : z ≤ 8 * z := by linarith
    have next : x * (8 : ℝ) ^ (m + 1) = 8 * z := by
      simp only [z, pow_succ]
      ring
    rw [next] at hEnd ⊢
    have less := ih (z8.trans hEnd)
    have k := one_band lower (hx.trans xz) z1
    have scale : Real.log 2 / (4 * Real.log y) ≤ Real.log 2 / (4 * Real.log (8 * z)) := by
      have log8 : 0 < Real.log (8 * z) := Real.log_pos (by linarith)
      apply div_le_div_of_nonneg_left (Real.log_nonneg (by norm_num)) (by positivity)
      exact mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) hEnd) (by norm_num)
    have join := bandMass_add xz z8
    push_cast
    change ((m : ℝ) + 1) * (Real.log 2 / (4 * Real.log y)) ≤ bandMass x (8 * z)
    change (m : ℝ) * (Real.log 2 / (4 * Real.log y)) ≤ bandMass x z at less
    linarith only [less, scale, k, join]

theorem prime_band_lower {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ c > (0 : ℝ), ∀ᶠ T : ℝ in atTop, c ≤ bandMass (T ^ a) (T ^ b) := by
  have hb : 0 < b := ha.trans hab
  have d0 : 0 < b - a := sub_pos.mpr hab
  have l2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have l8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  refine ⟨(b-a) * Real.log 2 / (8 * b * Real.log 8), by positivity, ?_⟩
  obtain ⟨X, thetaLower⟩ := eventually_atTop.mp theta_eventually_lower
  have hcut := (tendsto_rpow_atTop ha).eventually_ge_atTop (max X 2)
  have hsize := Real.tendsto_log_atTop.eventually_ge_atTop (2 * Real.log 8 / (b-a))
  filter_upwards [hcut, hsize, eventually_ge_atTop (2 : ℝ)] with T hcut hsize hT
  have T0 : 0 < T := by linarith
  have logT : 0 < Real.log T := Real.log_pos (by linarith)
  let t := (b-a) * Real.log T / Real.log 8
  let m := ⌊t⌋₊
  have t2 : 2 ≤ t := (le_div_iff₀ l8).2 (by
    have h := (div_le_iff₀ d0).1 hsize
    linarith)
  have m_hi : (m : ℝ) ≤ t := Nat.floor_le (by linarith)
  have m_lo : t / 2 ≤ (m : ℝ) := by
    have h := Nat.lt_floor_add_one t
    change t < (m : ℝ) + 1 at h
    linarith
  have end_le : T ^ a * (8 : ℝ) ^ m ≤ T ^ b := by
    apply (Real.le_rpow_iff_log_le (by positivity) T0).2
    rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow T0, Real.log_pow]
    have h := (le_div_iff₀ l8).1 m_hi
    linarith
  have each := repeat_band thetaLower
    ((le_max_left X 2).trans hcut)
    (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) ((le_max_right X 2).trans hcut)) m end_le
  have compare := bandMass_mono (a := T ^ a) end_le
  have logTb : 0 < Real.log (T ^ b) := by rw [Real.log_rpow T0]; positivity
  calc
    _ = t / 2 * (Real.log 2 / (4 * Real.log (T ^ b))) := by
      rw [Real.log_rpow T0]
      dsimp [t]
      field_simp
      ring
    _ ≤ (m : ℝ) * (Real.log 2 / (4 * Real.log (T ^ b))) :=
      mul_le_mul_of_nonneg_right m_lo (by positivity)
    _ ≤ bandMass (T ^ a) (T ^ a * 8 ^ m) := each
    _ ≤ _ := compare

end RegularReciprocalPool

open Filter Finset
open scoped Topology

namespace RegularReciprocalPool

noncomputable def smallCount (L : ℝ) : ℕ := ⌊L - √L⌋₊

noncomputable def smallWeight (L : ℝ) : ℝ := 1 + (4 * √L)⁻¹

noncomputable def smallExponent (L : ℝ) : ℝ := (32 * L)⁻¹

theorem small_count_bounds {L : ℝ} (hL : 1024 ≤ L) :
    (32 : ℝ) ≤ √L ∧ L / 2 ≤ (smallCount L : ℝ) ∧
      (smallCount L : ℝ) ≤ L - √L ∧ L - √L - 1 ≤ (smallCount L : ℝ) := by
  have root0 := Real.sqrt_nonneg L
  have sq := Real.sq_sqrt (by linarith : 0 ≤ L)
  have root32 : (32 : ℝ) ≤ √L := by
    by_contra! h
    nlinarith [mul_pos (sub_pos.mpr h) (show 0 < 32 + √L by linarith)]
  have root4 : √L ≤ L / 4 := by
    nlinarith [mul_nonneg root0 (show 0 ≤ √L - 4 by linarith)]
  have fhi : (smallCount L : ℝ) ≤ L - √L := Nat.floor_le (by linarith)
  have flo := Nat.lt_floor_add_one (L - √L)
  change L - √L < (smallCount L : ℝ) + 1 at flo
  exact ⟨root32, by linarith, fhi, by linarith⟩

theorem small_budget {L : ℝ} (hL : 1024 ≤ L) :
    (smallCount L : ℝ) * (smallWeight L + L⁻¹) ≤ L - √L / 4 := by
  obtain ⟨root32, _, k_hi, _⟩ := small_count_bounds hL
  have L0 : 0 < L := by linarith
  have root0 : 0 < √L := by linarith
  have kL : (smallCount L : ℝ) ≤ L := by linarith
  have part1 : (smallCount L : ℝ) * (4 * √L)⁻¹ ≤ √L / 4 := by
    calc
      _ ≤ L * (4 * √L)⁻¹ := mul_le_mul_of_nonneg_right kL (by positivity)
      _ = _ := by
        rw [← Real.sq_sqrt L0.le]
        rw [Real.sqrt_sq_eq_abs, abs_of_pos root0]
        field_simp
  have part2 : (smallCount L : ℝ) * L⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one L0]
    exact kL
  unfold smallWeight
  rw [mul_add, mul_add, mul_one]
  linarith

theorem small_weight_pow {L : ℝ} (hL : 1024 ≤ L) :
    1 + √L / 8 ≤ smallWeight L ^ smallCount L := by
  obtain ⟨root32, k_lo, _, _⟩ := small_count_bounds hL
  have L0 : 0 < L := by linarith
  have root0 : 0 < √L := by linarith
  have w0 : 0 ≤ (4 * √L)⁻¹ := by positivity
  have w2 : (-2 : ℝ) ≤ (4 * √L)⁻¹ := by linarith only [w0]
  have main := one_add_mul_le_pow w2 (smallCount L)
  unfold smallWeight
  apply le_trans _ main
  gcongr
  calc
    √L / 8 = (L / 2) * (4 * √L)⁻¹ := by
      rw [← Real.sq_sqrt L0.le]
      rw [Real.sqrt_sq_eq_abs, abs_of_pos root0]
      field_simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right k_lo (by positivity)

theorem eventual_log_loss (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, 2 * Real.log L + C ≤ √L / 4 := by
  have est := (isLittleO_log_rpow_atTop (by norm_num : 0 < (1 / 2 : ℝ))).def
    (by norm_num : 0 < (1 / 16 : ℝ))
  have large := (tendsto_rpow_atTop (by norm_num : 0 < (1/2 : ℝ))).eventually_ge_atTop (8 * C)
  filter_upwards [est, large, eventually_ge_atTop (1 : ℝ)] with L hlog hlarge hL
  rw [← Real.sqrt_eq_rpow] at hlog hlarge
  have est' : Real.log L ≤ √L / 16 := by
    simp only [Real.norm_of_nonneg (Real.log_nonneg hL),
      Real.norm_of_nonneg (Real.sqrt_nonneg L)] at hlog
    linarith
  linarith

theorem eventual_exp_dom :
    ∀ᶠ L : ℝ in atTop, 32 * L^2 ≤ Real.exp L := by
  have h := (tendsto_exp_div_rpow_atTop 2).eventually_ge_atTop 32
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with L h hL
  have hn := (le_div_iff₀ (show 0 < L ^ (2 : ℝ) by positivity)).1 h
  norm_num [Real.rpow_natCast] at hn
  exact hn

end RegularReciprocalPool

namespace RegularReciprocalPool

open Filter Finset

theorem general_band_lower :
    ∃ C : ℝ, ∀ {x y : ℝ}, 1 ≤ x → x ≤ y → 1 < y →
      Real.log (Real.log y) - Real.log x - C ≤ bandMass x y := by
  obtain ⟨C, lower⟩ := prime_recip_lower
  refine ⟨C + 1, ?_⟩
  intro x y x1 xy y1
  have nh : 1 ≤ ⌊y⌋₊ := (Nat.one_le_floor_iff y).2 y1.le
  have logy : 0 < Real.log y := Real.log_pos y1
  have lefloor := (Nat.lt_floor_add_one y).le
  have compareLog := Real.log_le_log logy (Real.log_le_log (by linarith) lefloor)
  have hupper : (∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ)⁻¹) ≤ harmonic ⌊x⌋₊ := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    refine sum_le_sum_of_subset_of_nonneg (fun p hp => mem_Icc.mpr ⟨
      (Nat.prime_of_mem_primesLE hp).one_le, Nat.le_of_mem_primesLE hp⟩) ?_
    intro _ _ _
    positivity
  have huh := hupper.trans (harmonic_floor_le_one_add_log x x1)
  have hlo := lower ⌊y⌋₊ nh
  rw [bandMass_eq_sub xy]
  linarith

theorem small_band_eventually :
    ∀ᶠ T : ℝ in atTop,
      let L := Real.log (Real.log T)
      1024 ≤ L ∧ L ≤ T ^ smallExponent L ∧
        L - √L / 4 ≤ bandMass L (T ^ smallExponent L) := by
  obtain ⟨C, lower⟩ := general_band_lower
  have tendsto_L := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have eloss := tendsto_L.eventually (eventual_log_loss (C + Real.log 32))
  have edom := tendsto_L.eventually eventual_exp_dom
  have big := tendsto_L.eventually_ge_atTop 1024
  filter_upwards [eloss, edom, big, eventually_ge_atTop (2 : ℝ)] with T loss expo big T2
  let L := Real.log (Real.log T)
  have Lbig : (1024 : ℝ) ≤ L := big
  have L0 : 0 < L := by linarith
  have L1 : 1 ≤ L := by linarith
  have T0 : 0 < T := by linarith
  have logT : 0 < Real.log T := Real.log_pos (by linarith)
  have eL : Real.exp L = Real.log T := Real.exp_log logT
  have y_bound : L ≤ T ^ smallExponent L := by
    apply (Real.le_rpow_iff_log_le L0 T0).2
    apply (Real.log_le_self L0.le).trans
    unfold smallExponent
    rw [inv_mul_eq_div, le_div_iff₀ (by positivity : 0 < 32 * L)]
    change 32 * L^2 ≤ Real.exp L at expo
    rw [eL] at expo
    nlinarith only [expo]
  have loglog : Real.log (Real.log (T ^ smallExponent L)) = L - Real.log 32 - Real.log L := by
    rw [Real.log_rpow T0, Real.log_mul (by unfold smallExponent; positivity) logT.ne']
    unfold smallExponent
    rw [Real.log_inv, Real.log_mul (by norm_num : (32 : ℝ) ≠ 0) L0.ne']
    change -(Real.log 32 + Real.log L) + L = L - Real.log 32 - Real.log L
    ring
  refine ⟨Lbig, y_bound, ?_⟩
  have h := lower L1 y_bound (by linarith)
  rw [loglog] at h
  change 2 * Real.log L + (C + Real.log 32) ≤ √L / 4 at loss
  linarith only [h, loss]

end RegularReciprocalPool

namespace RegularReciprocalPool

open Filter Finset

noncomputable def largeLeft (i : Fin 16) : ℝ := 1 / 16 + i.val / 8192

noncomputable def largeRight (i : Fin 16) : ℝ := 1 / 16 + (i.val + 1) / 8192

noncomputable def largeBlocks (T : ℝ) (i : Fin 16) : Finset ℕ :=
  primeBand (T ^ largeLeft i) (T ^ largeRight i)

theorem large_bounds {T : ℝ} (T1 : 1 ≤ T) {i : Fin 16} {p : ℕ}
    (hp : p ∈ largeBlocks T i) :
    p.Prime ∧ T ^ (1 / 16 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ T ^ (33 / 512 : ℝ) := by
  obtain ⟨hp', hlo, hhi⟩ := mem_primeBand.mp hp
  have ile : (i.val : ℝ) ≤ 15 := by exact_mod_cast (show i.val ≤ 15 by omega)
  have a : (1 / 16 : ℝ) ≤ largeLeft i := by
    unfold largeLeft
    exact le_add_of_nonneg_right (by positivity)
  have b : largeRight i ≤ 33 / 512 := by unfold largeRight; linarith
  exact ⟨hp', (Real.rpow_le_rpow_of_exponent_le T1 a).trans_lt hlo,
    hhi.trans (Real.rpow_le_rpow_of_exponent_le T1 b)⟩

private theorem large_order {T : ℝ} (T1 : 1 ≤ T) {i j : Fin 16} (ij : i < j) :
    Disjoint (largeBlocks T i) (largeBlocks T j) := by
  apply Finset.disjoint_left.mpr
  intro p hi hj
  have h : ((i.val : ℝ) + 1) ≤ j.val := by
    exact_mod_cast Nat.succ_le_of_lt ij
  have h' : largeRight i ≤ largeLeft j := by
    unfold largeRight largeLeft
    linarith
  exact ((mem_primeBand.mp hj).2.1.not_ge)
    ((mem_primeBand.mp hi).2.2.trans (Real.rpow_le_rpow_of_exponent_le T1 h'))

theorem large_disjoint {T : ℝ} (T1 : 1 ≤ T) :
    Pairwise fun i j => Disjoint (largeBlocks T i) (largeBlocks T j) := by
  intro i j ne
  rcases lt_or_gt_of_ne ne with ij | ji
  · exact large_order T1 ij
  · exact (large_order T1 ji).symm

theorem eventual_large_mass :
    ∃ b > (0 : ℝ), ∀ᶠ T : ℝ in atTop,
      b ≤ ∏ i : Fin 16, ∑ p ∈ largeBlocks T i, (p : ℝ)⁻¹ := by
  have each (i : Fin 16) : ∃ b > (0 : ℝ),
      ∀ᶠ T : ℝ in atTop, b ≤ ∑ p ∈ largeBlocks T i, (p : ℝ)⁻¹ :=
    prime_band_lower (a := largeLeft i) (b := largeRight i)
      (by unfold largeLeft; positivity) (by unfold largeLeft largeRight; linarith)
  choose c cpos hev using each
  refine ⟨∏ i, c i, prod_pos (fun i _ => cpos i), ?_⟩
  filter_upwards [Filter.eventually_all.mpr hev] with T hT
  exact prod_le_prod (fun i _ => (cpos i).le) (fun i _ => hT i)

private theorem real_prod_const_rpow {ι : Type*} [Fintype ι] {T : ℝ} (hT : 0 ≤ T) (s : ℝ) :
    (∏ _ : ι, T ^ s) = T ^ (s * Fintype.card ι) := by
  rw [Finset.prod_const, Finset.card_univ, Real.rpow_mul hT, Real.rpow_natCast]

theorem large_products {T : ℝ} (T1 : 1 ≤ T) {x : Fin 16 → ℕ}
    (hx : ∀ i, x i ∈ largeBlocks T i) :
    T ≤ (∏ i, x i : ℕ) ∧ (∏ i, x i : ℕ) ≤ T ^ (33 / 32 : ℝ) := by
  have T0 : 0 ≤ T := by linarith
  push_cast
  constructor
  · calc
      T = ∏ _ : Fin 16, T ^ (1 / 16 : ℝ) := by
        rw [real_prod_const_rpow T0]
        norm_num
      _ ≤ ∏ i, (x i : ℝ) :=
        prod_le_prod (fun _ _ => by positivity) (fun i _ => (large_bounds T1 (hx i)).2.1.le)
  · calc
      _ ≤ ∏ _ : Fin 16, T ^ (33 / 512 : ℝ) :=
        prod_le_prod (fun _ _ => by positivity) (fun i _ => (large_bounds T1 (hx i)).2.2)
      _ = _ := by
        rw [real_prod_const_rpow T0]
        norm_num

end RegularReciprocalPool

namespace RegularReciprocalPool

open Filter Finset

def Regular (N n : ℕ) : Prop :=
  N ≤ n ∧ (n : ℝ) ≤ (N : ℝ) ^ (1 + (1 / 16 : ℝ)) ∧
  (∀ q ∈ n.divisors, IsPrimePow q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 8 : ℝ)) ∧
  |(n.primeFactors.card : ℝ) - Real.log (Real.log n)| ≤
    (Real.log (Real.log n)) ^ (3 / 4 : ℝ) ∧
  |(n.primeFactorsList.length : ℝ) - Real.log (Real.log n)| ≤
    (Real.log (Real.log n)) ^ (3 / 4 : ℝ)

private theorem regular_of_bounds {N n : ℕ} (hN : 2 ≤ N)
    (hlo : (N : ℝ) ≤ n) (hhi : (n : ℝ) ≤ (N : ℝ) ^ (17 / 16 : ℝ))
    (hPrime : ∀ q ∈ n.primeFactors, (q : ℝ) ≤ (N : ℝ) ^ (1 / 8 : ℝ))
    (hf : Squarefree n) (hcount : n.primeFactors.card = 16 + smallCount (Real.log (Real.log N)))
    (hL : 1024 ≤ Real.log (Real.log N)) (quarter : 2 ≤ (Real.log (Real.log N)) ^ (1 / 4 : ℝ)) :
    Regular N n := by
  let L := Real.log (Real.log N)
  have N2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have N0 : 0 < (N : ℝ) := by linarith
  have n0 : 0 < (n : ℝ) := N0.trans_le hlo
  have logN : 0 < Real.log N := Real.log_pos (by linarith)
  have logs := Real.log_le_log N0 hlo
  have logn := logN.trans_le logs
  have Llo := Real.log_le_log logN logs
  have Lhi : Real.log (Real.log n) ≤ L + 1 := by
    have h := Real.log_le_log logn ((Real.le_rpow_iff_log_le n0 N0).1 hhi)
    rw [Real.log_mul (by norm_num : (17/16 : ℝ) ≠ 0) logN.ne'] at h
    have hh := Real.log_le_sub_one_of_pos (by norm_num : 0 < (17/16 : ℝ))
    change Real.log (Real.log n) ≤ L + 1
    change Real.log (Real.log n) ≤ Real.log (17/16 : ℝ) + L at h
    linarith
  obtain ⟨sqrt32, _, khi, klo⟩ := small_count_bounds hL
  have cardR : (n.primeFactors.card : ℝ) = 16 + (smallCount L : ℝ) := by exact_mod_cast hcount
  have main : |(n.primeFactors.card : ℝ) - Real.log (Real.log n)| ≤
      (Real.log (Real.log n)) ^ (3/4 : ℝ) := by
    have prev : L ≤ Real.log (Real.log n) := Llo
    have L0 : 0 ≤ L := by linarith
    rw [cardR, abs_of_nonpos (by linarith only [prev, khi, sqrt32])]
    calc
      _ ≤ 2 * √L := by linarith only [Lhi, klo, sqrt32]
      _ ≤ √L * L ^ (1 / 4 : ℝ) := by
        rw [mul_comm (2 : ℝ)]
        exact mul_le_mul_of_nonneg_left quarter (Real.sqrt_nonneg L)
      _ = L ^ (3 / 4 : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by linarith : 0 < L)]
        norm_num
      _ ≤ _ := Real.rpow_le_rpow L0 prev (by norm_num)
  refine ⟨by exact_mod_cast hlo, by convert hhi using 1; norm_num, ?_, main, ?_⟩
  · intro q hq primepow
    have qdvd := Nat.dvd_of_mem_divisors hq
    have qprime := Nat.squarefree_and_prime_pow_iff_prime.mp
      ⟨hf.squarefree_of_dvd qdvd, primepow⟩
    exact hPrime q (Nat.mem_primeFactors.mpr ⟨qprime, qdvd, hf.ne_zero⟩)
  · have eq : n.primeFactorsList.length = n.primeFactors.card := by
      rw [← Nat.toFinset_factors]
      exact (List.toFinset_card_of_nodup hf.nodup_primeFactorsList).symm
    rwa [eq]

set_option maxHeartbeats 2500000 in
private theorem pool_at {N : ℕ} {c : ℝ} (hN : 2 ≤ N) (hc : 0 < c)
    (mass_big : c ≤ ∏ i : Fin 16, ∑ p ∈ largeBlocks N i, (p : ℝ)⁻¹)
    (hL : 1024 ≤ Real.log (Real.log N))
    (quarter : 2 ≤ (Real.log (Real.log N)) ^ (1 / 4 : ℝ))
    (mass_small : Real.log (Real.log N) - √(Real.log (Real.log N)) / 4 ≤
      bandMass (Real.log (Real.log N)) ((N : ℝ) ^ smallExponent (Real.log (Real.log N)))) :
    ∃ P : Finset ℕ, (∀ n ∈ P, Regular N n) ∧
      c * (1 + √(Real.log (Real.log N)) / 8) ≤ ∑ n ∈ P, (n : ℝ)⁻¹ := by
  let T := (N : ℝ)
  let L := Real.log (Real.log T)
  obtain ⟨k, hk⟩ : ∃ j : ℕ, j = smallCount L := ⟨_, rfl⟩
  let Y := T ^ smallExponent L
  let M := primeBand L Y
  have T1 : 1 ≤ T := by dsimp [T]; exact_mod_cast (show 1 ≤ N by omega)
  have T0 : 0 < T := by linarith
  have L0 : 0 < L := by linarith
  have tinyExp : smallExponent L ≤ 1 / 32 := by
    rw [one_div]
    change (32 * L)⁻¹ ≤ (32 : ℝ)⁻¹
    apply (inv_le_inv₀ (by positivity : 0 < 32 * L) (by norm_num)).2
    have hLL : 1024 ≤ L := hL
    linarith
  have tiny_upper : Y ≤ T ^ (1 / 16 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le T1 (tinyExp.trans (by norm_num))
  have weight_cap (p : ℕ) (hp : p ∈ M) : 0 ≤ (p : ℝ)⁻¹ ∧ (p : ℝ)⁻¹ ≤ L⁻¹ := by
    have h := (mem_primeBand.mp hp).2.1
    exact ⟨by positivity, (inv_le_inv₀ (L0.trans h) L0).2 h.le⟩
  have budget : (k : ℝ) * (smallWeight L + L⁻¹) ≤ bandMass L Y := by
    rw [hk]
    exact (small_budget hL).trans mass_small
  obtain ⟨small, disj, small_spec⟩ := split_into_blocks M (fun p => (p : ℝ)⁻¹)
    (by positivity : 0 ≤ L⁻¹) (by unfold smallWeight; positivity : 0 < smallWeight L)
    weight_cap k budget
  let blocks : Fin 16 ⊕ Fin k → Finset ℕ := Sum.elim (largeBlocks T) small
  have separated : Pairwise fun i j => Disjoint (blocks i) (blocks j) := by
    intro i j hij
    rcases i with i | i <;> rcases j with j | j
    · exact large_disjoint T1 (fun e => hij (congrArg Sum.inl e))
    · apply Finset.disjoint_left.mpr
      intro p hi hj
      have x := (large_bounds T1 hi).2.1
      have y := (mem_primeBand.mp ((small_spec j).1 hj)).2.2
      exact x.not_ge (y.trans tiny_upper)
    · apply Finset.disjoint_left.mpr
      intro p hi hj
      have x := (large_bounds T1 hj).2.1
      have y := (mem_primeBand.mp ((small_spec i).1 hi)).2.2
      exact x.not_ge (y.trans tiny_upper)
    · exact disj (fun e => hij (congrArg Sum.inr e))
  have pprime (i) (p) (hp : p ∈ blocks i) : Nat.Prime p := by
    rcases i with i | i
    · exact (large_bounds T1 hp).1
    · exact (mem_primeBand.mp ((small_spec i).1 hp)).1
  obtain ⟨P, hP, mass⟩ := pool_from_primes blocks separated pprime
  refine ⟨P, ?_, ?_⟩
  · intro n hn
    obtain ⟨sq, count, values, vm, nv⟩ := hP n hn
    have big := large_products T1 (fun i => vm (Sum.inl i))
    push_cast at big
    have tiny_ge : 1 ≤ ∏ i : Fin k, (values (Sum.inr i) : ℝ) := by
      calc
        1 = ∏ _ : Fin k, (1 : ℝ) := by simp
        _ ≤ ∏ i : Fin k, (values (Sum.inr i) : ℝ) :=
          prod_le_prod (fun _ _ => by norm_num)
            (fun i _ => by exact_mod_cast (pprime _ _ (vm (Sum.inr i))).one_le)
    have tiny_le : (∏ i : Fin k, (values (Sum.inr i) : ℝ)) ≤ T ^ (1/32 : ℝ) := by
      have kL : (k : ℝ) ≤ L := by
        rw [hk]
        have hb := (small_count_bounds hL).2.2.1
        linarith only [hb, Real.sqrt_nonneg L]
      have each (i : Fin k) : (values (Sum.inr i) : ℝ) ≤ Y := by
        have hi : values (Sum.inr i) ∈ small i := vm (Sum.inr i)
        exact (mem_primeBand.mp ((small_spec i).1 hi)).2.2
      calc
        _ ≤ ∏ _ : Fin k, Y := prod_le_prod (fun _ _ => Nat.cast_nonneg _)
          (fun i _ => each i)
        _ = T ^ (smallExponent L * k) := by
          simpa only [Fintype.card_fin] using
            (real_prod_const_rpow (ι := Fin k) T0.le (smallExponent L))
        _ ≤ T ^ (1/32 : ℝ) := by
          have expo : smallExponent L * (k : ℝ) ≤ (1/32 : ℝ) := by
            unfold smallExponent
            rw [inv_mul_eq_div]
            apply (div_le_iff₀ (by positivity : 0 < 32 * L)).2
            nlinarith only [kL]
          exact Real.rpow_le_rpow_of_exponent_le T1 expo
    have prod_n : (n : ℝ) =
        (∏ i : Fin 16, (values (Sum.inl i) : ℝ)) * ∏ i : Fin k, (values (Sum.inr i) : ℝ) := by
      rw [nv, Nat.cast_prod, Fintype.prod_sum_type]
    have lo : T ≤ (n : ℝ) := by
      rw [prod_n]
      exact big.1.trans (le_mul_of_one_le_right (T0.le.trans big.1) tiny_ge)
    have hi : (n : ℝ) ≤ T ^ (17 / 16 : ℝ) := by
      rw [prod_n]
      calc
        _ ≤ T ^ (33 / 32 : ℝ) * T ^ (1 / 32 : ℝ) :=
          mul_le_mul big.2 tiny_le (zero_le_one.trans tiny_ge) (Real.rpow_nonneg T0.le _)
        _ = _ := by rw [← Real.rpow_add T0]; norm_num
    refine regular_of_bounds hN lo hi ?_ sq ?_ hL quarter
    · intro q hq
      have hqp := Nat.prime_of_mem_primeFactors hq
      have dvd := Nat.dvd_of_mem_primeFactors hq
      rw [nv] at dvd
      obtain ⟨i, _, hd⟩ := (hqp.prime.dvd_finsetProd_iff values).1 dvd
      rw [(Nat.prime_dvd_prime_iff_eq hqp (pprime i _ (vm i))).1 hd]
      rcases i with i | i
      · exact ((large_bounds T1 (vm (Sum.inl i))).2.2).trans
          (Real.rpow_le_rpow_of_exponent_le T1 (by norm_num))
      · exact ((mem_primeBand.mp ((small_spec i).1 (vm (Sum.inr i)))).2.2).trans
          (tiny_upper.trans (Real.rpow_le_rpow_of_exponent_le T1 (by norm_num)))
    · simpa [Fintype.card_sum, hk] using count
  · rw [mass, Fintype.prod_sum_type]
    have sm : 0 ≤ 1 + √L / 8 := by linarith [Real.sqrt_nonneg L]
    apply mul_le_mul mass_big _ sm (hc.le.trans mass_big)
    unfold blocks
    calc
      _ ≤ smallWeight L ^ k := by rw [hk]; exact small_weight_pow hL
      _ = ∏ _ : Fin k, smallWeight L := by simp
      _ ≤ ∏ i : Fin k, ∑ p ∈ small i, (p : ℝ)⁻¹ :=
        prod_le_prod (fun _ _ => by unfold smallWeight; positivity) (fun i _ => (small_spec i).2)

end RegularReciprocalPool

namespace RegularReciprocalPool

open Filter Finset

theorem arbitrarily_large_pool (r B : ℕ) :
    ∃ N ≥ max 2 B, ∃ P : Finset ℕ,
      (∀ n ∈ P, Regular N n) ∧ 6 * (r : ℚ) < ∑ n ∈ P, (1 / n : ℚ) := by
  obtain ⟨c, cpos, big⟩ := eventual_large_mass
  have tendsto_L := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have quarter : ∀ᶠ T : ℝ in atTop, 2 ≤ (Real.log (Real.log T)) ^ (1 / 4 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : 0 < (1/4 : ℝ))).comp tendsto_L).eventually_ge_atTop 2
  have mass_need : ∀ᶠ T : ℝ in atTop, 8 * (6 * (r : ℝ) + 1) / c ≤ √(Real.log (Real.log T)) := by
    simpa only [Real.sqrt_eq_rpow, Function.comp_apply] using
      ((tendsto_rpow_atTop (by norm_num : 0 < (1/2 : ℝ))).comp tendsto_L).eventually_ge_atTop
        (8 * (6 * (r : ℝ) + 1) / c)
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have ev : ∀ᶠ N : ℕ in atTop,
      N ≥ max 2 B ∧ ∃ P : Finset ℕ,
        (∀ n ∈ P, Regular N n) ∧ 6 * (r : ℚ) < ∑ n ∈ P, (1 / n : ℚ) := by
    filter_upwards [eventually_ge_atTop (max 2 B), hnat.eventually big, hnat.eventually small_band_eventually,
      hnat.eventually quarter, hnat.eventually mass_need] with N hn hb hs hq hm
    obtain ⟨L, _, low⟩ := hs
    obtain ⟨P, reg, mass⟩ := pool_at ((le_max_left 2 B).trans hn) cpos hb L hq low
    refine ⟨hn, P, reg, ?_⟩
    have hm' := (div_le_iff₀ cpos).1 hm
    have strict : 6 * (r : ℝ) < c * (1 + √(Real.log (Real.log N)) / 8) := by
      nlinarith only [hm', cpos]
    apply (Rat.cast_lt (K := ℝ)).mp
    push_cast
    simpa only [one_div] using strict.trans_le mass
  obtain ⟨N, hN, P, reg, mass⟩ := ev.exists
  exact ⟨N, hN, P, reg, mass⟩

end RegularReciprocalPool

theorem OMA.solution : OMA.R_Erdos46_erdos_46_variants_infinitely_many_disjoint_R1.H1 := by
  unfold OMA.R_Erdos46_erdos_46_variants_infinitely_many_disjoint_R1.H1
  refine ⟨1/8, 1/16, by norm_num, by norm_num, by norm_num, ?_⟩
  exact RegularReciprocalPool.arbitrarily_large_pool