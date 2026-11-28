import OMAReductions.R_Erdos5_erdos_5_variants_merikoski_bounded_gaps_R1
import Mathlib

-- Credit: @strantalis

/-!
# From two occupied sieve blocks to a normalized consecutive prime gap

Use the nine equal blocks in Banks, Freiberg and Maynard, Theorem 4.3(i),
with m = 1, and the offset covering of Lemma 5.2 (arXiv:1404.5094).
The sieve chooses the possible exceptional prime before the offsets are
constructed. The common shift ε disappears on taking differences.
-/

open Filter Real
open scoped Topology
namespace OMA.R_Erdos5_erdos_5_variants_merikoski_bounded_gaps_R1_H1_R2

/-- The two occupied blocks conclusion of the partitioned sieve.
The block size K and small positive ε are fixed. Z = 1 represents no
exception. The allowed offset differences are smooth up to ε log N. -/
def H1 : Prop := ∃ K : ℕ, 0 < K ∧ ∃ ε c : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < c ∧
  ∀ᶠ N : ℕ in atTop, ∃ Z : ℕ, (Z = 1 ∨ (Z.Prime ∧ c * log (log N) ≤ Z)) ∧
    let small := fun p : ℕ => p.Prime ∧ p ≠ Z ∧ (p : ℝ) ≤ ε * log N
    ∀ (h : Fin 9 × Fin K → ℕ), Function.Injective h → (∀ a, h a ≤ N) →
      (∀ p : ℕ, p.Prime → ∃ v : ℕ, ∀ a, ¬ Nat.ModEq p (h a) v) →
      (∀ a b, h a < h b → ∀ p : ℕ, p.Prime → p ∣ h b - h a → (p : ℝ) ≤ ε * log N) →
      ∀ r : ℕ → ℕ, (∀ a p, small p → ¬ p ∣ r p + h a) →
        ∃ n : ℕ, N < n ∧ n ≤ 2 * N ∧ (∀ p, small p → Nat.ModEq p n (r p)) ∧
          ∃ a b, a.1 < b.1 ∧ (n + h a).Prime ∧ (n + h b).Prime

/-- The Erdős–Rankin covering at y = ε log N. The protected offsets
approximate prescribed block locations to arbitrary fixed precision. -/
def H2 : Prop := ∀ (K : ℕ), 0 < K → ∀ ε c : ℝ, 0 < ε → ε ≤ 1 → 0 < c →
  ∀ β : Fin 9 → ℝ, (∀ i, 0 ≤ β i) → StrictMono β → ∀ η : ℝ, 0 < η →
    ∀ᶠ N : ℕ in atTop, ∀ Z : ℕ, (Z = 1 ∨ (Z.Prime ∧ c * log (log N) ≤ Z)) →
      let small := fun p : ℕ => p.Prime ∧ p ≠ Z ∧ (p : ℝ) ≤ ε * log N
      ∃ (z : ℕ) (h : Fin 9 × Fin K → ℕ) (r : ℕ → ℕ), z ≤ N ∧
        Function.Injective h ∧ (∀ a, 0 < h a ∧ h a ≤ z) ∧
        (∀ a b, a.1 < b.1 → h a < h b) ∧
        (∀ p : ℕ, p.Prime → ∃ v : ℕ, ∀ a, ¬ Nat.ModEq p (h a) v) ∧
        (∀ a b, h a < h b → ∀ p : ℕ, p.Prime → p ∣ h b - h a → (p : ℝ) ≤ ε * log N) ∧
        (∀ a p, small p → ¬ p ∣ r p + h a) ∧
        (∀ u : ℕ, 0 < u → u ≤ z → (∀ a, h a ≠ u) → ∃ p, small p ∧ p ∣ r p + u) ∧
        ∀ a, |(h a : ℝ) / log N - (β a.1 + ε)| ≤ η

/-- Minimizing the gap across two different occupied blocks rules out any
intermediate prime, even if a third block or an endpoint block also fires. -/
lemma adjacent_blocks {K : ℕ} (h : Fin 9 × Fin K → ℕ) (n z : ℕ)
    (bounds : ∀ a, 0 < h a ∧ h a ≤ z) (order : ∀ a b, a.1 < b.1 → h a < h b)
    (exhaust : ∀ u : ℕ, 0 < u → u ≤ z → (n + u).Prime → ∃ a, h a = u)
    (occupied : ∃ a b, a.1 < b.1 ∧ (n + h a).Prime ∧ (n + h b).Prime) :
    ∃ (a b : Fin 9 × Fin K) (t : ℕ), a.1 < b.1 ∧
      Nat.nth Nat.Prime t = n + h a ∧ Nat.nth Nat.Prime (t + 1) = n + h b := by
  classical
  let P (l : ℕ) := ∃ (a b : Fin 9 × Fin K), a.1 < b.1 ∧ (n + h a).Prime ∧
    (n + h b).Prime ∧ h b - h a = l
  have ex : ∃ l, P l := by
    obtain ⟨a, b, lt, pa, pb⟩ := occupied
    exact ⟨_, a, b, lt, pa, pb, rfl⟩
  obtain ⟨a, b, lt, pa, pb, gap⟩ := Nat.find_spec ex
  have ab := order a b lt
  have bt := (bounds b).2
  let t := Nat.count Nat.Prime (n + h a)
  let q := Nat.nth Nat.Prime (t + 1)
  have first : Nat.nth Nat.Prime t = n + h a := Nat.nth_count pa
  have lower : n + h a < q := first ▸ Nat.nth_strictMono Nat.infinite_setOfPred_prime t.lt_succ_self
  have upper : q ≤ n + h b := by
    by_contra! off
    have le := Nat.le_nth_of_lt_nth_succ off pb
    omega
  refine ⟨a, b, t, lt, first, le_antisymm upper ?_⟩
  by_contra! mid
  have eq : n + (q - n) = q := by omega
  obtain ⟨u, hu⟩ := exhaust (q - n) (by omega) (by omega)
    (by rw [eq]; exact Nat.prime_nth_prime (t + 1))
  have pu : (n + h u).Prime := by rw [hu, eq]; exact Nat.prime_nth_prime _
  by_cases ub : u.1 < b.1
  · have shorter : h b - h u < Nat.find ex := by omega
    exact (Nat.find_min ex shorter) ⟨u, b, ub, pu, pb, rfl⟩
  · have au : a.1 < u.1 := lt_of_lt_of_le lt (le_of_not_gt ub)
    have shorter : h u - h a < Nat.find ex := by omega
    exact (Nat.find_min ex shorter) ⟨a, u, au, pa, pu, rfl⟩

/-- At each sufficiently large scale there is a consecutive prime pair in
different blocks. Its normalized gap approximates the difference between
the two block locations with at most twice the offset error. -/
lemma finite_scale (sieve : H1) (cover : H2) (β : Fin 9 → ℝ)
    (pos : ∀ i, 0 ≤ β i) (mono : StrictMono β) (η : ℝ) (tol : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∃ (i j : Fin 9) (t : ℕ), i < j ∧
      N ≤ Nat.nth Nat.Prime t ∧ Nat.nth Nat.Prime t ≤ 3 * N ∧
      |(primeGap t : ℝ) / log N - (β j - β i)| ≤ 2 * η := by
  classical
  obtain ⟨K, hK, ε, c, hε, εle, hc, primeSieve⟩ := sieve
  filter_upwards [primeSieve, cover K hK ε c hε εle hc β pos mono η tol,
    eventually_ge_atTop 2] with N hs hcovers large
  obtain ⟨Z, exceptional, hit⟩ := hs
  obtain ⟨z, h, r, zN, inj, bounds, order, adm, smooth, safe, covers, approx⟩ :=
    hcovers Z exceptional
  obtain ⟨n, lt, le, congr, occupied⟩ :=
    hit h inj (fun a => (bounds a).2.trans zN) adm smooth r safe
  have exhaust (u : ℕ) (hu : 0 < u) (uz : u ≤ z) (pu : (n + u).Prime) : ∃ a, h a = u := by
    by_contra! missing
    obtain ⟨p, hp, dv⟩ := covers u hu uz missing
    have dv' := ((congr p hp).add_right u).dvd_iff (dvd_refl p) |>.mpr dv
    have same := (Nat.prime_dvd_prime_iff_eq hp.1 pu).mp dv'
    have poslog : 0 ≤ log (N : ℝ) := log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
    have small : (p : ℝ) ≤ N :=
      calc (p : ℝ) ≤ ε * log N := hp.2.2
           _ ≤ log N := mul_le_of_le_one_left poslog εle
           _ ≤ N := Real.log_le_self (by positivity)
    have bound : p ≤ N := by exact_mod_cast small
    omega
  obtain ⟨a, b, t, ab, first, second⟩ := adjacent_blocks h n z bounds order exhaust occupied
  have hle := order a b ab
  refine ⟨a.1, b.1, t, ab, by omega, by have := (bounds a).2; omega, ?_⟩
  have value : primeGap t = h b - h a := by unfold primeGap; rw [first, second]; omega
  rw [value, Nat.cast_sub hle.le, sub_div]
  have ea := abs_le.mp (approx a)
  have eb := abs_le.mp (approx b)
  apply abs_le.mpr
  constructor <;> linarith

/-- On a linear size interval, replacing log N by the logarithm of the
lower prime has asymptotically no effect. -/
lemma log_ratio (N p : ℕ → ℕ) (big : Tendsto N atTop atTop) (two : ∀ k, 2 ≤ N k)
    (lo : ∀ k, N k ≤ p k) (hi : ∀ k, p k ≤ 3 * N k) :
    Tendsto (fun k => log (p k : ℝ) / log (N k : ℝ)) atTop (𝓝 1) := by
  have diverge : Tendsto (fun k => log (N k : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp big)
  have err : Tendsto (fun k => log (3 : ℝ) / log (N k : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop diverge
  have ub := (tendsto_const_nhds (x := (1 : ℝ))).add err
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (by simpa using ub)
  · intro k
    have nk : (1 : ℝ) < N k := by exact_mod_cast (two k)
    exact (le_div_iff₀ (log_pos nk)).mpr (by simpa using log_le_log (by linarith) (by exact_mod_cast lo k))
  · intro k
    have nk : (1 : ℝ) < N k := by exact_mod_cast (two k)
    have pk : (0 : ℝ) < p k := lt_of_lt_of_le (by linarith : (0 : ℝ) < N k) (by exact_mod_cast lo k)
    have q : (p k : ℝ) ≤ 3 * (N k : ℝ) := by exact_mod_cast hi k
    have v := log_le_log pk q
    rw [log_mul (by norm_num) (by linarith)] at v
    have logs := log_pos nk
    apply (div_le_iff₀ logs).mpr
    rw [add_mul, one_mul, div_mul_cancel₀ _ logs.ne']
    linarith

theorem main : H1 → H2 → OMA.R_Erdos5_erdos_5_variants_merikoski_bounded_gaps_R1.H1 := by
  classical
  intro sieve cover
  refine ⟨8, ?_⟩
  intro β pos mono
  let δ (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)
  have samples (k : ℕ) : ∃ (N : ℕ) (i j : Fin 9) (t : ℕ), 2 ≤ N ∧ k ≤ N ∧ k ≤ t ∧ i < j ∧
      N ≤ Nat.nth Nat.Prime t ∧ Nat.nth Nat.Prime t ≤ 3 * N ∧
      |(primeGap t : ℝ) / log N - (β j - β i)| ≤ 2 * δ k := by
    have evt := finite_scale sieve cover β pos mono (δ k) (by dsimp [δ]; positivity)
    obtain ⟨N, h⟩ := (evt.and (eventually_ge_atTop (max 2 (max k (Nat.nth Nat.Prime k))))).exists
    obtain ⟨i, j, t, ij, lo, hi, error⟩ := h.1
    have bigger := h.2
    have bound : Nat.nth Nat.Prime k ≤ Nat.nth Nat.Prime t := by omega
    exact ⟨N, i, j, t, by omega, by omega, (Nat.nth_le_nth Nat.infinite_setOfPred_prime).mp bound,
      ij, lo, hi, error⟩
  choose N i j t two Nk tk ij lower upper error using samples
  let pair (k : ℕ) := (i k, j k)
  obtain ⟨v, inf⟩ := Finite.exists_infinite_fiber pair
  have infiniteFiber : {k | pair k = v}.Infinite := Set.infinite_coe_iff.mp inf
  let φ := Nat.nth (fun k => pair k = v)
  have monoφ : StrictMono φ := Nat.nth_strictMono infiniteFiber
  have fixed (k : ℕ) : pair (φ k) = v := Nat.nth_mem_of_infinite infiniteFiber k
  have fixed_i (k : ℕ) : i (φ k) = v.1 := congrArg Prod.fst (fixed k)
  have fixed_j (k : ℕ) : j (φ k) = v.2 := congrArg Prod.snd (fixed k)
  have incr : v.1 < v.2 := by simpa only [fixed_i, fixed_j] using ij (φ 0)
  have vanishes : Tendsto (fun k => 2 * δ (φ k)) atTop (𝓝 0) := by
    simpa only [δ, Function.comp_apply, mul_zero] using (tendsto_const_nhds (x := (2 : ℝ))).mul
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp monoφ.tendsto_atTop)
  have gap : Tendsto (fun k => (primeGap (t (φ k)) : ℝ) / log (N (φ k))) atTop (𝓝 (β v.2 - β v.1)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg) _ vanishes
    intro k
    simpa only [Real.dist_eq, fixed_i, fixed_j] using error (φ k)
  have big := tendsto_atTop_mono Nk tendsto_id
  have scale := (log_ratio N (fun k => Nat.nth Nat.Prime (t k)) big two lower upper).comp monoφ.tendsto_atTop
  have limit := gap.div scale (by norm_num : (1 : ℝ) ≠ 0)
  have normalized : Tendsto (fun k => (primeGap (t (φ k)) : ℝ) /
      log (Nat.nth Nat.Prime (t (φ k)))) atTop (𝓝 (β v.2 - β v.1)) := by
    rw [div_one] at limit
    apply limit.congr
    intro k
    have hn : (1 : ℝ) < N (φ k) := by exact_mod_cast two (φ k)
    change (_ / log (N (φ k))) / (_ / log (N (φ k))) = _
    field_simp [ne_of_gt (log_pos hn)]
  obtain ⟨ψ, monoψ, monoIndex⟩ := strictMono_subseq_of_id_le (u := fun k => t (φ k))
    (fun k => (monoφ.id_le k).trans (tk (φ k)))
  exact ⟨v.1, v.2, incr, _, monoIndex, normalized.comp monoψ.tendsto_atTop⟩

end OMA.R_Erdos5_erdos_5_variants_merikoski_bounded_gaps_R1_H1_R2
