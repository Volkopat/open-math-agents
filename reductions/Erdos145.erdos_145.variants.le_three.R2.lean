import FormalConjectures.ErdosProblems.«145»
import Mathlib

/-!
Squarefree-gap moments for exponents from zero through three.

A gap of weight w = g³√g is charged to an interior multiple of p² when
w (1 + ⌊log₂ p⌋) ≤ p. The product bound on primes in each dyadic block and
disjointness of the gaps give an unconditional total charge of at most 8N.
The remaining analytic estimate concerns the complementary completed gaps.
Chan (arXiv:2310.08448, Sections 1 and 2) gives the moment asymptotic and
describes the large-prime and small-prime cases in the proof.

Bertrand's postulate controls the gap crossing the cutoff. The fixed-gap
frequencies have a proof in PR 4209. The Cauchy argument adapts PRs 3976 and 4712.
-/
-- Credit: @Pasx71

namespace OMA.R_Erdos145_erdos_145_variants_le_three_R2

open Filter Finset Erdos145 Classical
open scoped Topology BigOperators

/-- Each fixed gap size has a limiting frequency. -/
def H1 : Prop := ∀ k : ℕ, ∃ d : ℝ,
  Tendsto (fun x : ℝ => 1/x * (((A x).filter
    (fun n => s (n+1)-s n = k)).card : ℝ)) atTop (𝓝 d)

/-- Bound the order-7/2 moment on gaps that have no large prime-square witness. -/
def H2 : Prop :=
  let w (n : ℕ) : ℝ := ((s (n+1)-s n : ℕ) : ℝ)^3 * Real.sqrt ((s (n+1)-s n : ℕ) : ℝ)
  let large (n : ℕ) := ∃ p q : ℕ, p.Prime ∧ s n < p^2*q ∧ p^2*q < s (n+1) ∧
    w n * ((Nat.log 2 p : ℝ)+1) ≤ p
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ y : ℝ in atTop,
    ∑ n ∈ ((A y).filter (fun n => s (n+1) ≤ ⌊y⌋₊)).filter (fun n => ¬ large n), w n ≤ C*y

/-- The primorial bound controls the number of primes in one dyadic block. -/
lemma prime_block_card (k : ℕ) :
    ((Nat.primesLE (2^(k+1))).filter (fun p => 2^k ≤ p)).card * k ≤ 4 * 2^k := by
  let B := (Nat.primesLE (2^(k+1))).filter (fun p => 2^k ≤ p)
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  calc
    2^(B.card*k) = ∏ _p ∈ B, 2^k := by rw [prod_const, ← pow_mul, mul_comm]
    _ ≤ ∏ p ∈ B, p := prod_le_prod (fun _ _ => Nat.zero_le _) (fun _ hp => (mem_filter.mp hp).2)
    _ ≤ ∏ p ∈ Nat.primesLE (2^(k+1)), p :=
      prod_le_prod_of_subset_of_one_le' (filter_subset ..) (fun _ hp _ => (Nat.mem_primesLE.mp hp).2.one_le)
    _ = primorial (2^(k+1)) := rfl
    _ ≤ 4^(2^(k+1)) := primorial_le_four_pow _
    _ = 2^(4*2^k) := by
      rw [show (4:ℕ) = 2^2 by decide, ← pow_mul, pow_succ 2 k]
      congr 1
      ring

lemma sum_reciprocal_steps (K : ℕ) :
    ∑ k ∈ range K, ((1:ℝ)/(k+1) - 1/(k+2)) = 1 - 1/(K+1) := by
  induction K with
  | zero => norm_num
  | succ k ih => rw [sum_range_succ, ih]; push_cast; ring

/-- For one dyadic block of primes, count disjoint prime-square multiples up to N. -/
lemma block_mass (T : Finset ℕ) (w : ℕ → ℝ) (p q : ℕ → ℕ) (N j : ℕ)
    (hinj : Set.InjOn (fun n => (p n, q n)) T)
    (hprime : ∀ n ∈ T, (p n).Prime)
    (hq : ∀ n ∈ T, 0 < q n) (hN : ∀ n ∈ T, (p n)^2*q n ≤ N)
    (hlog : ∀ n ∈ T, Nat.log 2 (p n) = j+1)
    (hw : ∀ n ∈ T, w n * ((j:ℝ)+2) ≤ p n) :
    ∑ n ∈ T, w n ≤ 8*N*(1/((j:ℝ)+1)-1/((j:ℝ)+2)) := by
  let k := j+1
  let B := (Nat.primesLE (2^(k+1))).filter (fun t => 2^k ≤ t)
  let Q := N / (2^k)^2
  have hlow (n) (hn : n ∈ T) : 2^k ≤ p n := by
    simpa only [hlog n hn, k] using Nat.pow_log_le_self 2 (hprime n hn).ne_zero
  have hupp (n) (hn : n ∈ T) : p n < 2^(k+1) := by
    simpa only [hlog n hn, k] using Nat.lt_pow_succ_log_self (by decide : 1 < 2) (p n)
  have hmaps : Set.MapsTo (fun n => (p n, q n)) T (↑(B ×ˢ Ioc 0 Q : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    intro n hn
    refine mem_product.mpr ⟨mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨(hupp n hn).le, hprime n hn⟩, hlow n hn⟩, ?_⟩
    refine mem_Ioc.mpr ⟨hq n hn, (Nat.le_div_iff_mul_le (by positivity : 0 < (2^k)^2)).mpr ?_⟩
    calc
      q n * (2^k)^2 ≤ q n * (p n)^2 := by gcongr; exact hlow n hn
      _ ≤ N := by simpa only [mul_comm] using hN n hn
  have hcard : T.card ≤ B.card * Q := by
    simpa only [card_product, Nat.card_Ioc, Nat.sub_zero] using card_le_card_of_injOn _ hmaps hinj
  have hcnt : 2^k * k * T.card ≤ 4*N := by
    apply Nat.le_of_mul_le_mul_right (c := 2^k) _ (by positivity)
    calc
      (2^k*k*T.card)*2^k ≤ (2^k*k*(B.card*Q))*2^k := by gcongr
      _ = (B.card*k) * (Q*(2^k)^2) := by ring
      _ ≤ (4*2^k)*N := Nat.mul_le_mul (prime_block_card k) (Nat.div_mul_le_self ..)
      _ = (4*N)*2^k := by ring
  have hsum : (∑ n ∈ T, w n) * ((j:ℝ)+2) ≤ T.card*(2*(2:ℝ)^k) := by
    rw [sum_mul]
    calc
      _ ≤ ∑ _n ∈ T, 2*(2:ℝ)^k := by
        apply sum_le_sum
        intro n hn
        apply (hw n hn).trans
        exact_mod_cast (show p n ≤ 2*2^k by simpa only [pow_succ, mul_comm] using (hupp n hn).le)
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  have hc : (2:ℝ)^k * k * T.card ≤ 4*N := by exact_mod_cast hcnt
  have hmass : (∑ n ∈ T, w n) * (((j:ℝ)+1)*((j:ℝ)+2)) ≤ 8*N := by
    have hk : (k:ℝ) = j+1 := by simp [k]
    calc
      _ = ((∑ n ∈ T, w n) * ((j:ℝ)+2)) * k := by rw [hk]; ring
      _ ≤ (T.card*(2*(2:ℝ)^k))*k := mul_le_mul_of_nonneg_right hsum (by positivity)
      _ = 2 * ((2:ℝ)^k * k * T.card) := by ring
      _ ≤ _ := by linarith only [hc]
  have hid : 8*(N:ℝ)*(1/((j:ℝ)+1)-1/((j:ℝ)+2)) =
      8*N/(((j:ℝ)+1)*((j:ℝ)+2)) := by
    field_simp
    ring
  rw [hid]
  exact (le_div_iff₀ (by positivity)).mpr hmass

/-- A prime-square witness in each gap bounds the total weight by 8N. -/
lemma witness_mass (T : Finset ℕ) (w : ℕ → ℝ) (N : ℕ)
    (hend : ∀ n ∈ T, s (n+1) ≤ N)
    (witness : ∀ n ∈ T, ∃ p q : ℕ, p.Prime ∧ s n < p^2*q ∧ p^2*q < s (n+1) ∧
      w n * ((Nat.log 2 p : ℝ)+1) ≤ p) :
    ∑ n ∈ T, w n ≤ 8*N := by
  classical
  choose! p q hp hleft hright hprice using witness
  have hinj : Set.InjOn (fun n => (p n, q n)) T := by
    intro a ha b hb heq
    have he : (p a)^2*q a = (p b)^2*q b :=
      congrArg (fun t : ℕ × ℕ => t.1^2*t.2) heq
    have mono : Monotone s := (Nat.nth_strictMono Nat.squarefree_infinite).monotone
    rcases lt_trichotomy a b with h | h | h
    · have := mono (show a+1 ≤ b from h)
      have := hright a ha
      have := hleft b hb
      omega
    · exact h
    · have := mono (show b+1 ≤ a from h)
      have := hright b hb
      have := hleft a ha
      omega
  let scale (n : ℕ) := Nat.log 2 (p n) - 1
  let K := T.sup scale + 1
  have maps : ∀ n ∈ T, scale n ∈ range K := fun n hn =>
    mem_range.mpr (Nat.lt_succ_of_le (le_sup hn))
  rw [← sum_fiberwise_of_maps_to maps w]
  calc
    _ ≤ ∑ j ∈ range K, 8*(N:ℝ)*(1/((j:ℝ)+1)-1/((j:ℝ)+2)) := by
      apply sum_le_sum
      intro j _
      let F := T.filter fun n => scale n = j
      have sub : F ⊆ T := filter_subset ..
      have hj (n) (hn : n ∈ F) : Nat.log 2 (p n) = j+1 := by
        have h1 := (mem_filter.mp hn).2
        have h2 := Nat.log_pos (by decide : 1 < 2) (hp n (sub hn)).two_le
        dsimp [scale] at h1
        omega
      apply block_mass F w p q N j (hinj.mono sub) (fun n hn => hp n (sub hn)) _ _ hj
      · intro n hn
        specialize hprice n (sub hn)
        rw [hj n hn] at hprice
        push_cast at hprice
        linarith only [hprice]
      · intro n hn
        by_contra! hzero
        have := hleft n (sub hn)
        simp [Nat.le_zero.mp hzero] at this
      · exact fun n hn => (hright n (sub hn)).le.trans (hend n (sub hn))
    _ = 8*(N:ℝ)*(1-1/((K:ℝ)+1)) := by rw [← mul_sum, sum_reciprocal_steps]
    _ ≤ 8*N := by
      have h : 0 ≤ 1/((K:ℝ)+1) := by positivity
      nlinarith only [mul_nonneg (show 0 ≤ 8*(N:ℝ) by positivity) h]

/-- The large-prime part and the residual bound together control all completed gaps. -/
lemma completed_moment (residual : H2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ y : ℝ in atTop,
      (∑ n ∈ (A y).filter (fun n => s (n+1) ≤ ⌊y⌋₊),
        ((s (n+1)-s n : ℕ) : ℝ)^3 * Real.sqrt ((s (n+1)-s n : ℕ) : ℝ)) ≤ C*y := by
  classical
  let w (n : ℕ) : ℝ := ((s (n+1)-s n : ℕ) : ℝ)^3 * Real.sqrt ((s (n+1)-s n : ℕ) : ℝ)
  let large (n : ℕ) := ∃ p q : ℕ, p.Prime ∧ s n < p^2*q ∧ p^2*q < s (n+1) ∧
    w n * ((Nat.log 2 p : ℝ)+1) ≤ p
  obtain ⟨C, hC, hb⟩ := residual
  refine ⟨C+8, by linarith, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (0:ℝ)] with y hy hy0
  let D := (A y).filter (fun n => s (n+1) ≤ ⌊y⌋₊)
  have hlarge : ∑ n ∈ D.filter large, w n ≤ 8*(⌊y⌋₊:ℝ) :=
    witness_mass _ _ _ (fun _ hn => (mem_filter.mp (mem_filter.mp hn).1).2)
      (fun _ hn => (mem_filter.mp hn).2)
  have hrest : ∑ n ∈ D.filter (fun n => ¬ large n), w n ≤ C*y := hy
  change ∑ n ∈ D, w n ≤ (C+8)*y
  linarith only [sum_filter_add_sum_filter_not D large w, hrest, hlarge, Nat.floor_le hy0]

/-- Every squarefree gap counted at x is completed by 2x. -/
lemma next_le_double {x : ℝ} (hx : 1 ≤ x) {n : ℕ} (hn : n ∈ A x) :
    s (n+1) ≤ ⌊2*x⌋₊ := by
  have hfloor : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).2 hx
  obtain ⟨p, hp, hgt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul ⌊x⌋₊ (by omega)
  have hleft : s n ≤ ⌊x⌋₊ := (Finset.mem_Icc.mp (Finset.mem_preimage.mp hn)).2
  have hnext : s (n+1) ≤ p := by
    by_contra! h
    have hback : p ≤ s n := Nat.le_nth_of_lt_nth_succ h hp.squarefree
    omega
  apply (Nat.le_floor_iff (by linarith : 0 ≤ 2*x)).2
  have hnat := hnext.trans hle
  have hreal : (s (n+1) : ℝ) ≤ 2*(⌊x⌋₊ : ℝ) := by exact_mod_cast hnat
  linarith [Nat.floor_le (by linarith : 0 ≤ x)]

lemma cubic_tail (moment : H2) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, 0 < K ∧ ∀ᶠ x : ℝ in atTop, 1/x * ∑ n ∈ (A x).filter
      (fun n => ¬ s (n+1)-s n < K), ((s (n+1)-s n : ℕ) : ℝ)^3 ≤ ε := by
  classical
  obtain ⟨C,hC,bounded⟩ := completed_moment moment
  obtain ⟨L,hL⟩ := exists_nat_gt (2*C/ε)
  have hLpos : (0:ℝ) < L := lt_trans (by positivity) hL
  have hLn : 0 < L := by exact_mod_cast hLpos
  have hscale : 2*C ≤ ε*L := by linarith [(div_lt_iff₀ hε).mp hL]
  obtain ⟨Y,hY⟩ := eventually_atTop.mp bounded
  refine ⟨L^2, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max Y 1)] with x hx
  have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
  have hxpos : 0 < x := by linarith
  have hbound := hY (2*x) (by linarith [(le_max_left Y 1).trans hx])
  let g (n : ℕ) : ℝ := ((s (n+1)-s n : ℕ) : ℝ)
  let T := (A x).filter (fun n => ¬ s (n+1)-s n < L^2)
  let D := (A (2*x)).filter (fun n => s (n+1) ≤ ⌊2*x⌋₊)
  have hsub : T ⊆ D := by
    intro n hn
    have hleft := (mem_filter.mp hn).1
    apply mem_filter.mpr
    refine ⟨?_, next_le_double hx1 hleft⟩
    apply mem_preimage.mpr
    exact mem_Icc.mpr ⟨Nat.zero_le _, ((mem_Icc.mp (mem_preimage.mp hleft)).2).trans
      (Nat.floor_mono (by linarith : x ≤ 2*x))⟩
  have hscaled : (L:ℝ) * (∑ n ∈ T, g n ^ 3) ≤ C*(2*x) := by
    calc
      _ = ∑ n ∈ T, (L:ℝ) * g n ^ 3 := mul_sum ..
      _ ≤ ∑ n ∈ T, g n ^ 3 * Real.sqrt (g n) := by
        apply sum_le_sum
        intro n hn
        have hn' : L^2 ≤ s (n+1)-s n := not_lt.mp (mem_filter.mp hn).2
        have hr : (L:ℝ)^2 ≤ g n := by dsimp [g]; exact_mod_cast hn'
        have hs := Real.sqrt_le_sqrt hr
        rw [Real.sqrt_sq hLpos.le] at hs
        rw [mul_comm (L:ℝ)]
        exact mul_le_mul_of_nonneg_left hs (by dsimp [g]; positivity)
      _ ≤ ∑ n ∈ D, g n ^ 3 * Real.sqrt (g n) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by dsimp [g]; positivity)
      _ ≤ _ := hbound
  change 1/x * (∑ n ∈ T, g n ^ 3) ≤ ε
  rw [one_div, ← div_eq_inv_mul, div_le_iff₀ hxpos]
  apply le_of_mul_le_mul_left _ hLpos
  calc
    _ ≤ C*(2*x) := hscaled
    _ ≤ L*(ε*x) := by nlinarith only [mul_le_mul_of_nonneg_right hscale hxpos.le]


lemma sumByGapSize (D : Finset ℕ) (g : ℕ → ℕ) (a : ℝ) (K : ℕ) :
    (∑ k ∈ range K, ((D.filter fun n => g n=k).card : ℝ) * (k:ℝ)^a) =
    ∑ n ∈ D.filter (fun n => g n < K), (g n:ℝ)^a := by
  calc
    _ = ∑ k ∈ range K, ∑ n ∈ D.filter (fun n => g n=k), (g n:ℝ)^a := by
      apply sum_congr rfl
      intro k _
      rw [← nsmul_eq_mul,← sum_const]
      apply sum_congr rfl
      intro n hn
      rw [(mem_filter.mp hn).2]
    _ = _ := by simpa only [mem_range] using sum_fiberwise_eq_sum_filter D (range K) g (fun n => (g n:ℝ)^a)

theorem main : H1 → H2 → type_of% @Erdos145.erdos_145.variants.le_three := by
  classical
  intro freq moment
  have tail := cubic_tail moment
  intro a ha
  let g (n : ℕ) := s (n+1) - s n
  have hg (n : ℕ) : ((g n : ℕ) : ℝ) = (s (n+1) : ℝ) - s n :=
    Nat.cast_sub ((Nat.nth_strictMono Nat.squarefree_infinite).monotone (Nat.le_succ n))
  let f (x : ℝ) := (1/x) * ∑ n ∈ A x, (g n:ℝ)^a
  suffices h : ∃ β, Tendsto f atTop (𝓝 β) by simpa only [f,hg] using h
  choose d hd using freq
  let T (K : ℕ) (x : ℝ) := ∑ k ∈ range K, (1/x * ((A x).filter fun n => g n=k).card) * (k:ℝ)^a
  have tend (K : ℕ) : Tendsto (T K) atTop (𝓝 (∑ k ∈ range K, d k*(k:ℝ)^a)) :=
    tendsto_finsetSum _ (fun k _ => (hd k).mul_const _)
  have terr (K : ℕ) (ε : ℝ) (hK : 0 < K)
      (hT : ∀ᶠ x : ℝ in atTop, 1/x * ∑ n ∈ (A x).filter (fun n => ¬ s (n+1) - s n < K),
        ((s (n+1) - s n : ℕ) : ℝ)^3 ≤ ε) :
      ∀ᶠ x : ℝ in atTop, |f x - T K x| ≤ ε := by
    filter_upwards [hT, eventually_gt_atTop (0:ℝ)] with x hb hx
    have te : T K x = (1/x) * ∑ n ∈ (A x).filter (fun n => g n < K), (g n:ℝ)^a := by
      unfold T
      rw [← sumByGapSize (A x) g a K, mul_sum]
      exact sum_congr rfl (fun k _ => by ring)
    let D := (A x).filter (fun n => ¬ g n < K)
    have split := sum_filter_add_sum_filter_not (A x) (fun n => g n < K) (fun n => (g n:ℝ)^a)
    have diff : f x - T K x = (1/x) * ∑ n ∈ D, (g n:ℝ)^a := by
      rw [te]
      unfold f
      dsimp [D]
      rw [← split, mul_add]
      ring
    have hKr : (1:ℝ) ≤ K := by exact_mod_cast hK
    have hsum : ∑ n ∈ D, (g n:ℝ)^a ≤ ∑ n ∈ D, (g n:ℝ)^3 := by
      apply sum_le_sum
      intro n hn
      have h1 : (K:ℝ) ≤ g n := by exact_mod_cast (not_lt.mp (mem_filter.mp hn).2)
      have h1' : (1:ℝ) ≤ g n := hKr.trans h1
      calc (g n:ℝ)^a ≤ (g n:ℝ)^(3:ℝ) := Real.rpow_le_rpow_of_exponent_le h1' ha.2
        _ = (g n:ℝ)^3 := Real.rpow_natCast _ 3
    have hnn : 0 ≤ f x - T K x := by
      rw [diff]
      exact mul_nonneg (by positivity) (sum_nonneg (fun n _ => by positivity))
    rw [abs_of_nonneg hnn, diff]
    calc (1/x) * ∑ n ∈ D, (g n:ℝ)^a ≤ (1/x) * ∑ n ∈ D, (g n:ℝ)^3 :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ ε := hb
  apply cauchySeq_tendsto_of_complete
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨K, hK, hTail⟩ := tail (ε/4) (by linarith)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (tend K).cauchySeq (ε/2) (by linarith)
  obtain ⟨M, hM⟩ := eventually_atTop.mp (terr K (ε/4) hK hTail)
  refine ⟨max N M, ?_⟩
  intro x hx y hy
  have ht := hN x (le_trans (le_max_left _ _) hx) y (le_trans (le_max_left _ _) hy)
  have h₁ := hM x (le_trans (le_max_right _ _) hx)
  have h₂ := hM y (le_trans (le_max_right _ _) hy)
  rw [Real.dist_eq] at ht ⊢
  rw [abs_le] at h₁ h₂
  rw [abs_lt] at ht ⊢
  constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2, ht.1, ht.2]

end OMA.R_Erdos145_erdos_145_variants_le_three_R2
