import FormalConjectures.ErdosProblems.«968»
import Mathlib

-- Reduction Erdos968.erdos_968.variants.infinite_decreasingTriples.R2 of Erdős Problem 968 — infinite decreasingTriples
-- Credit: @Ciphore
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
Isolate the standard Maynard–Tao prime-cluster theorem as the analytic input.

The first hypothesis is the common-slope affine form of Maynard–Tao: for every prescribed
number `r` there is a width `k` such that every admissible affine family of at least `k`
forms has, arbitrarily far out, a specialization containing at least `r` primes.  The
affine offsets `(i+1)k!`, `i < k`, are admissible: primes at most `k` divide every
offset, while a prime larger than `k` cannot cover all residue classes with only `k`
forbidden residues.  Hence three primes occur in bounded intervals arbitrarily far out.

The second hypothesis is the zero density of the primes.  The conversion from bounded
three-prime intervals to decreasing triples of `u n` is included here.
-/

namespace OMA.R_Erdos968_erdos_968_variants_infinite_decreasingTriples_R2

open Filter Erdos968

/-- Maynard–Tao prime clusters for admissible affine forms with a common slope. -/
def H1 : Prop :=
  ∀ r : ℕ, ∃ k : ℕ, ∀ (H : Finset ℕ) (M b : ℕ), k ≤ H.card → 0 < M →
    (∀ p, p.Prime → ∃ x, ∀ a ∈ H, ¬ p ∣ M * x + b + a) →
    ∀ N : ℕ, ∃ x, N < x ∧ r ≤ (H.filter fun a => (M * x + b + a).Prime).card

/-- The zero density of the primes. -/
def H2 : Prop := ∀ δ : ℝ, 0 < δ →
  ∀ᶠ x : ℕ in atTop, (x.primeCounting : ℝ) < δ * x

/-- Admissibility of a family whose offsets are multiples of `k!`. -/
lemma factorial_offset_admissible {k M b : ℕ} {H : Finset ℕ}
    (hcard : H.card = k) (hfac : ∀ a ∈ H, k.factorial ∣ a)
    (hcop : ∀ p, p.Prime → p ∣ M → ∀ a ∈ H, ¬ p ∣ b + a) :
    ∀ p, p.Prime → ∃ x, ∀ a ∈ H, ¬ p ∣ M * x + b + a := by
  classical
  intro p hp
  by_cases hM : p ∣ M
  · refine ⟨0, ?_⟩
    simpa using hcop p hp hM
  let : Fact p.Prime := ⟨hp⟩
  have hM' : (M : ZMod p) ≠ 0 := fun h => hM ((ZMod.natCast_eq_zero_iff M p).mp h)
  obtain ⟨r, hr⟩ : ∃ r : ZMod p, ∀ a ∈ H, r + (a : ZMod p) ≠ 0 := by
    by_cases hpk : p ≤ k
    · refine ⟨1, ?_⟩
      intro a ha
      have hd := (Nat.dvd_factorial hp.pos hpk).trans (hfac a ha)
      rw [(ZMod.natCast_eq_zero_iff a p).mpr hd, add_zero]
      exact one_ne_zero
    · let T : Finset (ZMod p) := H.image (fun a : ℕ => -(a : ZMod p))
      have hT : T.card < Fintype.card (ZMod p) := by
        rw [ZMod.card p]
        exact Finset.card_image_le.trans_lt (hcard.symm ▸ Nat.lt_of_not_ge hpk)
      obtain ⟨r, hr⟩ : ∃ r : ZMod p, r ∉ T := by
        by_contra h
        push Not at h
        have heq : T = Finset.univ := Finset.eq_univ_of_forall h
        rw [heq, Finset.card_univ] at hT
        exact (lt_irrefl _ hT)
      refine ⟨r, fun a ha h => hr ?_⟩
      exact Finset.mem_image.mpr ⟨a, ha, (eq_neg_of_add_eq_zero_left h).symm⟩
  let t : ZMod p := (M : ZMod p)⁻¹ * (r - (b : ZMod p))
  refine ⟨t.val, ?_⟩
  intro a ha hd
  have hz := (ZMod.natCast_eq_zero_iff _ p).mpr hd
  push_cast at hz
  rw [ZMod.natCast_zmod_val] at hz
  have heq : (M : ZMod p) * t + (b : ZMod p) = r := by
    dsimp [t]
    rw [← mul_assoc, mul_inv_cancel₀ hM', one_mul, sub_add_cancel]
  rw [heq] at hz
  exact hr a ha hz

/-- The standard cluster theorem implies bounded intervals with three primes. -/
lemma bounded_three_prime_intervals (hmay : H1) :
    ∃ B : ℕ, ∀ X : ℕ, ∃ m ≥ X,
      3 ≤ ((Finset.Icc m (m + B)).filter Nat.Prime).card := by
  obtain ⟨k, hk⟩ := hmay 3
  let K := k.factorial
  let H : Finset ℕ := (Finset.range k).image fun i => (i + 1) * K
  have hK : 0 < K := Nat.factorial_pos k
  have hcard : H.card = k := by
    dsimp [H]
    rw [Finset.card_image_of_injective]
    · exact Finset.card_range k
    · intro i j hij
      have hmul := Nat.mul_right_cancel hK hij
      omega
  have hfac : ∀ a ∈ H, k.factorial ∣ a := by
    intro a ha
    dsimp [H] at ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact dvd_mul_left K (i + 1)
  have hcop : ∀ p, p.Prime → p ∣ 1 → ∀ a ∈ H, ¬ p ∣ 1 + a := by
    intro p hp hp1
    have hle := Nat.le_of_dvd (by omega : 0 < 1) hp1
    have hp2 := hp.two_le
    omega
  have admissible : ∀ p, p.Prime → ∃ x, ∀ a ∈ H, ¬ p ∣ 1 * x + 1 + a := by
    simpa using factorial_offset_admissible (M := 1) (b := 1) hcard hfac hcop
  refine ⟨k * K, ?_⟩
  intro X
  obtain ⟨x, hx, hthree⟩ := hk H 1 1 hcard.ge (by omega) admissible X
  let m := x + 1 + K
  refine ⟨m, by omega, ?_⟩
  have hinj : Set.InjOn (fun a => x + 1 + a) (H.filter fun a => (1 * x + 1 + a).Prime) := by
    intro a _ b _ hab
    exact Nat.add_left_cancel hab
  have hmap : ∀ a ∈ H.filter (fun a => (1 * x + 1 + a).Prime),
      x + 1 + a ∈ (Finset.Icc m (m + k * K)).filter Nat.Prime := by
    intro a ha
    obtain ⟨haH, hpa⟩ := Finset.mem_filter.mp ha
    dsimp [H] at haH
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp haH
    have hik : i + 1 ≤ k := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
    have hlower : m ≤ x + 1 + (i + 1) * K := by
      dsimp [m]
      exact Nat.add_le_add_left (Nat.le_mul_of_pos_left K (Nat.succ_pos i)) _
    have hupper : x + 1 + (i + 1) * K ≤ m + k * K := by
      dsimp [m]
      have hle : (i + 1) * K ≤ k * K := Nat.mul_le_mul_right K hik
      omega
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hlower, hupper⟩, ?_⟩
    simpa using hpa
  have hle := Finset.card_le_card_of_injOn (fun a => x + 1 + a) hmap hinj
  exact hthree.trans hle

-- Converting the ordered elements of the interval to their global
-- prime indices allows the intermediate primes to be taken consecutive.
lemma get_cluster (B X : ℕ) (h : ∀ T : ℕ, ∃ m ≥ T,
    3 ≤ ((Finset.Icc m (m + B)).filter Nat.Prime).card) :
    ∃ i > X, Nat.nth Nat.Prime (i+2) ≤ Nat.nth Nat.Prime i + B := by
  have mono := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  obtain ⟨m, hX, hm⟩ := h (Nat.nth Nat.Prime X + 1)
  let s := (Finset.Icc m (m+B)).filter Nat.Prime
  change 3 ≤ s.card at hm
  let f := s.orderEmbOfFin (k := s.card) rfl
  let a : Fin s.card := ⟨0, by omega⟩
  let b : Fin s.card := ⟨1, by omega⟩
  let c : Fin s.card := ⟨2, by omega⟩
  have item (j : Fin s.card) : (m ≤ f j ∧ f j ≤ m+B) ∧ Nat.Prime (f j) := by
    have mem : f j ∈ s := s.orderEmbOfFin_mem rfl j
    exact ⟨Finset.mem_Icc.mp (Finset.mem_filter.mp mem).1, (Finset.mem_filter.mp mem).2⟩
  obtain ⟨i, _, hi⟩ := Nat.exists_lt_card_nth_eq (item a).2
  obtain ⟨j, _, hj⟩ := Nat.exists_lt_card_nth_eq (item b).2
  obtain ⟨k, _, hk⟩ := Nat.exists_lt_card_nth_eq (item c).2
  have ij : i < j := mono.lt_iff_lt.mp (hi.trans_lt ((f.strictMono (show a < b by change (0:ℕ) < 1; decide)).trans_eq hj.symm))
  have jk : j < k := mono.lt_iff_lt.mp (hj.trans_lt ((f.strictMono (show b < c by change (1:ℕ) < 2; decide)).trans_eq hk.symm))
  have xi : X < i := mono.lt_iff_lt.mp (by rw [hi]; exact lt_of_lt_of_le (by omega : Nat.nth Nat.Prime X < m) (item a).1.1)
  refine ⟨i, xi, ?_⟩
  calc
    Nat.nth Nat.Prime (i+2) ≤ Nat.nth Nat.Prime k := mono.monotone (by omega)
    _ = f c := hk
    _ ≤ m + B := (item c).1.2
    _ ≤ Nat.nth Nat.Prime i + B := by rw [hi]; exact Nat.add_le_add_right (item a).1.1 B

lemma eventual_large (h : H2) (B : ℕ) :
    ∀ᶠ n : ℕ in atTop, (B:ℝ)*((n:ℝ)+1) < Nat.nth Nat.Prime n := by
  have pos : 0 < (B:ℝ)+1 := by positivity
  have t := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).tendsto_atTop
  filter_upwards [t.eventually (h (1/((B:ℝ)+1)) (by positivity))] with n hn
  have pc : (Nat.nth Nat.Prime n).primeCounting = n+1 := by
    change Nat.count Nat.Prime (Nat.nth Nat.Prime n + 1) = n+1
    rw [Nat.count_succ, if_pos (Nat.prime_nth_prime n)]
    exact congrArg (· + 1) (Nat.primeCounting'_nth_eq n)
  rw [pc] at hn
  push_cast at hn
  rw [one_div_mul_eq_div] at hn
  have hh := (lt_div_iff₀ pos).mp hn
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

lemma ratio_step (i B : ℕ) (bound : Nat.nth Nat.Prime (i+1) ≤ Nat.nth Nat.Prime i+B)
    (large : (B:ℝ)*((i:ℝ)+1) < Nat.nth Nat.Prime i) : u (i+1) < u i := by
  unfold u
  push_cast
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
  have gap : (Nat.nth Nat.Prime (i+1):ℝ) ≤ Nat.nth Nat.Prime i + (B:ℝ) := by exact_mod_cast bound
  have scaled := mul_le_mul_of_nonneg_right gap (show 0 ≤ (i:ℝ)+1 by positivity)
  linarith only [scaled,large]

theorem main : H1 → H2 → type_of% @Erdos968.erdos_968.variants.infinite_decreasingTriples := by
  intro hmay density
  obtain ⟨B, clusters⟩ := bounded_three_prime_intervals hmay
  obtain ⟨T, hT⟩ := eventually_atTop.1 (eventual_large density B)
  apply Set.infinite_of_forall_exists_gt
  intro x
  obtain ⟨i, big, small⟩ := get_cluster B (max T x) clusters
  have ti : T ≤ i := (le_max_left T x).trans big.le
  have mono := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone
  have h01 := mono (show i ≤ i+1 by omega)
  have h12 := mono (show i+1 ≤ i+2 by omega)
  refine ⟨i, ⟨ratio_step i B (h12.trans small) (hT i ti), ?_⟩, (le_max_right T x).trans_lt big⟩
  exact ratio_step (i+1) B (small.trans (Nat.add_le_add_right h01 B)) (hT (i+1) (by omega))

end OMA.R_Erdos968_erdos_968_variants_infinite_decreasingTriples_R2
