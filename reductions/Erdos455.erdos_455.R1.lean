import FormalConjectures.ErdosProblems.«455»
import Mathlib

-- Reduction Erdos455.erdos_455.R1 of Erdős Problem 455
-- Credit: @rickmanelius
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Erdős 455: convex sequences of primes, split by the differences modulo 3

Let `q` be a strictly increasing sequence of primes whose differences `d(n) = q(n + 1) - q(n)`
are nondecreasing. The target asks whether `q(n) / n^2 → ∞` (Richter proved
`liminf q(n) / n^2 > 0.352`).

Proved below, with no hypothesis:

* `diff_mono`: `d` is nondecreasing.
* `three_dvd_of_repeat`: if `d(n + 1) = d(n)` with `n ≥ 2`, then `3 ∣ d(n)`; otherwise `q(n)`,
  `q(n) + d(n)`, `q(n) + 2 d(n)` are three primes above `3` covering every residue modulo `3`.
* `diff_unbounded`: `d` is unbounded, since a difference `c` constant from `N` on would make
  `q(N + q(N)) = q(N) (1 + c)` prime.
* `count_bound`: under the two hypotheses with a given `ε`, `n - 1 ≤ 2 ε d(n)` for all large
  `n`. The indices `m` in `[2, n]` with `3 ∣ d(m)` are counted by `H2`. The others carry distinct
  values (a repeated value not divisible by `3` would give two equal consecutive differences,
  because `d` is monotone), so they inject into the values counted by `H1`.
* `growth`: `q(n) ≥ (n - k) d(k)` for `k ≤ n`; with `k = n / 2` this turns
  `d(n) ≥ (n - 1) / (2 ε)` into `q(n) ≥ n^2 / (16 ε)`.

Both hypotheses are implied by the target, which forces `#{n : d(n) ≤ D} = o(D)`. The point of
the split is that differences not divisible by `3` never repeat, so for them it suffices to
count distinct values.

* `H1`: the values of the differences that are not divisible by `3` have density zero.
* `H2`: the indices `n` with `3 ∣ d(n)` and `d(n) ≤ D` number `o(D)`.
-/

namespace OMA.R_Erdos455_erdos_455_R1

open Filter


/-- The differences of a convex sequence are nondecreasing. -/
lemma diff_mono {q : ℕ → ℕ} (hconv : ∀ n, q (n + 2) - q (n + 1) ≥ q (n + 1) - q n) :
    Monotone (fun n => q (n + 1) - q n) :=
  monotone_nat_of_le_succ fun n => hconv n

/-- Two consecutive equal differences `d` of a strictly increasing sequence of primes force
`3 ∣ d`, once the terms exceed `3`. -/
lemma three_dvd_of_repeat {q : ℕ → ℕ} (hq : StrictMono q) (hprime : ∀ n, (q n).Prime)
    {n : ℕ} (hn : 2 ≤ n) (h : q (n + 2) - q (n + 1) = q (n + 1) - q n) :
    3 ∣ q (n + 1) - q n := by
  have h01 : q n < q (n + 1) := hq (by omega)
  have h12 : q (n + 1) < q (n + 2) := hq (by omega)
  have hq4 : 4 ≤ q n := by
    have h0 := (hprime 0).two_le
    have a1 : q 0 < q 1 := hq (by omega)
    have a2 : q 1 < q 2 := hq (by omega)
    have a3 : q 2 ≤ q n := hq.monotone hn
    omega
  by_contra h3
  have e1 : q (n + 1) = q n + (q (n + 1) - q n) := by omega
  have e2 : q (n + 2) = q n + 2 * (q (n + 1) - q n) := by omega
  have key : 3 ∣ q n ∨ 3 ∣ q (n + 1) ∨ 3 ∣ q (n + 2) := by
    have hs : (q (n + 1) - q n) % 3 = 1 ∨ (q (n + 1) - q n) % 3 = 2 := by omega
    have hr : q n % 3 = 0 ∨ q n % 3 = 1 ∨ q n % 3 = 2 := by omega
    rcases hr with hr | hr | hr
    · left
      omega
    · rcases hs with hs | hs
      · right; right
        omega
      · right; left
        omega
    · rcases hs with hs | hs
      · right; left
        omega
      · right; right
        omega
  rcases key with k | k | k
  · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three (hprime n)).1 k
    omega
  · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three (hprime (n + 1))).1 k
    omega
  · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three (hprime (n + 2))).1 k
    omega

/-- The differences are unbounded: a constant difference `c` from `N` on would make
`q (N + q N) = q N (1 + c)` prime. -/
lemma diff_unbounded {q : ℕ → ℕ} (hq : StrictMono q) (hprime : ∀ n, (q n).Prime)
    (hconv : ∀ n, q (n + 2) - q (n + 1) ≥ q (n + 1) - q n) :
    ∀ B, ∃ n, B < q (n + 1) - q n := by
  have hmono := diff_mono hconv
  by_contra hcon
  push Not at hcon
  obtain ⟨B, hB⟩ := hcon
  have hconst : ∃ N, ∀ n ≥ N, q (n + 1) - q n = q (N + 1) - q N := by
    by_contra h
    push Not at h
    have key : ∀ k, ∃ N, k ≤ q (N + 1) - q N := by
      intro k
      induction k with
      | zero => exact ⟨0, Nat.zero_le _⟩
      | succ k ih =>
        obtain ⟨N, hN⟩ := ih
        obtain ⟨n, hn, hne⟩ := h N
        have := hmono hn
        simp only at this
        exact ⟨n, by omega⟩
    obtain ⟨N, hN⟩ := key (B + 1)
    have := hB N
    omega
  obtain ⟨N, hN⟩ := hconst
  set c := q (N + 1) - q N with hc
  have hc1 : 1 ≤ c := by
    have := hq (show N < N + 1 by omega)
    omega
  have hlin : ∀ j, q (N + j) = q N + j * c := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h1 := hN (N + j) (by omega)
      have h2 := hq (show N + j < N + j + 1 by omega)
      have e : N + (j + 1) = N + j + 1 := by ring
      rw [e]
      have : q (N + j + 1) = q (N + j) + c := by omega
      rw [this, ih]
      ring
  have hp := hprime (N + q N)
  rw [hlin (q N), show q N + q N * c = q N * (1 + c) by ring] at hp
  have h2 := (hprime N).two_le
  exact Nat.not_prime_mul (by omega) (by omega) hp

/-- For every strictly increasing sequence of primes with nondecreasing differences, the values of the
differences that are not divisible by `3` have density zero. -/
def H1 : Prop :=
  ∀ q : ℕ → ℕ, StrictMono q → (∀ n, (q n).Prime ∧ q (n + 2) - q (n + 1) ≥ q (n + 1) - q n) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ D : ℕ in atTop,
      ({v : ℕ | v ≤ D ∧ ¬ 3 ∣ v ∧ ∃ n, q (n + 1) - q n = v}.ncard : ℝ) ≤ ε * D

/-- For every strictly increasing sequence of primes with nondecreasing differences, the indices `n`
with `3 ∣ d(n)` and `d(n) ≤ D` number `o(D)`. -/
def H2 : Prop :=
  ∀ q : ℕ → ℕ, StrictMono q → (∀ n, (q n).Prime ∧ q (n + 2) - q (n + 1) ≥ q (n + 1) - q n) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ D : ℕ in atTop, ∀ M : ℕ,
      (((Finset.range M).filter (fun n => q (n + 1) - q n ≤ D ∧ 3 ∣ q (n + 1) - q n)).card : ℝ)
        ≤ ε * D

/-- The counting step: if the differences not divisible by `3` take few values and the
differences divisible by `3` are few, then `n - 1 ≤ 2 ε d(n)` for all large `n`. -/
lemma count_bound {q : ℕ → ℕ} (hq : StrictMono q) (hprime : ∀ n, (q n).Prime)
    (hconv : ∀ n, q (n + 2) - q (n + 1) ≥ q (n + 1) - q n) {ε : ℝ}
    (hA : ∀ᶠ D : ℕ in atTop,
      ({v : ℕ | v ≤ D ∧ ¬ 3 ∣ v ∧ ∃ n, q (n + 1) - q n = v}.ncard : ℝ) ≤ ε * D)
    (hB : ∀ᶠ D : ℕ in atTop, ∀ M : ℕ,
      (((Finset.range M).filter (fun n => q (n + 1) - q n ≤ D ∧ 3 ∣ q (n + 1) - q n)).card : ℝ)
        ≤ ε * D) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) - 1 ≤ 2 * ε * ((q (n + 1) - q n : ℕ) : ℝ) := by
  have hmono := diff_mono hconv
  obtain ⟨D₀, hD₀⟩ := (hA.and hB).exists_forall_of_atTop
  have htend : Tendsto (fun n => q (n + 1) - q n) atTop atTop :=
    tendsto_atTop_atTop_of_monotone hmono fun b => by
      obtain ⟨n, hn⟩ := diff_unbounded hq hprime hconv b
      exact ⟨n, hn.le⟩
  filter_upwards [htend.eventually_ge_atTop D₀, eventually_ge_atTop 2] with n hn hn2
  obtain ⟨hA', hB'⟩ := hD₀ _ hn
  set D := q (n + 1) - q n with hD
  have hle : ∀ m ≤ n, q (m + 1) - q m ≤ D := fun m hm => hmono hm
  -- the multiples of three
  have h3 : ((Finset.Icc 2 n).filter (fun m => 3 ∣ q (m + 1) - q m)).card ≤
      ((Finset.range (n + 1)).filter
        (fun m => q (m + 1) - q m ≤ D ∧ 3 ∣ q (m + 1) - q m)).card := by
    apply Finset.card_le_card
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at hm ⊢
    exact ⟨by omega, hle m hm.1.2, hm.2⟩
  -- the others inject into their values
  have h' : ((Finset.Icc 2 n).filter (fun m => ¬ 3 ∣ q (m + 1) - q m)).card ≤
      {v : ℕ | v ≤ D ∧ ¬ 3 ∣ v ∧ ∃ n, q (n + 1) - q n = v}.ncard := by
    set S' := (Finset.Icc 2 n).filter (fun m => ¬ 3 ∣ q (m + 1) - q m) with hS'
    have hmem : ∀ m ∈ S', 2 ≤ m ∧ m ≤ n ∧ ¬ 3 ∣ q (m + 1) - q m := by
      intro m hm
      simp only [hS', Finset.mem_filter, Finset.mem_Icc] at hm
      exact ⟨hm.1.1, hm.1.2, hm.2⟩
    have hinj : Set.InjOn (fun m => q (m + 1) - q m) (S' : Set ℕ) := by
      intro a ha b hb hab
      simp only at hab
      by_contra hne
      have ha' := hmem a ha
      have hb' := hmem b hb
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have h1 : q (a + 1) - q a ≤ q (a + 1 + 1) - q (a + 1) := hmono (by omega)
        have h2 : q (a + 1 + 1) - q (a + 1) ≤ q (b + 1) - q b := hmono (by omega)
        have heq : q (a + 2) - q (a + 1) = q (a + 1) - q a := by
          show q (a + 1 + 1) - q (a + 1) = q (a + 1) - q a
          omega
        exact ha'.2.2 (three_dvd_of_repeat hq hprime ha'.1 heq)
      · have h1 : q (b + 1) - q b ≤ q (b + 1 + 1) - q (b + 1) := hmono (by omega)
        have h2 : q (b + 1 + 1) - q (b + 1) ≤ q (a + 1) - q a := hmono (by omega)
        have heq : q (b + 2) - q (b + 1) = q (b + 1) - q b := by
          show q (b + 1 + 1) - q (b + 1) = q (b + 1) - q b
          omega
        exact hb'.2.2 (three_dvd_of_repeat hq hprime hb'.1 heq)
    rw [← Finset.card_image_of_injOn hinj, ← Set.ncard_coe_finset]
    apply Set.ncard_le_ncard _ ((Set.finite_Iic D).subset fun v hv => hv.1)
    intro v hv
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hv
    obtain ⟨m, hm, rfl⟩ := hv
    have hm' := hmem m hm
    exact ⟨hle m hm'.2.1, hm'.2.2, m, rfl⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.Icc 2 n)
    (fun m => 3 ∣ q (m + 1) - q m)
  rw [Nat.card_Icc] at hsplit
  have hB'' := hB' (n + 1)
  have h3R : (((Finset.Icc 2 n).filter (fun m => 3 ∣ q (m + 1) - q m)).card : ℝ) ≤ ε * D :=
    (by exact_mod_cast h3 : (((Finset.Icc 2 n).filter (fun m => 3 ∣ q (m + 1) - q m)).card : ℝ)
      ≤ (((Finset.range (n + 1)).filter
        (fun m => q (m + 1) - q m ≤ D ∧ 3 ∣ q (m + 1) - q m)).card : ℝ)).trans hB''
  have h'R : (((Finset.Icc 2 n).filter (fun m => ¬ 3 ∣ q (m + 1) - q m)).card : ℝ) ≤ ε * D :=
    (by exact_mod_cast h' : (((Finset.Icc 2 n).filter (fun m => ¬ 3 ∣ q (m + 1) - q m)).card : ℝ)
      ≤ ({v : ℕ | v ≤ D ∧ ¬ 3 ∣ v ∧ ∃ n, q (n + 1) - q n = v}.ncard : ℝ)).trans hA'
  have hsum : ((n + 1 - 2 : ℕ) : ℝ) =
      (((Finset.Icc 2 n).filter (fun m => 3 ∣ q (m + 1) - q m)).card : ℝ) +
      (((Finset.Icc 2 n).filter (fun m => ¬ 3 ∣ q (m + 1) - q m)).card : ℝ) := by
    rw [← hsplit]
    push_cast
    ring
  have hcast : ((n + 1 - 2 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hcast] at hsum
  linarith

/-- A convex sequence grows at least linearly from any index: `q n ≥ (n - k) d(k)`. -/
lemma growth {q : ℕ → ℕ} (hq : StrictMono q)
    (hconv : ∀ n, q (n + 2) - q (n + 1) ≥ q (n + 1) - q n) {k n : ℕ} (hkn : k ≤ n) :
    (n - k) * (q (k + 1) - q k) ≤ q n := by
  have hmono := diff_mono hconv
  induction n, hkn using Nat.le_induction with
  | base => simp
  | succ n hkn ih =>
    have h1 : q (k + 1) - q k ≤ q (n + 1) - q n := hmono hkn
    have h2 : q n < q (n + 1) := hq (by omega)
    have e : n + 1 - k = (n - k) + 1 := by omega
    rw [e, add_mul, one_mul]
    omega

theorem main : H1 → H2 → type_of% @Erdos455.erdos_455 := by
  intro h1 h2 q hq hp
  have hprime : ∀ n, (q n).Prime := fun n => (hp n).1
  have hconv : ∀ n, q (n + 2) - q (n + 1) ≥ q (n + 1) - q n := fun n => (hp n).2
  rw [Filter.tendsto_atTop]
  intro C
  set C' : ℝ := max C 1 with hC'
  have hC'1 : 1 ≤ C' := le_max_right _ _
  set ε : ℝ := 1 / (16 * C') with hεdef
  have hε : 0 < ε := by positivity
  have hcount := count_bound hq hprime hconv (h1 q hq hp ε hε) (h2 q hq hp ε hε)
  obtain ⟨N₁, hN₁⟩ := hcount.exists_forall_of_atTop
  filter_upwards [eventually_ge_atTop (2 * N₁ + 16)] with n hn
  set k := n / 2 with hk
  have hkN : N₁ ≤ k := by omega
  have hkn : k ≤ n := Nat.div_le_self _ _
  have hdk := hN₁ k hkN
  have hg := growth hq hconv hkn
  have hgR : (((n - k : ℕ) : ℝ)) * ((q (k + 1) - q k : ℕ) : ℝ) ≤ (q n : ℝ) := by
    exact_mod_cast hg
  have ha : (n : ℝ) / 2 ≤ ((n - k : ℕ) : ℝ) := by
    have : n ≤ 2 * (n - k) := by omega
    have : (n : ℝ) ≤ 2 * ((n - k : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have hk1 : (n : ℝ) / 4 ≤ (k : ℝ) - 1 := by
    have : n + 4 ≤ 4 * k := by omega
    have : (n : ℝ) + 4 ≤ 4 * (k : ℝ) := by exact_mod_cast this
    linarith
  have hnpos : (0 : ℝ) < n := by
    have : (0 : ℝ) < (16 : ℕ) := by norm_num
    exact_mod_cast (show 0 < n by omega)
  have hb0 : (0 : ℝ) ≤ ((q (k + 1) - q k : ℕ) : ℝ) := Nat.cast_nonneg _
  have ha0 : (0 : ℝ) ≤ ((n - k : ℕ) : ℝ) := Nat.cast_nonneg _
  -- q n * (2 ε) ≥ (n/2) (n/4)
  have hkey : (n : ℝ) / 2 * ((n : ℝ) / 4) ≤ (q n : ℝ) * (2 * ε) := by
    have e1 : (n : ℝ) / 4 ≤ 2 * ε * ((q (k + 1) - q k : ℕ) : ℝ) := hk1.trans hdk
    calc (n : ℝ) / 2 * ((n : ℝ) / 4) ≤ ((n - k : ℕ) : ℝ) * (2 * ε * ((q (k + 1) - q k : ℕ) : ℝ)) :=
          mul_le_mul ha e1 (by positivity) ha0
      _ = (((n - k : ℕ) : ℝ) * ((q (k + 1) - q k : ℕ) : ℝ)) * (2 * ε) := by ring
      _ ≤ (q n : ℝ) * (2 * ε) := mul_le_mul_of_nonneg_right hgR (by positivity)
  have hεC : 16 * C' * ε = 1 := by
    rw [hεdef]
    field_simp
  rw [le_div_iff₀ (by positivity)]
  have hC : C ≤ C' := le_max_left _ _
  have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  calc C * (n : ℝ) ^ 2 ≤ C' * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hC hn2
    _ = (16 * C' * ε) * (C' * (n : ℝ) ^ 2) / (16 * C' * ε) := by rw [hεC]; ring
    _ ≤ (q n : ℝ) := by
        rw [hεC, div_one]
        nlinarith

end OMA.R_Erdos455_erdos_455_R1
