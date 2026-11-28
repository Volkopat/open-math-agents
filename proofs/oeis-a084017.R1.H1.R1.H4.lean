-- split of proofs/oeis-a084017.lean (1 068 065 B > 512 KiB lint) via the reductions mechanism
import OMAReductions.R_oeis_a084017_R1_H1_R1
import Mathlib

/-!
# OEIS A084017 : no term is zero (Murthy and Srikanth, 2003)

Proof = the kernel-verified chain from the DemosMathNT project,
inlined because a submission may only import Mathlib besides
OMAStatements. Sections, in dependency order :
  - section A084013src : palindromic-multiple toolkit of A084013.lean
    (its `import A077727` was dead - no reference in the body)
  - section A084017src : A084017.lean, the Murthy-Srikanth
    construction (assemble_* + hres_* + residual machinery)
  - section A084017R2src : A084017R2.lean, the residualHard family
    and the capstone A084017.A084017 for `~ 10 | n`
  - section SpecA084017src : Spec_A084017.lean (SpecPropA084017N,
    SpecPropA084017)
  - section PinnedTensrc : Pinned_A084017_ten.lean, the `10 | n`
    case, ending in proven_A084017_full

Adaptations vs the kernel sources (identical to the sibling port
oeis-a084023, whose body covers the same dependency cone) :
  - local `import`s and file-scope `set_option autoImplicit` /
    `relaxedAutoImplicit` dropped (not allowed at top level) ;
  - `set_option maxHeartbeats 800000` (file scope in the source)
    propagated per-declaration in the `in` form ;
  - `@[irreducible]` on `seg` dropped (attributes other than simp are
    not allowed ; dropping it only makes `seg` more reducible, every
    use unfolds via `simp [seg]`) ;
  - `end DeadCount` added to close a section left open at kernel
    file end (no `variable` inside, so a pure marker) ;
  - the whole cone is wrapped in `namespace OMA.A084017Port` so no
    name can collide with other submissions : internal namespaces
    become OMA.A084017Port.A084017 / .PinnedTen / .DeadCount ... and
    the internal `open A084017` inside PinnedTen resolves to
    OMA.A084017Port.A084017.

The bridge below is a definitional-equality cast, no re-proof :
`OMA.S_oeis_a084017.qualifies n` unfolds to the same conjunction as
`SpecPropA084017N n`, the clause `z = tz n` being the def
`((Nat.digits 10 n).takeWhile (. = 0)).length` on both sides.
-/

namespace OMA.A084017Port

section A084013src





open scoped Pointwise


section DeadCount


section PalDiag


end PalDiag


theorem ofDigits_append' {α : Type*} [Semiring α] (b : α) (l1 l2 : List ℕ) :
    Nat.ofDigits b (l1 ++ l2) =
      Nat.ofDigits b l1 + b ^ l1.length * Nat.ofDigits b l2 := by
  induction l1 with
  | nil =>
    show Nat.ofDigits b l2 =
        Nat.ofDigits b [] + b ^ (0 : ℕ) * Nat.ofDigits b l2
    rw [show Nat.ofDigits b [] = (0 : α) from rfl, pow_zero, one_mul,
      zero_add]
  | cons d t ih =>
    rw [List.cons_append]
    show (d : α) + b * Nat.ofDigits b (t ++ l2) =
      (d : α) + b * Nat.ofDigits b t
        + b ^ (t.length + 1) * Nat.ofDigits b l2
    rw [ih, mul_add, ← mul_assoc, ← pow_succ', ← add_assoc]

theorem ofDigits_singleton' {α : Type*} [Semiring α] (b : α) (d : ℕ) :
    Nat.ofDigits b [d] = (d : α) := by simp [Nat.ofDigits]


theorem ofDigits_zmod_range (m : ℕ) (g : ℕ → ℕ) (j : ℕ) :
    Nat.ofDigits (10 : ZMod m) ((List.range j).map g) =
      ∑ i ∈ Finset.range j, (g i : ZMod m) * (10 : ZMod m) ^ i := by
  induction j with
  | zero => simp [Nat.ofDigits]
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_singleton,
      ofDigits_append', ofDigits_singleton', List.length_map,
      List.length_range, Finset.sum_range_succ, ih]
    ring


theorem ofDigits_zmod_rev (m : ℕ) (g : ℕ → ℕ) (j : ℕ) :
    Nat.ofDigits (10 : ZMod m) ((List.range j).map g).reverse =
      ∑ i ∈ Finset.range j, (g i : ZMod m) * (10 : ZMod m) ^ (j - 1 - i) := by
  have hrw : ((List.range j).map g).reverse =
      (List.range j).map (fun i => g (j - 1 - i)) := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_reverse, List.length_map, List.length_range,
      List.getElem_map, List.getElem_range]
  rw [hrw, ofDigits_zmod_range m (fun i => g (j - 1 - i)) j]
  have hr : ∑ i ∈ Finset.range j,
      (g (j - 1 - i) : ZMod m) * (10 : ZMod m) ^ i =
      ∑ i ∈ Finset.range j,
        (g i : ZMod m) * (10 : ZMod m) ^ (j - 1 - i) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    rw [show j - 1 - (j - 1 - i) = i by omega]
  exact hr


theorem ofDigits_replicate_zero (s : ℕ) :
    Nat.ofDigits 10 (List.replicate s 0) = 0 := by
  induction s with
  | zero => simp
  | succ s ih => simp [List.replicate_succ, Nat.ofDigits_cons, ih]







end DeadCount

end A084013src

section A084017src



open Classical Finset




open scoped Pointwise


theorem ten_pow_mod81 (i : ℕ) :
    (10 : ZMod 81) ^ i = 1 + 9 * ((i % 9 : ℕ) : ZMod 81) := by
  conv_lhs => rw [← Nat.div_add_mod i 9, pow_add, pow_mul]
  have h9 : (10 : ZMod 81) ^ 9 = 1 := by decide
  rw [h9, one_pow, one_mul]
  have hlt : i % 9 < 9 := Nat.mod_lt _ (by norm_num)
  set r := i % 9 with hr
  interval_cases r <;> decide


theorem nine_mul_cast_mod9 (i : ℕ) :
    (9 : ZMod 81) * ((i % 9 : ℕ) : ZMod 81) = 9 * (i : ZMod 81) := by
  have hcast : (i : ZMod 81) = 9 * ((i / 9 : ℕ) : ZMod 81)
      + ((i % 9 : ℕ) : ZMod 81) := by
    have h1 : (i : ZMod 81)
        = ((9 * (i / 9) + i % 9 : ℕ) : ZMod 81) := by
      rw [Nat.div_add_mod]
    rw [h1]; push_cast; ring
  have h81 : ((81 : ℕ) : ZMod 81) = 0 := ZMod.natCast_self 81
  calc (9 : ZMod 81) * ((i % 9 : ℕ) : ZMod 81)
      = 9 * ((i : ZMod 81) - 9 * ((i / 9 : ℕ) : ZMod 81)) := by
        rw [hcast]; ring
    _ = 9 * (i : ZMod 81) - 81 * ((i / 9 : ℕ) : ZMod 81) := by ring
    _ = 9 * (i : ZMod 81) := by
        have : (81 : ZMod 81) = 0 := by
          rw [← Nat.cast_ofNat] ; exact h81
        rw [show (81 : ZMod 81) = ((81 : ℕ) : ZMod 81) from rfl, h81]
        ring


theorem ofDigits_cast (l : List ℕ) :
    ((Nat.ofDigits 10 l : ℕ) : ZMod 81)
      = Nat.ofDigits (10 : ZMod 81) l := by
  induction l with
  | nil => rfl
  | cons d ds ih =>
    rw [Nat.ofDigits_cons, Nat.cast_add, Nat.cast_mul, ih]
    rw [show d :: ds = [d] ++ ds from rfl, ofDigits_append',
      ofDigits_singleton', List.length_singleton, pow_one,
      Nat.cast_ofNat]


theorem pal_mod81_even : ∀ (A : List ℕ),
    Nat.ofDigits (10 : ZMod 81) (A ++ A.reverse)
      = ((A.sum : ℕ) : ZMod 81)
          * (2 + 9 * (2 * (A.length : ZMod 81) - 1)) := by
  intro A; induction A with
  | nil => simp [Nat.ofDigits]
  | cons a A' ih =>
    have h1 : (a :: A') ++ (a :: A').reverse
        = a :: ((A' ++ A'.reverse) ++ [a]) := by
      simp [List.reverse_cons]
    rw [h1]
    rw [show a :: ((A' ++ A'.reverse) ++ [a])
        = [a] ++ ((A' ++ A'.reverse) ++ [a]) from rfl]
    rw [ofDigits_append', ofDigits_singleton', List.length_singleton,
      pow_one,
      show (A' ++ A'.reverse) ++ [a] = A' ++ A'.reverse ++ [a]
        from rfl,
      ofDigits_append', ofDigits_singleton', ih]
    have hlen : ((A' ++ A'.reverse).length : ℕ) = 2 * A'.length := by
      simp; omega
    rw [hlen]
    have hpow : (10 : ZMod 81) ^ (2 * A'.length + 1)
        = 1 + 9 * ((2 * A'.length + 1 : ℕ) : ZMod 81) := by
      rw [ten_pow_mod81]
      congr 1
      exact nine_mul_cast_mod9 _
    have h2 : (10 : ZMod 81) ^ (2 * A'.length + 1)
        = 10 * 10 ^ (2 * A'.length) := pow_succ' _ _
    have hpow2 :
        (10 : ZMod 81) * (10 ^ (2 * A'.length) * (a : ZMod 81))
          = 10 ^ (2 * A'.length + 1) * (a : ZMod 81) := by
      rw [← mul_assoc, ← h2]
    rw [mul_add, hpow2, hpow, List.sum_cons, List.length_cons]
    push_cast
    have h81 : (81 : ZMod 81) = 0 := by decide
    linear_combination
      (((List.map Nat.cast A').sum : ZMod 81)
        * (2 * (A'.length : ZMod 81) - 1)) * h81


theorem dvd3_pow_of_sigma_even (A : List ℕ) {v : ℕ} (hv : v ≤ 4)
    (hσ : 3 ^ v ∣ 2 * A.sum) :
    3 ^ v ∣ Nat.ofDigits 10 (A ++ A.reverse) := by
  haveI : NeZero (3 ^ v) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hdiv : 3 ^ v ∣ 81 :=
    ⟨3 ^ (4 - v), by
      rw [← pow_add, show v + (4 - v) = 4 by omega]; norm_num⟩
  have hSdvd : 3 ^ v ∣ A.sum :=
    Nat.Coprime.dvd_of_dvd_mul_left
      (Nat.Coprime.pow_left _ (by decide : Nat.Coprime 3 2)) hσ
  by_cases hA : A = []
  · subst hA; simp [Nat.ofDigits]
  have hl : 1 ≤ 2 * A.length := by
    have : A.length ≠ 0 := by
      intro h; apply hA; exact List.length_eq_zero_iff.mp h
    omega
  have hU : ((2 + 9 * (2 * A.length - 1) : ℕ) : ZMod 81)
      = 2 + 9 * (2 * (A.length : ZMod 81) - 1) := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hl, Nat.cast_mul]
    norm_num
  have hmod : Nat.ofDigits 10 (A ++ A.reverse)
      ≡ A.sum * (2 + 9 * (2 * A.length - 1)) [MOD 81] := by
    have h := pal_mod81_even A
    rw [← ofDigits_cast] at h
    rw [← hU, ← Nat.cast_mul] at h
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h
  have hmodv : Nat.ofDigits 10 (A ++ A.reverse)
      ≡ A.sum * (2 + 9 * (2 * A.length - 1)) [MOD 3 ^ v] :=
    Nat.ModEq.of_dvd hdiv hmod
  have hS0 : A.sum * (2 + 9 * (2 * A.length - 1)) ≡ 0 [MOD 3 ^ v] :=
    Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left hSdvd _)
  exact Nat.modEq_zero_iff_dvd.mp (hmodv.trans hS0)


def palW (m L i : ℕ) : ZMod m :=
  (10 : ZMod m) ^ i + (10 : ZMod m) ^ (L - 1 - i)


def pairDigit (e : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i % 2 = 0 then e (i / 2) else 9 - e (i / 2)

theorem pairDigit_even (e : ℕ → ℕ) (k : ℕ) :
    pairDigit e (2 * k) = e k := by
  unfold pairDigit
  rw [show (2 * k) % 2 = 0 by omega, show (2 * k) / 2 = k by omega]
  simp

theorem pairDigit_odd (e : ℕ → ℕ) (k : ℕ) :
    pairDigit e (2 * k + 1) = 9 - e k := by
  unfold pairDigit
  rw [show (2 * k + 1) % 2 = 1 by omega,
    show (2 * k + 1) / 2 = k by omega]
  simp






theorem sum_range_pair {α : Type*} [AddCommMonoid α] (f : ℕ → α) (K : ℕ) :
    ∑ i ∈ Finset.range (2 * K), f i
      = ∑ k ∈ Finset.range K, (f (2 * k) + f (2 * k + 1)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have h1 : ∑ i ∈ Finset.range (2 * (K + 1)), f i
        = ∑ i ∈ Finset.range (2 * K), f i + f (2 * K)
          + f (2 * K + 1) := by
      rw [show 2 * (K + 1) = 2 * K + 1 + 1 from by ring,
        Finset.sum_range_succ, Finset.sum_range_succ]
    rw [h1, ih, Finset.sum_range_succ, add_assoc]


def twt (m L k : ℕ) : ZMod m := palW m L (2 * k) - palW m L (2 * k + 1)


theorem decomp235 (n : ℕ) (hn : n ≠ 0) :
    ∃ a b v m : ℕ, n = 2 ^ a * 5 ^ b * 3 ^ v * m
      ∧ m.Coprime 30 ∧ (¬ 2 ∣ m) ∧ (¬ 5 ∣ m) ∧ (¬ 3 ∣ m) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set a := padicValNat 2 n with ha
  set q1 := Nat.divMaxPow n 2 with hq1d
  set b := padicValNat 5 q1 with hb
  set q2 := Nat.divMaxPow q1 5 with hq2d
  set v := padicValNat 3 q2 with hv
  set m := Nat.divMaxPow q2 3 with hmd
  have hq1 : q1 * 2 ^ a = n := Nat.divMaxPow_mul_pow_padicValNat 2 n
  have hq2 : q2 * 5 ^ b = q1 := Nat.divMaxPow_mul_pow_padicValNat 5 q1
  have hmq : m * 3 ^ v = q2 := Nat.divMaxPow_mul_pow_padicValNat 3 q2
  have hq10 : q1 ≠ 0 := by
    intro h; rw [h, zero_mul] at hq1; exact hn hq1.symm
  have hq20 : q2 ≠ 0 := by
    intro h; rw [h, zero_mul] at hq2; exact hq10 hq2.symm
  have hm0 : m ≠ 0 := by
    intro h; rw [h, zero_mul] at hmq; exact hq20 hmq.symm
  have h2q1 : ¬ 2 ∣ q1 := Nat.not_dvd_divMaxPow (by norm_num) hn
  have h5q2 : ¬ 5 ∣ q2 := Nat.not_dvd_divMaxPow (by norm_num) hq10
  have h3m : ¬ 3 ∣ m := Nat.not_dvd_divMaxPow (by norm_num) hq20
  have hmq2 : m ∣ q2 := ⟨3 ^ v, hmq.symm⟩
  have hq2q1 : q2 ∣ q1 := ⟨5 ^ b, hq2.symm⟩
  have h2m : ¬ 2 ∣ m := fun h =>
    h2q1 (h.trans (hmq2.trans hq2q1))
  have h5m : ¬ 5 ∣ m := fun h => h5q2 (h.trans hmq2)
  have hc30 : m.Coprime 30 := by
    have h2 : Nat.Coprime m 2 :=
      ((Nat.prime_two.coprime_iff_not_dvd).mpr h2m).symm
    have h3 : Nat.Coprime m 3 :=
      ((Nat.prime_three.coprime_iff_not_dvd).mpr h3m).symm
    have h5 : Nat.Coprime m 5 :=
      ((Nat.prime_five.coprime_iff_not_dvd).mpr h5m).symm
    have h6 : Nat.Coprime m 6 := Nat.Coprime.mul_right h2 h3
    have h30 : Nat.Coprime m (6 * 5) := Nat.Coprime.mul_right h6 h5
    exact h30
  refine ⟨a, b, v, m, ?_, hc30, h2m, h5m, h3m⟩
  have e1 : n = q1 * 2 ^ a := hq1.symm
  rw [e1, ← hq2, ← hmq]; ring


theorem sum_pair_weights_gen {m K L : ℕ} (e : ℕ → ℕ) (he : ∀ k, e k ≤ 9) :
    ∑ i ∈ Finset.range (2 * K),
        (pairDigit e i : ZMod m) * palW m L i
    = ∑ k ∈ Finset.range K,
        ((9 : ZMod m) * palW m L (2 * k + 1)
        + (e k : ZMod m) * (palW m L (2 * k)
            - palW m L (2 * k + 1))) := by
  rw [sum_range_pair
    (fun i => (pairDigit e i : ZMod m) * palW m L i) K]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [pairDigit_even, pairDigit_odd]
  rw [Nat.cast_sub (he k)]
  push_cast
  ring


theorem ofDigits_pair_center {m K g : ℕ} (e : ℕ → ℕ)
    (he : ∀ k, e k ≤ 9) (C : List ℕ) (hC : C.length = g) :
    Nat.ofDigits (10 : ZMod m)
      ((List.range (2 * K)).map (pairDigit e) ++ C
        ++ ((List.range (2 * K)).map (pairDigit e)).reverse)
    = Nat.ofDigits (10 : ZMod m) C * (10 : ZMod m) ^ (2 * K)
      + ∑ k ∈ Finset.range K,
          ((9 : ZMod m) * palW m (4 * K + g) (2 * k + 1)
          + (e k : ZMod m)
            * (palW m (4 * K + g) (2 * k)
              - palW m (4 * K + g) (2 * k + 1))) := by
  have hlen : ((List.range (2 * K)).map (pairDigit e)).length = 2 * K := by
    rw [List.length_map, List.length_range]
  rw [ofDigits_append', ofDigits_append', hlen,
    List.length_append, hlen, hC]
  rw [ofDigits_zmod_range, ofDigits_zmod_rev]
  rw [Finset.mul_sum]
  
  have hterm : ∀ i ∈ Finset.range (2 * K),
      (10 : ZMod m) ^ (2 * K + g)
          * ((pairDigit e i : ZMod m) * 10 ^ (2 * K - 1 - i))
      = (pairDigit e i : ZMod m)
          * (10 : ZMod m) ^ (4 * K + g - 1 - i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    calc (10 : ZMod m) ^ (2 * K + g)
          * ((pairDigit e i : ZMod m) * 10 ^ (2 * K - 1 - i))
        = (pairDigit e i : ZMod m)
            * ((10 : ZMod m) ^ (2 * K + g) * 10 ^ (2 * K - 1 - i)) := by
          ring
      _ = (pairDigit e i : ZMod m)
            * (10 : ZMod m) ^ (2 * K + g + (2 * K - 1 - i)) := by
          rw [← pow_add]
      _ = (pairDigit e i : ZMod m)
            * (10 : ZMod m) ^ (4 * K + g - 1 - i) := by
          rw [show 2 * K + g + (2 * K - 1 - i)
              = 4 * K + g - 1 - i by omega]
  have hsum : ∑ i ∈ Finset.range (2 * K),
        (pairDigit e i : ZMod m) * (10 : ZMod m) ^ i
      + ∑ i ∈ Finset.range (2 * K), (10 : ZMod m) ^ (2 * K + g)
          * ((pairDigit e i : ZMod m) * 10 ^ (2 * K - 1 - i))
      = ∑ i ∈ Finset.range (2 * K),
          (pairDigit e i : ZMod m) * palW m (4 * K + g) i := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [hterm i (Finset.mem_range.mpr hi)]
    unfold palW
    rw [mul_add]
  
  rw [add_right_comm, hsum]
  rw [show (10 : ZMod m) ^ (2 * K) * Nat.ofDigits (10 : ZMod m) C
      = Nat.ofDigits (10 : ZMod m) C * (10 : ZMod m) ^ (2 * K)
      from mul_comm _ _, add_comm]
  rw [sum_pair_weights_gen e he]


namespace A084017

open Finset List Nat BigOperators Pointwise


variable {m : ℕ} [NeZero m]



set_option maxHeartbeats 800000 in
noncomputable def seg (w : ZMod m) (k : ℕ) : Finset (ZMod m) :=
  Finset.image (fun j : ℕ => (j : ZMod m) * w) (Finset.range (k + 1))

set_option maxHeartbeats 800000 in
theorem mem_seg {w : ZMod m} {k : ℕ} {x : ZMod m} :
    x ∈ seg w k ↔ ∃ j ≤ k, (j : ZMod m) * w = x := by
  simp [seg]

set_option maxHeartbeats 800000 in
theorem seg_mono {w : ZMod m} {a b : ℕ} (h : a ≤ b) : seg w a ⊆ seg w b := by
  intro x hx
  simp [seg] at hx ⊢
  obtain ⟨j, hj, rfl⟩ := hx
  exact ⟨j, le_trans hj h, rfl⟩

set_option maxHeartbeats 800000 in
theorem zero_mem_seg (w : ZMod m) (k : ℕ) : (0 : ZMod m) ∈ seg w k := by
  simp [seg]
  exact ⟨0, by simp⟩


set_option maxHeartbeats 800000 in
theorem seg_add_w (w : ZMod m) (k : ℕ) :
    seg w k + {w} ⊆ seg w (k + 1) := by
  intro x hx
  rw [Finset.mem_add] at hx
  obtain ⟨y, hy, z, hz, hsum⟩ := hx
  rw [Finset.mem_singleton] at hz
  subst hz
  rw [← hsum]
  rw [mem_seg] at hy ⊢
  obtain ⟨j, hj, rfl⟩ := hy
  exact ⟨j + 1, by omega, by push_cast; ring⟩

set_option maxHeartbeats 800000 in
theorem add_sing_sing (S : Finset (ZMod m)) (x y : ZMod m) :
    (S + {x}) + {y} = S + {x + y} := by
  ext e
  simp [Finset.mem_add, add_assoc]

set_option maxHeartbeats 800000 in
theorem add_sing_zero (S : Finset (ZMod m)) :
    S + ({(0 : ZMod m)}) = S := by
  ext e
  simp [Finset.mem_add]

set_option maxHeartbeats 800000 in
theorem seg_zero (w : ZMod m) : seg w 0 = ({(0 : ZMod m)}) := by
  simp [seg]


set_option maxHeartbeats 800000 in
theorem card_add_seg_ge (S : Finset (ZMod m)) (w : ZMod m) (k : ℕ) :
    min (S.card + k) ((S + seg w m).card) ≤ (S + seg w k).card := by
  induction k with
  | zero =>
    rw [seg_zero, add_sing_zero]
    simp
  | succ k ih =>
    set T := S + seg w k with hTdef
    have hTk : T ⊆ S + seg w (k + 1) :=
      Finset.add_subset_add_left (seg_mono (Nat.le_succ k))
    by_cases hst : S + seg w (k + 1) = T
    · 
      have hinv : T + {w} ⊆ T := by
        have h1 : T + {w} ⊆ S + seg w (k + 1) := by
          intro x hx
          rw [Finset.mem_add] at hx
          obtain ⟨t, ht, z, hz, hsum⟩ := hx
          rw [Finset.mem_singleton] at hz
          subst hz
          rw [← hsum]
          rw [hTdef, Finset.mem_add] at ht
          obtain ⟨a, ha, b, hb, hs2⟩ := ht
          rw [← hs2, add_assoc]
          exact Finset.add_mem_add ha
            (seg_add_w z k (Finset.add_mem_add hb (Finset.mem_singleton_self _)))
        exact hst ▸ h1
      have hS : S ⊆ T := by
        intro x hx
        have h := Finset.add_mem_add hx (zero_mem_seg w k)
        rw [hTdef]
        rwa [add_zero] at h
      have hinvj : ∀ j : ℕ, S + {((j : ℕ) : ZMod m) * w} ⊆ T := by
        intro j
        induction j with
        | zero =>
          simp only [Nat.cast_zero, zero_mul]
          rw [add_sing_zero]
          exact hS
        | succ j ih =>
          have hstep : (((j + 1 : ℕ) : ZMod m) * w) = ((j : ℕ) : ZMod m) * w + w := by
            push_cast; ring
          rw [hstep]
          rw [← add_sing_sing]
          exact (Finset.add_subset_add ih (Finset.Subset.refl _)).trans hinv
      have hsm : S + seg w m ⊆ T := by
        intro x hx
        rw [Finset.mem_add] at hx
        obtain ⟨a, ha, b, hb, hsum⟩ := hx
        rw [← hsum]
        rw [mem_seg] at hb
        obtain ⟨j, hj, rfl⟩ := hb
        exact hinvj j (Finset.add_mem_add ha (Finset.mem_singleton_self _))
      rw [hst]
      exact le_trans (min_le_right _ _) (Finset.card_le_card hsm)
    · 
      have hss : T ⊂ S + seg w (k + 1) :=
        Finset.ssubset_iff_subset_ne.mpr ⟨hTk, fun h => hst h.symm⟩
      have hcard : T.card + 1 ≤ (S + seg w (k + 1)).card := Finset.card_lt_card hss
      rcases Nat.lt_or_ge (S.card + k) ((S + seg w m).card) with hB | hB
      · 
        rw [min_eq_left (le_of_lt hB)] at ih
        calc min (S.card + (k + 1)) (S + seg w m).card
            ≤ S.card + (k + 1) := min_le_left _ _
          _ = S.card + k + 1 := rfl
          _ ≤ T.card + 1 := by omega
          _ ≤ (S + seg w (k + 1)).card := hcard
      · 
        rw [min_eq_right hB] at ih
        calc min (S.card + (k + 1)) (S + seg w m).card
            ≤ (S + seg w m).card := min_le_right _ _
          _ ≤ T.card := ih
          _ ≤ T.card + 1 := by omega
          _ ≤ (S + seg w (k + 1)).card := hcard



open Finset List Nat BigOperators Pointwise



set_option maxHeartbeats 800000 in
theorem card_add_sing (T : Finset (ZMod m)) (g : ZMod m) :
    (T + {g}).card = T.card := by
  have h : T + {g} = T.image (· + g) := by
    ext e
    constructor
    · intro h
      rw [Finset.mem_add] at h
      obtain ⟨y, hy, z, hz, hsum⟩ := h
      rw [Finset.mem_singleton] at hz; subst hz
      rw [Finset.mem_image]
      exact ⟨y, hy, hsum⟩
    · intro h
      rw [Finset.mem_image] at h
      obtain ⟨y, hy, hsum⟩ := h
      rw [Finset.mem_add]
      exact ⟨y, hy, g, Finset.mem_singleton_self g, hsum⟩
  rw [h]
  exact Finset.card_image_of_injective T (add_left_injective g)


set_option maxHeartbeats 800000 in
theorem inv_add {T : Finset (ZMod m)} {x y : ZMod m}
    (hx : T + {x} = T) (hy : T + {y} = T) : T + {x + y} = T := by
  rw [← add_sing_sing, hx, hy]

set_option maxHeartbeats 800000 in
theorem inv_neg {T : Finset (ZMod m)} {x : ZMod m}
    (hx : T + {x} = T) : T + {-x} = T := by
  have h : (T + {x}) + {-x} = T := by
    rw [add_sing_sing]
    simp [add_sing_zero]
  rw [hx] at h
  exact h


set_option maxHeartbeats 800000 in
theorem add_sing_comm (T A : Finset (ZMod m)) (y : ZMod m) :
    (T + A) + {y} = (T + {y}) + A := by
  ext e
  constructor <;> intro he
  · rw [Finset.mem_add] at he
    obtain ⟨u, hu, v, hv, hsum⟩ := he
    rw [Finset.mem_singleton] at hv; subst hv
    rw [Finset.mem_add] at hu
    obtain ⟨t, ht, a, ha, htu⟩ := hu
    have hge : (t + v) + a = e := by
      rw [add_right_comm, htu, hsum]
    exact Finset.mem_add.mpr
      ⟨t + v, Finset.mem_add.mpr ⟨t, ht, v, Finset.mem_singleton_self v, rfl⟩, a, ha, hge⟩
  · rw [Finset.mem_add] at he
    obtain ⟨u, hu, a, ha, hsum⟩ := he
    rw [Finset.mem_add] at hu
    obtain ⟨t, ht, v, hv, htu⟩ := hu
    rw [Finset.mem_singleton] at hv; subst hv
    have hge : (t + a) + v = e := by
      rw [← add_right_comm, htu, hsum]
    exact Finset.mem_add.mpr
      ⟨t + a, Finset.mem_add.mpr ⟨t, ht, a, ha, rfl⟩, v, Finset.mem_singleton_self v, hge⟩


set_option maxHeartbeats 800000 in
theorem inv_nsmul {T : Finset (ZMod m)} {x : ZMod m}
    (hx : T + {x} = T) : ∀ n : ℕ, T + {n • x} = T := by
  intro n
  induction n with
  | zero => simp [add_sing_zero]
  | succ n ih =>
    have hs : (n + 1) • x = n • x + x := by rw [succ_nsmul]
    rw [hs]
    exact inv_add ih hx


set_option maxHeartbeats 800000 in
theorem inv_zsmul {T : Finset (ZMod m)} {x : ZMod m}
    (hx : T + {x} = T) (z : ℤ) : T + {z • x} = T := by
  cases z with
  | ofNat n =>
    have h : ((n : ℤ) • x) = n • x := by simp
    rw [Int.ofNat_eq_coe, h]
    exact inv_nsmul hx n
  | negSucc n =>
    have h1 : (Int.negSucc n • x) = -(((n + 1 : ℕ) : ℤ) • x) := by
      have e : (Int.negSucc n : ℤ) = -((n : ℤ) + 1) := rfl
      rw [e, neg_zsmul]
      simp
    rw [h1]
    have h2 : (((n + 1 : ℕ) : ℤ) • x) = (n + 1 : ℕ) • x := by simp
    rw [h2]
    exact inv_neg (inv_nsmul hx (n + 1))



open Finset List Nat BigOperators Pointwise



set_option maxHeartbeats 800000 in
theorem exists_comb {a b : ℕ} (hgcd : Nat.gcd (Nat.gcd a b) m = 1) :
    ∃ x y : ℤ, (x : ZMod m) * (a : ZMod m) + (y : ZMod m) * (b : ZMod m) = 1 := by
  have h1 := Nat.gcd_eq_gcd_ab (Nat.gcd a b) m
  rw [hgcd] at h1
  
  have h2 := Nat.gcd_eq_gcd_ab a b
  
  refine ⟨a.gcdA b * (Nat.gcd a b).gcdA m, a.gcdB b * (Nat.gcd a b).gcdA m, ?_⟩
  have eq : (a.gcdA b * (Nat.gcd a b).gcdA m : ℤ) * a
      + (a.gcdB b * (Nat.gcd a b).gcdA m : ℤ) * b
      = (Nat.gcd a b : ℤ) * (Nat.gcd a b).gcdA m := by
    rw [h2]; ring
  have key : (((Nat.gcd a b : ℤ) * (Nat.gcd a b).gcdA m : ℤ) : ZMod m) = 1 := by
    have hm1 : ((Nat.gcd a b : ℤ) * (Nat.gcd a b).gcdA m : ℤ)
        = 1 - (m : ℤ) * (Nat.gcd a b).gcdB m := by
      rw [Nat.cast_one] at h1
      linarith
    rw [hm1]
    push_cast
    simp [CharP.cast_eq_zero (ZMod m) m]
  have conv : ((a.gcdA b * (Nat.gcd a b).gcdA m : ℤ) : ZMod m) * (a : ZMod m)
      + ((a.gcdB b * (Nat.gcd a b).gcdA m : ℤ) : ZMod m) * (b : ZMod m)
      = (((a.gcdA b * (Nat.gcd a b).gcdA m : ℤ) * a
          + (a.gcdB b * (Nat.gcd a b).gcdA m : ℤ) * b : ℤ) : ZMod m) := by
    push_cast; ring
  rw [conv, eq]
  exact key


set_option maxHeartbeats 800000 in
theorem inv_all {T : Finset (ZMod m)} {w₁ w₂ : ZMod m} {a b : ℕ}
    (hw₁ : T + {w₁} = T) (hw₂ : T + {w₂} = T)
    (ha : w₁ = (a : ZMod m)) (hb : w₂ = (b : ZMod m))
    (hgcd : Nat.gcd (Nat.gcd a b) m = 1) :
    ∀ g : ZMod m, T + {g} = T := by
  obtain ⟨x, y, hxy⟩ := exists_comb hgcd
  have h1 : T + {(1 : ZMod m)} = T := by
    rw [← hxy]
    have hix : T + {((x : ℤ) : ZMod m) * w₁} = T := by
      rw [← zsmul_eq_mul]
      exact inv_zsmul hw₁ x
    have hiy : T + {((y : ℤ) : ZMod m) * w₂} = T := by
      rw [← zsmul_eq_mul]
      exact inv_zsmul hw₂ y
    rw [← ha, ← hb]
    exact inv_add hix hiy
  intro g
  have hg : g = ((g.val : ℤ) • (1 : ZMod m)) := by
    rw [zsmul_eq_mul]
    simp
  rw [hg]
  exact inv_zsmul h1 _


set_option maxHeartbeats 800000 in
theorem eq_univ_of_inv_all {T : Finset (ZMod m)} (hT : T.Nonempty)
    (h : ∀ g : ZMod m, T + {g} = T) : T = Finset.univ := by
  apply Finset.eq_univ_iff_forall.mpr
  intro y
  obtain ⟨t, ht⟩ := hT
  have hmem : t + (y - t) ∈ T + {y - t} :=
    Finset.add_mem_add ht (Finset.mem_singleton_self _)
  rw [h] at hmem
  have : t + (y - t) = y := by simp
  rwa [this] at hmem



open Finset List Nat BigOperators Pointwise



set_option maxHeartbeats 800000 in
theorem seg_stable {w : ZMod m} {k : ℕ} (hk : m - 1 ≤ k) :
    seg w k + {w} ⊆ seg w k := by
  intro x hx
  rw [Finset.mem_add] at hx
  obtain ⟨y, hy, z, hz, hsum⟩ := hx
  rw [Finset.mem_singleton] at hz; subst hz
  rw [← hsum]
  rw [mem_seg] at hy ⊢
  obtain ⟨j, hj, rfl⟩ := hy
  rcases Nat.lt_or_ge j k with hjk | hjk
  · exact ⟨j + 1, by omega, by push_cast; ring⟩
  · have hjk' : j = k := by omega
    rw [hjk']
    have hkm : m ≤ k + 1 := by omega
    refine ⟨k + 1 - m, by have := NeZero.ne m; omega, ?_⟩
    have e : ((k + 1 - m : ℕ) : ZMod m) = ((k + 1 : ℕ) : ZMod m) := by
      rw [Nat.cast_sub hkm, CharP.cast_eq_zero (ZMod m) m, sub_zero]
    rw [e]
    push_cast
    ring


end A084017



namespace A084017

open Finset List Nat BigOperators Pointwise


variable {m : ℕ} [NeZero m]


set_option maxHeartbeats 800000 in
theorem subset_add_of_zero_mem {S T : Finset (ZMod m)} (h0 : (0 : ZMod m) ∈ T) :
    S ⊆ S + T := by
  intro x hx
  have h := Finset.add_mem_add hx h0
  rwa [add_zero] at h

set_option maxHeartbeats 800000 in
theorem segk_invariant {S : Finset (ZMod m)} {w : ZMod m} {k : ℕ}
    (h : (S + seg w k).card < S.card + k) :
    (S + seg w k) + {w} = S + seg w k := by
  have hg := card_add_seg_ge S w k
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro x hx
    rw [Finset.mem_add] at hx
    obtain ⟨t, ht, z, hz, hsum⟩ := hx
    rw [Finset.mem_singleton] at hz
    rw [← hsum, hz]
    rw [Finset.mem_add] at ht
    obtain ⟨a', ha', b', hb', htu⟩ := ht
    rw [← htu, add_assoc]
    rcases Nat.lt_or_ge m (k + 2) with hm | hm
    · 
      have hbw : b' + w ∈ seg w k :=
        seg_stable (k := k) (by have := NeZero.ne m; omega)
          (Finset.add_mem_add hb' (Finset.mem_singleton_self w))
      exact Finset.add_mem_add ha' hbw
    · 
      have hsub : seg w k ⊆ seg w m := seg_mono (by omega)
      have hsub2 : S + seg w k ⊆ S + seg w m := Finset.add_subset_add_left hsub
      have hcard : (S + seg w m).card ≤ (S + seg w k).card := by
        have hmin : min (S.card + k) (S + seg w m).card = (S + seg w m).card := by
          apply min_eq_right
          by_contra hc
          push_neg at hc
          rw [min_eq_left (le_of_lt hc)] at hg
          omega
        rw [hmin] at hg
        exact hg
      have heq : S + seg w k = S + seg w m :=
        Finset.eq_of_subset_of_card_le hsub2 hcard
      rw [mem_seg] at hb'
      obtain ⟨j, hj, rfl⟩ := hb'
      have hbw : (↑j * w + w : ZMod m) ∈ seg w m :=
        mem_seg.mpr ⟨j + 1, by omega, by push_cast; ring⟩
      rw [heq]
      exact Finset.add_mem_add ha' hbw
  · rw [card_add_sing]

set_option maxHeartbeats 800000 in
theorem pair_covers9 {S : Finset (ZMod m)} {a b : ℕ} {w₁ w₂ : ZMod m}
    (ha : w₁ = (a : ZMod m)) (hb : w₂ = (b : ZMod m))
    (hgcd : Nat.gcd (Nat.gcd a b) m = 1) (hS0 : (0 : ZMod m) ∈ S) :
    min (S.card + 9) m ≤ (S + seg w₁ 9 + seg w₂ 9).card := by
  set T₁ := S + seg w₁ 9 with hT1
  set T₂ := T₁ + seg w₂ 9 with hT2
  have hST1 : S ⊆ T₁ := subset_add_of_zero_mem (zero_mem_seg w₁ 9)
  have hT1T2 : T₁ ⊆ T₂ := subset_add_of_zero_mem (zero_mem_seg w₂ 9)
  by_cases hbig : S.card + 9 ≤ T₁.card
  · calc min (S.card + 9) m ≤ S.card + 9 := min_le_left _ _
      _ ≤ T₂.card := le_trans hbig (Finset.card_le_card hT1T2)
  · push_neg at hbig
    have hbig' : (S + seg w₁ 9).card < S.card + 9 := by rwa [hT1] at hbig
    have hw1 : T₁ + {w₁} = T₁ := by
      rw [hT1]
      exact segk_invariant hbig'
    by_cases hbig2 : T₁.card + 9 ≤ T₂.card
    · have hs : S.card ≤ T₁.card := Finset.card_le_card hST1
      calc min (S.card + 9) m ≤ S.card + 9 := min_le_left _ _
        _ ≤ T₁.card + 9 := by omega
        _ ≤ T₂.card := hbig2
    · push_neg at hbig2
      have hbig2' : (T₁ + seg w₂ 9).card < T₁.card + 9 := by rwa [hT2] at hbig2
      have hw2 : T₂ + {w₂} = T₂ := by
        rw [hT2]
        exact segk_invariant hbig2'
      have hw1' : T₂ + {w₁} = T₂ := by
        rw [hT2, add_sing_comm, hw1]
      have hne : T₂.Nonempty := ⟨0, hT1T2 (hST1 hS0)⟩
      have hu : T₂ = Finset.univ :=
        eq_univ_of_inv_all hne (inv_all hw1' hw2 ha hb hgcd)
      rw [hu, Finset.card_univ, ZMod.card]
      exact min_le_right _ _

set_option maxHeartbeats 800000 in
theorem zero_mem_sum_seg9 (w : ℕ → ZMod m) (r : ℕ) :
    (0 : ZMod m) ∈ ∑ i ∈ Finset.range r, seg (w i) 9 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ]
    exact (zero_add (0 : ZMod m)) ▸
      Finset.add_mem_add ih (zero_mem_seg (w r) 9)

set_option maxHeartbeats 800000 in
theorem pair_covers_iter9 {S : Finset (ZMod m)} {w : ℕ → ZMod m} {a : ℕ → ℕ}
    (ha : ∀ i, w i = (a i : ZMod m))
    (hgcd : ∀ i, Nat.gcd (Nat.gcd (a (2 * i)) (a (2 * i + 1))) m = 1)
    (hS0 : (0 : ZMod m) ∈ S) (r : ℕ) :
    min (S.card + 9 * r) m ≤
      (S + ∑ i ∈ Finset.range (2 * r), seg (w i) 9).card := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h2r : 2 * (r + 1) = 2 * r + 1 + 1 := by ring
    rw [h2r, Finset.sum_range_succ, Finset.sum_range_succ]
    rw [← add_assoc, ← add_assoc]
    have hT0 : (0 : ZMod m) ∈
        S + ∑ i ∈ Finset.range (2 * r), seg (w i) 9 :=
      (zero_add (0 : ZMod m)) ▸
        Finset.add_mem_add hS0 (zero_mem_sum_seg9 w (2 * r))
    have hstep := pair_covers9 (ha (2 * r)) (ha (2 * r + 1)) (hgcd r) hT0
    have hmin : min (S.card + 9 * (r + 1)) m
        ≤ min ((S + ∑ i ∈ Finset.range (2 * r), seg (w i) 9).card + 9) m := by
      rw [show S.card + 9 * (r + 1) = (S.card + 9 * r) + 9 by ring]
      exact min_add_le_min' ih
    exact hmin.trans hstep
  where
    min_add_le_min' {x y : ℕ} (h : min x m ≤ y) :
        min (x + 9) m ≤ min (y + 9) m := by
      rcases Nat.lt_or_ge x m with hc | hc
      · rw [min_eq_left (le_of_lt hc)] at h
        exact le_min (by omega) (min_le_right _ _)
      · rw [min_eq_right hc] at h
        rw [min_eq_right (by omega : m ≤ y + 9)]
        exact min_le_right _ _

set_option maxHeartbeats 800000 in
theorem covers_univ {S : Finset (ZMod m)} {w : ℕ → ZMod m} {a : ℕ → ℕ}
    (ha : ∀ i, w i = (a i : ZMod m))
    (hgcd : ∀ i, Nat.gcd (Nat.gcd (a (2 * i)) (a (2 * i + 1))) m = 1)
    (hS0 : (0 : ZMod m) ∈ S) {r : ℕ} (hr : m ≤ S.card + 9 * r) :
    S + ∑ i ∈ Finset.range (2 * r), seg (w i) 9 = Finset.univ := by
  have h := pair_covers_iter9 ha hgcd hS0 r
  rw [min_eq_right hr] at h
  exact Finset.eq_univ_of_card _ (by
    rw [ZMod.card]
    exact le_antisymm
      (le_trans (Finset.card_le_univ _) (le_of_eq (ZMod.card m))) h)

end A084017



namespace A084017


end A084017


namespace A084017


set_option maxHeartbeats 800000 in
theorem palW_pair_factor {m L k : ℕ} (hk : 4 * k + 2 ≤ L) :
    palW m L (2 * k) - palW m L (2 * k + 1)
      = (9 : ZMod m) * (10 : ZMod m) ^ (2 * k)
          * ((10 : ZMod m) ^ (L - 2 - 4 * k) - 1) := by
  unfold palW
  have h1 : L - 1 - 2 * k = (L - 2 - 4 * k) + (2 * k + 1) := by omega
  have h2 : L - 1 - (2 * k + 1) = (L - 2 - 4 * k) + 2 * k := by omega
  rw [h1, h2, pow_add, pow_add]
  ring


end A084017

namespace A084017


set_option maxHeartbeats 800000 in
theorem gadget_val_m {m le K g : ℕ} (de : List ℕ) (hle : de.length = le)
    (e : ℕ → ℕ) (he : ∀ k, e k ≤ 9) (C : List ℕ) (hC : C.length = g) :
    Nat.ofDigits (10 : ZMod m)
      (de ++ (((List.range (2 * K)).map (pairDigit e) ++ C)
          ++ ((List.range (2 * K)).map (pairDigit e)).reverse)
        ++ de.reverse)
    = (Nat.ofDigits (10 : ZMod m) de
        + Nat.ofDigits (10 : ZMod m) de.reverse * (10 : ZMod m) ^ (le + (4 * K + g)))
      + (10 : ZMod m) ^ le
          * (Nat.ofDigits (10 : ZMod m) C * (10 : ZMod m) ^ (2 * K)
            + ∑ k ∈ Finset.range K,
                ((9 : ZMod m) * palW m (4 * K + g) (2 * k + 1)
                + (e k : ZMod m)
                    * (palW m (4 * K + g) (2 * k) - palW m (4 * K + g) (2 * k + 1)))) := by
  set G := (List.range (2 * K)).map (pairDigit e) with hG
  set X := (G ++ C) ++ G.reverse with hX
  have hGl : G.length = 2 * K := by rw [hG, List.length_map, List.length_range]
  have hXl : X.length = 4 * K + g := by
    rw [hX, List.length_append, List.length_append, hGl,
      List.length_reverse, hGl, hC]; ring
  have hlen : (de ++ X).length = le + (4 * K + g) := by
    rw [List.length_append, hle, hXl]
  rw [ofDigits_append', ofDigits_append', hlen]
  have hInner := ofDigits_pair_center (m := m) (K := K) (g := g) e he C hC
  rw [← hG] at hInner
  rw [hX, hInner, hle]
  ring

end A084017

namespace A084017
open Finset List Nat BigOperators Pointwise
variable {m : ℕ} [NeZero m]


set_option maxHeartbeats 800000 in
theorem mem_sum_seg {w : ℕ → ZMod m} {r : ℕ} {x : ZMod m}
    (hx : x ∈ ∑ i ∈ Finset.range r, seg (w i) 9) :
    ∃ d : ℕ → ℕ, (∀ i, d i ≤ 9)
      ∧ x = ∑ i ∈ Finset.range r, (d i : ZMod m) * w i := by
  induction r generalizing x with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty, mem_zero] at hx
    exact ⟨fun _ => 0, fun _ => Nat.zero_le 9, by simpa using hx⟩
  | succ r ih =>
    rw [Finset.sum_range_succ] at hx
    rw [Finset.mem_add] at hx
    obtain ⟨y, hy, z, hz, hsum⟩ := hx
    obtain ⟨d, hd, hx'⟩ := ih hy
    rw [mem_seg] at hz
    obtain ⟨j, hj, rfl⟩ := hz
    refine ⟨Function.update d r j, ?_, ?_⟩
    · intro i
      by_cases hi : i = r
      · rw [hi, Function.update_self]; exact hj
      · rw [Function.update_of_ne hi]; exact hd i
    · rw [← hsum, hx', Finset.sum_range_succ]
      rw [Function.update_self]
      rw [add_right_cancel_iff]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [Function.update_of_ne (by omega : i ≠ r)]

end A084017

namespace A084017
open Finset List Nat BigOperators Pointwise
variable {m : ℕ} [NeZero m]


end A084017


namespace A084017
open Finset List Nat BigOperators Pointwise
variable {M : ℕ} [NeZero M]


set_option maxHeartbeats 800000 in
theorem nine_mul_repunit (t : ℕ) : 9 * ((10 ^ t - 1) / 9) = 10 ^ t - 1 := by
  have h9 : 9 ∣ 10 ^ t - 1 := by
    have hm : (10 : ℕ) ≡ 1 [MOD 9] := by decide
    have h2 : (10 : ℕ) ^ t ≡ 1 ^ t [MOD 9] := hm.pow t
    rw [one_pow] at h2
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow t 10 (by norm_num))).mp h2.symm
  exact Nat.mul_div_cancel' h9


set_option maxHeartbeats 800000 in
theorem repunit_gcd (a b : ℕ) :
    Nat.gcd ((10 ^ a - 1) / 9) ((10 ^ b - 1) / 9)
      = (10 ^ Nat.gcd a b - 1) / 9 := by
  have h9a := nine_mul_repunit a
  have h9b := nine_mul_repunit b
  have h9g := nine_mul_repunit (Nat.gcd a b)
  have h := Nat.gcd_mul_left 9 ((10 ^ a - 1) / 9) ((10 ^ b - 1) / 9)
  rw [h9a, h9b, Nat.pow_sub_one_gcd_pow_sub_one] at h
  rw [← h9g] at h
  exact (Nat.mul_left_cancel (by norm_num : 0 < 9) h).symm


set_option maxHeartbeats 800000 in
theorem repunit_succ (t : ℕ) :
    (10 ^ (t + 1) - 1) / 9 = 10 * ((10 ^ t - 1) / 9) + 1 := by
  have h9 := nine_mul_repunit t
  have h10 := nine_mul_repunit (t + 1)
  have hA : 9 * ((10 ^ (t + 1) - 1) / 9) = 9 * (10 * ((10 ^ t - 1) / 9) + 1) := by
    rw [h10]
    have hcalc : 10 ^ (t + 1) - 1 = 9 * (10 * ((10 ^ t - 1) / 9) + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      have e1 : 9 * (10 * ((10 ^ t - 1) / 9)) = 10 * (10 ^ t - 1) := by
        rw [Nat.mul_left_comm, h9]
      rw [e1]
      have hp : 1 ≤ 10 ^ t := Nat.one_le_pow t 10 (by norm_num)
      rw [Nat.mul_sub, Nat.mul_one, pow_succ]
      omega
    exact hcalc
  exact Nat.mul_left_cancel (by norm_num : 0 < 9) hA


set_option maxHeartbeats 800000 in
theorem repunit_coprime10 {t : ℕ} (ht : 1 ≤ t) :
    Nat.Coprime ((10 ^ t - 1) / 9) 10 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  rw [Nat.succ_eq_add_one, repunit_succ]
  have h : (10 : ℕ).Coprime (1 + ((10 ^ t - 1) / 9) * 10) :=
    (Nat.coprime_add_mul_right_right 10 1 _).mpr (Nat.coprime_one_right 10)
  have e : 10 * ((10 ^ t - 1) / 9) + 1 = 1 + ((10 ^ t - 1) / 9) * 10 := by ring
  rw [e]
  exact h.symm

end A084017

namespace A084017
open Finset List Nat BigOperators Pointwise
variable {M : ℕ} [NeZero M]


set_option maxHeartbeats 800000 in
theorem gadget_extract3 {K g : ℕ} (hM10 : M.Coprime 10)
    (hg3 : 3 ≤ g) (hgodd : Odd g)
    (hK : M ≤ 1 + 9 * (K / 2)) (t : ZMod M) :
    ∃ e : ℕ → ℕ, (∀ k, e k ≤ 9)
      ∧ (∑ k ∈ Finset.range K, (e k : ZMod M)
          * (((10 : ℕ) ^ (2 * k)
              * ((10 ^ (4 * K + g - 2 - 4 * k) - 1) / 9) : ℕ) : ZMod M)) = t := by
  set L := 4 * K + g with hL
  set r := K / 2 with hr
  set a : ℕ → ℕ := fun i =>
    if i < K then 10 ^ (2 * i) * ((10 ^ (L - 2 - 4 * i) - 1) / 9) else 1 with ha
  set w : ℕ → ZMod M := fun i => (a i : ZMod M) with hw
  
  have hDg : ∀ i, 2 * i + 1 < K
      → Nat.gcd (L - 2 - 4 * (2 * i)) (L - 2 - 4 * (2 * i + 1)) = 1 := by
    intro i hi
    obtain ⟨c, hc⟩ := hgodd
    have hD1pos : 1 ≤ L - 2 - 4 * (2 * i + 1) := by
      rw [hL]; omega
    have hD2 : L - 2 - 4 * (2 * i) = (L - 2 - 4 * (2 * i + 1)) + 4 := by omega
    have hodd : Odd (L - 2 - 4 * (2 * i + 1)) := by
      refine ⟨2 * K + c - 4 * i - 3, ?_⟩
      rw [hL]
      omega
    rw [hD2, Nat.gcd_self_add_left]
    have hd : Nat.gcd 4 (L - 2 - 4 * (2 * i + 1)) ∈ Nat.divisors 4 :=
      Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _, by norm_num⟩
    rw [show Nat.divisors 4 = {1, 2, 4} from by decide,
      Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with h1 | h2 | h4'
    · exact h1
    · exfalso
      have hgd : Nat.gcd 4 (L - 2 - 4 * (2 * i + 1)) ∣ L - 2 - 4 * (2 * i + 1) :=
        Nat.gcd_dvd_right _ _
      rw [h2] at hgd
      obtain ⟨c', hc'⟩ := hodd
      omega
    · exfalso
      have hgd : Nat.gcd 4 (L - 2 - 4 * (2 * i + 1)) ∣ L - 2 - 4 * (2 * i + 1) :=
        Nat.gcd_dvd_right _ _
      rw [h4'] at hgd
      obtain ⟨c', hc'⟩ := hodd
      omega
  have haw : ∀ i, w i = (a i : ZMod M) := fun i => rfl
  have hgcd : ∀ i, Nat.gcd (Nat.gcd (a (2 * i)) (a (2 * i + 1))) M = 1 := by
    intro i
    by_cases hi : 2 * i + 1 < K
    · rw [ha]; dsimp only
      rw [if_pos (by omega : 2 * i < K), if_pos hi]
      have hD1 : 1 ≤ L - 2 - 4 * (2 * i) := by rw [hL]; omega
      have hD2 : 1 ≤ L - 2 - 4 * (2 * i + 1) := by rw [hL]; omega
      
      have hg : Nat.gcd (10 ^ (2 * (2 * i)) * ((10 ^ (L - 2 - 4 * (2 * i)) - 1) / 9))
          (10 ^ (2 * (2 * i + 1)) * ((10 ^ (L - 2 - 4 * (2 * i + 1)) - 1) / 9))
          = 10 ^ (4 * i) := by
        have e1 : 2 * (2 * i + 1) = 4 * i + 2 := by ring
        have e2 : 2 * (2 * i) = 4 * i := by ring
        rw [e1, e2, pow_add, Nat.mul_assoc, Nat.gcd_mul_left]
        have hc10 : Nat.Coprime ((10 ^ (L - 2 - 4 * (2 * i)) - 1) / 9) (10 ^ 2) :=
          (repunit_coprime10 hD1).pow_right 2
        rw [show Nat.gcd ((10 ^ (L - 2 - 4 * (2 * i)) - 1) / 9)
            (10 ^ 2 * ((10 ^ (L - 2 - 4 * (2 * i + 1)) - 1) / 9))
            = Nat.gcd (10 ^ 2 * ((10 ^ (L - 2 - 4 * (2 * i + 1)) - 1) / 9))
              ((10 ^ (L - 2 - 4 * (2 * i)) - 1) / 9) from Nat.gcd_comm _ _]
        rw [Nat.Coprime.gcd_mul_left_cancel
          ((10 ^ (L - 2 - 4 * (2 * i + 1)) - 1) / 9) hc10.symm]
        rw [Nat.gcd_comm, repunit_gcd, hDg i hi]
        simp
      rw [hg]
      exact (hM10.pow_right (4 * i)).symm
    · rw [ha]; dsimp only
      rw [if_neg (by omega : ¬ 2 * i + 1 < K)]
      simp
  have hS0 : (0 : ZMod M) ∈ ({0} : Finset (ZMod M)) := Finset.mem_singleton_self 0
  have hcard : ({0} : Finset (ZMod M)).card = 1 := Finset.card_singleton 0
  have hcover : ({0} : Finset (ZMod M))
      + ∑ i ∈ Finset.range (2 * r), seg (w i) 9 = Finset.univ :=
    covers_univ (m := M) haw hgcd hS0 (r := r) (by rw [hcard]; omega)
  have ht : t ∈ ({0} : Finset (ZMod M))
      + ∑ i ∈ Finset.range (2 * r), seg (w i) 9 := by
    rw [hcover]; exact Finset.mem_univ t
  rw [Finset.mem_add] at ht
  obtain ⟨s, hs, c', hc', hsum⟩ := ht
  rw [Finset.mem_singleton] at hs
  obtain ⟨d, hd, hcx⟩ := mem_sum_seg hc'
  refine ⟨fun k => if k < 2 * r then d k else 0, ?_, ?_⟩
  · intro k
    by_cases hk : k < 2 * r
    · simp only [hk, ite_true]; exact hd k
    · simp only [hk, ite_false]; exact Nat.zero_le 9
  · have hsub : ∑ k ∈ Finset.range K,
          ((if k < 2 * r then d k else 0 : ℕ) : ZMod M)
          * (((10 : ℕ) ^ (2 * k)
              * ((10 ^ (4 * K + g - 2 - 4 * k) - 1) / 9) : ℕ) : ZMod M)
        = ∑ k ∈ Finset.range (2 * r), (d k : ZMod M)
          * (((10 : ℕ) ^ (2 * k)
              * ((10 ^ (4 * K + g - 2 - 4 * k) - 1) / 9) : ℕ) : ZMod M) := by
      have hss : Finset.range (2 * r) ⊆ Finset.range K := by
        intro x hx; rw [Finset.mem_range] at hx ⊢; omega
      rw [← Finset.sum_subset hss (fun k hk hk2 => by
        rw [if_neg (mt Finset.mem_range.mpr hk2), Nat.cast_zero, zero_mul])]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [if_pos (Finset.mem_range.mp hk)]
    rw [hsub]
    have hwr : ∑ k ∈ Finset.range (2 * r), (d k : ZMod M)
          * (((10 : ℕ) ^ (2 * k)
              * ((10 ^ (4 * K + g - 2 - 4 * k) - 1) / 9) : ℕ) : ZMod M)
        = ∑ k ∈ Finset.range (2 * r), (d k : ZMod M) * w k := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      rw [hw, ha]; dsimp only
      rw [if_pos (by omega : k < K)]
    rw [hwr]
    rw [← hcx, ← hsum, hs, zero_add]


set_option maxHeartbeats 800000 in
theorem gadget_extract3_even {K g : ℕ} (hM10 : M.Coprime 10)
    (hM11 : M.Coprime 11) (hM101 : M.Coprime 101)
    (hg3 : 3 ≤ g) (hgev : Even g)
    (hK : M ≤ 1 + 9 * (K / 2)) (t : ZMod M) :
    ∃ e : ℕ → ℕ, (∀ k, e k ≤ 9)
      ∧ (∑ k ∈ Finset.range K, (e k : ZMod M)
          * (((10 : ℕ) ^ (2 * k)
              * ((10 ^ (4 * K + g - 2 - 4 * k) - 1) / 9) : ℕ) : ZMod M)) = t := by
  set L := 4 * K + g with hL
  set r := K / 2 with hr
  set a : ℕ → ℕ := fun i =>
    if i < K then 10 ^ (2 * i) * ((10 ^ (L - 2 - 4 * i) - 1) / 9) else 1 with ha
  set w : ℕ → ZMod M := fun i => (a i : ZMod M) with hw
  have hDg : ∀ i, 2 * i + 1 < K
      → Nat.gcd (L - 2 - 4 * (2 * i)) (L - 2 - 4 * (2 * i + 1)) = 2
        ∨ Nat.gcd (L - 2 - 4 * (2 * i)) (L - 2 - 4 * (2 * i + 1)) = 4 := by
    intro i hi
    obtain ⟨c, hc⟩ := hgev
    have hD2 : L - 2 - 4 * (2 * i) = (L - 2 - 4 * (2 * i + 1)) + 4 := by omega
    have hev : 2 ∣ L - 2 - 4 * (2 * i + 1) := by
      refine ⟨2 * K + c - 4 * i - 3, ?_⟩
      rw [hL]
      omega
    rw [hD2, Nat.gcd_self_add_left]
    have hd : Nat.gcd 4 (L - 2 - 4 * (2 * i + 1)) ∈ Nat.divisors 4 :=
      Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _, by norm_num⟩
    rw [show Nat.divisors 4 = {1, 2, 4} from by decide,
      Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with h1 | h2 | h4'
    · exfalso
      have hgd : (2 : ℕ) ∣ Nat.gcd 4 (L - 2 - 4 * (2 * i + 1)) :=
        Nat.dvd_gcd (by norm_num) hev
      rw [h1] at hgd
      norm_num at hgd
    · exact Or.inl h2
    · exact Or.inr h4'
  have haw : ∀ i, w i = (a i : ZMod M) := fun i => rfl
  have hM1111 : M.Coprime 1111 := by
    have h := Nat.coprime_mul_iff_right.mpr ⟨hM11, hM101⟩
    rwa [show (1111 : ℕ) = 11 * 101 from by norm_num]
  have hgcd : ∀ i, Nat.gcd (Nat.gcd (a (2 * i)) (a (2 * i + 1))) M = 1 := by
    intro i
    by_cases hi : 2 * i + 1 < K
    · rw [ha]; dsimp only
      rw [if_pos (by omega : 2 * i < K), if_pos hi]
      have hD1 : 1 ≤ L - 2 - 4 * (2 * i) := by rw [hL]; omega
      have hD2 : 1 ≤ L - 2 - 4 * (2 * i + 1) := by rw [hL]; omega
      have hg : Nat.gcd (10 ^ (2 * (2 * i)) * ((10 ^ (L - 2 - 4 * (2 * i)) - 1) / 9))
          (10 ^ (2 * (2 * i + 1)) * ((10 ^ (L - 2 - 4 * (2 * i + 1)) - 1) / 9))
          = 10 ^ (4 * i) * ((10 ^ Nat.gcd (L - 2 - 4 * (2 * i))
              (L - 2 - 4 * (2 * i + 1)) - 1) / 9) := by
        have e1 : 2 * (2 * i + 1) = 4 * i + 2 := by ring
        have e2 : 2 * (2 * i) = 4 * i := by ring
        rw [e1, e2, pow_add, Nat.mul_assoc, Nat.gcd_mul_left]
        have hc10 : Nat.Coprime ((10 ^ (L - 2 - 4 * (2 * i)) - 1) / 9) (10 ^ 2) :=
          (repunit_coprime10 hD1).pow_right 2
        rw [show Nat.gcd ((10 ^ (L - 2 - 4 * (2 * i)) - 1) / 9)
            (10 ^ 2 * ((10 ^ (L - 2 - 4 * (2 * i + 1)) - 1) / 9))
            = Nat.gcd (10 ^ 2 * ((10 ^ (L - 2 - 4 * (2 * i + 1)) - 1) / 9))
              ((10 ^ (L - 2 - 4 * (2 * i)) - 1) / 9) from Nat.gcd_comm _ _]
        rw [Nat.Coprime.gcd_mul_left_cancel
          ((10 ^ (L - 2 - 4 * (2 * i + 1)) - 1) / 9) hc10.symm]
        rw [Nat.gcd_comm, repunit_gcd]
      rw [hg, Nat.Coprime.gcd_mul_left_cancel _ (hM10.pow_right (4 * i)).symm]
      rcases hDg i hi with h2 | h4
      · rw [h2, show ((10 ^ 2 - 1) / 9 : ℕ) = 11 from by norm_num, Nat.gcd_comm]
        exact Nat.coprime_iff_gcd_eq_one.mp hM11
      · rw [h4, show ((10 ^ 4 - 1) / 9 : ℕ) = 1111 from by norm_num, Nat.gcd_comm]
        exact Nat.coprime_iff_gcd_eq_one.mp hM1111
    · rw [ha]; dsimp only
      rw [if_neg (by omega : ¬ 2 * i + 1 < K)]
      simp
  have hS0 : (0 : ZMod M) ∈ ({0} : Finset (ZMod M)) := Finset.mem_singleton_self 0
  have hcard : ({0} : Finset (ZMod M)).card = 1 := Finset.card_singleton 0
  have hcover : ({0} : Finset (ZMod M))
      + ∑ i ∈ Finset.range (2 * r), seg (w i) 9 = Finset.univ :=
    covers_univ (m := M) haw hgcd hS0 (r := r) (by rw [hcard]; omega)
  have ht : t ∈ ({0} : Finset (ZMod M))
      + ∑ i ∈ Finset.range (2 * r), seg (w i) 9 := by
    rw [hcover]; exact Finset.mem_univ t
  rw [Finset.mem_add] at ht
  obtain ⟨s, hs, c', hc', hsum⟩ := ht
  rw [Finset.mem_singleton] at hs
  obtain ⟨d, hd, hcx⟩ := mem_sum_seg hc'
  refine ⟨fun k => if k < 2 * r then d k else 0, ?_, ?_⟩
  · intro k
    by_cases hk : k < 2 * r
    · simp only [hk, ite_true]; exact hd k
    · simp only [hk, ite_false]; exact Nat.zero_le 9
  · have hsub : ∑ k ∈ Finset.range K,
          ((if k < 2 * r then d k else 0 : ℕ) : ZMod M)
          * (((10 : ℕ) ^ (2 * k)
              * ((10 ^ (4 * K + g - 2 - 4 * k) - 1) / 9) : ℕ) : ZMod M)
        = ∑ k ∈ Finset.range (2 * r), (d k : ZMod M)
          * (((10 : ℕ) ^ (2 * k)
              * ((10 ^ (4 * K + g - 2 - 4 * k) - 1) / 9) : ℕ) : ZMod M) := by
      have hss : Finset.range (2 * r) ⊆ Finset.range K := by
        intro x hx; rw [Finset.mem_range] at hx ⊢; omega
      rw [← Finset.sum_subset hss (fun k hk hk2 => by
        rw [if_neg (mt Finset.mem_range.mpr hk2), Nat.cast_zero, zero_mul])]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [if_pos (Finset.mem_range.mp hk)]
    rw [hsub]
    have hwr : ∑ k ∈ Finset.range (2 * r), (d k : ZMod M)
          * (((10 : ℕ) ^ (2 * k)
              * ((10 ^ (4 * K + g - 2 - 4 * k) - 1) / 9) : ℕ) : ZMod M)
        = ∑ k ∈ Finset.range (2 * r), (d k : ZMod M) * w k := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      rw [hw, ha]; dsimp only
      rw [if_pos (by omega : k < K)]
    rw [hwr]
    rw [← hcx, ← hsum, hs, zero_add]

end A084017


namespace A084017
open Finset List Nat BigOperators Pointwise


end A084017


namespace A084017
open Finset List Nat BigOperators Pointwise


end A084017


namespace A084017
open Finset List Nat BigOperators Pointwise


set_option maxHeartbeats 800000 in
theorem ofDigits_rep9 (j : ℕ) :
    Nat.ofDigits 10 (List.replicate j 9) = 10 ^ j - 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [List.replicate_succ, Nat.ofDigits_cons, ih, pow_succ]
    have h1 : 1 ≤ 10 ^ j := Nat.one_le_pow _ _ (by norm_num)
    omega


set_option maxHeartbeats 800000 in
theorem pow3_sub_one (y : ℕ) (hy : 1 ≤ y) :
    y ^ 3 - 1 = (y - 1) * (y ^ 2 + y + 1) := by
  have hy3 : 1 ≤ y ^ 3 := Nat.one_le_pow _ _ hy
  zify [hy, hy3]
  ring


set_option maxHeartbeats 800000 in
theorem three_pow2_dvd_pow10_sub_one (k : ℕ) :
    3 ^ (k + 2) ∣ 10 ^ (3 ^ k) - 1 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    obtain ⟨t, ht⟩ := ih
    have h1 : 1 ≤ 10 ^ (3 ^ k) := Nat.one_le_pow _ _ (by norm_num)
    have h2 : (10 : ℕ) ^ (3 ^ (k + 1)) = (10 ^ (3 ^ k)) ^ 3 := by
      rw [pow_succ, pow_mul]
    rw [h2, pow3_sub_one _ h1, ht]
    
    have hxmod : (10 ^ (3 ^ k)) % 3 = 1 := by
      rw [Nat.pow_mod]; norm_num
    obtain ⟨q, hq⟩ : ∃ q, 10 ^ (3 ^ k) = 3 * q + 1 :=
      ⟨(10 ^ (3 ^ k) - 1) / 3, by
        have := Nat.div_add_mod (10 ^ (3 ^ k)) 3
        omega⟩
    rw [hq]
    
    use t * (3 * q * q + 3 * q + 1)
    rw [pow_succ 3 (k + 2)]
    ring


set_option maxHeartbeats 800000 in
theorem pow3v_dvd_pow10_sub_one {v j : ℕ} (hv : 2 ≤ v) (hj : 3 ^ (v - 2) ∣ j) :
    3 ^ v ∣ 10 ^ j - 1 := by
  obtain ⟨t, rfl⟩ := hj
  rw [pow_mul]
  obtain ⟨s, hs⟩ := three_pow2_dvd_pow10_sub_one (v - 2)
  rw [Nat.sub_add_cancel hv] at hs
  have h10 : 1 ≤ 10 ^ (3 ^ (v - 2)) := Nat.one_le_pow _ _ (by norm_num)
  have hx : (10 : ℕ) ^ (3 ^ (v - 2)) = 1 + 3 ^ v * s := by omega
  rw [hx]
  have hns : (3 ^ v * s : ℕ) ≡ 0 [MOD 3 ^ v] :=
    Nat.modEq_zero_iff_dvd.mpr (Nat.dvd_mul_right _ _)
  have hxmod1 : (1 + 3 ^ v * s : ℕ) ≡ 1 [MOD 3 ^ v] := by
    have h := (Nat.ModEq.refl 1).add hns
    simpa using h
  have hmod : (1 + 3 ^ v * s : ℕ) ^ t ≡ 1 [MOD 3 ^ v] := by
    induction t with
    | zero => rfl
    | succ t iht =>
      rw [pow_succ]
      simpa using Nat.ModEq.mul iht hxmod1
  have hle : 1 ≤ (1 + 3 ^ v * s) ^ t := Nat.one_le_pow _ _ (by omega)
  exact (Nat.modEq_iff_dvd' hle).mp hmod.symm

end A084017

namespace A084017
open Finset List Nat BigOperators Pointwise


set_option maxHeartbeats 800000 in
theorem center_repunit_val (j T : ℕ) :
    Nat.ofDigits 10 (List.replicate j 9 ++ List.replicate T 0 ++ [0]
        ++ List.replicate T 0 ++ List.replicate j 9)
      = (10 ^ j - 1) * (1 + 10 ^ (j + 2 * T + 1)) := by
  have h1 : Nat.ofDigits 10 (List.replicate j 9 ++ List.replicate T 0 ++ [0]
      ++ List.replicate T 0) = 10 ^ j - 1 := by
    rw [Nat.ofDigits_append_replicate_zero, Nat.ofDigits_append,
      Nat.ofDigits_append_replicate_zero, ofDigits_rep9]
    simp [Nat.ofDigits]
  have hlen : ((List.replicate j 9 ++ List.replicate T 0 ++ [0]
      ++ List.replicate T 0) : List ℕ).length = j + 2 * T + 1 := by
    simp [List.length_append, List.length_replicate]
    omega
  rw [Nat.ofDigits_append, h1, ofDigits_rep9, hlen]
  rw [mul_add, mul_one, mul_comm (10 ^ (j + 2 * T + 1)) (10 ^ j - 1)]

set_option maxHeartbeats 800000 in
theorem center_repunit_len_sum (j T : ℕ) :
    (List.replicate j 9 ++ List.replicate T 0 ++ [0]
        ++ List.replicate T 0 ++ List.replicate j 9).length = 2 * j + 2 * T + 1
    ∧ (List.replicate j 9 ++ List.replicate T 0 ++ [0]
        ++ List.replicate T 0 ++ List.replicate j 9).sum = 18 * j := by
  constructor
  · simp [List.length_append, List.length_replicate]
    omega
  · simp only [List.sum_append, List.sum_replicate, nsmul_eq_mul,
      List.sum_cons, List.sum_nil, Nat.cast_id]
    ring

set_option maxHeartbeats 800000 in
theorem center_repunit_pal (j T : ℕ) :
    (List.replicate j 9 ++ List.replicate T 0 ++ [0]
        ++ List.replicate T 0 ++ List.replicate j 9).Palindrome := by
  apply List.Palindrome.of_reverse_eq
  simp only [List.reverse_append, List.reverse_replicate, List.reverse_cons,
    List.reverse_nil, List.append_assoc, List.cons_append, List.nil_append,
    List.singleton_append]

set_option maxHeartbeats 800000 in
theorem center_repunit_lt10 (j T : ℕ) :
    ∀ x ∈ (List.replicate j 9 ++ List.replicate T 0 ++ [0]
        ++ List.replicate T 0 ++ List.replicate j 9), x < 10 := by
  intro x hx
  simp only [List.mem_append, List.mem_replicate, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  omega


set_option maxHeartbeats 800000 in
theorem center_repunit_dvd3 {v j T : ℕ} (hv : 2 ≤ v) (hj : 3 ^ (v - 2) ∣ j) :
    3 ^ v ∣ Nat.ofDigits 10 (List.replicate j 9 ++ List.replicate T 0 ++ [0]
        ++ List.replicate T 0 ++ List.replicate j 9) := by
  rw [center_repunit_val]
  exact dvd_mul_of_dvd_left (pow3v_dvd_pow10_sub_one hv hj) _

end A084017


namespace A084017
open Finset List Nat BigOperators Pointwise


set_option maxHeartbeats 800000 in
theorem center_repunit_even_val (j T : ℕ) :
    Nat.ofDigits 10 (List.replicate j 9 ++ List.replicate T 0
        ++ List.replicate T 0 ++ List.replicate j 9)
      = (10 ^ j - 1) * (1 + 10 ^ (j + 2 * T)) := by
  have h1 : Nat.ofDigits 10 (List.replicate j 9 ++ List.replicate T 0
      ++ List.replicate T 0) = 10 ^ j - 1 := by
    rw [Nat.ofDigits_append_replicate_zero, Nat.ofDigits_append_replicate_zero,
      ofDigits_rep9]
  have hlen : ((List.replicate j 9 ++ List.replicate T 0
      ++ List.replicate T 0) : List ℕ).length = j + 2 * T := by
    simp [List.length_append, List.length_replicate]
    omega
  rw [Nat.ofDigits_append, h1, ofDigits_rep9, hlen]
  rw [mul_add, mul_one, mul_comm (10 ^ (j + 2 * T)) (10 ^ j - 1)]

set_option maxHeartbeats 800000 in
theorem center_repunit_even_len_sum (j T : ℕ) :
    (List.replicate j 9 ++ List.replicate T 0
        ++ List.replicate T 0 ++ List.replicate j 9).length = 2 * j + 2 * T
    ∧ (List.replicate j 9 ++ List.replicate T 0
        ++ List.replicate T 0 ++ List.replicate j 9).sum = 18 * j := by
  constructor
  · simp [List.length_append, List.length_replicate]
    omega
  · simp only [List.sum_append, List.sum_replicate, nsmul_eq_mul, Nat.cast_id]
    ring

set_option maxHeartbeats 800000 in
theorem center_repunit_even_pal (j T : ℕ) :
    (List.replicate j 9 ++ List.replicate T 0
        ++ List.replicate T 0 ++ List.replicate j 9).Palindrome := by
  apply List.Palindrome.of_reverse_eq
  simp only [List.reverse_append, List.reverse_replicate, List.append_assoc]

set_option maxHeartbeats 800000 in
theorem center_repunit_even_lt10 (j T : ℕ) :
    ∀ x ∈ (List.replicate j 9 ++ List.replicate T 0
        ++ List.replicate T 0 ++ List.replicate j 9), x < 10 := by
  intro x hx
  simp only [List.mem_append, List.mem_replicate] at hx
  omega

set_option maxHeartbeats 800000 in
theorem center_repunit_even_dvd3 {v j T : ℕ} (hv : 2 ≤ v) (hj : 3 ^ (v - 2) ∣ j) :
    3 ^ v ∣ Nat.ofDigits 10 (List.replicate j 9 ++ List.replicate T 0
        ++ List.replicate T 0 ++ List.replicate j 9) := by
  rw [center_repunit_even_val]
  exact dvd_mul_of_dvd_left (pow3v_dvd_pow10_sub_one hv hj) _

end A084017


namespace A084017
open Finset List Nat BigOperators Pointwise


set_option maxHeartbeats 800000 in
theorem ofDigits_add_complement (L : List ℕ) (hL : ∀ d ∈ L, d ≤ 9) :
    Nat.ofDigits 10 L + Nat.ofDigits 10 (L.map (9 - ·)) = 10 ^ L.length - 1 := by
  induction L with
  | nil => simp
  | cons d t ih =>
    have hd : d ≤ 9 := hL d List.mem_cons_self
    have ht : ∀ x ∈ t, x ≤ 9 := fun x hx => hL x (List.mem_cons_of_mem _ hx)
    rw [List.map_cons, Nat.ofDigits_cons, Nat.ofDigits_cons, List.length_cons,
      pow_succ]
    have h1 : 1 ≤ 10 ^ t.length := Nat.one_le_pow _ _ (by norm_num)
    have := ih ht
    omega


set_option maxHeartbeats 800000 in
theorem digits_pow10_sub {B u : ℕ} (hB : B ≠ 0) (hBu : B ≤ 10 ^ u)
    (hlen : (Nat.digits 10 (B - 1)).length < u) :
    Nat.digits 10 (10 ^ u - B)
      = (Nat.digits 10 (B - 1)
          ++ List.replicate (u - (Nat.digits 10 (B - 1)).length) 0).map (9 - ·) := by
  set D := Nat.digits 10 (B - 1) with hD
  have hlt : ∀ l ∈ D, l < 10 := fun l hl =>
    Nat.digits_lt_base (by norm_num) hl
  have hlt' : ∀ l ∈ D ++ List.replicate (u - D.length) 0, l ≤ 9 := by
    intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · have := hlt l hl
      omega
    · have := (List.mem_replicate.mp hl).2
      omega
  have hval : Nat.ofDigits 10
        ((D ++ List.replicate (u - D.length) 0).map (9 - ·)) = 10 ^ u - B := by
    have hcomp := ofDigits_add_complement (D ++ List.replicate (u - D.length) 0)
      hlt'
    rw [List.length_append, List.length_replicate,
      Nat.add_sub_of_le (Nat.le_of_lt hlen), Nat.ofDigits_append_replicate_zero,
      Nat.ofDigits_digits] at hcomp
    have hB1 : 1 ≤ B := Nat.one_le_iff_ne_zero.mpr hB
    have h10 : 1 ≤ 10 ^ u := Nat.one_le_pow _ _ (by norm_num)
    omega
  have hdig := Nat.digits_ofDigits 10 (by norm_num : 1 < 10)
    ((D ++ List.replicate (u - D.length) 0).map (9 - ·)) ?_ ?_
  · rw [hval] at hdig
    exact hdig
  · intro l hl
    rw [List.mem_map] at hl
    obtain ⟨x, hx, rfl⟩ := hl
    have := hlt' x hx
    omega
  · 
    intro hnil
    have hrep : List.replicate (u - D.length) 0 ≠ [] := by
      intro h
      rw [List.replicate_eq_nil_iff] at h
      omega
    rw [List.getLast_map, List.getLast_append_of_right_ne_nil _ _ hrep,
      List.getLast_replicate]
    norm_num

end A084017

namespace A084017
open Finset List Nat BigOperators Pointwise


end A084017


namespace A084017
open Finset List Nat BigOperators Pointwise


end A084017

namespace A084017
open Finset List Nat BigOperators Pointwise


end A084017


namespace A084017
open Finset List Nat BigOperators Pointwise


set_option maxHeartbeats 800000 in
theorem mid_pal {K : ℕ} (e : ℕ → ℕ) (C : List ℕ) (hC : C.Palindrome) :
    ((List.range (2 * K)).map (pairDigit e) ++ C
      ++ ((List.range (2 * K)).map (pairDigit e)).reverse).Palindrome := by
  apply List.Palindrome.of_reverse_eq
  rw [List.reverse_append, List.reverse_append, List.reverse_reverse,
    hC.reverse_eq, List.append_assoc]


set_option maxHeartbeats 800000 in
theorem mid_lt10 {K : ℕ} (e : ℕ → ℕ) (he : ∀ k, e k ≤ 9) (C : List ℕ)
    (hC : ∀ x ∈ C, x < 10) :
    ∀ x ∈ (List.range (2 * K)).map (pairDigit e) ++ C
      ++ ((List.range (2 * K)).map (pairDigit e)).reverse, x < 10 := by
  have hpd : ∀ i, pairDigit e i < 10 := by
    intro i
    unfold pairDigit
    by_cases h : i % 2 = 0
    · rw [if_pos h]
      have := he (i / 2)
      omega
    · rw [if_neg h]
      have := he (i / 2)
      omega
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · rcases List.mem_append.mp hx with hx | hx
    · rw [List.mem_map] at hx
      obtain ⟨i, _, rfl⟩ := hx
      exact hpd i
    · exact hC x hx
  · rw [List.mem_reverse, List.mem_map] at hx
    obtain ⟨i, _, rfl⟩ := hx
    exact hpd i


set_option maxHeartbeats 800000 in
theorem pairDigit_sum (e : ℕ → ℕ) (he : ∀ k, e k ≤ 9) (K : ℕ) :
    ((List.range (2 * K)).map (pairDigit e)).sum = 9 * K := by
  induction K with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, List.range_add,
      List.map_append, List.sum_append, ih]
    have hr2 : (List.range 2).map (2 * k + ·) = [2 * k, 2 * k + 1] := by
      rw [List.range_succ, List.range_succ, List.range_zero]
      simp [List.map_cons, List.map_nil]
    rw [hr2]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero]
    rw [pairDigit_even, pairDigit_odd]
    have := he k
    omega


set_option maxHeartbeats 800000 in
theorem mid_sum {K : ℕ} (e : ℕ → ℕ) (he : ∀ k, e k ≤ 9) (C : List ℕ) :
    ((List.range (2 * K)).map (pairDigit e) ++ C
      ++ ((List.range (2 * K)).map (pairDigit e)).reverse).sum
      = 18 * K + C.sum := by
  rw [List.sum_append, List.sum_append, List.sum_reverse,
    pairDigit_sum e he]
  ring

end A084017


namespace A084017
open Finset List Nat BigOperators Pointwise


set_option maxHeartbeats 800000 in
theorem sum_twt_81 {q K g : ℕ} (e : ℕ → ℕ) :
    ∑ k ∈ Finset.range K, (e k : ZMod q) * twt q (4 * K + g) k
      = (81 : ZMod q)
          * ∑ k ∈ Finset.range K, (e k : ZMod q)
              * (((10 ^ (2 * k))
                  * ((10 ^ (4 * K + g - 2 - 4 * k) - 1) / 9) : ℕ) : ZMod q) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  set D := 4 * K + g - 2 - 4 * k with hD
  have hf := palW_pair_factor (m := q) (L := 4 * K + g) (k := k)
    (by omega : 4 * k + 2 ≤ 4 * K + g)
  have htwt : twt q (4 * K + g) k
      = (9 : ZMod q) * (10 : ZMod q) ^ (2 * k)
          * ((10 : ZMod q) ^ D - 1) := by
    unfold twt
    rw [hf]
  rw [htwt]
  have h9 : (9 : ZMod q) * (((10 ^ D - 1) / 9 : ℕ) : ZMod q)
      = (10 : ZMod q) ^ D - 1 := by
    conv_lhs => rw [← Nat.cast_ofNat]
    rw [← Nat.cast_mul, nine_mul_repunit,
      Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num : (0:ℕ) < 10))]
    push_cast
    ring
  have h81a : (81 : ZMod q)
        * (((10 ^ (2 * k)) * ((10 ^ D - 1) / 9) : ℕ) : ZMod q)
      = 9 * (10 : ZMod q) ^ (2 * k)
          * (9 * (((10 ^ D - 1) / 9 : ℕ) : ZMod q)) := by
    have hnat : (81 : ℕ) * ((10 ^ (2 * k)) * ((10 ^ D - 1) / 9))
        = 9 * (10 ^ (2 * k)) * (9 * ((10 ^ D - 1) / 9)) := by ring
    conv_lhs => rw [← Nat.cast_ofNat, ← Nat.cast_mul, hnat]
    push_cast
    ring
  rw [show (81 : ZMod q) * ((e k : ZMod q)
        * (((10 ^ (2 * k)) * ((10 ^ D - 1) / 9) : ℕ) : ZMod q))
      = (e k : ZMod q) * ((81 : ZMod q)
          * (((10 ^ (2 * k)) * ((10 ^ D - 1) / 9) : ℕ) : ZMod q)) from by ring]
  rw [h81a, h9]

end A084017


namespace A084017
open Finset List Nat BigOperators Pointwise


end A084017


namespace A084017
open Finset List Nat BigOperators Pointwise


set_option maxHeartbeats 800000 in
theorem extract3_target {m v K g : ℕ} [NeZero m]
    (hm3 : m.Coprime 3) (hm10 : m.Coprime 10)
    (hg3 : 3 ≤ g) (hgodd : Odd g)
    (hK : m * 3 ^ (v - 4) ≤ 1 + 9 * (K / 2)) (t : ZMod m) :
    ∃ e : ℕ → ℕ, (∀ k, e k ≤ 9)
      ∧ ∃ T : ZMod (m * 3 ^ v),
          (∑ k ∈ Finset.range K, (e k : ZMod (m * 3 ^ v))
              * twt (m * 3 ^ v) (4 * K + g) k) = T
        ∧ ((ZMod.castHom (Nat.dvd_mul_right m (3 ^ v)) (ZMod m)) T
            = 81 * t)
        ∧ ((ZMod.castHom (Nat.dvd_mul_left (3 ^ v) m) (ZMod (3 ^ v))) T
            = 0) := by
  set M := m * 3 ^ (v - 4) with hM
  have hmpos : 0 < m := NeZero.pos m
  have h3 : (0:ℕ) < 3 ^ (v - 4) := pow_pos (by norm_num) _
  haveI : NeZero (3 ^ (v - 4)) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero M := ⟨by
    rw [hM]
    exact mul_ne_zero (NeZero.ne m) (pow_ne_zero _ (by norm_num))⟩
  have hM10 : M.Coprime 10 := Nat.coprime_mul_iff_left.mpr
    ⟨hm10, Nat.Coprime.pow_left _ (by norm_num)⟩
  have hcop : m.Coprime (3 ^ (v - 4)) := hm3.pow_right _
  set iv : ℕ := ((m : ZMod (3 ^ (v - 4)))⁻¹).val with hiv
  set s : ℕ := (iv * (3 ^ (v - 4) - t.val % 3 ^ (v - 4)))
      % 3 ^ (v - 4) with hs
  set trep : ℕ := t.val + m * s with htrep
  have hunit : IsUnit (↑m : ZMod (3 ^ (v - 4))) :=
    (ZMod.isUnit_iff_coprime m (3 ^ (v - 4))).mpr hcop
  have htrep_m : (↑trep : ZMod m) = t := by
    rw [htrep, Nat.cast_add, Nat.cast_mul]
    have h0 : (m : ZMod m) = 0 := ZMod.natCast_self m
    rw [h0, zero_mul, add_zero, ZMod.natCast_val, ZMod.cast_id]
  have htrep_3 : 3 ^ (v - 4) ∣ trep := by
    have hstep : (↑trep : ZMod (3 ^ (v - 4))) = 0 := by
      rw [htrep, Nat.cast_add, Nat.cast_mul]
      have hs_cast : (↑s : ZMod (3 ^ (v - 4)))
          = ↑(iv * (3 ^ (v - 4) - t.val % 3 ^ (v - 4))) := by
        rw [hs, ZMod.natCast_eq_natCast_iff]
        exact Nat.mod_modEq _ _
      rw [hs_cast, Nat.cast_mul]
      have hiv_cast : (↑iv : ZMod (3 ^ (v - 4))) = (↑m)⁻¹ := by
        rw [hiv, ZMod.natCast_val, ZMod.cast_id]
      rw [hiv_cast]
      have hsub : (↑(3 ^ (v - 4) - t.val % 3 ^ (v - 4))
          : ZMod (3 ^ (v - 4))) = -(↑(t.val % 3 ^ (v - 4))) := by
        rw [Nat.cast_sub ((Nat.mod_lt _ h3).le)]
        have hN : ((3 ^ (v - 4) : ℕ) : ZMod (3 ^ (v - 4))) = 0 :=
          ZMod.natCast_self _
        rw [hN, zero_sub]
      rw [hsub]
      have hr : (↑(t.val % 3 ^ (v - 4)) : ZMod (3 ^ (v - 4)))
          = ↑(t.val) := by
        rw [ZMod.natCast_eq_natCast_iff]
        exact Nat.mod_modEq _ _
      rw [hr]
      have h1 : (↑m : ZMod (3 ^ (v - 4))) * (↑m)⁻¹ = 1 :=
        ZMod.mul_inv_of_unit _ hunit
      rw [← mul_assoc, h1, one_mul, add_neg_cancel]
    rw [← CharP.cast_eq_zero_iff (ZMod (3 ^ (v - 4))) (3 ^ (v - 4)) trep]
    exact hstep
  obtain ⟨e, he, hsum⟩ :=
    gadget_extract3 hM10 hg3 hgodd hK (↑trep : ZMod M)
  refine ⟨e, he, (((81 * trep : ℕ) : ZMod (m * 3 ^ v))), ?_, ?_, ?_⟩
  · rw [sum_twt_81]
    set S := ∑ k ∈ Finset.range K,
        e k * (10 ^ (2 * k)
            * ((10 ^ (4 * K + g - 2 - 4 * k) - 1) / 9)) with hS
    have hSM : (↑S : ZMod M) = (↑trep : ZMod M) := by
      rw [hS, Nat.cast_sum, ← hsum]
      apply Finset.sum_congr rfl
      intro k _
      rw [Nat.cast_mul]
    have hSval : S ≡ trep [MOD M] := by
      have hv1 : (↑S : ZMod M).val = (↑trep : ZMod M).val :=
        congrArg ZMod.val hSM
      rw [ZMod.val_natCast, ZMod.val_natCast] at hv1
      rw [Nat.ModEq, hv1]
    have h81M : 81 * S ≡ 81 * trep [MOD 81 * M] :=
      Nat.ModEq.mul_left' 81 hSval
    have h81M' : m * 3 ^ v ∣ 81 * M := by
      rw [hM, show (81 : ℕ) = 3 ^ 4 from by norm_num]
      have hA : 3 ^ 4 * (m * 3 ^ (v - 4)) = m * (3 ^ 4 * 3 ^ (v - 4)) := by
        ring
      rw [hA, ← pow_add]
      exact Nat.mul_dvd_mul_left m (pow_dvd_pow 3 (by omega))
    have h81Mv : 81 * S ≡ 81 * trep [MOD m * 3 ^ v] := by
      rw [Nat.ModEq] at h81M ⊢
      rw [← Nat.mod_mod_of_dvd _ h81M', h81M,
        Nat.mod_mod_of_dvd _ h81M']
    have hcast : ((81 * S : ℕ) : ZMod (m * 3 ^ v))
        = ((81 * trep : ℕ) : ZMod (m * 3 ^ v)) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr h81Mv
    rw [← hcast, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum,
      Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    push_cast
    ring
  · have hc := map_natCast (ZMod.castHom (Nat.dvd_mul_right m (3 ^ v))
        (ZMod m)) (81 * trep)
    rw [hc, Nat.cast_mul, Nat.cast_ofNat, htrep_m]
  · have hc := map_natCast (ZMod.castHom (Nat.dvd_mul_left (3 ^ v) m)
        (ZMod (3 ^ v))) (81 * trep)
    rw [hc]
    rw [CharP.cast_eq_zero_iff (ZMod (3 ^ v)) (3 ^ v) (81 * trep)]
    obtain ⟨w, hw⟩ := htrep_3
    rw [hw, show (81 : ℕ) = 3 ^ 4 from by norm_num]
    have hA : 3 ^ 4 * (3 ^ (v - 4) * w) = 3 ^ (4 + (v - 4)) * w := by
      rw [← mul_assoc, ← pow_add]
    rw [hA]
    exact dvd_mul_of_dvd_left (pow_dvd_pow 3 (by omega)) _

end A084017


namespace A084017

set_option maxHeartbeats 800000 in
theorem cast_ofDigits {q : ℕ} (L : List ℕ) :
    ((Nat.ofDigits 10 L : ℕ) : ZMod q) = Nat.ofDigits (10 : ZMod q) L := by
  induction L with
  | nil => simp [Nat.ofDigits]
  | cons d t ih => simp [Nat.ofDigits, ih]

end A084017


namespace A084017
open Finset List Nat BigOperators Pointwise


set_option maxHeartbeats 800000 in
theorem sum_palW_odd {m K g : ℕ} (hK : 1 ≤ K) :
    ∑ k ∈ Finset.range K, palW m (4 * K + g) (2 * k + 1)
      = ((10 : ZMod m) + (10 : ZMod m) ^ (2 * K + g))
          * ∑ k ∈ Finset.range K, (10 : ZMod m) ^ (2 * k) := by
  have hsplit : ∑ k ∈ Finset.range K, palW m (4 * K + g) (2 * k + 1)
      = ∑ k ∈ Finset.range K, (10 : ZMod m) ^ (2 * k + 1)
        + ∑ k ∈ Finset.range K,
            (10 : ZMod m) ^ (4 * K + g - 1 - (2 * k + 1)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rfl
  rw [hsplit]
  have hA : ∑ k ∈ Finset.range K, (10 : ZMod m) ^ (2 * k + 1)
      = (10 : ZMod m) * ∑ k ∈ Finset.range K, (10 : ZMod m) ^ (2 * k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [pow_succ]
    ring
  have hB : ∑ k ∈ Finset.range K, (10 : ZMod m) ^ (4 * K + g - 1 - (2 * k + 1))
      = (10 : ZMod m) ^ (2 * K + g)
          * ∑ k ∈ Finset.range K, (10 : ZMod m) ^ (2 * k) := by
    have href : ∑ k ∈ Finset.range K,
        (10 : ZMod m) ^ (4 * K + g - 1 - (2 * k + 1))
        = ∑ j ∈ Finset.range K, (10 : ZMod m) ^ (2 * K + g + 2 * j) := by
      rw [← Finset.sum_range_reflect (fun j => (10 : ZMod m) ^ (2 * K + g + 2 * j)) K]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      congr 1
      omega
    rw [href, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_add]
  rw [hA, hB]
  ring

end A084017


namespace A084017


set_option maxHeartbeats 800000 in
theorem spw_dvd_3pow {v K : ℕ} (hv : 2 ≤ v) (hK : 3 ^ (v - 2) ∣ K) :
    3 ^ v ∣ 9 * (∑ k ∈ Finset.range K, (100 : ℕ) ^ k) := by
  have h100 : (100 : ℕ) ^ K ≡ 1 ^ K [MOD 99] :=
    Nat.ModEq.pow K (by norm_num : (100:ℕ) ≡ 1 [MOD 99])
  rw [one_pow] at h100
  have h99 : 99 ∣ 100 ^ K - 1 :=
    (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp h100.symm
  have hgeom : (∑ k ∈ Finset.range K, (100 : ℕ) ^ k)
      = (100 ^ K - 1) / 99 :=
    Nat.geomSum_eq (by norm_num) K
  have h99R : 99 * (∑ k ∈ Finset.range K, (100 : ℕ) ^ k)
      = 100 ^ K - 1 := by
    rw [hgeom, mul_comm, Nat.div_mul_cancel h99]
  have h3v : 3 ^ v ∣ 100 ^ K - 1 := by
    have h : 100 ^ K = 10 ^ (2 * K) := by
      rw [show (100:ℕ) = 10^2 from by norm_num, ← pow_mul]
    rw [h]
    exact pow3v_dvd_pow10_sub_one hv (mul_comm K 2 ▸ dvd_mul_of_dvd_left hK 2)
  rw [← h99R] at h3v
  obtain ⟨w, hw⟩ := h3v
  have h11R : 3 ^ (v - 2) ∣ 11 * (∑ k ∈ Finset.range K, (100 : ℕ) ^ k) := by
    refine ⟨w, ?_⟩
    have heq : 9 * (11 * (∑ k ∈ Finset.range K, (100 : ℕ) ^ k))
        = 9 * (3 ^ (v - 2) * w) := by
      have h1 : 9 * (11 * (∑ k ∈ Finset.range K, (100 : ℕ) ^ k))
          = 99 * (∑ k ∈ Finset.range K, (100 : ℕ) ^ k) := by ring
      rw [h1, hw]
      have h2 : 9 * (3 ^ (v - 2) * w) = 3 ^ v * w := by
        rw [show (9:ℕ) = 3^2 from by norm_num, ← mul_assoc, ← pow_add,
          show 2 + (v - 2) = v from by omega]
      rw [h2]
    exact Nat.mul_left_cancel (by norm_num) heq
  have hc311 : (3 ^ (v - 2)).Coprime 11 :=
    Nat.Coprime.pow_left _ (by norm_num)
  have hR : 3 ^ (v - 2) ∣ ∑ k ∈ Finset.range K, (100 : ℕ) ^ k :=
    hc311.dvd_of_dvd_mul_left h11R
  obtain ⟨s, hs⟩ := hR
  refine ⟨s, ?_⟩
  rw [hs]
  have : 9 * (3 ^ (v - 2) * s) = 3 ^ v * s := by
    rw [show (9:ℕ) = 3^2 from by norm_num, ← mul_assoc, ← pow_add,
      show 2 + (v - 2) = v from by omega]
  rw [this]

end A084017


namespace A084017
open Finset List Nat BigOperators Pointwise


set_option maxHeartbeats 800000 in
theorem castHom_ten {q m' : ℕ} (h : m' ∣ q) :
    (ZMod.castHom h (ZMod m')) (10 : ZMod q) = 10 := by
  have hh := map_natCast (ZMod.castHom h (ZMod m')) (10 : ℕ)
  simpa using hh


set_option maxHeartbeats 800000 in
theorem castHom_nine {q m' : ℕ} (h : m' ∣ q) :
    (ZMod.castHom h (ZMod m')) (9 : ZMod q) = 9 := by
  have hh := map_natCast (ZMod.castHom h (ZMod m')) (9 : ℕ)
  simpa using hh


set_option maxHeartbeats 800000 in
theorem castHom_ofDigits {q m' : ℕ} (h : m' ∣ q) (L : List ℕ) :
    (ZMod.castHom h (ZMod m')) (Nat.ofDigits (10 : ZMod q) L)
      = Nat.ofDigits (10 : ZMod m') L := by
  induction L with
  | nil => simp [Nat.ofDigits]
  | cons d t ih =>
    rw [show Nat.ofDigits (10 : ZMod q) (d :: t)
        = (d : ZMod q) + 10 * Nat.ofDigits (10 : ZMod q) t from rfl]
    rw [map_add, map_natCast, map_mul, ih, castHom_ten]
    rfl


set_option maxHeartbeats 800000 in
theorem castHom_palW {q m' : ℕ} (h : m' ∣ q) (L i : ℕ) :
    (ZMod.castHom h (ZMod m')) (palW q L i) = palW m' L i := by
  unfold palW
  rw [map_add, map_pow, map_pow, castHom_ten]


set_option maxHeartbeats 800000 in
theorem P_dvd_3m {m v le K g : ℕ} [NeZero m]
    (hm3 : m.Coprime 3) (hm10 : m.Coprime 10) (hv : 2 ≤ v) (hK1 : 1 ≤ K)
    (de : List ℕ) (hle : de.length = le)
    (C : List ℕ) (hC : C.length = g)
    (hg3 : 3 ≤ g) (hgodd : Odd g)
    (hKcov : m * 3 ^ (v - 4) ≤ 1 + 9 * (K / 2))
    (hK3 : 3 ^ (v - 2) ∣ K)
    (he3 : 3 ^ v ∣ Nat.ofDigits 10 de)
    (he3r : 3 ^ v ∣ Nat.ofDigits 10 de.reverse)
    (hC3 : 3 ^ v ∣ Nat.ofDigits 10 C) :
    ∃ e' : ℕ → ℕ, (∀ k, e' k ≤ 9)
      ∧ m * 3 ^ v ∣ Nat.ofDigits 10
          (de ++ (((List.range (2 * K)).map (pairDigit e') ++ C)
            ++ ((List.range (2 * K)).map (pairDigit e')).reverse)
            ++ de.reverse) := by
  set q := m * 3 ^ v with hq
  haveI : NeZero q := ⟨by
    rw [hq]
    exact mul_ne_zero (NeZero.ne m) (pow_ne_zero _ (by norm_num))⟩
  haveI : NeZero (3 ^ v) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hcop81 : m.Coprime 81 := by
    have h := hm3.pow_right 4
    norm_num at h ⊢
    exact h
  have hunit : IsUnit ((10 : ZMod m) ^ le * 81) := by
    rw [show ((10 : ZMod m) ^ le * 81)
        = ((10 ^ le * 81 : ℕ) : ZMod m) from by push_cast; ring]
    rw [ZMod.isUnit_iff_coprime]
    exact Nat.coprime_mul_iff_left.mpr ⟨hm10.symm.pow_left le, hcop81.symm⟩
  set E : ZMod m := Nat.ofDigits (10 : ZMod m) de
      + Nat.ofDigits (10 : ZMod m) de.reverse
          * (10 : ZMod m) ^ (le + (4 * K + g)) with hE
  set X : ZMod m := Nat.ofDigits (10 : ZMod m) C * (10 : ZMod m) ^ (2 * K)
      + 9 * ∑ k ∈ Finset.range K, palW m (4 * K + g) (2 * k + 1) with hX
  set t : ZMod m := -(E + (10 : ZMod m) ^ le * X)
      * ((10 : ZMod m) ^ le * 81)⁻¹ with ht
  obtain ⟨e', he', T, hTsum, hTm, hT3⟩ :=
    extract3_target hm3 hm10 hg3 hgodd hKcov t
  refine ⟨e', he', ?_⟩
  have hPq : (Nat.ofDigits (10 : ZMod q)
      (de ++ (((List.range (2 * K)).map (pairDigit e') ++ C)
          ++ ((List.range (2 * K)).map (pairDigit e')).reverse)
          ++ de.reverse))
      = (Nat.ofDigits (10 : ZMod q) de
          + Nat.ofDigits (10 : ZMod q) de.reverse
              * (10 : ZMod q) ^ (le + (4 * K + g)))
        + (10 : ZMod q) ^ le
            * (Nat.ofDigits (10 : ZMod q) C * (10 : ZMod q) ^ (2 * K)
              + ∑ k ∈ Finset.range K,
                  ((9 : ZMod q) * palW q (4 * K + g) (2 * k + 1)
                  + (e' k : ZMod q)
                      * (palW q (4 * K + g) (2 * k)
                        - palW q (4 * K + g) (2 * k + 1)))) :=
    gadget_val_m de hle e' he' C hC
  simp only [twt] at hTsum
  have hsumq : ∑ k ∈ Finset.range K,
      ((9 : ZMod q) * palW q (4 * K + g) (2 * k + 1)
        + (e' k : ZMod q)
            * (palW q (4 * K + g) (2 * k) - palW q (4 * K + g) (2 * k + 1)))
      = 9 * (∑ k ∈ Finset.range K, palW q (4 * K + g) (2 * k + 1)) + T := by
    rw [Finset.sum_add_distrib, hTsum, ← Finset.mul_sum]
  rw [hsumq] at hPq
  have hPm : (Nat.ofDigits (10 : ZMod m)
      (de ++ (((List.range (2 * K)).map (pairDigit e') ++ C)
          ++ ((List.range (2 * K)).map (pairDigit e')).reverse)
          ++ de.reverse)) = 0 := by
    have hcast := congrArg (ZMod.castHom (Nat.dvd_mul_right m (3 ^ v))
      (ZMod m)) hPq
    rw [castHom_ofDigits] at hcast
    rw [map_add, map_add, castHom_ofDigits, map_mul, castHom_ofDigits,
      map_pow, castHom_ten] at hcast
    rw [map_mul, map_pow, castHom_ten] at hcast
    rw [map_add, map_mul, castHom_ofDigits, map_pow, castHom_ten] at hcast
    rw [map_add] at hcast
    have h9 : (ZMod.castHom (Nat.dvd_mul_right m (3 ^ v)) (ZMod m))
        (9 * ∑ k ∈ Finset.range K, palW q (4 * K + g) (2 * k + 1))
        = 9 * ∑ k ∈ Finset.range K, palW m (4 * K + g) (2 * k + 1) := by
      rw [map_mul, map_sum, castHom_nine]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      exact castHom_palW _ _ _
    rw [h9, hTm] at hcast
    rw [hcast]
    have htz : ((10 : ZMod m) ^ le * 81) * t
        = -(E + (10 : ZMod m) ^ le * X) := by
      rw [ht]
      rw [show (10 : ZMod m) ^ le * 81
          * (-(E + (10 : ZMod m) ^ le * X) * ((10 : ZMod m) ^ le * 81)⁻¹)
          = -(E + (10 : ZMod m) ^ le * X)
            * ((10 : ZMod m) ^ le * 81 * ((10 : ZMod m) ^ le * 81)⁻¹)
          from by ring]
      rw [ZMod.mul_inv_of_unit _ hunit, mul_one]
    rw [← hE]
    rw [show E + (10 : ZMod m) ^ le * (Nat.ofDigits (10 : ZMod m) C
            * (10 : ZMod m) ^ (2 * K)
          + (9 * ∑ k ∈ Finset.range K, palW m (4 * K + g) (2 * k + 1)
            + 81 * t))
        = E + (10 : ZMod m) ^ le * X + ((10 : ZMod m) ^ le * 81) * t
        from by rw [hX]; ring]
    rw [htz]
    ring
  have hP3 : (Nat.ofDigits (10 : ZMod (3 ^ v))
      (de ++ (((List.range (2 * K)).map (pairDigit e') ++ C)
          ++ ((List.range (2 * K)).map (pairDigit e')).reverse)
          ++ de.reverse)) = 0 := by
    have hcast := congrArg (ZMod.castHom (Nat.dvd_mul_left (3 ^ v) m)
      (ZMod (3 ^ v))) hPq
    rw [castHom_ofDigits] at hcast
    rw [map_add, map_add, castHom_ofDigits, map_mul, castHom_ofDigits,
      map_pow, castHom_ten] at hcast
    rw [map_mul, map_pow, castHom_ten] at hcast
    rw [map_add, map_mul, castHom_ofDigits, map_pow, castHom_ten] at hcast
    rw [map_add] at hcast
    have hd0 : Nat.ofDigits (10 : ZMod (3 ^ v)) de = 0 := by
      rw [← cast_ofDigits]
      exact (CharP.cast_eq_zero_iff (ZMod (3 ^ v)) (3 ^ v) _).mpr he3
    have hdr0 : Nat.ofDigits (10 : ZMod (3 ^ v)) de.reverse = 0 := by
      rw [← cast_ofDigits]
      exact (CharP.cast_eq_zero_iff (ZMod (3 ^ v)) (3 ^ v) _).mpr he3r
    have hC0 : Nat.ofDigits (10 : ZMod (3 ^ v)) C = 0 := by
      rw [← cast_ofDigits]
      exact (CharP.cast_eq_zero_iff (ZMod (3 ^ v)) (3 ^ v) _).mpr hC3
    have h9v : (ZMod.castHom (Nat.dvd_mul_left (3 ^ v) m) (ZMod (3 ^ v)))
        (9 * ∑ k ∈ Finset.range K, palW q (4 * K + g) (2 * k + 1)) = 0 := by
      rw [map_mul, map_sum, castHom_nine]
      have hsp : ∑ k ∈ Finset.range K,
          (ZMod.castHom (Nat.dvd_mul_left (3 ^ v) m) (ZMod (3 ^ v)))
            (palW q (4 * K + g) (2 * k + 1))
          = ∑ k ∈ Finset.range K, palW (3 ^ v) (4 * K + g) (2 * k + 1) :=
        Finset.sum_congr rfl (fun k _ => castHom_palW _ _ _)
      rw [hsp, sum_palW_odd hK1]
      have hgeo : ∑ k ∈ Finset.range K, (10 : ZMod (3 ^ v)) ^ (2 * k)
          = ((∑ k ∈ Finset.range K, (100 : ℕ) ^ k : ℕ) : ZMod (3 ^ v)) := by
        rw [Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [pow_mul]
        rw [show (10 : ZMod (3 ^ v)) ^ 2
            = ((100 : ℕ) : ZMod (3 ^ v)) from by norm_cast]
        rw [← Nat.cast_pow]
      rw [hgeo]
      have hkill : (9 : ZMod (3 ^ v))
          * ((∑ k ∈ Finset.range K, (100 : ℕ) ^ k : ℕ) : ZMod (3 ^ v))
          = 0 := by
        rw [show (9 : ZMod (3 ^ v)) = ((9 : ℕ) : ZMod (3 ^ v)) from by
          norm_cast]
        rw [← Nat.cast_mul]
        exact (CharP.cast_eq_zero_iff (ZMod (3 ^ v)) (3 ^ v) _).mpr
          (spw_dvd_3pow hv hK3)
      rw [show (9 : ZMod (3 ^ v))
          * (((10 : ZMod (3 ^ v)) + (10 : ZMod (3 ^ v)) ^ (2 * K + g))
            * ((∑ k ∈ Finset.range K, (100 : ℕ) ^ k : ℕ) : ZMod (3 ^ v)))
          = (9 * ((∑ k ∈ Finset.range K, (100 : ℕ) ^ k : ℕ) : ZMod (3 ^ v)))
            * ((10 : ZMod (3 ^ v)) + (10 : ZMod (3 ^ v)) ^ (2 * K + g))
          from by ring]
      rw [hkill, zero_mul]
    rw [h9v, hT3] at hcast
    rw [hcast, hd0, hdr0, hC0]
    ring
  have hdm : m ∣ Nat.ofDigits 10
      (de ++ (((List.range (2 * K)).map (pairDigit e') ++ C)
          ++ ((List.range (2 * K)).map (pairDigit e')).reverse)
          ++ de.reverse) := by
    rw [← CharP.cast_eq_zero_iff (ZMod m) m _]
    rw [cast_ofDigits]
    exact hPm
  have hd3 : 3 ^ v ∣ Nat.ofDigits 10
      (de ++ (((List.range (2 * K)).map (pairDigit e') ++ C)
          ++ ((List.range (2 * K)).map (pairDigit e')).reverse)
          ++ de.reverse) := by
    rw [← CharP.cast_eq_zero_iff (ZMod (3 ^ v)) (3 ^ v) _]
    rw [cast_ofDigits]
    exact hP3
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (hm3.pow_right v) hdm hd3

end A084017


namespace A084017
open Finset List Nat BigOperators Pointwise


set_option maxHeartbeats 800000 in
theorem extract3_target81 {m v K g : ℕ} [NeZero m]
    (hm3 : m.Coprime 3) (hm10 : m.Coprime 10)
    (hg3 : 3 ≤ g) (hgodd : Odd g)
    (hK : m * 3 ^ (v - 4) ≤ 1 + 9 * (K / 2)) (t : ZMod m) (s₀ : ℕ) :
    ∃ e : ℕ → ℕ, (∀ k, e k ≤ 9)
      ∧ ∃ T : ZMod (m * 3 ^ v),
          (∑ k ∈ Finset.range K, (e k : ZMod (m * 3 ^ v))
              * twt (m * 3 ^ v) (4 * K + g) k) = T
        ∧ ((ZMod.castHom (Nat.dvd_mul_right m (3 ^ v)) (ZMod m)) T
            = 81 * t)
        ∧ ((ZMod.castHom (Nat.dvd_mul_left (3 ^ v) m) (ZMod (3 ^ v))) T
            = 81 * (s₀ : ZMod (3 ^ v))) := by
  set M := m * 3 ^ (v - 4) with hM
  have hmpos : 0 < m := NeZero.pos m
  have h3 : (0:ℕ) < 3 ^ (v - 4) := pow_pos (by norm_num) _
  haveI : NeZero (3 ^ (v - 4)) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero M := ⟨by
    rw [hM]
    exact mul_ne_zero (NeZero.ne m) (pow_ne_zero _ (by norm_num))⟩
  have hM10 : M.Coprime 10 := Nat.coprime_mul_iff_left.mpr
    ⟨hm10, Nat.Coprime.pow_left _ (by norm_num)⟩
  have hcop : m.Coprime (3 ^ (v - 4)) := hm3.pow_right _
  set iv : ℕ := ((m : ZMod (3 ^ (v - 4)))⁻¹).val with hiv
  set s : ℕ := (iv * (s₀ % 3 ^ (v - 4) + 3 ^ (v - 4)
      - t.val % 3 ^ (v - 4))) % 3 ^ (v - 4) with hs
  set trep : ℕ := t.val + m * s with htrep
  have hunit : IsUnit (↑m : ZMod (3 ^ (v - 4))) :=
    (ZMod.isUnit_iff_coprime m (3 ^ (v - 4))).mpr hcop
  have htrep_m : (↑trep : ZMod m) = t := by
    rw [htrep, Nat.cast_add, Nat.cast_mul]
    have h0 : (m : ZMod m) = 0 := ZMod.natCast_self m
    rw [h0, zero_mul, add_zero, ZMod.natCast_val, ZMod.cast_id]
  have htrep_3 : trep ≡ s₀ [MOD 3 ^ (v - 4)] := by
    have hstep : (↑trep : ZMod (3 ^ (v - 4))) = ↑(s₀ % 3 ^ (v - 4)) := by
      rw [htrep, Nat.cast_add, Nat.cast_mul]
      have hs_cast : (↑s : ZMod (3 ^ (v - 4)))
          = ↑(iv * (s₀ % 3 ^ (v - 4) + 3 ^ (v - 4)
            - t.val % 3 ^ (v - 4))) := by
        rw [hs, ZMod.natCast_eq_natCast_iff]
        exact Nat.mod_modEq _ _
      rw [hs_cast, Nat.cast_mul]
      have hiv_cast : (↑iv : ZMod (3 ^ (v - 4))) = (↑m)⁻¹ := by
        rw [hiv, ZMod.natCast_val, ZMod.cast_id]
      rw [hiv_cast]
      have hlt : t.val % 3 ^ (v - 4) ≤ s₀ % 3 ^ (v - 4) + 3 ^ (v - 4) := by
        have h := Nat.mod_lt (t.val) h3
        have h' := Nat.mod_lt s₀ h3
        omega
      have hsub : (↑(s₀ % 3 ^ (v - 4) + 3 ^ (v - 4) - t.val % 3 ^ (v - 4))
          : ZMod (3 ^ (v - 4))) = ↑(s₀ % 3 ^ (v - 4))
            - ↑(t.val % 3 ^ (v - 4)) := by
        rw [Nat.cast_sub hlt, Nat.cast_add]
        have hN : ((3 ^ (v - 4) : ℕ) : ZMod (3 ^ (v - 4))) = 0 :=
          ZMod.natCast_self _
        rw [hN, add_zero]
      rw [hsub]
      have hr : (↑(t.val % 3 ^ (v - 4)) : ZMod (3 ^ (v - 4)))
          = ↑(t.val) := by
        rw [ZMod.natCast_eq_natCast_iff]
        exact Nat.mod_modEq _ _
      rw [hr]
      have h1 : (↑m : ZMod (3 ^ (v - 4))) * (↑m)⁻¹ = 1 :=
        ZMod.mul_inv_of_unit _ hunit
      rw [← mul_assoc, h1, one_mul, add_sub_cancel]
    have hv1 : (↑trep : ZMod (3 ^ (v - 4))).val
        = (↑(s₀ % 3 ^ (v - 4)) : ZMod (3 ^ (v - 4))).val :=
      congrArg ZMod.val hstep
    rw [ZMod.val_natCast, ZMod.val_natCast] at hv1
    rw [Nat.ModEq, hv1, Nat.mod_mod]
  obtain ⟨e, he, hsum⟩ :=
    gadget_extract3 hM10 hg3 hgodd hK (↑trep : ZMod M)
  refine ⟨e, he, (((81 * trep : ℕ) : ZMod (m * 3 ^ v))), ?_, ?_, ?_⟩
  · rw [sum_twt_81]
    set S := ∑ k ∈ Finset.range K,
        e k * (10 ^ (2 * k)
            * ((10 ^ (4 * K + g - 2 - 4 * k) - 1) / 9)) with hS
    have hSM : (↑S : ZMod M) = (↑trep : ZMod M) := by
      rw [hS, Nat.cast_sum, ← hsum]
      apply Finset.sum_congr rfl
      intro k _
      rw [Nat.cast_mul]
    have hSval : S ≡ trep [MOD M] := by
      have hv1 : (↑S : ZMod M).val = (↑trep : ZMod M).val :=
        congrArg ZMod.val hSM
      rw [ZMod.val_natCast, ZMod.val_natCast] at hv1
      rw [Nat.ModEq, hv1]
    have h81M : 81 * S ≡ 81 * trep [MOD 81 * M] :=
      Nat.ModEq.mul_left' 81 hSval
    have h81M' : m * 3 ^ v ∣ 81 * M := by
      rw [hM, show (81 : ℕ) = 3 ^ 4 from by norm_num]
      have hA : 3 ^ 4 * (m * 3 ^ (v - 4)) = m * (3 ^ 4 * 3 ^ (v - 4)) := by
        ring
      rw [hA, ← pow_add]
      exact Nat.mul_dvd_mul_left m (pow_dvd_pow 3 (by omega))
    have h81Mv : 81 * S ≡ 81 * trep [MOD m * 3 ^ v] := by
      rw [Nat.ModEq] at h81M ⊢
      rw [← Nat.mod_mod_of_dvd _ h81M', h81M,
        Nat.mod_mod_of_dvd _ h81M']
    have hcast : ((81 * S : ℕ) : ZMod (m * 3 ^ v))
        = ((81 * trep : ℕ) : ZMod (m * 3 ^ v)) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr h81Mv
    rw [← hcast, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum,
      Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    push_cast
    ring
  · have hc := map_natCast (ZMod.castHom (Nat.dvd_mul_right m (3 ^ v))
        (ZMod m)) (81 * trep)
    rw [hc, Nat.cast_mul, Nat.cast_ofNat, htrep_m]
  · have hc := map_natCast (ZMod.castHom (Nat.dvd_mul_left (3 ^ v) m)
        (ZMod (3 ^ v))) (81 * trep)
    rw [hc]
    have hdvd : 3 ^ v ∣ 81 * 3 ^ (v - 4) := by
      refine ⟨3 ^ (4 - v), ?_⟩
      rw [show (81 : ℕ) = 3 ^ 4 from by norm_num, ← pow_add, ← pow_add]
      congr 1
      omega
    have h81 : 81 * trep ≡ 81 * s₀ [MOD 3 ^ v] :=
      Nat.ModEq.of_dvd hdvd (Nat.ModEq.mul_left' 81 htrep_3)
    have hcast : ((81 * trep : ℕ) : ZMod (3 ^ v))
        = ((81 * s₀ : ℕ) : ZMod (3 ^ v)) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr h81
    rw [hcast]
    push_cast
    ring


set_option maxHeartbeats 800000 in
theorem P_dvd_3m81 {m v le K g : ℕ} [NeZero m]
    (hm3 : m.Coprime 3) (hm10 : m.Coprime 10)
    (de : List ℕ) (hle : de.length = le)
    (C : List ℕ) (hC : C.length = g)
    (hg3 : 3 ≤ g) (hgodd : Odd g)
    (hKcov : m * 3 ^ (v - 4) ≤ 1 + 9 * (K / 2))
    (s₀ : ℕ)
    (hs0 : (Nat.ofDigits (10 : ZMod (3 ^ v)) de
        + Nat.ofDigits (10 : ZMod (3 ^ v)) de.reverse
            * (10 : ZMod (3 ^ v)) ^ (le + (4 * K + g)))
      + (10 : ZMod (3 ^ v)) ^ le
        * (Nat.ofDigits (10 : ZMod (3 ^ v)) C
            * (10 : ZMod (3 ^ v)) ^ (2 * K)
          + (9 * ∑ k ∈ Finset.range K, palW (3 ^ v) (4 * K + g) (2 * k + 1)
            + 81 * (s₀ : ZMod (3 ^ v)))) = 0) :
    ∃ e' : ℕ → ℕ, (∀ k, e' k ≤ 9)
      ∧ m * 3 ^ v ∣ Nat.ofDigits 10
          (de ++ (((List.range (2 * K)).map (pairDigit e') ++ C)
            ++ ((List.range (2 * K)).map (pairDigit e')).reverse)
            ++ de.reverse) := by
  classical
  set q := m * 3 ^ v with hq
  haveI : NeZero q := ⟨by
    rw [hq]
    exact mul_ne_zero (NeZero.ne m) (pow_ne_zero _ (by norm_num))⟩
  haveI : NeZero (3 ^ v) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hcop81 : m.Coprime 81 := by
    have h := hm3.pow_right 4
    norm_num at h ⊢
    exact h
  have hunit : IsUnit ((10 : ZMod m) ^ le * 81) := by
    rw [show ((10 : ZMod m) ^ le * 81)
        = ((10 ^ le * 81 : ℕ) : ZMod m) from by push_cast; ring]
    rw [ZMod.isUnit_iff_coprime]
    exact Nat.coprime_mul_iff_left.mpr ⟨hm10.symm.pow_left le, hcop81.symm⟩
  set E : ZMod m := Nat.ofDigits (10 : ZMod m) de
      + Nat.ofDigits (10 : ZMod m) de.reverse
          * (10 : ZMod m) ^ (le + (4 * K + g)) with hE
  set X : ZMod m := Nat.ofDigits (10 : ZMod m) C * (10 : ZMod m) ^ (2 * K)
      + 9 * ∑ k ∈ Finset.range K, palW m (4 * K + g) (2 * k + 1) with hX
  set t : ZMod m := -(E + (10 : ZMod m) ^ le * X)
      * ((10 : ZMod m) ^ le * 81)⁻¹ with ht
  obtain ⟨e', he', T, hTsum, hTm, hT3⟩ :=
    extract3_target81 hm3 hm10 hg3 hgodd hKcov t s₀
  refine ⟨e', he', ?_⟩
  have hPq : (Nat.ofDigits (10 : ZMod q)
      (de ++ (((List.range (2 * K)).map (pairDigit e') ++ C)
          ++ ((List.range (2 * K)).map (pairDigit e')).reverse)
          ++ de.reverse))
      = (Nat.ofDigits (10 : ZMod q) de
          + Nat.ofDigits (10 : ZMod q) de.reverse
              * (10 : ZMod q) ^ (le + (4 * K + g)))
        + (10 : ZMod q) ^ le
            * (Nat.ofDigits (10 : ZMod q) C * (10 : ZMod q) ^ (2 * K)
              + ∑ k ∈ Finset.range K,
                  ((9 : ZMod q) * palW q (4 * K + g) (2 * k + 1)
                  + (e' k : ZMod q)
                      * (palW q (4 * K + g) (2 * k)
                        - palW q (4 * K + g) (2 * k + 1)))) :=
    gadget_val_m de hle e' he' C hC
  simp only [twt] at hTsum
  have hsumq : ∑ k ∈ Finset.range K,
      ((9 : ZMod q) * palW q (4 * K + g) (2 * k + 1)
        + (e' k : ZMod q)
            * (palW q (4 * K + g) (2 * k) - palW q (4 * K + g) (2 * k + 1)))
      = 9 * (∑ k ∈ Finset.range K, palW q (4 * K + g) (2 * k + 1)) + T := by
    rw [Finset.sum_add_distrib, hTsum, ← Finset.mul_sum]
  rw [hsumq] at hPq
  have hPm : (Nat.ofDigits (10 : ZMod m)
      (de ++ (((List.range (2 * K)).map (pairDigit e') ++ C)
          ++ ((List.range (2 * K)).map (pairDigit e')).reverse)
          ++ de.reverse)) = 0 := by
    have hcast := congrArg (ZMod.castHom (Nat.dvd_mul_right m (3 ^ v))
      (ZMod m)) hPq
    rw [castHom_ofDigits] at hcast
    rw [map_add, map_add, castHom_ofDigits, map_mul, castHom_ofDigits,
      map_pow, castHom_ten] at hcast
    rw [map_mul, map_pow, castHom_ten] at hcast
    rw [map_add, map_mul, castHom_ofDigits, map_pow, castHom_ten] at hcast
    rw [map_add] at hcast
    have h9 : (ZMod.castHom (Nat.dvd_mul_right m (3 ^ v)) (ZMod m))
        (9 * ∑ k ∈ Finset.range K, palW q (4 * K + g) (2 * k + 1))
        = 9 * ∑ k ∈ Finset.range K, palW m (4 * K + g) (2 * k + 1) := by
      rw [map_mul, map_sum, castHom_nine]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      exact castHom_palW _ _ _
    rw [h9, hTm] at hcast
    rw [hcast]
    have htz : ((10 : ZMod m) ^ le * 81) * t
        = -(E + (10 : ZMod m) ^ le * X) := by
      rw [ht]
      rw [show (10 : ZMod m) ^ le * 81
          * (-(E + (10 : ZMod m) ^ le * X) * ((10 : ZMod m) ^ le * 81)⁻¹)
          = -(E + (10 : ZMod m) ^ le * X)
            * ((10 : ZMod m) ^ le * 81 * ((10 : ZMod m) ^ le * 81)⁻¹)
          from by ring]
      rw [ZMod.mul_inv_of_unit _ hunit, mul_one]
    rw [← hE]
    rw [show E + (10 : ZMod m) ^ le * (Nat.ofDigits (10 : ZMod m) C
            * (10 : ZMod m) ^ (2 * K)
          + (9 * ∑ k ∈ Finset.range K, palW m (4 * K + g) (2 * k + 1)
            + 81 * t))
        = E + (10 : ZMod m) ^ le * X + ((10 : ZMod m) ^ le * 81) * t
        from by rw [hX]; ring]
    rw [htz]
    ring
  have hP3 : (Nat.ofDigits (10 : ZMod (3 ^ v))
      (de ++ (((List.range (2 * K)).map (pairDigit e') ++ C)
          ++ ((List.range (2 * K)).map (pairDigit e')).reverse)
          ++ de.reverse)) = 0 := by
    have hcast := congrArg (ZMod.castHom (Nat.dvd_mul_left (3 ^ v) m)
      (ZMod (3 ^ v))) hPq
    rw [castHom_ofDigits] at hcast
    rw [map_add, map_add, castHom_ofDigits, map_mul, castHom_ofDigits,
      map_pow, castHom_ten] at hcast
    rw [map_mul, map_pow, castHom_ten] at hcast
    rw [map_add, map_mul, castHom_ofDigits, map_pow, castHom_ten] at hcast
    rw [map_add] at hcast
    have hsp : (ZMod.castHom (Nat.dvd_mul_left (3 ^ v) m) (ZMod (3 ^ v)))
        (9 * ∑ k ∈ Finset.range K, palW q (4 * K + g) (2 * k + 1))
        = 9 * ∑ k ∈ Finset.range K,
            palW (3 ^ v) (4 * K + g) (2 * k + 1) := by
      rw [map_mul, map_sum, castHom_nine]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      exact castHom_palW _ _ _
    rw [hsp, hT3] at hcast
    rw [hcast]
    linear_combination hs0
  have hdm : m ∣ Nat.ofDigits 10
      (de ++ (((List.range (2 * K)).map (pairDigit e') ++ C)
          ++ ((List.range (2 * K)).map (pairDigit e')).reverse)
          ++ de.reverse) := by
    rw [← CharP.cast_eq_zero_iff (ZMod m) m _]
    rw [cast_ofDigits]
    exact hPm
  have hd3 : 3 ^ v ∣ Nat.ofDigits 10
      (de ++ (((List.range (2 * K)).map (pairDigit e') ++ C)
          ++ ((List.range (2 * K)).map (pairDigit e')).reverse)
          ++ de.reverse) := by
    rw [← CharP.cast_eq_zero_iff (ZMod (3 ^ v)) (3 ^ v) _]
    rw [cast_ofDigits]
    exact hP3
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (hm3.pow_right v) hdm hd3



set_option maxHeartbeats 800000 in
theorem extract3_target81_even {m v K g : ℕ} [NeZero m]
    (hm3 : m.Coprime 3) (hm10 : m.Coprime 10)
    (hm11 : m.Coprime 11) (hm101 : m.Coprime 101)
    (hg3 : 3 ≤ g) (hgev : Even g)
    (hK : m * 3 ^ (v - 4) ≤ 1 + 9 * (K / 2)) (t : ZMod m) (s₀ : ℕ) :
    ∃ e : ℕ → ℕ, (∀ k, e k ≤ 9)
      ∧ ∃ T : ZMod (m * 3 ^ v),
          (∑ k ∈ Finset.range K, (e k : ZMod (m * 3 ^ v))
              * twt (m * 3 ^ v) (4 * K + g) k) = T
        ∧ ((ZMod.castHom (Nat.dvd_mul_right m (3 ^ v)) (ZMod m)) T
            = 81 * t)
        ∧ ((ZMod.castHom (Nat.dvd_mul_left (3 ^ v) m) (ZMod (3 ^ v))) T
            = 81 * (s₀ : ZMod (3 ^ v))) := by
  set M := m * 3 ^ (v - 4) with hM
  have hmpos : 0 < m := NeZero.pos m
  have h3 : (0:ℕ) < 3 ^ (v - 4) := pow_pos (by norm_num) _
  haveI : NeZero (3 ^ (v - 4)) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero M := ⟨by
    rw [hM]
    exact mul_ne_zero (NeZero.ne m) (pow_ne_zero _ (by norm_num))⟩
  have hM10 : M.Coprime 10 := Nat.coprime_mul_iff_left.mpr
    ⟨hm10, Nat.Coprime.pow_left _ (by norm_num)⟩
  have hM11 : M.Coprime 11 := Nat.coprime_mul_iff_left.mpr
    ⟨hm11, Nat.Coprime.pow_left _ (by norm_num)⟩
  have hM101 : M.Coprime 101 := Nat.coprime_mul_iff_left.mpr
    ⟨hm101, Nat.Coprime.pow_left _ (by norm_num)⟩
  have hcop : m.Coprime (3 ^ (v - 4)) := hm3.pow_right _
  set iv : ℕ := ((m : ZMod (3 ^ (v - 4)))⁻¹).val with hiv
  set s : ℕ := (iv * (s₀ % 3 ^ (v - 4) + 3 ^ (v - 4)
      - t.val % 3 ^ (v - 4))) % 3 ^ (v - 4) with hs
  set trep : ℕ := t.val + m * s with htrep
  have hunit : IsUnit (↑m : ZMod (3 ^ (v - 4))) :=
    (ZMod.isUnit_iff_coprime m (3 ^ (v - 4))).mpr hcop
  have htrep_m : (↑trep : ZMod m) = t := by
    rw [htrep, Nat.cast_add, Nat.cast_mul]
    have h0 : (m : ZMod m) = 0 := ZMod.natCast_self m
    rw [h0, zero_mul, add_zero, ZMod.natCast_val, ZMod.cast_id]
  have htrep_3 : trep ≡ s₀ [MOD 3 ^ (v - 4)] := by
    have hstep : (↑trep : ZMod (3 ^ (v - 4))) = ↑(s₀ % 3 ^ (v - 4)) := by
      rw [htrep, Nat.cast_add, Nat.cast_mul]
      have hs_cast : (↑s : ZMod (3 ^ (v - 4)))
          = ↑(iv * (s₀ % 3 ^ (v - 4) + 3 ^ (v - 4)
            - t.val % 3 ^ (v - 4))) := by
        rw [hs, ZMod.natCast_eq_natCast_iff]
        exact Nat.mod_modEq _ _
      rw [hs_cast, Nat.cast_mul]
      have hiv_cast : (↑iv : ZMod (3 ^ (v - 4))) = (↑m)⁻¹ := by
        rw [hiv, ZMod.natCast_val, ZMod.cast_id]
      rw [hiv_cast]
      have hlt : t.val % 3 ^ (v - 4) ≤ s₀ % 3 ^ (v - 4) + 3 ^ (v - 4) := by
        have h := Nat.mod_lt (t.val) h3
        have h' := Nat.mod_lt s₀ h3
        omega
      have hsub : (↑(s₀ % 3 ^ (v - 4) + 3 ^ (v - 4) - t.val % 3 ^ (v - 4))
          : ZMod (3 ^ (v - 4))) = ↑(s₀ % 3 ^ (v - 4))
            - ↑(t.val % 3 ^ (v - 4)) := by
        rw [Nat.cast_sub hlt, Nat.cast_add]
        have hN : ((3 ^ (v - 4) : ℕ) : ZMod (3 ^ (v - 4))) = 0 :=
          ZMod.natCast_self _
        rw [hN, add_zero]
      rw [hsub]
      have hr : (↑(t.val % 3 ^ (v - 4)) : ZMod (3 ^ (v - 4)))
          = ↑(t.val) := by
        rw [ZMod.natCast_eq_natCast_iff]
        exact Nat.mod_modEq _ _
      rw [hr]
      have h1 : (↑m : ZMod (3 ^ (v - 4))) * (↑m)⁻¹ = 1 :=
        ZMod.mul_inv_of_unit _ hunit
      rw [← mul_assoc, h1, one_mul, add_sub_cancel]
    have hv1 : (↑trep : ZMod (3 ^ (v - 4))).val
        = (↑(s₀ % 3 ^ (v - 4)) : ZMod (3 ^ (v - 4))).val :=
      congrArg ZMod.val hstep
    rw [ZMod.val_natCast, ZMod.val_natCast] at hv1
    rw [Nat.ModEq, hv1, Nat.mod_mod]
  obtain ⟨e, he, hsum⟩ :=
    gadget_extract3_even hM10 hM11 hM101 hg3 hgev hK (↑trep : ZMod M)
  refine ⟨e, he, (((81 * trep : ℕ) : ZMod (m * 3 ^ v))), ?_, ?_, ?_⟩
  · rw [sum_twt_81]
    set S := ∑ k ∈ Finset.range K,
        e k * (10 ^ (2 * k)
            * ((10 ^ (4 * K + g - 2 - 4 * k) - 1) / 9)) with hS
    have hSM : (↑S : ZMod M) = (↑trep : ZMod M) := by
      rw [hS, Nat.cast_sum, ← hsum]
      apply Finset.sum_congr rfl
      intro k _
      rw [Nat.cast_mul]
    have hSval : S ≡ trep [MOD M] := by
      have hv1 : (↑S : ZMod M).val = (↑trep : ZMod M).val :=
        congrArg ZMod.val hSM
      rw [ZMod.val_natCast, ZMod.val_natCast] at hv1
      rw [Nat.ModEq, hv1]
    have h81M : 81 * S ≡ 81 * trep [MOD 81 * M] :=
      Nat.ModEq.mul_left' 81 hSval
    have h81M' : m * 3 ^ v ∣ 81 * M := by
      rw [hM, show (81 : ℕ) = 3 ^ 4 from by norm_num]
      have hA : 3 ^ 4 * (m * 3 ^ (v - 4)) = m * (3 ^ 4 * 3 ^ (v - 4)) := by
        ring
      rw [hA, ← pow_add]
      exact Nat.mul_dvd_mul_left m (pow_dvd_pow 3 (by omega))
    have h81Mv : 81 * S ≡ 81 * trep [MOD m * 3 ^ v] := by
      rw [Nat.ModEq] at h81M ⊢
      rw [← Nat.mod_mod_of_dvd _ h81M', h81M,
        Nat.mod_mod_of_dvd _ h81M']
    have hcast : ((81 * S : ℕ) : ZMod (m * 3 ^ v))
        = ((81 * trep : ℕ) : ZMod (m * 3 ^ v)) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr h81Mv
    rw [← hcast, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum,
      Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    push_cast
    ring
  · have hc := map_natCast (ZMod.castHom (Nat.dvd_mul_right m (3 ^ v))
        (ZMod m)) (81 * trep)
    rw [hc, Nat.cast_mul, Nat.cast_ofNat, htrep_m]
  · have hc := map_natCast (ZMod.castHom (Nat.dvd_mul_left (3 ^ v) m)
        (ZMod (3 ^ v))) (81 * trep)
    rw [hc]
    have hdvd : 3 ^ v ∣ 81 * 3 ^ (v - 4) := by
      refine ⟨3 ^ (4 - v), ?_⟩
      rw [show (81 : ℕ) = 3 ^ 4 from by norm_num, ← pow_add, ← pow_add]
      congr 1
      omega
    have h81 : 81 * trep ≡ 81 * s₀ [MOD 3 ^ v] :=
      Nat.ModEq.of_dvd hdvd (Nat.ModEq.mul_left' 81 htrep_3)
    have hcast : ((81 * trep : ℕ) : ZMod (3 ^ v))
        = ((81 * s₀ : ℕ) : ZMod (3 ^ v)) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr h81
    rw [hcast]
    push_cast
    ring

set_option maxHeartbeats 800000 in
theorem P_dvd_3m81_even {m v le K g : ℕ} [NeZero m]
    (hm3 : m.Coprime 3) (hm10 : m.Coprime 10)
    (hm11 : m.Coprime 11) (hm101 : m.Coprime 101)
    (de : List ℕ) (hle : de.length = le)
    (C : List ℕ) (hC : C.length = g)
    (hg3 : 3 ≤ g) (hgev : Even g)
    (hKcov : m * 3 ^ (v - 4) ≤ 1 + 9 * (K / 2))
    (s₀ : ℕ)
    (hs0 : (Nat.ofDigits (10 : ZMod (3 ^ v)) de
        + Nat.ofDigits (10 : ZMod (3 ^ v)) de.reverse
            * (10 : ZMod (3 ^ v)) ^ (le + (4 * K + g)))
      + (10 : ZMod (3 ^ v)) ^ le
        * (Nat.ofDigits (10 : ZMod (3 ^ v)) C
            * (10 : ZMod (3 ^ v)) ^ (2 * K)
          + (9 * ∑ k ∈ Finset.range K, palW (3 ^ v) (4 * K + g) (2 * k + 1)
            + 81 * (s₀ : ZMod (3 ^ v)))) = 0) :
    ∃ e' : ℕ → ℕ, (∀ k, e' k ≤ 9)
      ∧ m * 3 ^ v ∣ Nat.ofDigits 10
          (de ++ (((List.range (2 * K)).map (pairDigit e') ++ C)
            ++ ((List.range (2 * K)).map (pairDigit e')).reverse)
            ++ de.reverse) := by
  classical
  set q := m * 3 ^ v with hq
  haveI : NeZero q := ⟨by
    rw [hq]
    exact mul_ne_zero (NeZero.ne m) (pow_ne_zero _ (by norm_num))⟩
  haveI : NeZero (3 ^ v) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hcop81 : m.Coprime 81 := by
    have h := hm3.pow_right 4
    norm_num at h ⊢
    exact h
  have hunit : IsUnit ((10 : ZMod m) ^ le * 81) := by
    rw [show ((10 : ZMod m) ^ le * 81)
        = ((10 ^ le * 81 : ℕ) : ZMod m) from by push_cast; ring]
    rw [ZMod.isUnit_iff_coprime]
    exact Nat.coprime_mul_iff_left.mpr ⟨hm10.symm.pow_left le, hcop81.symm⟩
  set E : ZMod m := Nat.ofDigits (10 : ZMod m) de
      + Nat.ofDigits (10 : ZMod m) de.reverse
          * (10 : ZMod m) ^ (le + (4 * K + g)) with hE
  set X : ZMod m := Nat.ofDigits (10 : ZMod m) C * (10 : ZMod m) ^ (2 * K)
      + 9 * ∑ k ∈ Finset.range K, palW m (4 * K + g) (2 * k + 1) with hX
  set t : ZMod m := -(E + (10 : ZMod m) ^ le * X)
      * ((10 : ZMod m) ^ le * 81)⁻¹ with ht
  obtain ⟨e', he', T, hTsum, hTm, hT3⟩ :=
    extract3_target81_even hm3 hm10 hm11 hm101 hg3 hgev hKcov t s₀
  refine ⟨e', he', ?_⟩
  have hPq : (Nat.ofDigits (10 : ZMod q)
      (de ++ (((List.range (2 * K)).map (pairDigit e') ++ C)
          ++ ((List.range (2 * K)).map (pairDigit e')).reverse)
          ++ de.reverse))
      = (Nat.ofDigits (10 : ZMod q) de
          + Nat.ofDigits (10 : ZMod q) de.reverse
              * (10 : ZMod q) ^ (le + (4 * K + g)))
        + (10 : ZMod q) ^ le
            * (Nat.ofDigits (10 : ZMod q) C * (10 : ZMod q) ^ (2 * K)
              + ∑ k ∈ Finset.range K,
                  ((9 : ZMod q) * palW q (4 * K + g) (2 * k + 1)
                  + (e' k : ZMod q)
                      * (palW q (4 * K + g) (2 * k)
                        - palW q (4 * K + g) (2 * k + 1)))) :=
    gadget_val_m de hle e' he' C hC
  simp only [twt] at hTsum
  have hsumq : ∑ k ∈ Finset.range K,
      ((9 : ZMod q) * palW q (4 * K + g) (2 * k + 1)
        + (e' k : ZMod q)
            * (palW q (4 * K + g) (2 * k) - palW q (4 * K + g) (2 * k + 1)))
      = 9 * (∑ k ∈ Finset.range K, palW q (4 * K + g) (2 * k + 1)) + T := by
    rw [Finset.sum_add_distrib, hTsum, ← Finset.mul_sum]
  rw [hsumq] at hPq
  have hPm : (Nat.ofDigits (10 : ZMod m)
      (de ++ (((List.range (2 * K)).map (pairDigit e') ++ C)
          ++ ((List.range (2 * K)).map (pairDigit e')).reverse)
          ++ de.reverse)) = 0 := by
    have hcast := congrArg (ZMod.castHom (Nat.dvd_mul_right m (3 ^ v))
      (ZMod m)) hPq
    rw [castHom_ofDigits] at hcast
    rw [map_add, map_add, castHom_ofDigits, map_mul, castHom_ofDigits,
      map_pow, castHom_ten] at hcast
    rw [map_mul, map_pow, castHom_ten] at hcast
    rw [map_add, map_mul, castHom_ofDigits, map_pow, castHom_ten] at hcast
    rw [map_add] at hcast
    have h9 : (ZMod.castHom (Nat.dvd_mul_right m (3 ^ v)) (ZMod m))
        (9 * ∑ k ∈ Finset.range K, palW q (4 * K + g) (2 * k + 1))
        = 9 * ∑ k ∈ Finset.range K, palW m (4 * K + g) (2 * k + 1) := by
      rw [map_mul, map_sum, castHom_nine]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      exact castHom_palW _ _ _
    rw [h9, hTm] at hcast
    rw [hcast]
    have htz : ((10 : ZMod m) ^ le * 81) * t
        = -(E + (10 : ZMod m) ^ le * X) := by
      rw [ht]
      rw [show (10 : ZMod m) ^ le * 81
          * (-(E + (10 : ZMod m) ^ le * X) * ((10 : ZMod m) ^ le * 81)⁻¹)
          = -(E + (10 : ZMod m) ^ le * X)
            * ((10 : ZMod m) ^ le * 81 * ((10 : ZMod m) ^ le * 81)⁻¹)
          from by ring]
      rw [ZMod.mul_inv_of_unit _ hunit, mul_one]
    rw [← hE]
    rw [show E + (10 : ZMod m) ^ le * (Nat.ofDigits (10 : ZMod m) C
            * (10 : ZMod m) ^ (2 * K)
          + (9 * ∑ k ∈ Finset.range K, palW m (4 * K + g) (2 * k + 1)
            + 81 * t))
        = E + (10 : ZMod m) ^ le * X + ((10 : ZMod m) ^ le * 81) * t
        from by rw [hX]; ring]
    rw [htz]
    ring
  have hP3 : (Nat.ofDigits (10 : ZMod (3 ^ v))
      (de ++ (((List.range (2 * K)).map (pairDigit e') ++ C)
          ++ ((List.range (2 * K)).map (pairDigit e')).reverse)
          ++ de.reverse)) = 0 := by
    have hcast := congrArg (ZMod.castHom (Nat.dvd_mul_left (3 ^ v) m)
      (ZMod (3 ^ v))) hPq
    rw [castHom_ofDigits] at hcast
    rw [map_add, map_add, castHom_ofDigits, map_mul, castHom_ofDigits,
      map_pow, castHom_ten] at hcast
    rw [map_mul, map_pow, castHom_ten] at hcast
    rw [map_add, map_mul, castHom_ofDigits, map_pow, castHom_ten] at hcast
    rw [map_add] at hcast
    have hsp : (ZMod.castHom (Nat.dvd_mul_left (3 ^ v) m) (ZMod (3 ^ v)))
        (9 * ∑ k ∈ Finset.range K, palW q (4 * K + g) (2 * k + 1))
        = 9 * ∑ k ∈ Finset.range K,
            palW (3 ^ v) (4 * K + g) (2 * k + 1) := by
      rw [map_mul, map_sum, castHom_nine]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      exact castHom_palW _ _ _
    rw [hsp, hT3] at hcast
    rw [hcast]
    linear_combination hs0
  have hdm : m ∣ Nat.ofDigits 10
      (de ++ (((List.range (2 * K)).map (pairDigit e') ++ C)
          ++ ((List.range (2 * K)).map (pairDigit e')).reverse)
          ++ de.reverse) := by
    rw [← CharP.cast_eq_zero_iff (ZMod m) m _]
    rw [cast_ofDigits]
    exact hPm
  have hd3 : 3 ^ v ∣ Nat.ofDigits 10
      (de ++ (((List.range (2 * K)).map (pairDigit e') ++ C)
          ++ ((List.range (2 * K)).map (pairDigit e')).reverse)
          ++ de.reverse) := by
    rw [← CharP.cast_eq_zero_iff (ZMod (3 ^ v)) (3 ^ v) _]
    rw [cast_ofDigits]
    exact hP3
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (hm3.pow_right v) hdm hd3


set_option maxHeartbeats 800000 in
theorem sandwich_spec_gen (D MID : List ℕ) (hD : D ≠ [])
    (hD10 : ∀ x ∈ D, x < 10) (hD0 : D.head hD ≠ 0)
    (hMID : MID.Palindrome) (hd : ∀ x ∈ MID, x < 10)
    {L : List ℕ} (hL : L = D ++ MID ++ D.reverse) {P : ℕ}
    (hP : P = Nat.ofDigits 10 L) :
    P ≠ 0 ∧ (Nat.digits 10 P).Palindrome
      ∧ (Nat.digits 10 P).length = 2 * D.length + MID.length
      ∧ (Nat.digits 10 P).sum = 2 * D.sum + MID.sum := by
  subst hP; subst hL
  have hrevne : D.reverse ≠ [] := List.reverse_ne_nil_iff.mpr hD
  have hall : ∀ x ∈ D ++ MID ++ D.reverse, x < 10 := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · exact hD10 x hx
      · exact hd x hx
    · exact hD10 x (List.mem_reverse.mp hx)
  have hLne : D ++ MID ++ D.reverse ≠ [] := by
    intro h
    exact hrevne (List.append_eq_nil_iff.mp h).2
  have hgl? : (D ++ MID ++ D.reverse).getLast?
      = some (D.head hD) := by
    rw [List.getLast?_append, List.getLast?_reverse]
    have hhd : D.head? = some (D.head hD) := List.head?_eq_some_head hD
    rw [hhd]
    simp
  have hlast : ∀ h : D ++ MID ++ D.reverse ≠ [],
      (D ++ MID ++ D.reverse).getLast h ≠ 0 := by
    intro h
    have heq := (List.getLast_eq_iff_getLast?_eq_some h
      (a := D.head hD)).mpr hgl?
    rw [heq]; exact hD0
  have hdigits : Nat.digits 10 (Nat.ofDigits 10 (D ++ MID ++ D.reverse))
      = D ++ MID ++ D.reverse :=
    Nat.digits_ofDigits 10 (by norm_num) _ hall hlast
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hP0
    rw [hP0] at hdigits
    rw [Nat.digits_zero] at hdigits
    exact hLne hdigits.symm
  · rw [hdigits]
    apply List.Palindrome.of_reverse_eq
    show (D ++ MID ++ D.reverse).reverse = D ++ MID ++ D.reverse
    rw [List.reverse_append, List.reverse_append, List.reverse_reverse,
      hMID.reverse_eq, List.append_assoc]
  · rw [hdigits]
    show (D ++ MID ++ D.reverse).length = _
    simp only [List.length_append, List.length_reverse]
    ring
  · rw [hdigits]
    show (D ++ MID ++ D.reverse).sum = _
    simp only [List.sum_append, List.sum_reverse]
    ring


set_option maxHeartbeats 800000 in
theorem ofDigits_replicate_zero (s : ℕ) :
    Nat.ofDigits 10 (List.replicate s 0) = 0 := by
  induction s with
  | zero => simp [Nat.ofDigits]
  | succ s ih =>
    rw [List.replicate_succ, Nat.ofDigits, ih]
    ring


set_option maxHeartbeats 800000 in
theorem pow25_dvd_pow10 {a' b' k : ℕ} (h : max a' b' ≤ k) :
    2 ^ a' * 5 ^ b' ∣ 10 ^ k := by
  have h10 : (10:ℕ) ^ k = 2 ^ k * 5 ^ k := by
    rw [show (10:ℕ) = 2 * 5 from by norm_num, mul_pow]
  rw [h10]
  exact Nat.mul_dvd_mul (pow_dvd_pow 2 (by omega))
    (pow_dvd_pow 5 (by omega))


set_option maxHeartbeats 800000 in
def r0b (a' b' q : ℕ) : ℕ :=
  (3 ^ (q - 2) - (Nat.digits 10 (9 * 2 ^ a' * 5 ^ b')).sum / 9 % 3 ^ (q - 2))
    % 3 ^ (q - 2)


set_option maxHeartbeats 800000 in
def rhob (a' b' q : ℕ) : ℕ :=
  ((Nat.digits 10 (9 * 2 ^ a' * 5 ^ b')).sum / 9 + r0b a' b' q) / 3 ^ (q - 2)


set_option maxHeartbeats 800000 in
theorem border_pal {a' b' q s₁ t : ℕ} (hq : 4 ≤ q)
    (hmin : a' = 0 ∨ b' = 0) (hs₁ : max a' b' ≤ s₁) :
    ∃ D : List ℕ, D.Palindrome ∧ (∀ x ∈ D, x < 10) ∧ D ≠ []
      ∧ (∀ h : D ≠ [], D.head h ≠ 0)
      ∧ 2 ^ a' * 5 ^ b' ∣ Nat.ofDigits 10 D
      ∧ ((Nat.ofDigits 10 D : ZMod 81) = 0)
      ∧ (D.sum = 2 * 3 ^ q * (rhob a' b' q + t))
      ∧ (r0b a' b' q < 3 ^ (q - 2)
          ∧ D.length = 2 * ((Nat.digits 10 (9 * 2 ^ a' * 5 ^ b')).length
              + s₁ + r0b a' b' q) + 2 * 3 ^ (q - 2) * t) := by
  classical
  set V := 9 * 2 ^ a' * 5 ^ b' with hV
  have hV9 : 9 ∣ V := ⟨2 ^ a' * 5 ^ b', by rw [hV]; ring⟩
  have hVpos : 0 < V := by
    rw [hV]
    positivity
  have h9sdV : 9 ∣ (Nat.digits 10 V).sum := by
    have hmod := Nat.modEq_nine_digits_sum V
    have : (Nat.digits 10 V).sum % 9 = 0 := by
      have h' := hmod
      rw [Nat.ModEq] at h'
      rw [h'.symm]
      exact Nat.mod_eq_zero_of_dvd hV9
    exact Nat.dvd_of_mod_eq_zero this
  set sdV := (Nat.digits 10 V).sum / 9 with hsdV
  have hsdV9 : 9 * sdV = (Nat.digits 10 V).sum :=
    Nat.mul_div_cancel' h9sdV
  set p3 := 3 ^ (q - 2) with hp3
  have hp3pos : 0 < p3 := pow_pos (by norm_num) _
  set r₀ := (p3 - sdV % p3) % p3 with hr₀
  have hr₀lt : r₀ < p3 := Nat.mod_lt _ hp3pos
  set w' := r₀ + p3 * t with hw'
  set X := Nat.digits 10 V ++ List.replicate s₁ 0
      ++ List.replicate w' 9 with hX
  have hX10 : ∀ x ∈ X, x < 10 := by
    intro x hx
    rw [hX] at hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · exact Nat.digits_lt_base' (b := 8) hx
      · have := List.mem_replicate.mp hx
        omega
    · have := List.mem_replicate.mp hx
      omega
  have hXne : X ≠ [] := by
    rw [hX]
    intro h
    have h1 := (List.append_eq_nil_iff.mp
      (List.append_eq_nil_iff.mp h).1).1
    exact (Nat.digits_ne_nil_iff_ne_zero.mpr hVpos.ne') h1
  have hsigX : X.sum = 9 * (sdV + w') := by
    rw [hX, List.sum_append, List.sum_append, List.sum_replicate,
      List.sum_replicate, ← hsdV9]
    ring
  have hsdwr : (sdV + r₀) % p3 = 0 := by
    have hlt : sdV % p3 < p3 := Nat.mod_lt _ hp3pos
    by_cases hz : sdV % p3 = 0
    · have hr0z : r₀ = 0 := by
        rw [hr₀, hz, Nat.sub_zero, Nat.mod_self]
      rw [hr0z, Nat.add_zero]
      exact hz
    · apply Nat.mod_eq_zero_of_dvd
      refine ⟨sdV / p3 + 1, ?_⟩
      have hdm : p3 * (sdV / p3) + sdV % p3 = sdV := Nat.div_add_mod _ _
      have h1 : p3 - sdV % p3 < p3 := by omega
      have h2 : r₀ = p3 - sdV % p3 := by
        rw [hr₀]
        exact Nat.mod_eq_of_lt h1
      rw [h2, Nat.mul_succ]
      omega
  obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero hsdwr
  have hsigX3 : X.sum = 3 ^ q * (c + t) := by
    rw [hsigX]
    rw [show sdV + w' = p3 * c + p3 * t from by
      rw [hw', ← hc]; ring]
    rw [show (3 : ℕ) ^ q = 9 * 3 ^ (q - 2) from by
      rw [show (9 : ℕ) = 3 ^ 2 from by norm_num, ← pow_add,
        show 2 + (q - 2) = q from by omega]]
    rw [← hp3]
    ring
  set D := X ++ X.reverse with hD
  have hDpal : D.Palindrome := hD.symm ▸ List.Palindrome.append_reverse X
  have hD10 : ∀ x ∈ D, x < 10 := by
    intro x hx
    rcases List.mem_append.mp (hD ▸ hx) with hx | hx
    · exact hX10 x hx
    · exact hX10 x (List.mem_reverse.mp hx)
  have hDne : D ≠ [] := by
    rw [hD]
    intro h
    have := List.append_eq_nil_iff.mp h
    exact hXne this.1
  have hV10 : V % 10 ≠ 0 := by
    intro h0
    have h10d : 10 ∣ V := Nat.dvd_of_mod_eq_zero h0
    rcases hmin with rfl | rfl
    · rw [hV, pow_zero, mul_one] at h10d
      have h2 : 2 ∣ 9 * 5 ^ b' := dvd_trans (by norm_num : 2 ∣ 10) h10d
      have hmod : (9 * 5 ^ b') ≡ 1 [MOD 2] := by
        have h5 : (5 : ℕ) ≡ 1 [MOD 2] := by decide
        have := Nat.ModEq.mul (by decide : (9 : ℕ) ≡ 1 [MOD 2])
          (Nat.ModEq.pow b' h5)
        simpa using this
      rw [Nat.ModEq] at hmod
      rw [Nat.mod_eq_zero_of_dvd h2] at hmod
      norm_num at hmod
    · rw [hV, pow_zero, mul_one] at h10d
      have h5 : 5 ∣ 9 * 2 ^ a' := dvd_trans (by norm_num : 5 ∣ 10) h10d
      have hcop : (5 : ℕ).Coprime (2 ^ a') :=
        (Nat.coprime_comm.mp (by decide : Nat.Coprime 2 5)).pow_right _
      have h9 : 5 ∣ 9 := hcop.dvd_of_dvd_mul_right h5
      norm_num at h9
  have hVhead : (Nat.digits 10 V).head? = some (V % 10) := by
    rw [Nat.digits_def' (by norm_num) hVpos]
    rfl
  have hXhead : X.head? = some (V % 10) := by
    rw [hX, List.head?_append, List.head?_append, hVhead]
    simp
  have hD0 : ∀ h : D ≠ [], D.head h ≠ 0 := by
    intro h
    have e3 : D.head? = some (V % 10) := by
      rw [hD, List.head?_append, hXhead]
      simp
    have e4 : D.head? = some (D.head h) := List.head?_eq_some_head h
    rw [e3] at e4
    have hh : D.head h = V % 10 := Option.some.inj e4.symm
    rw [hh]
    exact hV10
  have hofDX : Nat.ofDigits 10 X
      = V + 10 ^ ((Nat.digits 10 V).length + s₁) * (10 ^ w' - 1) := by
    rw [hX, ofDigits_append', ofDigits_append', ofDigits_replicate_zero,
      ofDigits_rep9, Nat.ofDigits_digits]
    rw [List.length_append, List.length_replicate]
    ring
  have hofDX_dvd : 2 ^ a' * 5 ^ b' ∣ Nat.ofDigits 10 X := by
    rw [hofDX]
    apply Nat.dvd_add
    · rw [hV]
      exact ⟨9, by ring⟩
    · apply dvd_mul_of_dvd_left
      apply pow25_dvd_pow10
      omega
  have hofDD : Nat.ofDigits 10 D
      = Nat.ofDigits 10 X + 10 ^ X.length
          * Nat.ofDigits 10 X.reverse := by
    rw [hD]
    rw [ofDigits_append']
  have hXl : X.length = (Nat.digits 10 V).length + s₁ + w' := by
    rw [hX, List.length_append, List.length_append,
      List.length_replicate, List.length_replicate]
  refine ⟨D, hDpal, hD10, hDne, hD0, ?_, ?_, ?_, ?_⟩
  · rw [hofDD]
    apply Nat.dvd_add hofDX_dvd
    apply dvd_mul_of_dvd_left
    apply pow25_dvd_pow10
    omega
  · have hmod := pal_mod81_even X
    have hsig81 : ((X.sum : ℕ) : ZMod 81) = 0 := by
      rw [hsigX3]
      have h81d : 81 ∣ 3 ^ q * (c + t) :=
        dvd_mul_of_dvd_left (pow_dvd_pow 3 hq) _
      exact (CharP.cast_eq_zero_iff (ZMod 81) 81 _).mpr h81d
    rw [hD, hmod, hsig81, zero_mul]
  · have hceq : rhob a' b' q = c := by
      show ((Nat.digits 10 (9 * 2 ^ a' * 5 ^ b')).sum / 9 + r0b a' b' q)
          / 3 ^ (q - 2) = c
      rw [← hV]
      show (sdV + r₀) / p3 = c
      conv_lhs => rw [hc, mul_comm p3 c]
      exact Nat.mul_div_cancel _ hp3pos
    rw [hceq, hD, List.sum_append, List.sum_reverse, hsigX3]
    ring
  · refine ⟨?_, ?_⟩
    · show r0b a' b' q < 3 ^ (q - 2)
      exact hr₀lt
    · show D.length = 2 * ((Nat.digits 10 V).length + s₁ + r₀) + 2 * p3 * t
      rw [hD, List.length_append, List.length_reverse, hXl, hw']
      ring

end A084017


namespace A084017
open Finset List Nat BigOperators Pointwise


set_option maxHeartbeats 800000 in
theorem B_dvd_P {a' b' le : ℕ} {de MID : List ℕ} (hle : de.length = le)
    (he : 2 ^ a' * 5 ^ b' ∣ Nat.ofDigits 10 de) (hle_big : max a' b' ≤ le) :
    2 ^ a' * 5 ^ b' ∣ Nat.ofDigits 10 (de ++ MID ++ de.reverse) := by
  rw [ofDigits_append', ofDigits_append']
  apply Nat.dvd_add
  · apply Nat.dvd_add he
    apply dvd_mul_of_dvd_left
    rw [hle]
    exact pow25_dvd_pow10 hle_big
  · apply dvd_mul_of_dvd_left
    apply pow25_dvd_pow10
    rw [List.length_append, hle]
    omega


set_option maxHeartbeats 800000 in
theorem n_dvd_P_pow10 {a b v m z a' b' P : ℕ}
    (h25 : 2 ^ a' * 5 ^ b' ∣ P) (h3m : 3 ^ v * m ∣ P)
    (ha : a' + z = a) (hb : b' + z = b) (hm30 : m.Coprime 30) :
    2 ^ a * 5 ^ b * 3 ^ v * m ∣ P * 10 ^ z := by
  have hm2 : m.Coprime 2 := by
    have h : Nat.Coprime 2 m := (Nat.prime_two.coprime_iff_not_dvd).mpr
      (by
        intro h2
        have h2g : (2:ℕ) ∣ m.gcd 30 := Nat.dvd_gcd h2 (by norm_num)
        have hg : m.gcd 30 = 1 := hm30
        rw [hg] at h2g
        norm_num at h2g)
    exact h.symm
  have hm5 : m.Coprime 5 := by
    have h : Nat.Coprime 5 m := (Nat.prime_five.coprime_iff_not_dvd).mpr
      (by
        intro h5
        have h5g : (5:ℕ) ∣ m.gcd 30 := Nat.dvd_gcd h5 (by norm_num)
        have hg : m.gcd 30 = 1 := hm30
        rw [hg] at h5g
        norm_num at h5g)
    exact h.symm
  have hcop : (2 ^ a' * 5 ^ b').Coprime (3 ^ v * m) := by
    apply Nat.coprime_mul_iff_right.mpr
    constructor
    · apply Nat.Coprime.mul_left
      · exact ((by decide : Nat.Coprime 2 3).pow_right v).pow_left a'
      · exact ((by decide : Nat.Coprime 5 3).pow_right v).pow_left b'
    · apply Nat.Coprime.mul_left
      · exact (hm2.symm.pow_left a')
      · exact (hm5.symm.pow_left b')
  have hjoin : 2 ^ a' * 5 ^ b' * (3 ^ v * m) ∣ P :=
    hcop.mul_dvd_of_dvd_of_dvd h25 h3m
  have h10 : 10 ^ z = 2 ^ z * 5 ^ z := by
    rw [show (10 : ℕ) = 2 * 5 from by norm_num, mul_pow]
  have h2a : 2 ^ a = 2 ^ a' * 2 ^ z := by rw [← ha, pow_add]
  have h5b : 5 ^ b = 5 ^ b' * 5 ^ z := by rw [← hb, pow_add]
  rw [h2a, h5b, h10]
  have hfactor : 2 ^ a' * 2 ^ z * (5 ^ b' * 5 ^ z) * 3 ^ v * m
      = (2 ^ a' * 5 ^ b' * (3 ^ v * m)) * (2 ^ z * 5 ^ z) := by ring
  rw [hfactor]
  exact Nat.mul_dvd_mul_right hjoin _

end A084017

namespace A084017
open Finset List Nat BigOperators Pointwise


set_option maxHeartbeats 800000 in
theorem repunit100_mod9 (K : ℕ) :
    (∑ k ∈ Finset.range K, (100 : ℕ) ^ k) ≡ K [MOD 9] := by
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_sum]
  simp only [Nat.cast_pow]
  have h100 : ((100 : ℕ) : ZMod 9) = 1 := by decide
  rw [h100]
  simp


set_option maxHeartbeats 800000 in
theorem hs0_solver {v le K g : ℕ} (hv : 5 ≤ v) (hK1 : 1 ≤ K)
    (de : List ℕ)
    (hde_pal : de.reverse = de)
    (hde81 : 81 ∣ Nat.ofDigits 10 de)
    (C : List ℕ)
    (hC81 : 81 ∣ Nat.ofDigits 10 C)
    (hK9 : 9 ∣ K) :
    ∃ s₀ : ℕ,
      (Nat.ofDigits (10 : ZMod (3 ^ v)) de
          + Nat.ofDigits (10 : ZMod (3 ^ v)) de.reverse
              * (10 : ZMod (3 ^ v)) ^ (le + (4 * K + g)))
        + (10 : ZMod (3 ^ v)) ^ le
          * (Nat.ofDigits (10 : ZMod (3 ^ v)) C
              * (10 : ZMod (3 ^ v)) ^ (2 * K)
            + (9 * ∑ k ∈ Finset.range K, palW (3 ^ v) (4 * K + g) (2 * k + 1)
              + 81 * (s₀ : ZMod (3 ^ v)))) = 0 := by
  haveI : NeZero (3 ^ (v - 4)) := ⟨pow_ne_zero _ (by norm_num)⟩
  haveI : NeZero (3 ^ v) := ⟨pow_ne_zero _ (by norm_num)⟩
  obtain ⟨eb, heb⟩ := hde81
  obtain ⟨cb, hcb⟩ := hC81
  
  have hR9 : 9 ∣ (10 + 10 ^ (2 * K + g))
      * ∑ k ∈ Finset.range K, (100 : ℕ) ^ k := by
    have h1 : ((10 + 10 ^ (2 * K + g)) : ℕ) ≡ 2 [MOD 9] := by
      have h10 : (10 : ℕ) ≡ 1 [MOD 9] := by decide
      have hp := Nat.ModEq.pow (2 * K + g) h10
      have := h10.add hp
      simpa using this
    have hmod := Nat.ModEq.mul h1 (repunit100_mod9 K)
    have h2K : 2 * K ≡ 0 [MOD 9] := Nat.modEq_zero_iff_dvd.mpr (by
      rw [mul_comm]
      exact dvd_mul_of_dvd_left hK9 2)
    exact Nat.modEq_zero_iff_dvd.mp (hmod.trans h2K)
  obtain ⟨wb, hwb⟩ := hR9
  
  set rest : ℕ := eb * (1 + 10 ^ (le + (4 * K + g)))
      + 10 ^ le * (cb * 10 ^ (2 * K) + wb) with hrest
  have hunit : IsUnit (((10 ^ le : ℕ) : ZMod (3 ^ (v - 4)))) := by
    rw [ZMod.isUnit_iff_coprime]
    exact ((by decide : Nat.Coprime 10 3).pow_right (v - 4)).pow_left le
  set s₀z : ZMod (3 ^ (v - 4)) := -↑rest * ((10 ^ le : ℕ) : ZMod (3 ^ (v - 4)))⁻¹ with hs₀z
  set s₀ : ℕ := s₀z.val with hs₀
  have hB'0 : ((rest + 10 ^ le * s₀ : ℕ) : ZMod (3 ^ (v - 4))) = 0 := by
    rw [Nat.cast_add, Nat.cast_mul, hs₀, ZMod.natCast_val, ZMod.cast_id]
    have hmul : ((10 ^ le : ℕ) : ZMod (3 ^ (v - 4))) * s₀z = -↑rest := by
      have hinv : ((10 ^ le : ℕ) : ZMod (3 ^ (v - 4)))
          * ((10 ^ le : ℕ) : ZMod (3 ^ (v - 4)))⁻¹ = 1 :=
        ZMod.mul_inv_of_unit _ hunit
      calc ((10 ^ le : ℕ) : ZMod (3 ^ (v - 4))) * s₀z
          = -↑rest * (((10 ^ le : ℕ) : ZMod (3 ^ (v - 4)))
              * ((10 ^ le : ℕ) : ZMod (3 ^ (v - 4)))⁻¹) := by
            rw [hs₀z]; ring
        _ = -↑rest * 1 := by rw [hinv]
        _ = -↑rest := by ring
    rw [hmul, add_neg_cancel]
  have hdv : 3 ^ (v - 4) ∣ rest + 10 ^ le * s₀ :=
    (CharP.cast_eq_zero_iff (ZMod (3 ^ (v - 4))) (3 ^ (v - 4)) _).mp hB'0
  obtain ⟨w', hw'⟩ := hdv
  
  refine ⟨s₀, ?_⟩
  
  have hLHS : (Nat.ofDigits (10 : ZMod (3 ^ v)) de
      + Nat.ofDigits (10 : ZMod (3 ^ v)) de.reverse
          * (10 : ZMod (3 ^ v)) ^ (le + (4 * K + g)))
    + (10 : ZMod (3 ^ v)) ^ le
      * (Nat.ofDigits (10 : ZMod (3 ^ v)) C
          * (10 : ZMod (3 ^ v)) ^ (2 * K)
        + (9 * ∑ k ∈ Finset.range K, palW (3 ^ v) (4 * K + g) (2 * k + 1)
          + 81 * (s₀ : ZMod (3 ^ v))))
      = ((81 * (rest + 10 ^ le * s₀) : ℕ) : ZMod (3 ^ v)) := by
    rw [hde_pal]
    rw [← cast_ofDigits, ← cast_ofDigits]
    
    rw [heb, hcb]
    have hso := sum_palW_odd (m := 3 ^ v) (K := K) (g := g) hK1
    rw [hso]
    
    have hgeo : ∑ k ∈ Finset.range K, (10 : ZMod (3 ^ v)) ^ (2 * k)
        = ((∑ k ∈ Finset.range K, (100 : ℕ) ^ k : ℕ) : ZMod (3 ^ v)) := by
      rw [Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [pow_mul]
      have h2 : (10 : ZMod (3 ^ v)) ^ 2 = ((100 : ℕ) : ZMod (3 ^ v)) := by
        norm_cast
      rw [h2]
      exact (Nat.cast_pow ..).symm
    rw [hgeo]
    
    rw [show (10 + (10 : ZMod (3 ^ v)) ^ (2 * K + g))
        = ((10 + 10 ^ (2 * K + g) : ℕ) : ZMod (3 ^ v)) from by
          push_cast; ring]
    rw [← Nat.cast_mul, hwb, hrest]
    push_cast
    ring
  rw [hLHS]
  
  have h81 : (81 : ℕ) * (rest + 10 ^ le * s₀) = 3 ^ v * w' := by
    rw [hw']
    rw [show (81 : ℕ) = 3 ^ 4 from by norm_num, ← mul_assoc, ← pow_add,
      show 4 + (v - 4) = v from by omega]
  rw [h81]
  exact (CharP.cast_eq_zero_iff (ZMod (3 ^ v)) (3 ^ v) _).mpr (dvd_mul_right _ _)

end A084017

namespace A084017
open Finset List Nat BigOperators Pointwise


set_option maxHeartbeats 800000 in
theorem hs0_v4 {v le K g : ℕ} (hv2 : 2 ≤ v) (hv4 : v ≤ 4) (hK1 : 1 ≤ K)
    (de : List ℕ) (hde_pal : de.reverse = de)
    (hde3v : 3 ^ v ∣ Nat.ofDigits 10 de)
    (C : List ℕ) (hC3v : 3 ^ v ∣ Nat.ofDigits 10 C)
    (hKv : 3 ^ (v - 2) ∣ K) :
    ∃ s₀ : ℕ,
      (Nat.ofDigits (10 : ZMod (3 ^ v)) de
          + Nat.ofDigits (10 : ZMod (3 ^ v)) de.reverse
              * (10 : ZMod (3 ^ v)) ^ (le + (4 * K + g)))
        + (10 : ZMod (3 ^ v)) ^ le
          * (Nat.ofDigits (10 : ZMod (3 ^ v)) C
              * (10 : ZMod (3 ^ v)) ^ (2 * K)
            + (9 * ∑ k ∈ Finset.range K, palW (3 ^ v) (4 * K + g) (2 * k + 1)
              + 81 * (s₀ : ZMod (3 ^ v)))) = 0 := by
  haveI : NeZero (3 ^ v) := ⟨pow_ne_zero _ (by norm_num)⟩
  refine ⟨0, ?_⟩
  have hde0 : Nat.ofDigits (10 : ZMod (3 ^ v)) de = 0 := by
    rw [← cast_ofDigits]
    exact (CharP.cast_eq_zero_iff (ZMod (3 ^ v)) (3 ^ v) _).mpr hde3v
  have hde0' : Nat.ofDigits (10 : ZMod (3 ^ v)) de.reverse = 0 := by
    rw [hde_pal]; exact hde0
  have hC0 : Nat.ofDigits (10 : ZMod (3 ^ v)) C = 0 := by
    rw [← cast_ofDigits]
    exact (CharP.cast_eq_zero_iff (ZMod (3 ^ v)) (3 ^ v) _).mpr hC3v
  have h9S : (9 : ZMod (3 ^ v))
      * ∑ k ∈ Finset.range K, palW (3 ^ v) (4 * K + g) (2 * k + 1) = 0 := by
    rcases Nat.lt_or_ge v 3 with hv | hv
    · have h9 : ((9 : ℕ) : ZMod (3 ^ v)) = 0 := by
        have hd : 3 ^ v ∣ 3 ^ 2 := pow_dvd_pow 3 (by omega)
        norm_num at hd
        exact (CharP.cast_eq_zero_iff (ZMod (3 ^ v)) (3 ^ v) _).mpr hd
      rw [show (9 : ZMod (3 ^ v)) = ((9 : ℕ) : ZMod (3 ^ v)) from by norm_cast]
      rw [h9, zero_mul]
    · have hso := sum_palW_odd (m := 3 ^ v) (K := K) (g := g) hK1
      rw [hso]
      have hgeo : ∑ k ∈ Finset.range K, (10 : ZMod (3 ^ v)) ^ (2 * k)
          = ((∑ k ∈ Finset.range K, (100 : ℕ) ^ k : ℕ) : ZMod (3 ^ v)) := by
        rw [Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [pow_mul]
        have h2 : (10 : ZMod (3 ^ v)) ^ 2 = ((100 : ℕ) : ZMod (3 ^ v)) := by
          norm_cast
        rw [h2]
        exact (Nat.cast_pow ..).symm
      rw [hgeo]
      rw [show (10 + (10 : ZMod (3 ^ v)) ^ (2 * K + g))
          = ((10 + 10 ^ (2 * K + g) : ℕ) : ZMod (3 ^ v)) from by
            push_cast; ring]
      rw [← Nat.cast_mul]
      rw [show (9 : ZMod (3 ^ v)) = ((9 : ℕ) : ZMod (3 ^ v)) from by norm_cast]
      rw [← Nat.cast_mul]
      rw [CharP.cast_eq_zero_iff (ZMod (3 ^ v)) (3 ^ v) _]
      have hmod : (10 + 10 ^ (2 * K + g)) * (∑ k ∈ Finset.range K, 100 ^ k)
          ≡ 2 * K [MOD 9] := by
        have h1 : ((10 + 10 ^ (2 * K + g)) : ℕ) ≡ 2 [MOD 9] := by
          have h10 : (10 : ℕ) ≡ 1 [MOD 9] := by decide
          have hp := Nat.ModEq.pow (2 * K + g) h10
          simpa using h10.add hp
        exact Nat.ModEq.mul h1 (repunit100_mod9 K)
      have h3v2 : 3 ^ (v - 2) ∣ (10 + 10 ^ (2 * K + g))
          * ∑ k ∈ Finset.range K, 100 ^ k := by
        have h9' : (10 + 10 ^ (2 * K + g)) * (∑ k ∈ Finset.range K, 100 ^ k)
            ≡ 2 * K [MOD 3 ^ (v - 2)] :=
          Nat.ModEq.of_dvd (show 3 ^ (v - 2) ∣ 9 from by
            have h : 3 ^ (v - 2) ∣ 3 ^ 2 := pow_dvd_pow 3 (by omega)
            norm_num at h ⊢; exact h) hmod
        have h2K0 : 2 * K ≡ 0 [MOD 3 ^ (v - 2)] :=
          Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right hKv 2)
        exact Nat.modEq_zero_iff_dvd.mp (h9'.trans h2K0)
      rw [show (3 : ℕ) ^ v = 9 * 3 ^ (v - 2) from by
        rw [show (9 : ℕ) = 3 ^ 2 from by norm_num, ← pow_add,
          show 2 + (v - 2) = v from by omega]]
      exact Nat.mul_dvd_mul_left 9 h3v2
  rw [hde0, hde0', hC0, h9S]
  simp

end A084017


namespace A084017
open Finset List Nat BigOperators Pointwise


set_option maxHeartbeats 800000 in
theorem sigma_t_solve {v ρ S M : ℕ} (hM : 0 < M)
    (hcop : (4 * 3 ^ v).Coprime M) :
    ∃ t : ℕ, t < M ∧ M ∣ 4 * 3 ^ v * (ρ + t) + 18 * S := by
  haveI : NeZero M := ⟨hM.ne'⟩
  set u : ZMod M := ((4 * 3 ^ v : ℕ) : ZMod M) with hu
  have hunit : IsUnit u := by
    rw [hu, ZMod.isUnit_iff_coprime]
    exact hcop
  set t : ℕ := (-(↑(4 * 3 ^ v * ρ + 18 * S) * u⁻¹) : ZMod M).val with ht
  have hkey : u * (t : ZMod M) = -(↑(4 * 3 ^ v * ρ + 18 * S) : ZMod M) := by
    show u * ((-(↑(4 * 3 ^ v * ρ + 18 * S) * u⁻¹) : ZMod M).val : ZMod M) = _
    rw [ZMod.natCast_val, ZMod.cast_id]
    calc u * (-(↑(4 * 3 ^ v * ρ + 18 * S) * u⁻¹))
        = -(u * (↑(4 * 3 ^ v * ρ + 18 * S) * u⁻¹)) := by rw [mul_neg]
      _ = -(↑(4 * 3 ^ v * ρ + 18 * S) * (u * u⁻¹)) := by ring
      _ = -↑(4 * 3 ^ v * ρ + 18 * S) := by
          rw [ZMod.mul_inv_of_unit _ hunit]; ring
  refine ⟨t, ?_, ?_⟩
  · show t < M
    exact ZMod.val_lt _
  · have hcast : ((4 * 3 ^ v * (ρ + t) + 18 * S : ℕ) : ZMod M) = 0 := by
      have hu' : u = (4 : ZMod M) * (3 : ZMod M) ^ v := by
        rw [hu]; push_cast; ring
      have hkey2 : u * (t : ZMod M) = -(u * ↑ρ + 18 * ↑S) := by
        rw [hkey]
        congr 1
        rw [hu]
        push_cast
        ring
      have hstep : u * ((ρ : ZMod M) + (t : ZMod M)) + 18 * (S : ZMod M)
          = 0 := by
        linear_combination hkey2
      have heq : ((4 * 3 ^ v * (ρ + t) + 18 * S : ℕ) : ZMod M)
          = u * (↑ρ + ↑t) + 18 * ↑S := by
        rw [hu']
        push_cast
        ring
      rw [heq, hstep]
    exact (CharP.cast_eq_zero_iff (ZMod M) M _).mp hcast


set_option maxHeartbeats 800000 in
theorem five_pow_bound (b : ℕ) : 8 * b + 5 ≤ 27 * 5 ^ b := by
  induction b with
  | zero => norm_num
  | succ k ih =>
    have h5k : 1 ≤ 5 ^ k := Nat.one_le_pow _ _ (by norm_num)
    calc 8 * (k + 1) + 5 = (8 * k + 5) + 8 := by ring
      _ ≤ 27 * 5 ^ k + 8 := by omega
      _ ≤ 27 * 5 * 5 ^ k := by omega
      _ = 27 * 5 ^ (k + 1) := by ring


set_option maxHeartbeats 800000 in
theorem assemble_v5 {b v m : ℕ} (hm30 : m.Coprime 30)
    (hv : 5 ≤ v) (hm : (2 ≤ m) ∨ (m = 1 ∧ 1 ≤ b)) :
    ∃ P z : ℕ, P ≠ 0
      ∧ (0 < z → 10 ∣ 5 ^ b * 3 ^ v * m)
      ∧ (Nat.digits 10 P).Palindrome
      ∧ (Nat.digits 10 P).length + z = 5 ^ b * 3 ^ v * m
      ∧ 5 ^ b * 3 ^ v * m ∣ P * 10 ^ z
      ∧ 5 ^ b * 3 ^ v * m ∣ (Nat.digits 10 P).sum := by
  classical
  have hm0 : 0 < m := by rcases hm with h | ⟨h, _⟩ <;> omega
  haveI : NeZero m := ⟨hm0.ne'⟩
  have hm3 : m.Coprime 3 := hm30.coprime_dvd_right (by norm_num)
  have hm10 : m.Coprime 10 := hm30.coprime_dvd_right (by norm_num)
  have hm2 : m.Coprime 2 := hm30.coprime_dvd_right (by norm_num)
  set K := m * 3 ^ (v - 2) with hK
  set j := 3 ^ (v - 2) with hj
  set M := m * 5 ^ b with hM
  have hM0 : 0 < M := by
    rw [hM]
    exact Nat.mul_pos hm0 (pow_pos (by norm_num) _)
  have h4m : (4 : ℕ).Coprime m := hm2.symm.pow_left 2
  have h3vm : (3 ^ v).Coprime m := hm3.symm.pow_left v
  have h45b : (4 : ℕ).Coprime (5 ^ b) := (by decide : Nat.Coprime 4 5).pow_right b
  have h3v5b : (3 ^ v).Coprime (5 ^ b) :=
    ((by decide : Nat.Coprime 3 5).pow_right b).pow_left v
  have hcop43 : (4 * 3 ^ v).Coprime M := by
    rw [hM]
    exact Nat.Coprime.mul_right (h4m.mul_left h3vm) (h45b.mul_left h3v5b)
  obtain ⟨t, htlt, htdvd⟩ := sigma_t_solve (v := v) (ρ := rhob 0 b v)
    (S := K + j) (M := M) hM0 hcop43
  obtain ⟨D, hDpal, hD10, hDne, hD0, hD25, hD81, hDσ, hr₀lt, hlenD⟩ :=
    border_pal (a' := 0) (b' := b) (q := v) (s₁ := b) (t := t)
      (by omega) (Or.inl rfl) (by simp)
  set lenD := D.length with hlenD'
  have hv2 : 2 ≤ v := by omega
  
  have lenV_le : (Nat.digits 10 (9 * 2 ^ 0 * 5 ^ b)).length ≤ b + 2 := by
    have hVpos : (9 * 2 ^ 0 * 5 ^ b : ℕ) ≠ 0 := by positivity
    have hb := Nat.base_pow_length_digits_le 10 (9 * 2 ^ 0 * 5 ^ b)
      (by norm_num) hVpos
    have hlt : 10 * (9 * 2 ^ 0 * 5 ^ b) < 10 ^ (b + 2) := by
      have h1 : (5 : ℕ) ^ b ≤ 10 ^ b := Nat.pow_le_pow_left (by norm_num) b
      calc 10 * (9 * 2 ^ 0 * 5 ^ b) = 90 * 5 ^ b := by ring
        _ ≤ 90 * 10 ^ b := Nat.mul_le_mul_left 90 h1
        _ < 100 * 10 ^ b := by omega
        _ = 10 ^ (b + 2) := by ring
    have hpow : 10 ^ ((Nat.digits 10 (9 * 2 ^ 0 * 5 ^ b)).length)
        < 10 ^ (b + 2) := lt_of_le_of_lt hb hlt
    have hlt' := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 10)).mp hpow
    omega
  
  have hnodd : Odd (5 ^ b * 3 ^ v * m) := by
    have h5o : Odd (5 ^ b) := Odd.pow (by decide : Odd 5)
    have h3o : Odd (3 ^ v) := Odd.pow (by decide : Odd 3)
    have hmo : Odd m := by
      have h2 : ¬ (2 : ℕ) ∣ m :=
        (Nat.prime_two.coprime_iff_not_dvd).mp hm2.symm
      rw [← Nat.not_even_iff_odd]
      rintro ⟨c, hc⟩
      exact h2 ⟨c, by omega⟩
    exact (h5o.mul h3o).mul hmo
  have hSodd : Odd (1 + 4 * K + 2 * j + 2 * lenD) := by
    have hev : Even (4 * K + 2 * j + 2 * lenD) := by
      have e1 : Even (4 * K) := ⟨2 * K, by ring⟩
      have e2 : Even (2 * j) := ⟨j, by ring⟩
      have e3 : Even (2 * lenD) := ⟨lenD, by ring⟩
      exact (e1.add e2).add e3
    have := hev.add_one
    convert this using 1
    ring
  set X := 5 ^ b * 3 ^ v * m
      - (1 + 4 * K + 2 * j + 2 * lenD) with hX
  have hXeven : Even X := by
    obtain ⟨an, han⟩ := hnodd
    obtain ⟨as, has⟩ := hSodd
    use an - as
    rw [hX, han, has]
    omega
  set T := X / 2 with hT
  have hbound : 1 + 4 * K + 2 * j + 2 * lenD ≤ 5 ^ b * 3 ^ v * m := by
    have hvdec : 3 ^ v = 9 * 3 ^ (v - 2) := by
      rw [show (9 : ℕ) = 3 ^ 2 from by norm_num, ← pow_add,
        show 2 + (v - 2) = v from by omega]
    have hd : 2 * lenD ≤ 8 * b + 4 + 4 * (3 ^ (v - 2) * (m * 5 ^ b)) := by
      rw [hlenD]
      have ht' : t + 1 ≤ m * 5 ^ b := htlt
      have h2 : 4 * (3 ^ (v - 2) * t)
          ≤ 4 * (3 ^ (v - 2) * (m * 5 ^ b - 1)) :=
        Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left (3 ^ (v - 2)) (by omega))
      calc 2 * (2 * ((Nat.digits 10 (9 * 2 ^ 0 * 5 ^ b)).length + b
              + r0b 0 b v) + 2 * 3 ^ (v - 2) * t)
          = 4 * ((Nat.digits 10 (9 * 2 ^ 0 * 5 ^ b)).length + b + r0b 0 b v)
            + 4 * (3 ^ (v - 2) * t) := by ring
        _ ≤ 4 * ((b + 2) + b + (3 ^ (v - 2) - 1))
            + 4 * (3 ^ (v - 2) * (m * 5 ^ b - 1)) := by
          apply Nat.add_le_add _ h2
          apply Nat.mul_le_mul_left
          omega
        _ ≤ 8 * b + 4 + 4 * (3 ^ (v - 2) * (m * 5 ^ b)) := by
          rw [Nat.mul_sub]
          have h1 : 1 ≤ 3 ^ (v - 2) := Nat.one_le_pow _ _ (by norm_num)
          have hM1 : 0 < m * 5 ^ b := by positivity
          have hE : 3 ^ (v - 2) ≤ 3 ^ (v - 2) * (m * 5 ^ b) :=
            Nat.le_mul_of_pos_right _ hM1
          omega
    have hstuff : 5 ^ b ≤ 5 * (m * 5 ^ b) - 4 * m - 2 := by
      rcases hm with h2 | ⟨h1eq, h1b⟩
      · have hm7 : 7 ≤ m := by
          by_contra hlt
          interval_cases m <;> revert hm30 <;> decide
        have hkey : 5 * (m * 5 ^ b) ≥ 5 ^ b + 4 * m + 2 := by
          have e1 : 5 * (m * 5 ^ b) = 5 ^ b * (5 * m) := by ring
          have h5m1 : (5 * m - 1) ≤ 5 ^ b * (5 * m - 1) :=
            Nat.le_mul_of_pos_left _ (by positivity)
          have e2 : 5 ^ b * (5 * m) = 5 ^ b * (5 * m - 1) + 5 ^ b := by
            conv_lhs => rw [show 5 * m = (5 * m - 1) + 1 from by omega]
            rw [Nat.mul_add, Nat.mul_one]
          rw [e1, e2]
          omega
        omega
      · subst h1eq
        have hb : 1 ≤ b := h1b
        have h1 : 1 ≤ 5 ^ (b - 1) := Nat.one_le_pow _ _ (by norm_num)
        have hpow : 5 ^ b = 5 * 5 ^ (b - 1) := by
          conv_lhs => rw [show b = (b - 1) + 1 from by omega, pow_succ]
          ring
        have e6 : 5 * (1 * 5 ^ b) = 25 * 5 ^ (b - 1) := by
          rw [hpow]
          ring
        rw [e6, hpow]
        omega
    have hb5 := five_pow_bound b
    have hp3 : 27 ≤ 3 ^ (v - 2) := by
      rw [show (27 : ℕ) = 3 ^ 3 from by norm_num]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hmid : 8 * b + 5
        ≤ 3 ^ (v - 2) * (5 * (m * 5 ^ b) - 4 * m - 2) := by
      have e2 : 3 ^ (v - 2) * 5 ^ b
          ≤ 3 ^ (v - 2) * (5 * (m * 5 ^ b) - 4 * m - 2) :=
        Nat.mul_le_mul_left _ hstuff
      have e3 : 27 * 5 ^ b ≤ 3 ^ (v - 2) * 5 ^ b :=
        Nat.mul_le_mul_right _ hp3
      omega
    calc 1 + 4 * K + 2 * j + 2 * lenD
        ≤ 5 + 8 * b + 3 ^ (v - 2) * (4 * m + 2 + 4 * (m * 5 ^ b)) := by
          rw [hK, hj]
          have e4 : 3 ^ (v - 2) * (4 * m + 2 + 4 * (m * 5 ^ b))
              = 4 * (m * 3 ^ (v - 2)) + 2 * 3 ^ (v - 2)
                + 4 * (3 ^ (v - 2) * (m * 5 ^ b)) := by ring
          rw [e4]
          omega
      _ ≤ 3 ^ (v - 2) * (5 * (m * 5 ^ b) - 4 * m - 2)
            + 3 ^ (v - 2) * (4 * m + 2 + 4 * (m * 5 ^ b)) := by omega
      _ = 5 ^ b * 3 ^ v * m := by
          have h5M : 4 * m + 2 ≤ 5 * (m * 5 ^ b) := by omega
          have e5 : 3 ^ (v - 2) * (5 * (m * 5 ^ b) - 4 * m - 2)
              + 3 ^ (v - 2) * (4 * m + 2 + 4 * (m * 5 ^ b))
              = 3 ^ (v - 2) * (9 * (m * 5 ^ b)) := by
            rw [← Nat.mul_add]
            congr 1
            omega
          rw [e5, hvdec]
          ring
  
  set C := List.replicate j 9 ++ List.replicate T 0 ++ [0]
      ++ List.replicate T 0 ++ List.replicate j 9 with hC
  have hCg : C.length = 2 * j + 2 * T + 1 := (center_repunit_len_sum j T).1
  have hCσ : C.sum = 18 * j := (center_repunit_len_sum j T).2
  have hCval3 : 3 ^ v ∣ Nat.ofDigits 10 C :=
    center_repunit_dvd3 hv2 ⟨1, by rw [hj]; ring⟩
  have hK1 : 1 ≤ K := by
    rw [hK]
    have : 0 < m * 3 ^ (v - 2) := by positivity
    omega
  have hde_pal : D.reverse = D := hDpal.reverse_eq
  have hde81 : 81 ∣ Nat.ofDigits 10 D := by
    have h : ((Nat.ofDigits 10 D : ℕ) : ZMod 81) = 0 := by
      rw [cast_ofDigits]
      exact hD81
    exact (CharP.cast_eq_zero_iff (ZMod 81) 81 _).mp h
  have hC81 : 81 ∣ Nat.ofDigits 10 C :=
    dvd_trans (pow_dvd_pow 3 (by omega : 4 ≤ v)) hCval3
  have hK9 : 9 ∣ K := by
    rw [hK]
    exact dvd_mul_of_dvd_right (pow_dvd_pow 3 (by omega : 2 ≤ v - 2)) m
  obtain ⟨s₀, hs0⟩ := hs0_solver hv hK1 D hde_pal hde81 C hC81 hK9
  have hg3 : 3 ≤ 2 * j + 2 * T + 1 := by omega
  have hgodd : Odd (2 * j + 2 * T + 1) := ⟨j + T, by ring⟩
  have hKcov : m * 3 ^ (v - 4) ≤ 1 + 9 * (K / 2) := by
    have hpow : 3 ^ (v - 2) = 9 * 3 ^ (v - 4) := by
      rw [show (9 : ℕ) = 3 ^ 2 from by norm_num, ← pow_add,
        show 2 + (v - 4) = v - 2 from by omega]
    have hF : 0 < m * 3 ^ (v - 4) := by positivity
    rw [hK, hj, hpow]
    have e : m * (9 * 3 ^ (v - 4)) = 9 * (m * 3 ^ (v - 4)) := by ring
    rw [e]
    omega
  obtain ⟨e', he', hdvdP⟩ := P_dvd_3m81 hm3 hm10 D rfl C hCg hg3 hgodd
    hKcov s₀ hs0
  set MID := (List.range (2 * K)).map (pairDigit e') ++ C
      ++ ((List.range (2 * K)).map (pairDigit e')).reverse with hMID
  set P := Nat.ofDigits 10 (D ++ MID ++ D.reverse) with hP
  have hMIDpal : MID.Palindrome := mid_pal e' C (center_repunit_pal j T)
  have hMID10 : ∀ x ∈ MID, x < 10 := mid_lt10 e' he' C
    (center_repunit_lt10 j T)
  obtain ⟨hP0, hPpal, hPlen, hPσ⟩ := sandwich_spec_gen D MID hDne hD10
    (hD0 hDne) hMIDpal hMID10 rfl rfl
  have hMIDlen : MID.length = 4 * K + C.length := by
    rw [hMID, List.length_append, List.length_append, List.length_reverse,
      List.length_map, List.length_range]
    ring
  obtain ⟨rr, hrr⟩ := hXeven
  have h2T : 2 * T = X := by rw [hT]; omega
  have hX' : X + (1 + 4 * K + 2 * j + 2 * lenD) = 5 ^ b * 3 ^ v * m := by
    rw [hX]
    exact Nat.sub_add_cancel hbound
  have hlen : (Nat.digits 10 P).length = 5 ^ b * 3 ^ v * m := by
    rw [hPlen, hMIDlen, hCg]
    omega
  
  have hσ : 5 ^ b * 3 ^ v * m ∣ (Nat.digits 10 P).sum := by
    have hσP : (Nat.digits 10 P).sum = 4 * 3 ^ v * (rhob 0 b v + t)
        + 18 * (K + j) := by
      rw [hPσ, mid_sum e' he' C, hCσ, hDσ]
      ring
    rw [hσP]
    have h3vd : 3 ^ v ∣ 4 * 3 ^ v * (rhob 0 b v + t) + 18 * (K + j) := by
      have h1 : 3 ^ v ∣ 4 * 3 ^ v * (rhob 0 b v + t) :=
        ⟨4 * (rhob 0 b v + t), by ring⟩
      have h2 : 3 ^ v ∣ 18 * (K + j) := by
        rw [hK, hj]
        exact ⟨2 * (m + 1), by
          rw [show (3 : ℕ) ^ v = 9 * 3 ^ (v - 2) from by
            rw [show (9 : ℕ) = 3 ^ 2 from by norm_num, ← pow_add,
              show 2 + (v - 2) = v from by omega]]
          ring⟩
      exact Nat.dvd_add h1 h2
    have hM' : m * 5 ^ b ∣ 4 * 3 ^ v * (rhob 0 b v + t) + 18 * (K + j) := by
      rw [← hM]
      exact htdvd
    have hcop : (3 ^ v).Coprime (m * 5 ^ b) := h3vm.mul_right h3v5b
    have hjoin := hcop.mul_dvd_of_dvd_of_dvd h3vd hM'
    rwa [show 5 ^ b * 3 ^ v * m = 3 ^ v * (m * 5 ^ b) from by ring]
  
  have hPd : 5 ^ b * 3 ^ v * m ∣ P := by
    have h25 : 2 ^ 0 * 5 ^ b ∣ P := by
      have hle_big : max 0 b ≤ lenD := by
        rw [hlenD]
        omega
      have := B_dvd_P (le := lenD) (de := D) (MID := MID) rfl hD25 hle_big
      rwa [hP]
    obtain ⟨w, hw⟩ := hdvdP
    have h3m : 3 ^ v * m ∣ P := ⟨w, by rw [hw]; ring⟩
    have := n_dvd_P_pow10 (a := 0) (b := b) (v := v) (m := m) (z := 0)
      (a' := 0) (b' := b) (P := P) h25 h3m rfl (add_zero b) hm30
    rwa [pow_zero, one_mul, pow_zero, mul_one] at this
  refine ⟨P, 0, hP0, ?_, hPpal, ?_, ?_, hσ⟩
  · intro h
    omega
  · rw [hlen, add_zero]
  · rwa [pow_zero, mul_one]
end A084017


namespace A084017
open Finset List Nat BigOperators Pointwise


set_option maxHeartbeats 800000 in
theorem assemble_3pow {v : ℕ} (hv : 2 ≤ v) :
    ∃ P z : ℕ, P ≠ 0
      ∧ (0 < z → 10 ∣ 3 ^ v)
      ∧ (Nat.digits 10 P).Palindrome
      ∧ (Nat.digits 10 P).length + z = 3 ^ v
      ∧ 3 ^ v ∣ P * 10 ^ z
      ∧ 3 ^ v ∣ (Nat.digits 10 P).sum := by
  have hn : 0 < 3 ^ v := by positivity
  have hrep : Nat.digits 10 (10 ^ (3 ^ v) - 1) = List.replicate (3 ^ v) 9 := by
    have h := digits_pow10_sub (B := 1) (u := 3 ^ v) (by norm_num)
      (Nat.one_le_pow _ _ (by norm_num)) (by simp)
    simpa using h
  refine ⟨10 ^ (3 ^ v) - 1, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h10 : 2 ≤ 10 ^ (3 ^ v) := by
      calc (2:ℕ) ≤ 10 := by norm_num
        _ ≤ 10 ^ (3 ^ v) := Nat.le_pow (by omega)
    omega
  · intro h
    omega
  · rw [hrep]
    exact List.Palindrome.of_reverse_eq List.reverse_replicate
  · rw [hrep, List.length_replicate, add_zero]
  · rw [pow_zero, mul_one]
    exact pow3v_dvd_pow10_sub_one hv (pow_dvd_pow 3 (by omega : v - 2 ≤ v))
  · rw [hrep, List.sum_replicate]
    exact ⟨9, by ring⟩
end A084017
namespace A084017
open Finset List Nat BigOperators Pointwise


set_option maxHeartbeats 800000 in
theorem sigma_t_solve2 {v ρ S M w : ℕ} (hM : 0 < M)
    (hcop : (4 * 3 ^ v).Coprime M) (hcop2 : M.Coprime (2 ^ w)) :
    ∃ t : ℕ, t < M * 2 ^ w ∧ 2 ^ w ∣ (ρ + t)
        ∧ M ∣ 4 * 3 ^ v * (ρ + t) + 18 * S := by
  obtain ⟨t0, ht0, hd0⟩ := sigma_t_solve (v := v) (ρ := ρ) (S := S) (M := M)
    hM hcop
  by_cases hw : 0 < w
  · haveI : NeZero (2 ^ w) := ⟨by positivity⟩
    set Mu : ZMod (2 ^ w) := (M : ZMod (2 ^ w)) with hMu
    have hunit : IsUnit Mu := by
      rw [hMu, ZMod.isUnit_iff_coprime]
      exact hcop2
    set s := (-(↑ρ + ↑t0 : ZMod (2 ^ w)) * Mu⁻¹).val with hs
    have hkey : Mu * (s : ZMod (2 ^ w)) = -(↑ρ + ↑t0) := by
      show Mu * ((-(↑ρ + ↑t0) * Mu⁻¹ : ZMod (2^w)).val : ZMod (2^w)) = _
      rw [ZMod.natCast_val, ZMod.cast_id]
      calc Mu * (-(↑ρ + ↑t0) * Mu⁻¹)
          = -((↑ρ + ↑t0) * (Mu * Mu⁻¹)) := by ring
        _ = -(↑ρ + ↑t0) := by rw [ZMod.mul_inv_of_unit _ hunit]; ring
    set t := t0 + M * s with ht
    refine ⟨t, ?_, ?_, ?_⟩
    · show t < M * 2 ^ w
      have hs' : s < 2 ^ w := ZMod.val_lt _
      have hs'' : M * s ≤ M * (2 ^ w - 1) :=
        Nat.mul_le_mul_left M (by omega)
      have hM2 : 0 < M * 2 ^ w := Nat.mul_pos hM (by positivity)
      have hM2' : M ≤ M * 2 ^ w := Nat.le_mul_of_pos_right M (by positivity)
      have e : (M - 1) + M * (2 ^ w - 1) = M * 2 ^ w - 1 := by
        rw [Nat.mul_sub, Nat.mul_one]
        omega
      calc t0 + M * s ≤ (M - 1) + M * (2 ^ w - 1) := by
            apply Nat.add_le_add _ hs''
            omega
        _ = M * 2 ^ w - 1 := e
        _ < M * 2 ^ w := by omega
    · have ht2 : ((ρ + t : ℕ) : ZMod (2 ^ w)) = 0 := by
        have e : ((ρ + t : ℕ) : ZMod (2 ^ w)) = ↑ρ + (↑t0 + Mu * ↑s) := by
          rw [ht]
          push_cast
          rw [← hMu]
        rw [e, hkey]
        ring
      exact (CharP.cast_eq_zero_iff (ZMod (2^w)) (2^w) _).mp ht2
    · have htmod : t % M = t0 % M := by
        rw [ht, Nat.add_mul_mod_self_left]
      have hcast : ((4 * 3 ^ v * (ρ + t) + 18 * S : ℕ) : ZMod M) = 0 := by
        have htt : (t : ZMod M) = (t0 : ZMod M) := by
          rw [ZMod.natCast_eq_natCast_iff]
          exact htmod
        have hd0cast : ((4 * 3 ^ v * (ρ + t0) + 18 * S : ℕ) : ZMod M) = 0 :=
          (CharP.cast_eq_zero_iff (ZMod M) M _).mpr hd0
        have e : ((4 * 3 ^ v * (ρ + t) + 18 * S : ℕ) : ZMod M)
            = ((4 * 3 ^ v * (ρ + t0) + 18 * S : ℕ) : ZMod M) := by
          push_cast
          rw [htt]
        rw [e]
        exact hd0cast
      exact (CharP.cast_eq_zero_iff (ZMod M) M _).mp hcast
  · have h0 : w = 0 := Nat.eq_zero_of_not_pos hw
    subst h0
    refine ⟨t0, ?_, ?_, hd0⟩
    · rw [pow_zero, mul_one]
      exact ht0
    · rw [pow_zero]
      exact one_dvd _

set_option maxHeartbeats 800000 in
theorem n_dvd_P_pow10_le {a b v m z a' b' P : ℕ}
    (h25 : 2 ^ a' * 5 ^ b' ∣ P) (h3m : 3 ^ v * m ∣ P)
    (ha : a ≤ a' + z) (hb : b ≤ b' + z) (hm30 : m.Coprime 30) :
    2 ^ a * 5 ^ b * 3 ^ v * m ∣ P * 10 ^ z := by
  have hm2 : m.Coprime 2 := by
    have h : Nat.Coprime 2 m := (Nat.prime_two.coprime_iff_not_dvd).mpr
      (by
        intro h2
        have h2g : (2:ℕ) ∣ m.gcd 30 := Nat.dvd_gcd h2 (by norm_num)
        have hg : m.gcd 30 = 1 := hm30
        rw [hg] at h2g
        norm_num at h2g)
    exact h.symm
  have hm5 : m.Coprime 5 := by
    have h : Nat.Coprime 5 m := (Nat.prime_five.coprime_iff_not_dvd).mpr
      (by
        intro h5
        have h5g : (5:ℕ) ∣ m.gcd 30 := Nat.dvd_gcd h5 (by norm_num)
        have hg : m.gcd 30 = 1 := hm30
        rw [hg] at h5g
        norm_num at h5g)
    exact h.symm
  have hcop2 : (2 ^ a * 5 ^ b).Coprime (3 ^ v * m) := by
    apply Nat.coprime_mul_iff_right.mpr
    constructor
    · apply Nat.Coprime.mul_left
      · exact ((by decide : Nat.Coprime 2 3).pow_right v).pow_left a
      · exact ((by decide : Nat.Coprime 5 3).pow_right v).pow_left b
    · apply Nat.Coprime.mul_left
      · exact (hm2.symm.pow_left a)
      · exact (hm5.symm.pow_left b)
  have h10 : 10 ^ z = 2 ^ z * 5 ^ z := by
    rw [show (10 : ℕ) = 2 * 5 from by norm_num, mul_pow]
  have h2a : 2 ^ a ∣ 2 ^ a' * 2 ^ z := by
    rw [← pow_add]
    exact pow_dvd_pow 2 ha
  have h5b : 5 ^ b ∣ 5 ^ b' * 5 ^ z := by
    rw [← pow_add]
    exact pow_dvd_pow 5 hb
  have h25z : 2 ^ a * 5 ^ b ∣ (2 ^ a' * 5 ^ b') * 10 ^ z := by
    rw [h10]
    have e : 2 ^ a' * 5 ^ b' * (2 ^ z * 5 ^ z)
        = (2 ^ a' * 2 ^ z) * (5 ^ b' * 5 ^ z) := by ring
    rw [e]
    exact Nat.mul_dvd_mul h2a h5b
  have h25P : 2 ^ a * 5 ^ b ∣ P * 10 ^ z :=
    dvd_trans h25z (Nat.mul_dvd_mul_right h25 (10 ^ z))
  have h3mP : 3 ^ v * m ∣ P * 10 ^ z := dvd_mul_of_dvd_left h3m _
  have h := hcop2.mul_dvd_of_dvd_of_dvd h25P h3mP
  have e : 2 ^ a * 5 ^ b * (3 ^ v * m) = 2 ^ a * 5 ^ b * 3 ^ v * m :=
    by ring
  rwa [e] at h


end A084017

namespace A084017
open Finset List Nat BigOperators Pointwise



end A084017

namespace A084017
open Finset List Nat BigOperators Pointwise

set_option maxHeartbeats 800000 in
theorem assemble_even0 {a v m : ℕ} (ha : 1 ≤ a)
    (hm0 : 1 ≤ m) (hv : 5 ≤ v) (hm30 : m.Coprime 30)
    (hm11 : m.Coprime 11) (hm101 : m.Coprime 101) :
    ∃ P z : ℕ, P ≠ 0
      ∧ (0 < z → 10 ∣ 2 ^ a * 3 ^ v * m)
      ∧ (Nat.digits 10 P).Palindrome
      ∧ (Nat.digits 10 P).length + z = 2 ^ a * 3 ^ v * m
      ∧ 2 ^ a * 3 ^ v * m ∣ P * 10 ^ z
      ∧ 2 ^ a * 3 ^ v * m ∣ (Nat.digits 10 P).sum := by
  classical
  set z := min a 0 with hz
  have hzae : z = 0 := Nat.min_zero a
  set n := 2 ^ a * 3 ^ v * m with hn
  haveI : NeZero m := ⟨by omega⟩
  have hm3 : m.Coprime 3 := hm30.coprime_dvd_right (by norm_num)
  have hm10 : m.Coprime 10 := hm30.coprime_dvd_right (by norm_num)
  have hm2 : m.Coprime 2 := hm30.coprime_dvd_right (by norm_num)
  have hv2 : 2 ≤ v := by omega
  have hza : z ≤ a := Nat.min_le_left a 0
  
  set p2 := 2 ^ (a - 1) with hp2
  have hp2pos : 0 < p2 := pow_pos (by norm_num) _
  set c := p2 - m % p2 with hc
  have hmc : p2 ∣ m + c := by
    have hlt : m % p2 < p2 := Nat.mod_lt _ hp2pos
    have h2 := Nat.div_add_mod m p2
    have h3 : p2 * (m / p2 + 1) = p2 * (m / p2) + p2 := Nat.mul_succ _ _
    refine ⟨m / p2 + 1, ?_⟩
    rw [hc]
    omega
  have hcle : c ≤ p2 := Nat.sub_le _ _
  have hc1 : 1 ≤ c := by
    have hlt : m % p2 < p2 := Nat.mod_lt _ hp2pos
    rw [hc]
    omega
  
  set K := m * 3 ^ (v - 2) with hK
  set j := c * 3 ^ (v - 2) with hj
  set M := m with hM
  have hM0 : 0 < M := by
    rw [hM]
    exact Nat.pos_of_ne_zero (NeZero.ne m)
  have h4m : (4 : ℕ).Coprime m := hm2.symm.pow_left 2
  have h3vm : (3 ^ v).Coprime m := hm3.symm.pow_left v
  have hcop43 : (4 * 3 ^ v).Coprime M := by
    rw [hM]
    exact h4m.mul_left h3vm
  
  have hmo : Odd m := by
    have h2 : ¬ (2 : ℕ) ∣ m :=
      (Nat.prime_two.coprime_iff_not_dvd).mp hm2.symm
    rw [← Nat.not_even_iff_odd]
    rintro ⟨c', hc'⟩
    exact h2 ⟨c', by omega⟩
  have hModd : Odd M := by
    rw [hM]
    exact hmo
  have hnd : ¬ (2 : ℕ) ∣ M := by
    rintro ⟨r, hr⟩
    obtain ⟨s, hs⟩ := hModd
    omega
  have hcop2 : M.Coprime (2 ^ (a - 2)) :=
    ((Nat.prime_two.coprime_iff_not_dvd).mpr hnd).symm.pow_right _
  
  obtain ⟨t, htlt, ht2, htdvd⟩ := sigma_t_solve2 (v := v)
    (ρ := rhob a 0 v) (S := K + j) (M := M) (w := a - 2)
    hM0 hcop43 hcop2
  
  have hmin : a = 0 ∨ (0 : ℕ) = 0 := Or.inr rfl
  obtain ⟨D, hDpal, hD10, hDne, hD0, hD25, hD81, hDσ, hr₀lt, hlenD⟩ :=
    border_pal (a' := a) (b' := 0) (q := v)
      (s₁ := a) (t := t)
      (by omega) hmin (le_of_eq (Nat.max_eq_left (Nat.zero_le a)))
  set lenD := D.length with hlenD'
  have hlenN : lenD
      = 2 * ((Nat.digits 10 (9 * 2 ^ a)).length + a + r0b a 0 v)
        + 2 * (3 ^ (v - 2) * t) := by
    rw [hlenD]
    ring
  
  have lenV_le : (Nat.digits 10 (9 * 2 ^ a)).length ≤ a + 2 := by
    have hVpos : (9 * 2 ^ a : ℕ) ≠ 0 := by positivity
    have hb2 := Nat.base_pow_length_digits_le 10 (9 * 2 ^ a) (by norm_num) hVpos
    have hlt : 10 * (9 * 2 ^ a) < 10 ^ (a + 2) := by
      have h1 : (2 : ℕ) ^ a ≤ 10 ^ a := Nat.pow_le_pow_left (by norm_num) _
      calc 10 * (9 * 2 ^ a) = 90 * 2 ^ a := by ring
        _ ≤ 90 * 10 ^ a := Nat.mul_le_mul_left 90 h1
        _ < 100 * 10 ^ a := by omega
        _ = 10 ^ (a + 2) := by ring
    have hpow : 10 ^ ((Nat.digits 10 (9 * 2 ^ a)).length) < 10 ^ (a + 2) :=
      lt_of_le_of_lt hb2 hlt
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 10)).mp hpow
    omega
  have hne : Even n := by
    rw [hn]
    refine ⟨2 ^ (a - 1) * 3 ^ v * m, ?_⟩
    rw [show 2 ^ a = 2 * 2 ^ (a - 1) from by
      rw [← pow_succ', Nat.succ_eq_add_one, Nat.sub_add_cancel ha]]
    ring
  have hzlt : z < n := by
    have ha2 : a < 2 ^ a := Nat.lt_two_pow_self
    have h2n : 2 ^ a ≤ n := by
      rw [hn]
      calc 2 ^ a ≤ 2 ^ a * 3 ^ v :=
            Nat.le_mul_of_pos_right _ (by positivity)
        _ ≤ 2 ^ a * 3 ^ v * m :=
            Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hne2 : Even (n - z) := by
    rw [hzae, Nat.sub_zero]
    exact hne
  set S := 4 * K + 2 * j + 2 * lenD with hS
  have hSeven : Even S := by
    refine ⟨2 * K + j + lenD, ?_⟩
    rw [hS]
    ring
  set X := (n - z) - S with hX
  have hXeven : Even X := by
    obtain ⟨an, han⟩ := hne2
    obtain ⟨as, has⟩ := hSeven
    refine ⟨an - as, ?_⟩
    rw [hX, han, has]
    omega
  set T := X / 2 with hT
  
  have hbound : S + z ≤ n := by
    set E := 2 ^ a * 3 ^ (v - 2) * m with hE
    have hvdec : 3 ^ v = 9 * 3 ^ (v - 2) := by
      rw [show (9 : ℕ) = 3 ^ 2 from by norm_num, ← pow_add,
        show 2 + (v - 2) = v from by omega]
    have hE9 : n = 9 * E := by
      rw [hn, hE, hvdec]
      ring
    have g1 : 4 * (m * 3 ^ (v - 2)) ≤ 2 * E := by
      have h2a1 : 4 ≤ 2 * 2 ^ a := by
        have h : (2 : ℕ) ^ 1 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
        norm_num at h ⊢; omega
      calc 4 * (m * 3 ^ (v - 2))
          ≤ (2 * 2 ^ a) * (m * 3 ^ (v - 2)) := Nat.mul_le_mul_right _ h2a1
        _ = 2 * (2 ^ a * 3 ^ (v - 2) * m) := by ring
        _ = 2 * E := by rw [hE]
    have g2 : 2 * (c * 3 ^ (v - 2)) ≤ E := by
      have hc2 : 2 * c ≤ 2 ^ a := by
        calc 2 * c ≤ 2 * 2 ^ (a - 1) :=
              Nat.mul_le_mul_left 2 hcle
          _ = 2 ^ a := by
              rw [← pow_succ', Nat.succ_eq_add_one, Nat.sub_add_cancel ha]
      calc 2 * (c * 3 ^ (v - 2)) = (2 * c) * 3 ^ (v - 2) := by ring
        _ ≤ 2 ^ a * 3 ^ (v - 2) := Nat.mul_le_mul_right _ hc2
        _ ≤ E := by
            rw [hE]
            calc 2 ^ a * 3 ^ (v - 2)
                ≤ (2 ^ a * 3 ^ (v - 2)) * m :=
                  Nat.le_mul_of_pos_right _ (by omega)
              _ = 2 ^ a * 3 ^ (v - 2) * m := by ring
    have h4pow : 4 * 2 ^ (a - 2) ≤ 2 * 2 ^ a := by
      rcases Nat.lt_or_ge a 2 with hlt | hge
      · have e1 : a = 1 := by omega
        rw [e1]; norm_num
      · have e3 : 2 ^ a = 4 * 2 ^ (a - 2) := by
          conv_lhs => rw [← Nat.sub_add_cancel hge]
          rw [pow_add]
          ring
        rw [e3]
        exact Nat.le_mul_of_pos_left _ (by norm_num)
    have g4 : 4 * (3 ^ (v - 2) * t) + 4 * 3 ^ (v - 2) ≤ 2 * E := by
      have ht1 : t + 1 ≤ M * 2 ^ (a - 2) := htlt
      calc 4 * (3 ^ (v - 2) * t) + 4 * 3 ^ (v - 2)
          = 4 * 3 ^ (v - 2) * (t + 1) := by ring
        _ ≤ 4 * 3 ^ (v - 2) * (M * 2 ^ (a - 2)) :=
            Nat.mul_le_mul_left _ ht1
        _ = (4 * 2 ^ (a - 2)) * (3 ^ (v - 2) * M) := by ring
        _ ≤ (2 * 2 ^ a) * (3 ^ (v - 2) * M) :=
            Nat.mul_le_mul_right _ h4pow
        _ = 2 * E := by rw [hE, hM]; ring
    have g5 : 8 * a ≤ 2 * E := by
      have ha2' : a ≤ 2 ^ a := le_of_lt Nat.lt_two_pow_self
      have h27 : 4 ≤ 3 ^ (v - 2) * m := by
        have h : (3 : ℕ) ^ 3 ≤ 3 ^ (v - 2) :=
          Nat.pow_le_pow_right (by norm_num) (by omega : 3 ≤ v - 2)
        norm_num at h
        have h1 : 27 * 1 ≤ 3 ^ (v - 2) * m := Nat.mul_le_mul h (by omega)
        omega
      rw [hE]
      calc 8 * a ≤ 8 * 2 ^ a := Nat.mul_le_mul_left 8 ha2'
        _ = 4 * (2 * 2 ^ a) := by ring
        _ ≤ (3 ^ (v - 2) * m) * (2 * 2 ^ a) :=
            Nat.mul_le_mul_right _ h27
        _ = 2 * (2 ^ a * 3 ^ (v - 2) * m) := by ring
    have g6 : 4 * 3 ^ (v - 2) ≤ 4 * E := by
      apply Nat.mul_le_mul_left
      rw [hE]
      calc 3 ^ (v - 2)
          ≤ (2 ^ a * m) * 3 ^ (v - 2) :=
            Nat.le_mul_of_pos_left _ (by positivity)
        _ = 2 ^ a * 3 ^ (v - 2) * m := by ring
    have hr : r0b a 0 v + 1 ≤ 3 ^ (v - 2) := hr₀lt
    have hlen3 : 2 * lenD
        ≤ 8 * a + 4 * (3 ^ (v - 2) * t) + 4 * 3 ^ (v - 2) + 12 := by
      rw [hlenN]
      have hlv := lenV_le
      omega
    have hE2 : 8 ≤ E := by
      rw [hE]
      have hu4 : 27 ≤ 3 ^ (v - 2) := by
        have h : (3 : ℕ) ^ 3 ≤ 3 ^ (v - 2) :=
          Nat.pow_le_pow_right (by norm_num) (by omega : 3 ≤ v - 2)
        norm_num at h ⊢; exact h
      have h2a2 : 2 ≤ 2 ^ a := by
        have h : (2 : ℕ) ^ 1 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
        norm_num at h ⊢; exact h
      have h1 : 2 * 27 * 1 ≤ 2 ^ a * 3 ^ (v - 2) * m :=
        Nat.mul_le_mul (Nat.mul_le_mul h2a2 hu4) (by omega)
      omega
    rw [hzae, hS, hK, hj]
    omega
  
  set C := List.replicate j 9 ++ List.replicate T 0
      ++ List.replicate T 0 ++ List.replicate j 9 with hC
  have hCg : C.length = 2 * j + 2 * T := (center_repunit_even_len_sum j T).1
  have hCσ : C.sum = 18 * j := (center_repunit_even_len_sum j T).2
  have hCval3 : 3 ^ v ∣ Nat.ofDigits 10 C :=
    center_repunit_even_dvd3 hv2 ⟨c, by rw [hj]; ring⟩
  have hK1 : 1 ≤ K := by
    rw [hK]
    have : 0 < m * 3 ^ (v - 2) := by positivity
    omega
  have hde_pal : D.reverse = D := hDpal.reverse_eq
  have hde81 : 81 ∣ Nat.ofDigits 10 D := by
    have h : ((Nat.ofDigits 10 D : ℕ) : ZMod 81) = 0 := by
      rw [cast_ofDigits]
      exact hD81
    exact (CharP.cast_eq_zero_iff (ZMod 81) 81 _).mp h
  have hC81 : 81 ∣ Nat.ofDigits 10 C :=
    dvd_trans (pow_dvd_pow 3 (by omega : 4 ≤ v)) hCval3
  have hK9 : 9 ∣ K := by
    rw [hK]
    exact dvd_mul_of_dvd_right (pow_dvd_pow 3 (by omega : 2 ≤ v - 2)) m
  obtain ⟨s₀, hs0⟩ := hs0_solver hv hK1 D hde_pal hde81 C hC81 hK9
  have hj1 : 1 ≤ j := by
    rw [hj]
    exact Nat.mul_pos hc1 (by positivity)
  have hg3 : 3 ≤ 2 * j + 2 * T := by
    have hj2 : 2 ≤ j := by
      rw [hj]
      calc 2 ≤ 3 ^ (v - 2) := by
            have h := Nat.pow_le_pow_right (by norm_num : 1 ≤ 3)
              (by omega : 1 ≤ v - 2)
            norm_num at h ⊢; omega
          _ ≤ c * 3 ^ (v - 2) := Nat.le_mul_of_pos_left _ hc1
    omega
  have hgev : Even (2 * j + 2 * T) := ⟨j + T, by ring⟩
  have hKcov : m * 3 ^ (v - 4) ≤ 1 + 9 * (K / 2) := by
    have hpow : 3 ^ (v - 2) = 9 * 3 ^ (v - 4) := by
      rw [show (9 : ℕ) = 3 ^ 2 from by norm_num, ← pow_add,
        show 2 + (v - 4) = v - 2 from by omega]
    have hF : 0 < m * 3 ^ (v - 4) := by positivity
    rw [hK, hpow]
    have e : m * (9 * 3 ^ (v - 4)) = 9 * (m * 3 ^ (v - 4)) := by ring
    rw [e]
    omega
  obtain ⟨e', he', hdvdP⟩ := P_dvd_3m81_even hm3 hm10 hm11 hm101 D rfl C hCg hg3 hgev
    hKcov s₀ hs0
  set MID := (List.range (2 * K)).map (pairDigit e') ++ C
      ++ ((List.range (2 * K)).map (pairDigit e')).reverse with hMID
  set P := Nat.ofDigits 10 (D ++ MID ++ D.reverse) with hP
  have hMIDpal : MID.Palindrome := mid_pal e' C (center_repunit_even_pal j T)
  have hMID10 : ∀ x ∈ MID, x < 10 := mid_lt10 e' he' C
    (center_repunit_even_lt10 j T)
  obtain ⟨hP0, hPpal, hPlen, hPσ⟩ := sandwich_spec_gen D MID hDne hD10
    (hD0 hDne) hMIDpal hMID10 rfl rfl
  have hMIDlen : MID.length = 4 * K + C.length := by
    rw [hMID, List.length_append, List.length_append, List.length_reverse,
      List.length_map, List.length_range]
    ring
  obtain ⟨rr, hrr⟩ := hXeven
  have h2T : 2 * T = X := by rw [hT]; omega
  have hlen : (Nat.digits 10 P).length = n - z := by
    rw [hPlen, hMIDlen, hCg]
    omega
  
  have hσP : (Nat.digits 10 P).sum
      = 4 * 3 ^ v * (rhob a 0 v + t) + 18 * (K + j) := by
    rw [hPσ, mid_sum e' he' C, hCσ, hDσ]
    ring
  have h2a : 2 ^ a ∣ (Nat.digits 10 P).sum := by
    rw [hσP]
    apply Nat.dvd_add
    · have h21 : 2 ^ a ∣ 4 * (rhob a 0 v + t) := by
        rcases Nat.lt_or_ge 2 a with h | h
        · obtain ⟨u, hu⟩ := ht2
          have hpa : 2 ^ a = 2 ^ (a - 2) * 4 := by
            rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, ← pow_add,
              show a - 2 + 2 = a from by omega]
          rw [hpa]
          exact ⟨u, by rw [hu]; ring⟩
        · exact dvd_mul_of_dvd_left (show 2 ^ a ∣ 4 from pow_dvd_pow 2 (by omega)) _
      have e1 : 4 * 3 ^ v * (rhob a 0 v + t)
          = 3 ^ v * (4 * (rhob a 0 v + t)) := by ring
      rw [e1]
      exact dvd_mul_of_dvd_right h21 _
    · have h22 : 2 ^ a ∣ 2 * (m + c) := by
        obtain ⟨u, hu⟩ := hmc
        have hpa : 2 ^ a = 2 ^ (a - 1) * 2 := by
          rw [← pow_succ, Nat.sub_add_cancel ha]
        rw [hpa]
        exact ⟨u, by rw [hu]; ring⟩
      have e2 : 18 * (K + j) = (9 * 3 ^ (v - 2)) * (2 * (m + c)) := by
        rw [hK, hj, ← Nat.add_mul]
        ring
      rw [e2]
      exact dvd_mul_of_dvd_right h22 _
  have h3vd : 3 ^ v ∣ (Nat.digits 10 P).sum := by
    rw [hσP]
    apply Nat.dvd_add
    · exact ⟨4 * (rhob a 0 v + t), by ring⟩
    · refine ⟨2 * (m + c), ?_⟩
      rw [hK, hj, ← Nat.add_mul]
      rw [show (3 : ℕ) ^ v = 9 * 3 ^ (v - 2) from by
        rw [show (9 : ℕ) = 3 ^ 2 from by norm_num, ← pow_add,
          show 2 + (v - 2) = v from by omega]]
      ring
  have hMdvd : m ∣ (Nat.digits 10 P).sum := by
    rw [hσP, ← hM]
    exact htdvd
  have hσ : n ∣ (Nat.digits 10 P).sum := by
    have hcop2a : (2 ^ a).Coprime (3 ^ v) :=
      ((by decide : Nat.Coprime 2 3).pow_right v).pow_left a
    have hcopB : (2 ^ a * 3 ^ v).Coprime m :=
      Nat.Coprime.mul_left (hm2.symm.pow_left a) (hm3.symm.pow_left v)
    have hjoin1 := hcop2a.mul_dvd_of_dvd_of_dvd h2a h3vd
    have hjoin2 := hcopB.mul_dvd_of_dvd_of_dvd hjoin1 hMdvd
    rw [hn]
    rwa [show 2 ^ a * 3 ^ v * m = 2 ^ a * 3 ^ v * m from rfl]
  
  have hPd : n ∣ P * 10 ^ z := by
    have h25 : 2 ^ a * 5 ^ 0 ∣ P := by
      have hle_big : max a 0 ≤ lenD := by
        rw [hlenN]
        omega
      have := B_dvd_P (le := lenD) (de := D) (MID := MID) rfl hD25 hle_big
      rwa [hP]
    obtain ⟨w, hw⟩ := hdvdP
    have h3m : 3 ^ v * m ∣ P := ⟨w, by rw [hw]; ring⟩
    have := n_dvd_P_pow10_le (a := a) (b := 0) (v := v) (m := m) (z := 0)
      (a' := a) (b' := 0) (P := P) h25 h3m
      (by omega) (by omega) hm30
    rw [hzae]
    convert this using 2 <;> ring
  refine ⟨P, z, hP0, ?_, hPpal, ?_, hPd, hσ⟩
  · intro hz'
    omega
  · rw [hlen, hzae]
    omega

end A084017
namespace A084017
open Finset List Nat BigOperators Pointwise

set_option maxHeartbeats 800000 in
theorem sigma_c_solve {v ρ m M : ℕ} (hM : 0 < M)
    (hcop : (18 * 3 ^ (v - 2)).Coprime M) :
    ∃ c : ℕ, c < M ∧ M ∣ 4 * 81 * ρ + 18 * 3 ^ (v - 2) * (m + c) := by
  haveI : NeZero M := ⟨hM.ne'⟩
  set u : ZMod M := ((18 * 3 ^ (v - 2) : ℕ) : ZMod M) with hu
  have hunit : IsUnit u := by
    rw [hu, ZMod.isUnit_iff_coprime]
    exact hcop
  set c : ℕ := (-(↑(4 * 81 * ρ + 18 * 3 ^ (v - 2) * m) * u⁻¹) : ZMod M).val
    with hc
  have hkey : u * (c : ZMod M)
      = -(↑(4 * 81 * ρ + 18 * 3 ^ (v - 2) * m) : ZMod M) := by
    show u * ((-(↑(4 * 81 * ρ + 18 * 3 ^ (v - 2) * m) * u⁻¹) : ZMod M).val
        : ZMod M) = _
    rw [ZMod.natCast_val, ZMod.cast_id]
    calc u * (-(↑(4 * 81 * ρ + 18 * 3 ^ (v - 2) * m) * u⁻¹))
        = -(u * (↑(4 * 81 * ρ + 18 * 3 ^ (v - 2) * m) * u⁻¹)) := by
          rw [mul_neg]
      _ = -(↑(4 * 81 * ρ + 18 * 3 ^ (v - 2) * m) * (u * u⁻¹)) := by ring
      _ = -↑(4 * 81 * ρ + 18 * 3 ^ (v - 2) * m) := by
          rw [ZMod.mul_inv_of_unit _ hunit]; ring
  refine ⟨c, ?_, ?_⟩
  · show c < M
    exact ZMod.val_lt _
  · have hcast : ((4 * 81 * ρ + 18 * 3 ^ (v - 2) * (m + c) : ℕ) : ZMod M)
        = 0 := by
      have hu' : u = (18 : ZMod M) * (3 : ZMod M) ^ (v - 2) := by
        rw [hu]; push_cast; ring
      have hkey2 : u * (c : ZMod M)
          = -(4 * 81 * (ρ : ZMod M) + u * ↑m) := by
        rw [hkey]
        congr 1
        rw [hu]
        push_cast
        ring
      have hstep : u * ((m : ZMod M) + (c : ZMod M)) + 4 * 81 * (ρ : ZMod M)
          = 0 := by
        linear_combination hkey2
      have heq : ((4 * 81 * ρ + 18 * 3 ^ (v - 2) * (m + c) : ℕ) : ZMod M)
          = u * (↑m + ↑c) + 4 * 81 * ↑ρ := by
        rw [hu']
        push_cast
        ring
      rw [heq, hstep]
    exact (CharP.cast_eq_zero_iff (ZMod M) M _).mp hcast


set_option maxHeartbeats 800000 in
theorem assemble_v4o {b v m : ℕ} (hm30 : m.Coprime 30)
    (hv2 : 2 ≤ v) (hv4 : v ≤ 4)
    (hB : 8 * b + 44 ≤ 5 ^ b * m * 3 ^ (v - 2)) :
    ∃ P z : ℕ, P ≠ 0
      ∧ (0 < z → 10 ∣ 5 ^ b * 3 ^ v * m)
      ∧ (Nat.digits 10 P).Palindrome
      ∧ (Nat.digits 10 P).length + z = 5 ^ b * 3 ^ v * m
      ∧ 5 ^ b * 3 ^ v * m ∣ P * 10 ^ z
      ∧ 5 ^ b * 3 ^ v * m ∣ (Nat.digits 10 P).sum := by
  classical
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      simp at hm30
    exact h
  haveI : NeZero m := ⟨hm0.ne'⟩
  have hm3 : m.Coprime 3 := hm30.coprime_dvd_right (by norm_num)
  have hm10 : m.Coprime 10 := hm30.coprime_dvd_right (by norm_num)
  have hm2 : m.Coprime 2 := hm30.coprime_dvd_right (by norm_num)
  set K := m * 3 ^ (v - 2) with hK
  set M := m * 5 ^ b with hM
  have hM0 : 0 < M := by
    rw [hM]
    exact Nat.mul_pos hm0 (pow_pos (by norm_num) _)
  have h4m : (4 : ℕ).Coprime m := hm2.symm.pow_left 2
  have h3vm : (3 ^ v).Coprime m := hm3.symm.pow_left v
  have h45b : (4 : ℕ).Coprime (5 ^ b) :=
    (by decide : Nat.Coprime 4 5).pow_right b
  have h3v5b : (3 ^ v).Coprime (5 ^ b) :=
    ((by decide : Nat.Coprime 3 5).pow_right b).pow_left v
  have h18 : (18 * 3 ^ (v - 2)).Coprime M := by
    have e : 18 * 3 ^ (v - 2) = 2 * 3 ^ v := by
      rw [show (18 : ℕ) = 2 * 3 ^ 2 from by norm_num, mul_assoc, ← pow_add,
        show 2 + (v - 2) = v from by omega]
    rw [hM, e]
    have h2m : (2 * 3 ^ v).Coprime m := hm2.symm.mul_left h3vm
    have h25b : (2 * 3 ^ v).Coprime (5 ^ b) :=
      ((by decide : Nat.Coprime 2 5).pow_right b).mul_left h3v5b
    exact h2m.mul_right h25b
  obtain ⟨c, hclt, hcdvd⟩ := sigma_c_solve (v := v) (ρ := rhob 0 b 4)
    (m := m) (M := M) hM0 h18
  set j := (c + M) * 3 ^ (v - 2) with hj
  obtain ⟨D, hDpal, hD10, hDne, hD0, hD25, hD81, hDσ, hr₀lt, hlenD⟩ :=
    border_pal (a' := 0) (b' := b) (q := 4) (s₁ := b) (t := 0)
      (by norm_num) (Or.inl rfl) (by simp)
  set lenD := D.length with hlenD'
  have lenV_le : (Nat.digits 10 (9 * 2 ^ 0 * 5 ^ b)).length ≤ b + 2 := by
    have hVpos : (9 * 2 ^ 0 * 5 ^ b : ℕ) ≠ 0 := by positivity
    have hb := Nat.base_pow_length_digits_le 10 (9 * 2 ^ 0 * 5 ^ b)
      (by norm_num) hVpos
    have hlt : 10 * (9 * 2 ^ 0 * 5 ^ b) < 10 ^ (b + 2) := by
      have h1 : (5 : ℕ) ^ b ≤ 10 ^ b := Nat.pow_le_pow_left (by norm_num) b
      calc 10 * (9 * 2 ^ 0 * 5 ^ b) = 90 * 5 ^ b := by ring
        _ ≤ 90 * 10 ^ b := Nat.mul_le_mul_left 90 h1
        _ < 100 * 10 ^ b := by omega
        _ = 10 ^ (b + 2) := by ring
    have hpow : 10 ^ ((Nat.digits 10 (9 * 2 ^ 0 * 5 ^ b)).length)
        < 10 ^ (b + 2) := lt_of_le_of_lt hb hlt
    have hlt' := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 10)).mp hpow
    omega
  have hnodd : Odd (5 ^ b * 3 ^ v * m) := by
    have h5o : Odd (5 ^ b) := Odd.pow (by decide : Odd 5)
    have h3o : Odd (3 ^ v) := Odd.pow (by decide : Odd 3)
    have hmo : Odd m := by
      have h2 : ¬ (2 : ℕ) ∣ m :=
        (Nat.prime_two.coprime_iff_not_dvd).mp hm2.symm
      rw [← Nat.not_even_iff_odd]
      rintro ⟨c', hc'⟩
      exact h2 ⟨c', by omega⟩
    exact (h5o.mul h3o).mul hmo
  have hSodd : Odd (1 + 4 * K + 2 * j + 2 * lenD) := by
    have hev : Even (4 * K + 2 * j + 2 * lenD) := by
      have e1 : Even (4 * K) := ⟨2 * K, by ring⟩
      have e2 : Even (2 * j) := ⟨j, by ring⟩
      have e3 : Even (2 * lenD) := ⟨lenD, by ring⟩
      exact (e1.add e2).add e3
    have := hev.add_one
    convert this using 1
    ring
  set X := 5 ^ b * 3 ^ v * m
      - (1 + 4 * K + 2 * j + 2 * lenD) with hX
  have hXeven : Even X := by
    obtain ⟨an, han⟩ := hnodd
    obtain ⟨as, has⟩ := hSodd
    use an - as
    rw [hX, han, has]
    omega
  set T := X / 2 with hT
  have hbound : 1 + 4 * K + 2 * j + 2 * lenD ≤ 5 ^ b * 3 ^ v * m := by
    have hvdec : 3 ^ v = 9 * 3 ^ (v - 2) := by
      rw [show (9 : ℕ) = 3 ^ 2 from by norm_num, ← pow_add,
        show 2 + (v - 2) = v from by omega]
    have hd : 2 * lenD ≤ 8 * b + 40 := by
      rw [hlenD]
      have hr : r0b 0 b 4 ≤ 8 := by
        have h := hr₀lt
        norm_num at h ⊢
        omega
      have hlv := lenV_le
      omega
    have hKm : 4 * K ≤ 4 * (M * 3 ^ (v - 2)) := by
      rw [hK]
      have hmM : m * 3 ^ (v - 2) ≤ M * 3 ^ (v - 2) := by
        apply Nat.mul_le_mul_right
        rw [hM]
        exact Nat.le_mul_of_pos_right _ (pow_pos (by norm_num) _)
      omega
    have hjM : 2 * j ≤ 4 * (M * 3 ^ (v - 2)) := by
      rw [hj]
      calc 2 * ((c + M) * 3 ^ (v - 2)) = (2 * (c + M)) * 3 ^ (v - 2) := by
            ring
        _ ≤ (4 * M) * 3 ^ (v - 2) := Nat.mul_le_mul_right _ (by omega)
        _ = 4 * (M * 3 ^ (v - 2)) := by ring
    have hB' : 8 * b + 44 ≤ M * 3 ^ (v - 2) := by
      have e : (5 : ℕ) ^ b * m * 3 ^ (v - 2) = m * 5 ^ b * 3 ^ (v - 2) := by
        ring
      rw [e] at hB
      rw [hM]
      exact hB
    calc 1 + 4 * K + 2 * j + 2 * lenD
        ≤ 1 + 8 * (M * 3 ^ (v - 2)) + (8 * b + 40) := by omega
      _ ≤ 9 * (M * 3 ^ (v - 2)) := by omega
      _ = 5 ^ b * 3 ^ v * m := by rw [hM, hvdec]; ring
  set C := List.replicate j 9 ++ List.replicate T 0 ++ [0]
      ++ List.replicate T 0 ++ List.replicate j 9 with hC
  have hCg : C.length = 2 * j + 2 * T + 1 := (center_repunit_len_sum j T).1
  have hCσ : C.sum = 18 * j := (center_repunit_len_sum j T).2
  have hCval3 : 3 ^ v ∣ Nat.ofDigits 10 C :=
    center_repunit_dvd3 hv2 ⟨c + M, by rw [hj]; ring⟩
  have hK1 : 1 ≤ K := by
    rw [hK]
    have : 0 < m * 3 ^ (v - 2) := by positivity
    omega
  have hde_pal : D.reverse = D := hDpal.reverse_eq
  have hde81 : 81 ∣ Nat.ofDigits 10 D := by
    have h : ((Nat.ofDigits 10 D : ℕ) : ZMod 81) = 0 := by
      rw [cast_ofDigits]
      exact hD81
    exact (CharP.cast_eq_zero_iff (ZMod 81) 81 _).mp h
  have he3 : 3 ^ v ∣ Nat.ofDigits 10 D := by
    have h : 3 ^ v ∣ (3 : ℕ) ^ 4 := pow_dvd_pow 3 hv4
    norm_num at h
    exact dvd_trans h hde81
  have he3r : 3 ^ v ∣ Nat.ofDigits 10 D.reverse := by
    rw [hde_pal]; exact he3
  have hC3 : 3 ^ v ∣ Nat.ofDigits 10 C := hCval3
  have hK3 : 3 ^ (v - 2) ∣ K := ⟨m, by rw [hK]; ring⟩
  have hg3 : 3 ≤ 2 * j + 2 * T + 1 := by
    have hjp : 1 ≤ j := by
      rw [hj]
      have : 0 < (c + M) * 3 ^ (v - 2) := by positivity
      omega
    omega
  have hgodd : Odd (2 * j + 2 * T + 1) := ⟨j + T, by ring⟩
  have hKcov : m * 3 ^ (v - 4) ≤ 1 + 9 * (K / 2) := by
    have hv4' : v - 4 = 0 := by omega
    rw [hv4', pow_zero, mul_one]
    have hKm : m ≤ K := by
      rw [hK]
      exact Nat.le_mul_of_pos_right _ (pow_pos (by norm_num) _)
    have hdiv : m / 2 ≤ K / 2 := Nat.div_le_div_right hKm
    have h2m : m ≤ 2 * (m / 2) + 1 := by
      have := Nat.div_add_mod m 2
      omega
    omega
  obtain ⟨e', he', hdvdP⟩ := P_dvd_3m hm3 hm10 hv2 hK1 D rfl C hCg hg3
    hgodd hKcov hK3 he3 he3r hC3
  set MID := (List.range (2 * K)).map (pairDigit e') ++ C
      ++ ((List.range (2 * K)).map (pairDigit e')).reverse with hMID
  set P := Nat.ofDigits 10 (D ++ MID ++ D.reverse) with hP
  have hMIDpal : MID.Palindrome := mid_pal e' C (center_repunit_pal j T)
  have hMID10 : ∀ x ∈ MID, x < 10 := mid_lt10 e' he' C
    (center_repunit_lt10 j T)
  obtain ⟨hP0, hPpal, hPlen, hPσ⟩ := sandwich_spec_gen D MID hDne hD10
    (hD0 hDne) hMIDpal hMID10 rfl rfl
  have hMIDlen : MID.length = 4 * K + C.length := by
    rw [hMID, List.length_append, List.length_append, List.length_reverse,
      List.length_map, List.length_range]
    ring
  obtain ⟨rr, hrr⟩ := hXeven
  have h2T : 2 * T = X := by rw [hT]; omega
  have hlen : (Nat.digits 10 P).length = 5 ^ b * 3 ^ v * m := by
    rw [hPlen, hMIDlen, hCg]
    omega
  have hσ : 5 ^ b * 3 ^ v * m ∣ (Nat.digits 10 P).sum := by
    have hσP : (Nat.digits 10 P).sum
        = 4 * 81 * rhob 0 b 4 + 18 * (K + j) := by
      rw [hPσ, mid_sum e' he' C, hCσ, hDσ]
      ring
    rw [hσP]
    have h3vd : 3 ^ v ∣ 4 * 81 * rhob 0 b 4 + 18 * (K + j) := by
      have h1 : 3 ^ v ∣ 4 * 81 * rhob 0 b 4 := by
        have h81v : 3 ^ v ∣ 81 := by
          have h : 3 ^ v ∣ (3 : ℕ) ^ 4 := pow_dvd_pow 3 hv4
          norm_num at h
          exact h
        obtain ⟨w, hw⟩ := h81v
        exact ⟨4 * rhob 0 b 4 * w, by rw [hw]; ring⟩
      have h2 : 3 ^ v ∣ 18 * (K + j) := by
        rw [hK, hj]
        refine ⟨2 * (m + (c + M)), ?_⟩
        rw [show (3 : ℕ) ^ v = 9 * 3 ^ (v - 2) from by
          rw [show (9 : ℕ) = 3 ^ 2 from by norm_num, ← pow_add,
            show 2 + (v - 2) = v from by omega]]
        ring
      exact Nat.dvd_add h1 h2
    have hM' : M ∣ 4 * 81 * rhob 0 b 4 + 18 * (K + j) := by
      have e : 4 * 81 * rhob 0 b 4 + 18 * (K + j)
          = (4 * 81 * rhob 0 b 4 + 18 * 3 ^ (v - 2) * (m + c))
            + 18 * 3 ^ (v - 2) * M := by
        rw [hK, hj]
        ring
      rw [e]
      exact Nat.dvd_add hcdvd ⟨18 * 3 ^ (v - 2), by ring⟩
    have hcop : (3 ^ v).Coprime (m * 5 ^ b) := h3vm.mul_right h3v5b
    have hjoin := hcop.mul_dvd_of_dvd_of_dvd h3vd hM'
    rwa [show 5 ^ b * 3 ^ v * m = 3 ^ v * (m * 5 ^ b) from by ring]
  have hPd : 5 ^ b * 3 ^ v * m ∣ P := by
    have h25 : 2 ^ 0 * 5 ^ b ∣ P := by
      have hle_big : max 0 b ≤ lenD := by
        rw [hlenD]
        omega
      have := B_dvd_P (le := lenD) (de := D) (MID := MID) rfl hD25 hle_big
      rwa [hP]
    obtain ⟨w, hw⟩ := hdvdP
    have h3m : 3 ^ v * m ∣ P := ⟨w, by rw [hw]; ring⟩
    have := n_dvd_P_pow10 (a := 0) (b := b) (v := v) (m := m) (z := 0)
      (a' := 0) (b' := b) (P := P) h25 h3m rfl (add_zero b) hm30
    rwa [pow_zero, one_mul, pow_zero, mul_one] at this
  refine ⟨P, 0, hP0, ?_, hPpal, ?_, ?_, hσ⟩
  · intro h
    omega
  · rw [hlen, add_zero]
  · rwa [pow_zero, mul_one]
end A084017
namespace A084017
open Finset List Nat BigOperators Pointwise

set_option maxHeartbeats 800000 in
theorem assemble_zbig {a b v m : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hm0 : 1 ≤ m) (hv : 5 ≤ v) (hm30 : m.Coprime 30) :
    ∃ P z : ℕ, P ≠ 0
      ∧ (0 < z → 10 ∣ 2 ^ a * 5 ^ b * 3 ^ v * m)
      ∧ (Nat.digits 10 P).Palindrome
      ∧ (Nat.digits 10 P).length + z = 2 ^ a * 5 ^ b * 3 ^ v * m
      ∧ 2 ^ a * 5 ^ b * 3 ^ v * m ∣ P * 10 ^ z
      ∧ 2 ^ a * 5 ^ b * 3 ^ v * m ∣ (Nat.digits 10 P).sum := by
  classical
  set z := a + b + 1 + (a + b) % 2 with hz
  set n := 2 ^ a * 5 ^ b * 3 ^ v * m with hn
  haveI : NeZero m := ⟨by omega⟩
  have hm3 : m.Coprime 3 := hm30.coprime_dvd_right (by norm_num)
  have hm10 : m.Coprime 10 := hm30.coprime_dvd_right (by norm_num)
  have hm2 : m.Coprime 2 := hm30.coprime_dvd_right (by norm_num)
  have hv2 : 2 ≤ v := by omega
  have hza : a < z := by rw [hz]; omega
  have hzb : b < z := by rw [hz]; omega
  have hzodd : Odd z := by
    refine ⟨(a + b) / 2 + (a + b) % 2, ?_⟩
    rw [hz]
    omega
  have hz0 : 0 < z := by rw [hz]; omega
  have haz : a - z = 0 := Nat.sub_eq_zero_of_le (le_of_lt hza)
  have hbz : b - z = 0 := Nat.sub_eq_zero_of_le (le_of_lt hzb)
  
  set p2 := 2 ^ (a - 1) with hp2
  have hp2pos : 0 < p2 := pow_pos (by norm_num) _
  set c := p2 - m % p2 with hc
  have hmc : p2 ∣ m + c := by
    have hlt : m % p2 < p2 := Nat.mod_lt _ hp2pos
    have h2 := Nat.div_add_mod m p2
    have h3 : p2 * (m / p2 + 1) = p2 * (m / p2) + p2 := Nat.mul_succ _ _
    refine ⟨m / p2 + 1, ?_⟩
    rw [hc]
    omega
  have hcle : c ≤ p2 := Nat.sub_le _ _
  have hc1 : 1 ≤ c := by
    have hlt : m % p2 < p2 := Nat.mod_lt _ hp2pos
    rw [hc]
    omega
  
  set K := m * 3 ^ (v - 2) with hK
  set j := c * 3 ^ (v - 2) with hj
  set M := m * 5 ^ b with hM
  have hM0 : 0 < M := by
    rw [hM]
    exact Nat.mul_pos (by omega) (pow_pos (by norm_num) _)
  have h4m : (4 : ℕ).Coprime m := hm2.symm.pow_left 2
  have h3vm : (3 ^ v).Coprime m := hm3.symm.pow_left v
  have h45b : (4 : ℕ).Coprime (5 ^ b) := (by decide : Nat.Coprime 4 5).pow_right b
  have h3v5b : (3 ^ v).Coprime (5 ^ b) :=
    ((by decide : Nat.Coprime 3 5).pow_right b).pow_left v
  have hcop43 : (4 * 3 ^ v).Coprime M := by
    rw [hM]
    exact Nat.Coprime.mul_right (h4m.mul_left h3vm) (h45b.mul_left h3v5b)
  
  have hmo : Odd m := by
    have h2 : ¬ (2 : ℕ) ∣ m :=
      (Nat.prime_two.coprime_iff_not_dvd).mp hm2.symm
    rw [← Nat.not_even_iff_odd]
    rintro ⟨c', hc'⟩
    exact h2 ⟨c', by omega⟩
  have hModd : Odd M := by
    rw [hM]
    exact hmo.mul (Odd.pow (by decide : Odd 5))
  have hnd : ¬ (2 : ℕ) ∣ M := by
    rintro ⟨r, hr⟩
    obtain ⟨s, hs⟩ := hModd
    omega
  have hcop2 : M.Coprime (2 ^ (a - 2)) :=
    ((Nat.prime_two.coprime_iff_not_dvd).mpr hnd).symm.pow_right _
  
  obtain ⟨t, htlt, ht2, htdvd⟩ := sigma_t_solve2 (v := v)
    (ρ := rhob (a - z) (b - z) v) (S := K + j) (M := M) (w := a - 2)
    hM0 hcop43 hcop2
  
  have hmin : a - z = 0 ∨ b - z = 0 := Or.inl haz
  obtain ⟨D, hDpal, hD10, hDne, hD0, hD25, hD81, hDσ, hr₀lt, hlenD⟩ :=
    border_pal (a' := a - z) (b' := b - z) (q := v)
      (s₁ := max (a - z) (b - z)) (t := t)
      (by omega) hmin (le_refl _)
  set lenD := D.length with hlenD'
  have hlenN : lenD
      = 2 * ((Nat.digits 10 (9 * 2 ^ (a - z) * 5 ^ (b - z))).length
          + max (a - z) (b - z) + r0b (a - z) (b - z) v)
        + 2 * (3 ^ (v - 2) * t) := by
    rw [hlenD]
    ring
  
  have lenV_le : (Nat.digits 10 (9 * 2 ^ (a - z) * 5 ^ (b - z))).length
      ≤ a + b := by
    have hVpos : (9 * 2 ^ (a - z) * 5 ^ (b - z) : ℕ) ≠ 0 := by positivity
    have hb2 := Nat.base_pow_length_digits_le 10
      (9 * 2 ^ (a - z) * 5 ^ (b - z)) (by norm_num) hVpos
    have hlt : 10 * (9 * 2 ^ (a - z) * 5 ^ (b - z)) < 10 ^ (a + b) := by
      have h1 : 2 ^ (a - z) ≤ 10 ^ (a - z) :=
        Nat.pow_le_pow_left (by norm_num) _
      have h2 : 5 ^ (b - z) ≤ 10 ^ (b - z) :=
        Nat.pow_le_pow_left (by norm_num) _
      have h3 : 2 ^ (a - z) * 5 ^ (b - z) ≤ 10 ^ (a - z) * 10 ^ (b - z) :=
        Nat.mul_le_mul h1 h2
      have h4 : 10 ^ (a - z) * 10 ^ (b - z) = 10 ^ (a + b - 2 * z) := by
        rw [← pow_add]
        congr 1
        omega
      calc 10 * (9 * 2 ^ (a - z) * 5 ^ (b - z))
          = 90 * (2 ^ (a - z) * 5 ^ (b - z)) := by ring
        _ ≤ 90 * (10 ^ (a - z) * 10 ^ (b - z)) :=
            Nat.mul_le_mul_left 90 h3
        _ = 90 * 10 ^ (a + b - 2 * z) := by rw [h4]
        _ < 100 * 10 ^ (a + b - 2 * z) := by
            have hpos : 0 < 10 ^ (a + b - 2 * z) := by positivity
            omega
        _ = 10 ^ (a + b - 2 * z + 2) := by
            rw [show (100 : ℕ) = 10 ^ 2 from by norm_num, ← pow_add]
            congr 1
            omega
        _ ≤ 10 ^ (a + b) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpow := lt_of_le_of_lt hb2 hlt
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 10)).mp hpow
    omega
  
  have hne : Even n := by
    rw [hn]
    refine ⟨2 ^ (a - 1) * 5 ^ b * 3 ^ v * m, ?_⟩
    rw [show 2 ^ a = 2 * 2 ^ (a - 1) from by
      rw [← Nat.pow_succ', Nat.succ_eq_add_one, Nat.sub_add_cancel ha]]
    ring
  have hzlt : z < n := by
    have ha2 : a < 2 ^ a := Nat.lt_two_pow_self
    have hb5 : b < 5 ^ b := by
      have h2b : b < 2 ^ b := Nat.lt_two_pow_self
      have h25b : 2 ^ b ≤ 5 ^ b := Nat.pow_le_pow_left (by norm_num) _
      omega
    have hX1 : 1 ≤ 2 ^ a * 5 ^ b := Nat.succ_le_of_lt (by positivity)
    have h2aX : 2 ^ a ≤ 2 ^ a * 5 ^ b :=
      Nat.le_mul_of_pos_right _ (by positivity)
    have h5bX : 5 ^ b ≤ 2 ^ a * 5 ^ b :=
      Nat.le_mul_of_pos_left _ (by positivity)
    have hXn : 243 * (2 ^ a * 5 ^ b) ≤ n := by
      rw [hn]
      have h3 : 243 ≤ 3 ^ v * m := by
        have h : (3 : ℕ) ^ 5 ≤ 3 ^ v := Nat.pow_le_pow_right (by norm_num) hv
        norm_num at h
        calc 243 ≤ 3 ^ v * 1 := by omega
          _ ≤ 3 ^ v * m := Nat.mul_le_mul_left _ hm0
      calc 243 * (2 ^ a * 5 ^ b)
          ≤ (3 ^ v * m) * (2 ^ a * 5 ^ b) := Nat.mul_le_mul_right _ h3
        _ = 2 ^ a * 5 ^ b * 3 ^ v * m := by ring
    rw [hz]
    omega
  have hno : Odd (n - z) := by
    obtain ⟨en, hen⟩ := hne
    obtain ⟨oz, hoz⟩ := hzodd
    refine ⟨en - oz - 1, ?_⟩
    rw [hoz, hen] at hzlt ⊢
    omega
  set S := 1 + 4 * K + 2 * j + 2 * lenD with hS
  have hSodd : Odd S := by
    have e1 : Even (4 * K) := ⟨2 * K, by ring⟩
    have e2 : Even (2 * j) := ⟨j, by ring⟩
    have e3 : Even (2 * lenD) := ⟨lenD, by ring⟩
    obtain ⟨w, hw⟩ := (e1.add e2).add e3
    use w
    rw [hS]
    omega
  set X := (n - z) - S with hX
  have hXeven : Even X := by
    obtain ⟨an, han⟩ := hno
    obtain ⟨as, has⟩ := hSodd
    refine ⟨an - as, ?_⟩
    rw [hX, han, has]
    omega
  set T := X / 2 with hT
  
  have hbound : S + z ≤ n := by
    set E := 2 ^ a * 5 ^ b * 3 ^ (v - 2) * m with hE
    have hvdec : 3 ^ v = 9 * 3 ^ (v - 2) := by
      rw [show (9 : ℕ) = 3 ^ 2 from by norm_num, ← pow_add,
        show 2 + (v - 2) = v from by omega]
    have hE9 : n = 9 * E := by
      rw [hn, hE, hvdec]
      ring
    have g1 : 10 * (m * 3 ^ (v - 2)) ≤ E := by
      rw [hE]
      have h10 : 10 ≤ 2 ^ a * 5 ^ b := by
        calc 10 = 2 * 5 := by norm_num
          _ ≤ 2 ^ a * 5 ^ b :=
              Nat.mul_le_mul (Nat.pow_le_pow_right (n := 2) (by norm_num) ha)
                (Nat.pow_le_pow_right (n := 5) (by norm_num) hb)
      calc 10 * (m * 3 ^ (v - 2))
          ≤ (2 ^ a * 5 ^ b) * (m * 3 ^ (v - 2)) :=
            Nat.mul_le_mul_right _ h10
        _ = 2 ^ a * 5 ^ b * 3 ^ (v - 2) * m := by ring
    have g2 : 2 * (c * 3 ^ (v - 2)) ≤ E := by
      have hc2 : 2 * c ≤ 2 ^ a := by
        calc 2 * c ≤ 2 * 2 ^ (a - 1) :=
              Nat.mul_le_mul_left 2 hcle
          _ = 2 ^ a := by
              rw [← Nat.pow_succ', Nat.succ_eq_add_one, Nat.sub_add_cancel ha]
      calc 2 * (c * 3 ^ (v - 2)) = (2 * c) * 3 ^ (v - 2) := by ring
        _ ≤ 2 ^ a * 3 ^ (v - 2) := Nat.mul_le_mul_right _ hc2
        _ ≤ E := by
            rw [hE]
            calc 2 ^ a * 3 ^ (v - 2)
                ≤ (2 ^ a * 3 ^ (v - 2)) * (5 ^ b * m) :=
                  Nat.le_mul_of_pos_right _ (by positivity)
              _ = 2 ^ a * 5 ^ b * 3 ^ (v - 2) * m := by ring
    have h4pow : 4 * 2 ^ (a - 2) ≤ 2 * 2 ^ a := by
      rcases Nat.eq_or_lt_of_le ha with rfl | h2
      · norm_num
      · have e : a = (a - 2) + 2 := by omega
        calc 4 * 2 ^ (a - 2) ≤ 8 * 2 ^ (a - 2) := by
              apply Nat.mul_le_mul_right
              norm_num
          _ = 2 * 2 ^ ((a - 2) + 2) := by
              rw [pow_add]
              ring
          _ = 2 * 2 ^ a := by rw [← e]
    have g4 : 4 * (3 ^ (v - 2) * t) + 4 * 3 ^ (v - 2) ≤ 2 * E := by
      have ht1 : t + 1 ≤ M * 2 ^ (a - 2) := htlt
      calc 4 * (3 ^ (v - 2) * t) + 4 * 3 ^ (v - 2)
          = 4 * 3 ^ (v - 2) * (t + 1) := by ring
        _ ≤ 4 * 3 ^ (v - 2) * (M * 2 ^ (a - 2)) :=
            Nat.mul_le_mul_left _ ht1
        _ = (4 * 2 ^ (a - 2)) * (3 ^ (v - 2) * M) := by ring
        _ ≤ (2 * 2 ^ a) * (3 ^ (v - 2) * M) :=
            Nat.mul_le_mul_right _ h4pow
        _ = 2 * E := by rw [hE, hM]; ring
    have hpa : 2 * a ≤ 2 ^ a := by
      have h : a - 1 < 2 ^ (a - 1) := Nat.lt_two_pow_self
      calc 2 * a = 2 * ((a - 1) + 1) := by
            rw [Nat.sub_add_cancel ha]
          _ ≤ 2 * 2 ^ (a - 1) := Nat.mul_le_mul_left 2 (by omega)
          _ = 2 ^ a := by
              rw [← Nat.pow_succ', Nat.succ_eq_add_one, Nat.sub_add_cancel ha]
    have hpb : 5 * b ≤ 5 ^ b := by
      have h : b - 1 < 2 ^ (b - 1) := Nat.lt_two_pow_self
      have h2 : 2 ^ (b - 1) ≤ 5 ^ (b - 1) :=
        Nat.pow_le_pow_left (by norm_num) _
      calc 5 * b = 5 * ((b - 1) + 1) := by
            rw [Nat.sub_add_cancel hb]
          _ ≤ 5 * 5 ^ (b - 1) := Nat.mul_le_mul_left 5 (by omega)
          _ = 5 ^ b := by
              rw [← Nat.pow_succ', Nat.succ_eq_add_one, Nat.sub_add_cancel hb]
    have hab1 : a ≤ a * b := Nat.le_mul_of_pos_right _ hb
    have hab2 : b ≤ a * b := Nat.le_mul_of_pos_left _ ha
    have h25 : 2 * a * (5 * b) ≤ 2 ^ a * 5 ^ b := Nat.mul_le_mul hpa hpb
    have g5 : 8 * (a + b) ≤ 2 * E := by
      have hab : a + b ≤ 2 * (a * b) := by
        have h1 : a ≤ a * b := Nat.le_mul_of_pos_right _ hb
        have h2 : b ≤ a * b := Nat.le_mul_of_pos_left _ ha
        omega
      have hE' : 2 ^ a * 5 ^ b ≤ E := by
        rw [hE]
        calc 2 ^ a * 5 ^ b
            ≤ (2 ^ a * 5 ^ b) * (3 ^ (v - 2) * m) :=
              Nat.le_mul_of_pos_right _ (by positivity)
          _ = 2 ^ a * 5 ^ b * 3 ^ (v - 2) * m := by ring
      calc 8 * (a + b) ≤ 8 * (2 * (a * b)) := Nat.mul_le_mul_left _ hab
        _ = 16 * (a * b) := by ring
        _ ≤ 20 * (a * b) := by
            have h3 : 1 ≤ a * b := Nat.mul_pos ha hb
            omega
        _ = 2 * (2 * a * (5 * b)) := by ring
        _ ≤ 2 * (2 ^ a * 5 ^ b) := Nat.mul_le_mul_left _ h25
        _ ≤ 2 * E := Nat.mul_le_mul_left _ hE'
    have g6 : 4 * 3 ^ (v - 2) ≤ 4 * E := by
      apply Nat.mul_le_mul_left
      rw [hE]
      calc 3 ^ (v - 2)
          ≤ (2 ^ a * 5 ^ b * m) * 3 ^ (v - 2) :=
            Nat.le_mul_of_pos_left _ (by positivity)
        _ = 2 ^ a * 5 ^ b * 3 ^ (v - 2) * m := by ring
    have g7 : z ≤ E := by
      have hzz : z ≤ a + b + 2 := by rw [hz]; omega
      have hab1 : 1 ≤ a * b := Nat.mul_pos ha hb
      have hab' : a + b ≤ a * b + 1 := by
        have e : a * b = (a - 1) * (b - 1) + (a - 1) + (b - 1) + 1 := by
          conv_lhs => rw [show a = (a - 1) + 1
              from (Nat.sub_add_cancel ha).symm,
              show b = (b - 1) + 1 from (Nat.sub_add_cancel hb).symm]
          ring
        omega
      have h3 : (27 : ℕ) ≤ 3 ^ (v - 2) * m := by
        have h27 : (3 : ℕ) ^ 3 ≤ 3 ^ (v - 2) :=
          Nat.pow_le_pow_right (by norm_num) (by omega : 3 ≤ v - 2)
        norm_num at h27
        calc 27 ≤ 3 ^ (v - 2) * 1 := by omega
          _ ≤ 3 ^ (v - 2) * m := Nat.mul_le_mul_left _ hm0
      have hab25 : a * b ≤ 2 ^ a * 5 ^ b := by
        have h1 : a ≤ 2 ^ a := le_of_lt Nat.lt_two_pow_self
        have h2 : b ≤ 5 ^ b := by
          have h2b : b < 2 ^ b := Nat.lt_two_pow_self
          have h25b : 2 ^ b ≤ 5 ^ b := Nat.pow_le_pow_left (by norm_num) _
          omega
        exact Nat.mul_le_mul h1 h2
      have habE : 27 * (a * b) ≤ E := by
        have hstep := Nat.mul_le_mul h3 hab25
        rw [hE]
        calc 27 * (a * b)
            ≤ (3 ^ (v - 2) * m) * (2 ^ a * 5 ^ b) := hstep
          _ = 2 ^ a * 5 ^ b * 3 ^ (v - 2) * m := by ring
      omega
    have hmax : max (a - z) (b - z) ≤ a + b := by
      rw [Nat.max_le]
      omega
    have hr : r0b (a - z) (b - z) v + 1 ≤ 3 ^ (v - 2) := hr₀lt
    have hlen3 : 2 * lenD
        ≤ 8 * (a + b) + 4 * (3 ^ (v - 2) * t) + 4 * 3 ^ (v - 2) := by
      rw [hlenN]
      omega
    have hE2 : 2 ≤ E := by
      rw [hE]
      have hu4 : 2 ≤ 3 ^ (v - 2) := by
        have h : (3 : ℕ) ^ 3 ≤ 3 ^ (v - 2) :=
          Nat.pow_le_pow_right (by norm_num) (by omega : 3 ≤ v - 2)
        norm_num at h
        omega
      calc 2 ≤ 3 ^ (v - 2) * 1 := by omega
        _ ≤ 3 ^ (v - 2) * (2 ^ a * 5 ^ b * m) :=
            Nat.mul_le_mul_left _ (Nat.succ_le_of_lt (by positivity))
        _ = 2 ^ a * 5 ^ b * 3 ^ (v - 2) * m := by ring
    rw [hS, hK, hj]
    omega
  
  set C := List.replicate j 9 ++ List.replicate T 0 ++ [0]
      ++ List.replicate T 0 ++ List.replicate j 9 with hC
  have hCg : C.length = 2 * j + 2 * T + 1 := (center_repunit_len_sum j T).1
  have hCσ : C.sum = 18 * j := (center_repunit_len_sum j T).2
  have hCval3 : 3 ^ v ∣ Nat.ofDigits 10 C :=
    center_repunit_dvd3 hv2 ⟨c, by rw [hj]; ring⟩
  have hK1 : 1 ≤ K := by
    rw [hK]
    have : 0 < m * 3 ^ (v - 2) := by positivity
    omega
  have hde_pal : D.reverse = D := hDpal.reverse_eq
  have hde81 : 81 ∣ Nat.ofDigits 10 D := by
    have h : ((Nat.ofDigits 10 D : ℕ) : ZMod 81) = 0 := by
      rw [cast_ofDigits]
      exact hD81
    exact (CharP.cast_eq_zero_iff (ZMod 81) 81 _).mp h
  have hC81 : 81 ∣ Nat.ofDigits 10 C :=
    dvd_trans (pow_dvd_pow 3 (by omega : 4 ≤ v)) hCval3
  have hK9 : 9 ∣ K := by
    rw [hK]
    exact dvd_mul_of_dvd_right (pow_dvd_pow 3 (by omega : 2 ≤ v - 2)) m
  obtain ⟨s₀, hs0⟩ := hs0_solver hv hK1 D hde_pal hde81 C hC81 hK9
  have hj1 : 1 ≤ j := by
    rw [hj]
    exact Nat.mul_pos hc1 (by positivity)
  have hg3 : 3 ≤ 2 * j + 2 * T + 1 := by omega
  have hgodd : Odd (2 * j + 2 * T + 1) := ⟨j + T, by ring⟩
  have hKcov : m * 3 ^ (v - 4) ≤ 1 + 9 * (K / 2) := by
    have hpow : 3 ^ (v - 2) = 9 * 3 ^ (v - 4) := by
      rw [show (9 : ℕ) = 3 ^ 2 from by norm_num, ← pow_add,
        show 2 + (v - 4) = v - 2 from by omega]
    have hF : 0 < m * 3 ^ (v - 4) := by positivity
    rw [hK, hpow]
    have e : m * (9 * 3 ^ (v - 4)) = 9 * (m * 3 ^ (v - 4)) := by ring
    rw [e]
    omega
  obtain ⟨e', he', hdvdP⟩ := P_dvd_3m81 hm3 hm10 D rfl C hCg hg3 hgodd
    hKcov s₀ hs0
  set MID := (List.range (2 * K)).map (pairDigit e') ++ C
      ++ ((List.range (2 * K)).map (pairDigit e')).reverse with hMID
  set P := Nat.ofDigits 10 (D ++ MID ++ D.reverse) with hP
  have hMIDpal : MID.Palindrome := mid_pal e' C (center_repunit_pal j T)
  have hMID10 : ∀ x ∈ MID, x < 10 := mid_lt10 e' he' C
    (center_repunit_lt10 j T)
  obtain ⟨hP0, hPpal, hPlen, hPσ⟩ := sandwich_spec_gen D MID hDne hD10
    (hD0 hDne) hMIDpal hMID10 rfl rfl
  have hMIDlen : MID.length = 4 * K + C.length := by
    rw [hMID, List.length_append, List.length_append, List.length_reverse,
      List.length_map, List.length_range]
    ring
  obtain ⟨rr, hrr⟩ := hXeven
  have h2T : 2 * T = X := by rw [hT]; omega
  have hlen : (Nat.digits 10 P).length = n - z := by
    rw [hPlen, hMIDlen, hCg]
    omega
  
  have hσP : (Nat.digits 10 P).sum
      = 4 * 3 ^ v * (rhob (a - z) (b - z) v + t) + 18 * (K + j) := by
    rw [hPσ, mid_sum e' he' C, hCσ, hDσ]
    ring
  have h2a : 2 ^ a ∣ (Nat.digits 10 P).sum := by
    rw [hσP]
    apply Nat.dvd_add
    · have h21 : 2 ^ a ∣ 4 * (rhob (a - z) (b - z) v + t) := by
        rcases Nat.lt_or_ge 2 a with h | h
        · obtain ⟨u, hu⟩ := ht2
          have hpa : 2 ^ a = 2 ^ (a - 2) * 4 := by
            rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, ← pow_add,
              show a - 2 + 2 = a from by omega]
          rw [hpa]
          exact ⟨u, by rw [hu]; ring⟩
        · exact dvd_mul_of_dvd_left (show 2 ^ a ∣ 4 from pow_dvd_pow 2 (by omega)) _
      have e1 : 4 * 3 ^ v * (rhob (a - z) (b - z) v + t)
          = 3 ^ v * (4 * (rhob (a - z) (b - z) v + t)) := by ring
      rw [e1]
      exact dvd_mul_of_dvd_right h21 _
    · have h22 : 2 ^ a ∣ 2 * (m + c) := by
        obtain ⟨u, hu⟩ := hmc
        have hpa : 2 ^ a = 2 ^ (a - 1) * 2 := by
          rw [← pow_succ, Nat.sub_add_cancel ha]
        rw [hpa]
        exact ⟨u, by rw [hu]; ring⟩
      have e2 : 18 * (K + j) = (9 * 3 ^ (v - 2)) * (2 * (m + c)) := by
        rw [hK, hj, ← Nat.add_mul]
        ring
      rw [e2]
      exact dvd_mul_of_dvd_right h22 _
  have h3vd : 3 ^ v ∣ (Nat.digits 10 P).sum := by
    rw [hσP]
    apply Nat.dvd_add
    · exact ⟨4 * (rhob (a - z) (b - z) v + t), by ring⟩
    · refine ⟨2 * (m + c), ?_⟩
      rw [hK, hj, ← Nat.add_mul]
      rw [show (3 : ℕ) ^ v = 9 * 3 ^ (v - 2) from by
        rw [show (9 : ℕ) = 3 ^ 2 from by norm_num, ← pow_add,
          show 2 + (v - 2) = v from by omega]]
      ring
  have hMdvd : m * 5 ^ b ∣ (Nat.digits 10 P).sum := by
    rw [hσP, ← hM]
    exact htdvd
  have hσ : n ∣ (Nat.digits 10 P).sum := by
    have hcop2a : (2 ^ a).Coprime (3 ^ v) :=
      ((by decide : Nat.Coprime 2 3).pow_right v).pow_left a
    have hcopB : (2 ^ a * 3 ^ v).Coprime (m * 5 ^ b) := by
      apply Nat.Coprime.mul_right
      · exact Nat.Coprime.mul_left (hm2.symm.pow_left a) (hm3.symm.pow_left v)
      · exact Nat.Coprime.mul_left
          (((by decide : Nat.Coprime 2 5).pow_right b).pow_left a)
          (((by decide : Nat.Coprime 3 5).pow_right b).pow_left v)
    have hjoin1 := hcop2a.mul_dvd_of_dvd_of_dvd h2a h3vd
    have hjoin2 := hcopB.mul_dvd_of_dvd_of_dvd hjoin1 hMdvd
    rw [hn]
    rwa [show 2 ^ a * 5 ^ b * 3 ^ v * m = 2 ^ a * 3 ^ v * (m * 5 ^ b)
      from by ring]
  
  have hPd : n ∣ P * 10 ^ z := by
    have h25 : 2 ^ (a - z) * 5 ^ (b - z) ∣ P := by
      have hle_big : max (a - z) (b - z) ≤ lenD := by
        rw [hlenN]
        omega
      have := B_dvd_P (le := lenD) (de := D) (MID := MID) rfl hD25 hle_big
      rwa [hP]
    obtain ⟨w, hw⟩ := hdvdP
    have h3m : 3 ^ v * m ∣ P := ⟨w, by rw [hw]; ring⟩
    have := n_dvd_P_pow10_le (a := a) (b := b) (v := v) (m := m) (z := z)
      (a' := a - z) (b' := b - z) (P := P) h25 h3m
      (by rw [haz, Nat.zero_add]; exact le_of_lt hza)
      (by rw [hbz, Nat.zero_add]; exact le_of_lt hzb) hm30
    rwa [hn]
  refine ⟨P, z, hP0, ?_, hPpal, ?_, hPd, hσ⟩
  · intro _
    rw [hn]
    have h2a' : 2 ^ a = 2 * 2 ^ (a - 1) := by
      rw [← Nat.pow_succ', Nat.succ_eq_add_one, Nat.sub_add_cancel ha]
    have h5b' : 5 ^ b = 5 * 5 ^ (b - 1) := by
      rw [← Nat.pow_succ', Nat.succ_eq_add_one, Nat.sub_add_cancel hb]
    exact ⟨2 ^ (a - 1) * 5 ^ (b - 1) * 3 ^ v * m, by rw [h2a', h5b']; ring⟩
  · rw [hlen]
    exact Nat.sub_add_cancel (le_of_lt hzlt)

end A084017


namespace A084017
open Finset List Nat BigOperators Pointwise


set_option maxHeartbeats 800000 in
theorem sigma_cm_solve {v ρ' m M a : ℕ} (hM : 0 < M) (ha : 1 ≤ a)
    (hcop : (18 * 3 ^ (v - 2)).Coprime M) (hcop2 : M.Coprime (2 ^ (a - 1))) :
    ∃ c : ℕ, 1 ≤ c ∧ c ≤ 2 ^ (a - 1) * M ∧ 2 ^ (a - 1) ∣ m + c
      ∧ M ∣ 4 * 81 * ρ' + 18 * 3 ^ (v - 2) * (m + c) := by
  haveI : NeZero M := ⟨hM.ne'⟩
  set p2 := 2 ^ (a - 1) with hp2
  have hp2pos : 0 < p2 := pow_pos (by norm_num) _
  set c0 := p2 - m % p2 with hc0
  have hmc0 : p2 ∣ m + c0 := by
    have hlt : m % p2 < p2 := Nat.mod_lt _ hp2pos
    have h2 := Nat.div_add_mod m p2
    have h3 : p2 * (m / p2 + 1) = p2 * (m / p2) + p2 := Nat.mul_succ _ _
    refine ⟨m / p2 + 1, ?_⟩
    rw [hc0]
    omega
  have hc0le : c0 ≤ p2 := Nat.sub_le _ _
  have hc0ge : 1 ≤ c0 := by
    have hlt : m % p2 < p2 := Nat.mod_lt _ hp2pos
    rw [hc0]
    omega
  
  set u : ZMod M := ((18 * 3 ^ (v - 2) : ℕ) : ZMod M) with hu
  have hunit : IsUnit u := by
    rw [hu, ZMod.isUnit_iff_coprime]
    exact hcop
  have hp2u : IsUnit (p2 : ZMod M) := by
    rw [ZMod.isUnit_iff_coprime]
    exact hcop2.symm
  have hunit' : IsUnit (↑p2 * u : ZMod M) := hp2u.mul hunit
  set s : ℕ := (-(↑(4 * 81 * ρ' + 18 * 3 ^ (v - 2) * (m + c0))
      * (↑p2 * u)⁻¹) : ZMod M).val with hs
  have hkey : (↑p2 * u) * (s : ZMod M)
      = -(↑(4 * 81 * ρ' + 18 * 3 ^ (v - 2) * (m + c0)) : ZMod M) := by
    show (↑p2 * u) * ((-(↑(4 * 81 * ρ' + 18 * 3 ^ (v - 2) * (m + c0))
        * (↑p2 * u)⁻¹) : ZMod M).val : ZMod M) = _
    rw [ZMod.natCast_val, ZMod.cast_id]
    calc (↑p2 * u) * (-(↑(4 * 81 * ρ' + 18 * 3 ^ (v - 2) * (m + c0))
          * (↑p2 * u)⁻¹))
        = -((↑p2 * u) * (↑(4 * 81 * ρ' + 18 * 3 ^ (v - 2) * (m + c0))
            * (↑p2 * u)⁻¹)) := by rw [mul_neg]
      _ = -(↑(4 * 81 * ρ' + 18 * 3 ^ (v - 2) * (m + c0))
            * ((↑p2 * u) * (↑p2 * u)⁻¹)) := by ring
      _ = -↑(4 * 81 * ρ' + 18 * 3 ^ (v - 2) * (m + c0)) := by
          rw [ZMod.mul_inv_of_unit _ hunit']; ring
  refine ⟨c0 + p2 * s, by omega, ?_, ?_, ?_⟩
  · have hslt : s < M := ZMod.val_lt _
    have hsle : s ≤ M - 1 := by omega
    have hle : p2 * s ≤ p2 * (M - 1) := Nat.mul_le_mul_left p2 hsle
    calc c0 + p2 * s ≤ p2 + p2 * (M - 1) := by omega
      _ = p2 * M := by
          have h : p2 * (M - 1) + p2 = p2 * M := by
            rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hM]
          omega
  · have e : m + (c0 + p2 * s) = (m + c0) + p2 * s := by ring
    rw [e]
    exact Nat.dvd_add hmc0 (dvd_mul_right p2 s)
  · have hcast : ((4 * 81 * ρ' + 18 * 3 ^ (v - 2) * (m + (c0 + p2 * s)) : ℕ)
        : ZMod M) = 0 := by
      have hu' : u = (18 : ZMod M) * (3 : ZMod M) ^ (v - 2) := by
        rw [hu]; push_cast; ring
      have hstep : u * ((m : ZMod M) + ↑c0) + (↑p2 * u) * ↑s
          + 4 * 81 * (ρ' : ZMod M) = 0 := by
        have hkey2 : (↑p2 * u) * (s : ZMod M)
            = -(4 * 81 * (ρ' : ZMod M) + u * (↑m + ↑c0)) := by
          rw [hkey]
          congr 1
          rw [hu]
          push_cast
          ring
        linear_combination hkey2
      have heq : ((4 * 81 * ρ' + 18 * 3 ^ (v - 2) * (m + (c0 + p2 * s)) : ℕ)
          : ZMod M)
          = u * (↑m + ↑c0) + (↑p2 * u) * ↑s + 4 * 81 * ↑ρ' := by
        rw [hu']
        push_cast
        ring
      rw [heq, hstep]
    exact (CharP.cast_eq_zero_iff (ZMod M) M _).mp hcast

set_option maxHeartbeats 800000 in
theorem assemble_zbig4 {a b v m : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hm0 : 1 ≤ m) (hv2 : 2 ≤ v) (hv4 : v ≤ 4) (hm30 : m.Coprime 30)
    (hB2 : 36 * 2 ^ (a - 2) ≤ 2 * (2 ^ a * 5 ^ b * 3 ^ (v - 2) * m)) :
    ∃ P z : ℕ, P ≠ 0
      ∧ (0 < z → 10 ∣ 2 ^ a * 5 ^ b * 3 ^ v * m)
      ∧ (Nat.digits 10 P).Palindrome
      ∧ (Nat.digits 10 P).length + z = 2 ^ a * 5 ^ b * 3 ^ v * m
      ∧ 2 ^ a * 5 ^ b * 3 ^ v * m ∣ P * 10 ^ z
      ∧ 2 ^ a * 5 ^ b * 3 ^ v * m ∣ (Nat.digits 10 P).sum := by
  classical
  set z := a + b + 1 + (a + b) % 2 with hz
  set n := 2 ^ a * 5 ^ b * 3 ^ v * m with hn
  haveI : NeZero m := ⟨by omega⟩
  have hm3 : m.Coprime 3 := hm30.coprime_dvd_right (by norm_num)
  have hm10 : m.Coprime 10 := hm30.coprime_dvd_right (by norm_num)
  have hm2 : m.Coprime 2 := hm30.coprime_dvd_right (by norm_num)
  have hza : a < z := by rw [hz]; omega
  have hzb : b < z := by rw [hz]; omega
  have hzodd : Odd z := by
    refine ⟨(a + b) / 2 + (a + b) % 2, ?_⟩
    rw [hz]
    omega
  have hz0 : 0 < z := by rw [hz]; omega
  have haz : a - z = 0 := Nat.sub_eq_zero_of_le (le_of_lt hza)
  have hbz : b - z = 0 := Nat.sub_eq_zero_of_le (le_of_lt hzb)
  set K := m * 3 ^ (v - 2) with hK
  set M := m * 5 ^ b with hM
  set E := 2 ^ a * 5 ^ b * 3 ^ (v - 2) * m with hE
  have hE9 : n = 9 * E := by
    have hvdec : 3 ^ v = 9 * 3 ^ (v - 2) := by
      rw [show (9 : ℕ) = 3 ^ 2 from by norm_num, ← pow_add,
        show 2 + (v - 2) = v from by omega]
    rw [hn, hE, hvdec]
    ring
  have hM0 : 0 < M := by
    rw [hM]
    exact Nat.mul_pos (by omega) (pow_pos (by norm_num) _)
  have h4m : (4 : ℕ).Coprime m := hm2.symm.pow_left 2
  have h3vm : (3 ^ v).Coprime m := hm3.symm.pow_left v
  have h45b : (4 : ℕ).Coprime (5 ^ b) :=
    (by decide : Nat.Coprime 4 5).pow_right b
  have h3v5b : (3 ^ v).Coprime (5 ^ b) :=
    ((by decide : Nat.Coprime 3 5).pow_right b).pow_left v
  have hmo : Odd m := by
    have h2 : ¬ (2 : ℕ) ∣ m :=
      (Nat.prime_two.coprime_iff_not_dvd).mp hm2.symm
    rw [← Nat.not_even_iff_odd]
    rintro ⟨c', hc'⟩
    exact h2 ⟨c', by omega⟩
  have hModd : Odd M := by
    rw [hM]
    exact hmo.mul (Odd.pow (by decide : Odd 5))
  have hnd : ¬ (2 : ℕ) ∣ M := by
    rintro ⟨r, hr⟩
    obtain ⟨s, hs⟩ := hModd
    omega
  
  set t := 2 ^ (a - 2) - rhob 0 0 4 % 2 ^ (a - 2) with ht
  have ht2 : 2 ^ (a - 2) ∣ rhob 0 0 4 + t := by
    have hlt : rhob 0 0 4 % 2 ^ (a - 2) < 2 ^ (a - 2) :=
      Nat.mod_lt _ (by positivity)
    have hdm := Nat.div_add_mod (rhob 0 0 4) (2 ^ (a - 2))
    have hms : 2 ^ (a - 2) * (rhob 0 0 4 / 2 ^ (a - 2) + 1)
        = 2 ^ (a - 2) * (rhob 0 0 4 / 2 ^ (a - 2)) + 2 ^ (a - 2) :=
      Nat.mul_succ _ _
    refine ⟨rhob 0 0 4 / 2 ^ (a - 2) + 1, ?_⟩
    rw [ht]
    omega
  have htle : t ≤ 2 ^ (a - 2) := Nat.sub_le _ _
  
  have h18 : (18 * 3 ^ (v - 2)).Coprime M := by
    have e : 18 * 3 ^ (v - 2) = 2 * 3 ^ v := by
      rw [show (18 : ℕ) = 2 * 3 ^ 2 from by norm_num, mul_assoc, ← pow_add,
        show 2 + (v - 2) = v from by omega]
    rw [hM, e]
    have h2m : (2 * 3 ^ v).Coprime m := hm2.symm.mul_left h3vm
    have h25b : (2 * 3 ^ v).Coprime (5 ^ b) :=
      ((by decide : Nat.Coprime 2 5).pow_right b).mul_left h3v5b
    exact h2m.mul_right h25b
  have hcop2 : M.Coprime (2 ^ (a - 1)) :=
    ((Nat.prime_two.coprime_iff_not_dvd).mpr hnd).symm.pow_right _
  obtain ⟨c, hc1, hcle, hmc, hcdvd⟩ := sigma_cm_solve (v := v)
    (ρ' := rhob 0 0 4 + t) (m := m) (M := M) (a := a) hM0 ha h18 hcop2
  set j := c * 3 ^ (v - 2) with hj
  
  have hmin : a - z = 0 ∨ b - z = 0 := Or.inl haz
  obtain ⟨D, hDpal, hD10, hDne, hD0, hD25, hD81, hDσ, hr₀lt, hlenD⟩ :=
    border_pal (a' := a - z) (b' := b - z) (q := 4)
      (s₁ := max (a - z) (b - z)) (t := t)
      (by norm_num) hmin (le_refl _)
  rw [haz, hbz] at hDσ hr₀lt hlenD hD25
  set lenD := D.length with hlenD'
  have hd9 : Nat.digits 10 9 = [9] := by decide
  have hlenN : lenD = 2 * (1 + r0b 0 0 4) + 18 * t := by
    rw [hlenD]
    have hd : (9 : ℕ) * 2 ^ 0 * 5 ^ 0 = 9 := by norm_num
    rw [hd, hd9]
    norm_num
  
  have hne : Even n := by
    rw [hn]
    refine ⟨2 ^ (a - 1) * 5 ^ b * 3 ^ v * m, ?_⟩
    rw [show 2 ^ a = 2 * 2 ^ (a - 1) from by
      rw [← Nat.pow_succ', Nat.succ_eq_add_one, Nat.sub_add_cancel ha]]
    ring
  set S := 1 + 4 * K + 2 * j + 2 * lenD with hS
  have hSodd : Odd S := by
    have e1 : Even (4 * K) := ⟨2 * K, by ring⟩
    have e2 : Even (2 * j) := ⟨j, by ring⟩
    have e3 : Even (2 * lenD) := ⟨lenD, by ring⟩
    obtain ⟨w, hw⟩ := (e1.add e2).add e3
    use w
    rw [hS]
    omega
  have g7 : z ≤ E := by
    have hzz : z ≤ a + b + 2 := by rw [hz]; omega
    have h1a : a + 1 ≤ 2 ^ a := Nat.lt_two_pow_self
    have h54 : b + 4 ≤ 5 ^ b := by
      have h : ∀ k : ℕ, k + 5 ≤ 5 ^ (k + 1) := by
        intro k
        induction k with
        | zero => norm_num
        | succ k ih =>
            calc k + 1 + 5 ≤ 5 * (k + 5) := by omega
              _ ≤ 5 * 5 ^ (k + 1) := Nat.mul_le_mul_left 5 ih
              _ = 5 ^ (k + 1 + 1) := by ring
      have h2 := h (b - 1)
      rw [Nat.sub_add_cancel hb] at h2
      omega
    have hab2 : a + b + 2 ≤ (a + 1) * (b + 4) := by
      have e : (a + 1) * (b + 4) = a * b + 4 * a + b + 4 := by ring
      rw [e]
      have h0 : 0 ≤ a * b := Nat.zero_le _
      omega
    have h25ab : a + b + 2 ≤ 2 ^ a * 5 ^ b :=
      le_trans hab2 (Nat.mul_le_mul h1a h54)
    have hleE : 2 ^ a * 5 ^ b ≤ E := by
      rw [hE]
      have h1 : 0 < 3 ^ (v - 2) * m := by positivity
      calc 2 ^ a * 5 ^ b = 2 ^ a * 5 ^ b * 1 := by ring
        _ ≤ 2 ^ a * 5 ^ b * (3 ^ (v - 2) * m) :=
            Nat.mul_le_mul_left _ (by omega)
        _ = 2 ^ a * 5 ^ b * 3 ^ (v - 2) * m := by ring
    omega
  have hzlt : z < n := by
    rw [hE9]
    have hE1 : 0 < E := by rw [hE]; positivity
    omega
  have hno : Odd (n - z) := by
    obtain ⟨en, hen⟩ := hne
    obtain ⟨oz, hoz⟩ := hzodd
    refine ⟨en - oz - 1, ?_⟩
    rw [hoz, hen] at hzlt ⊢
    omega
  set X := (n - z) - S with hX
  have hXeven : Even X := by
    obtain ⟨an, han⟩ := hno
    obtain ⟨as, has⟩ := hSodd
    refine ⟨an - as, ?_⟩
    rw [hX, han, has]
    omega
  set T := X / 2 with hT
  
  have hbound : S + z ≤ n := by
    have g1 : 10 * (m * 3 ^ (v - 2)) ≤ E := by
      rw [hE]
      have h10 : 10 ≤ 2 ^ a * 5 ^ b := by
        calc 10 = 2 * 5 := by norm_num
          _ ≤ 2 ^ a * 5 ^ b :=
              Nat.mul_le_mul (Nat.pow_le_pow_right (n := 2) (by norm_num) ha)
                (Nat.pow_le_pow_right (n := 5) (by norm_num) hb)
      calc 10 * (m * 3 ^ (v - 2))
          ≤ (2 ^ a * 5 ^ b) * (m * 3 ^ (v - 2)) :=
            Nat.mul_le_mul_right _ h10
        _ = 2 ^ a * 5 ^ b * 3 ^ (v - 2) * m := by ring
    have g2 : 2 * j ≤ E := by
      rw [hj]
      have hc2 : 2 * c ≤ 2 ^ a * M := by
        calc 2 * c ≤ 2 * (2 ^ (a - 1) * M) := Nat.mul_le_mul_left 2 hcle
          _ = (2 * 2 ^ (a - 1)) * M := by ring
          _ = 2 ^ a * M := by
              rw [← Nat.pow_succ', Nat.succ_eq_add_one,
                Nat.sub_add_cancel ha]
      calc 2 * (c * 3 ^ (v - 2)) = (2 * c) * 3 ^ (v - 2) := by ring
        _ ≤ (2 ^ a * M) * 3 ^ (v - 2) := Nat.mul_le_mul_right _ hc2
        _ = E := by rw [hE, hM]; ring
    have g4 : 36 * t ≤ 2 * E :=
      le_trans (Nat.mul_le_mul_left 36 htle) hB2
    have hlen3 : 2 * lenD ≤ 2 * E + 36 := by
      rw [hlenN]
      have hr : r0b 0 0 4 ≤ 8 := by
        have h := hr₀lt
        norm_num at h
        omega
      calc 2 * (2 * (1 + r0b 0 0 4) + 18 * t)
          = 4 * (1 + r0b 0 0 4) + 36 * t := by ring
        _ ≤ 36 + 36 * t := by omega
        _ ≤ 36 + 2 * E := by omega
        _ = 2 * E + 36 := by ring
    have hE11 : 11 ≤ E := by
      have h1 : 1 ≤ 2 ^ (a - 2) := Nat.one_le_pow _ _ (by norm_num)
      omega
    rw [hS, hK, hE9]
    omega
  
  set C := List.replicate j 9 ++ List.replicate T 0 ++ [0]
      ++ List.replicate T 0 ++ List.replicate j 9 with hC
  have hCg : C.length = 2 * j + 2 * T + 1 := (center_repunit_len_sum j T).1
  have hCσ : C.sum = 18 * j := (center_repunit_len_sum j T).2
  have hCval3 : 3 ^ v ∣ Nat.ofDigits 10 C :=
    center_repunit_dvd3 hv2 ⟨c, by rw [hj]; ring⟩
  have hK1 : 1 ≤ K := by
    rw [hK]
    have : 0 < m * 3 ^ (v - 2) := by positivity
    omega
  have hde_pal : D.reverse = D := hDpal.reverse_eq
  have hde81 : 81 ∣ Nat.ofDigits 10 D := by
    have h : ((Nat.ofDigits 10 D : ℕ) : ZMod 81) = 0 := by
      rw [cast_ofDigits]
      exact hD81
    exact (CharP.cast_eq_zero_iff (ZMod 81) 81 _).mp h
  have he3 : 3 ^ v ∣ Nat.ofDigits 10 D := by
    have h : 3 ^ v ∣ (3 : ℕ) ^ 4 := pow_dvd_pow 3 hv4
    norm_num at h
    exact dvd_trans h hde81
  have he3r : 3 ^ v ∣ Nat.ofDigits 10 D.reverse := by
    rw [hde_pal]; exact he3
  have hC3 : 3 ^ v ∣ Nat.ofDigits 10 C := hCval3
  have hK3 : 3 ^ (v - 2) ∣ K := ⟨m, by rw [hK]; ring⟩
  have hj1 : 1 ≤ j := Nat.mul_pos hc1 (by positivity)
  have hg3 : 3 ≤ 2 * j + 2 * T + 1 := by omega
  have hgodd : Odd (2 * j + 2 * T + 1) := ⟨j + T, by ring⟩
  have hKcov : m * 3 ^ (v - 4) ≤ 1 + 9 * (K / 2) := by
    have hv4' : v - 4 = 0 := by omega
    rw [hv4', pow_zero, mul_one]
    have hKm : m ≤ K := by
      rw [hK]
      exact Nat.le_mul_of_pos_right _ (by positivity)
    have hdiv : m / 2 ≤ K / 2 := Nat.div_le_div_right hKm
    have h2m : m ≤ 2 * (m / 2) + 1 := by
      have := Nat.div_add_mod m 2
      omega
    omega
  obtain ⟨e', he', hdvdP⟩ := P_dvd_3m hm3 hm10 hv2 hK1 D rfl C hCg hg3
    hgodd hKcov hK3 he3 he3r hC3
  set MID := (List.range (2 * K)).map (pairDigit e') ++ C
      ++ ((List.range (2 * K)).map (pairDigit e')).reverse with hMID
  set P := Nat.ofDigits 10 (D ++ MID ++ D.reverse) with hP
  have hMIDpal : MID.Palindrome := mid_pal e' C (center_repunit_pal j T)
  have hMID10 : ∀ x ∈ MID, x < 10 := mid_lt10 e' he' C
    (center_repunit_lt10 j T)
  obtain ⟨hP0, hPpal, hPlen, hPσ⟩ := sandwich_spec_gen D MID hDne hD10
    (hD0 hDne) hMIDpal hMID10 rfl rfl
  have hMIDlen : MID.length = 4 * K + C.length := by
    rw [hMID, List.length_append, List.length_append, List.length_reverse,
      List.length_map, List.length_range]
    ring
  obtain ⟨rr, hrr⟩ := hXeven
  have h2T : 2 * T = X := by rw [hT]; omega
  have hlen : (Nat.digits 10 P).length = n - z := by
    rw [hPlen, hMIDlen, hCg]
    omega
  
  have hσP : (Nat.digits 10 P).sum
      = 4 * 81 * (rhob 0 0 4 + t) + 18 * (K + j) := by
    rw [hPσ, mid_sum e' he' C, hCσ, hDσ]
    ring
  have h2a : 2 ^ a ∣ (Nat.digits 10 P).sum := by
    rw [hσP]
    apply Nat.dvd_add
    · have h21 : 2 ^ a ∣ 4 * (rhob 0 0 4 + t) := by
        rcases Nat.lt_or_ge 2 a with h | h
        · obtain ⟨u, hu⟩ := ht2
          have hpa : 2 ^ a = 2 ^ (a - 2) * 4 := by
            rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, ← pow_add,
              show a - 2 + 2 = a from by omega]
          rw [hpa]
          exact ⟨u, by rw [hu]; ring⟩
        · exact dvd_mul_of_dvd_left
            (show 2 ^ a ∣ 4 from pow_dvd_pow 2 (by omega)) _
      have e1 : 4 * 81 * (rhob 0 0 4 + t)
          = 81 * (4 * (rhob 0 0 4 + t)) := by ring
      rw [e1]
      obtain ⟨w, hw⟩ := h21
      exact ⟨81 * w, by rw [hw]; ring⟩
    · have h22 : 2 ^ a ∣ 2 * (m + c) := by
        obtain ⟨u, hu⟩ := hmc
        have hpa : 2 ^ a = 2 ^ (a - 1) * 2 := by
          rw [← Nat.pow_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel ha]
        rw [hpa]
        exact ⟨u, by rw [hu]; ring⟩
      have e2 : 18 * (K + j) = (9 * 3 ^ (v - 2)) * (2 * (m + c)) := by
        rw [hK, hj, ← Nat.add_mul]
        ring
      rw [e2]
      exact dvd_mul_of_dvd_right h22 _
  have h3vd : 3 ^ v ∣ (Nat.digits 10 P).sum := by
    rw [hσP]
    apply Nat.dvd_add
    · have h81v : 3 ^ v ∣ 81 := by
        have h : 3 ^ v ∣ (3 : ℕ) ^ 4 := pow_dvd_pow 3 hv4
        norm_num at h
        exact h
      obtain ⟨w, hw⟩ := h81v
      exact ⟨4 * (rhob 0 0 4 + t) * w, by rw [hw]; ring⟩
    · refine ⟨2 * (m + c), ?_⟩
      rw [hK, hj, ← Nat.add_mul]
      rw [show (3 : ℕ) ^ v = 9 * 3 ^ (v - 2) from by
        rw [show (9 : ℕ) = 3 ^ 2 from by norm_num, ← pow_add,
          show 2 + (v - 2) = v from by omega]]
      ring
  have hMdvd : m * 5 ^ b ∣ (Nat.digits 10 P).sum := by
    have e : 18 * (K + j) = 18 * 3 ^ (v - 2) * (m + c) := by
      rw [hK, hj, ← Nat.add_mul]
      ring
    rw [hσP, e, ← hM]
    exact hcdvd
  have hσ : n ∣ (Nat.digits 10 P).sum := by
    have hcop2a : (2 ^ a).Coprime (3 ^ v) :=
      ((by decide : Nat.Coprime 2 3).pow_right v).pow_left a
    have hcopB : (2 ^ a * 3 ^ v).Coprime (m * 5 ^ b) := by
      apply Nat.Coprime.mul_right
      · exact Nat.Coprime.mul_left (hm2.symm.pow_left a) (hm3.symm.pow_left v)
      · exact Nat.Coprime.mul_left
          (((by decide : Nat.Coprime 2 5).pow_right b).pow_left a)
          (((by decide : Nat.Coprime 3 5).pow_right b).pow_left v)
    have hjoin1 := hcop2a.mul_dvd_of_dvd_of_dvd h2a h3vd
    have hjoin2 := hcopB.mul_dvd_of_dvd_of_dvd hjoin1 hMdvd
    rw [hn]
    rwa [show 2 ^ a * 5 ^ b * 3 ^ v * m = 2 ^ a * 3 ^ v * (m * 5 ^ b)
      from by ring]
  
  have hPd : n ∣ P * 10 ^ z := by
    have h25 : 2 ^ (a - z) * 5 ^ (b - z) ∣ P := by
      have hle_big : max 0 0 ≤ lenD := by simp
      have := B_dvd_P (le := lenD) (de := D) (MID := MID) rfl hD25 hle_big
      rwa [hP, haz, hbz]
    obtain ⟨w, hw⟩ := hdvdP
    have h3m : 3 ^ v * m ∣ P := ⟨w, by rw [hw]; ring⟩
    have := n_dvd_P_pow10_le (a := a) (b := b) (v := v) (m := m) (z := z)
      (a' := a - z) (b' := b - z) (P := P) h25 h3m
      (by rw [haz, Nat.zero_add]; exact le_of_lt hza)
      (by rw [hbz, Nat.zero_add]; exact le_of_lt hzb) hm30
    rwa [hn]
  refine ⟨P, z, hP0, ?_, hPpal, ?_, hPd, hσ⟩
  · intro _
    rw [hn]
    have h2a' : 2 ^ a = 2 * 2 ^ (a - 1) := by
      rw [← Nat.pow_succ', Nat.succ_eq_add_one, Nat.sub_add_cancel ha]
    have h5b' : 5 ^ b = 5 * 5 ^ (b - 1) := by
      rw [← Nat.pow_succ', Nat.succ_eq_add_one, Nat.sub_add_cancel hb]
    exact ⟨2 ^ (a - 1) * 5 ^ (b - 1) * 3 ^ v * m, by rw [h2a', h5b']; ring⟩
  · rw [hlen]
    exact Nat.sub_add_cancel (le_of_lt hzlt)

end A084017

namespace A084017
open Finset List Nat BigOperators Pointwise
set_option maxHeartbeats 800000 in
theorem border_pal_q {a' b' q s₁ t : ℕ} (hq2 : 2 ≤ q) (hq4 : q ≤ 4)
    (hmin : a' = 0 ∨ b' = 0) (hs₁ : max a' b' ≤ s₁) :
    ∃ D : List ℕ, D.Palindrome ∧ (∀ x ∈ D, x < 10) ∧ D ≠ []
      ∧ (∀ h : D ≠ [], D.head h ≠ 0)
      ∧ 2 ^ a' * 5 ^ b' ∣ Nat.ofDigits 10 D
      ∧ (3 ^ q ∣ Nat.ofDigits 10 D)
      ∧ (D.sum = 2 * 3 ^ q * (rhob a' b' q + t))
      ∧ (r0b a' b' q < 3 ^ (q - 2)
          ∧ D.length = 2 * ((Nat.digits 10 (9 * 2 ^ a' * 5 ^ b')).length
              + s₁ + r0b a' b' q) + 2 * 3 ^ (q - 2) * t) := by
  classical
  set V := 9 * 2 ^ a' * 5 ^ b' with hV
  have hV9 : 9 ∣ V := ⟨2 ^ a' * 5 ^ b', by rw [hV]; ring⟩
  have hVpos : 0 < V := by
    rw [hV]
    positivity
  have h9sdV : 9 ∣ (Nat.digits 10 V).sum := by
    have hmod := Nat.modEq_nine_digits_sum V
    have : (Nat.digits 10 V).sum % 9 = 0 := by
      have h' := hmod
      rw [Nat.ModEq] at h'
      rw [h'.symm]
      exact Nat.mod_eq_zero_of_dvd hV9
    exact Nat.dvd_of_mod_eq_zero this
  set sdV := (Nat.digits 10 V).sum / 9 with hsdV
  have hsdV9 : 9 * sdV = (Nat.digits 10 V).sum :=
    Nat.mul_div_cancel' h9sdV
  set p3 := 3 ^ (q - 2) with hp3
  have hp3pos : 0 < p3 := pow_pos (by norm_num) _
  set r₀ := (p3 - sdV % p3) % p3 with hr₀
  have hr₀lt : r₀ < p3 := Nat.mod_lt _ hp3pos
  set w' := r₀ + p3 * t with hw'
  set X := Nat.digits 10 V ++ List.replicate s₁ 0
      ++ List.replicate w' 9 with hX
  have hX10 : ∀ x ∈ X, x < 10 := by
    intro x hx
    rw [hX] at hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · exact Nat.digits_lt_base' (b := 8) hx
      · have := List.mem_replicate.mp hx
        omega
    · have := List.mem_replicate.mp hx
      omega
  have hXne : X ≠ [] := by
    rw [hX]
    intro h
    have h1 := (List.append_eq_nil_iff.mp
      (List.append_eq_nil_iff.mp h).1).1
    exact (Nat.digits_ne_nil_iff_ne_zero.mpr hVpos.ne') h1
  have hsigX : X.sum = 9 * (sdV + w') := by
    rw [hX, List.sum_append, List.sum_append, List.sum_replicate,
      List.sum_replicate, ← hsdV9]
    ring
  have hsdwr : (sdV + r₀) % p3 = 0 := by
    have hlt : sdV % p3 < p3 := Nat.mod_lt _ hp3pos
    by_cases hz : sdV % p3 = 0
    · have hr0z : r₀ = 0 := by
        rw [hr₀, hz, Nat.sub_zero, Nat.mod_self]
      rw [hr0z, Nat.add_zero]
      exact hz
    · apply Nat.mod_eq_zero_of_dvd
      refine ⟨sdV / p3 + 1, ?_⟩
      have hdm : p3 * (sdV / p3) + sdV % p3 = sdV := Nat.div_add_mod _ _
      have h1 : p3 - sdV % p3 < p3 := by omega
      have h2 : r₀ = p3 - sdV % p3 := by
        rw [hr₀]
        exact Nat.mod_eq_of_lt h1
      rw [h2, Nat.mul_succ]
      omega
  obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero hsdwr
  have hsigX3 : X.sum = 3 ^ q * (c + t) := by
    rw [hsigX]
    rw [show sdV + w' = p3 * c + p3 * t from by
      rw [hw', ← hc]; ring]
    rw [show (3 : ℕ) ^ q = 9 * 3 ^ (q - 2) from by
      rw [show (9 : ℕ) = 3 ^ 2 from by norm_num, ← pow_add,
        show 2 + (q - 2) = q from by omega]]
    rw [← hp3]
    ring
  set D := X ++ X.reverse with hD
  have hDpal : D.Palindrome := hD.symm ▸ List.Palindrome.append_reverse X
  have hD10 : ∀ x ∈ D, x < 10 := by
    intro x hx
    rcases List.mem_append.mp (hD ▸ hx) with hx | hx
    · exact hX10 x hx
    · exact hX10 x (List.mem_reverse.mp hx)
  have hDne : D ≠ [] := by
    rw [hD]
    intro h
    have := List.append_eq_nil_iff.mp h
    exact hXne this.1
  have hV10 : V % 10 ≠ 0 := by
    intro h0
    have h10d : 10 ∣ V := Nat.dvd_of_mod_eq_zero h0
    rcases hmin with rfl | rfl
    · rw [hV, pow_zero, mul_one] at h10d
      have h2 : 2 ∣ 9 * 5 ^ b' := dvd_trans (by norm_num : 2 ∣ 10) h10d
      have hmod : (9 * 5 ^ b') ≡ 1 [MOD 2] := by
        have h5 : (5 : ℕ) ≡ 1 [MOD 2] := by decide
        have := Nat.ModEq.mul (by decide : (9 : ℕ) ≡ 1 [MOD 2])
          (Nat.ModEq.pow b' h5)
        simpa using this
      rw [Nat.ModEq] at hmod
      rw [Nat.mod_eq_zero_of_dvd h2] at hmod
      norm_num at hmod
    · rw [hV, pow_zero, mul_one] at h10d
      have h5 : 5 ∣ 9 * 2 ^ a' := dvd_trans (by norm_num : 5 ∣ 10) h10d
      have hcop : (5 : ℕ).Coprime (2 ^ a') :=
        (Nat.coprime_comm.mp (by decide : Nat.Coprime 2 5)).pow_right _
      have h9 : 5 ∣ 9 := hcop.dvd_of_dvd_mul_right h5
      norm_num at h9
  have hVhead : (Nat.digits 10 V).head? = some (V % 10) := by
    rw [Nat.digits_def' (by norm_num) hVpos]
    rfl
  have hXhead : X.head? = some (V % 10) := by
    rw [hX, List.head?_append, List.head?_append, hVhead]
    simp
  have hD0 : ∀ h : D ≠ [], D.head h ≠ 0 := by
    intro h
    have e3 : D.head? = some (V % 10) := by
      rw [hD, List.head?_append, hXhead]
      simp
    have e4 : D.head? = some (D.head h) := List.head?_eq_some_head h
    rw [e3] at e4
    have hh : D.head h = V % 10 := Option.some.inj e4.symm
    rw [hh]
    exact hV10
  have hofDX : Nat.ofDigits 10 X
      = V + 10 ^ ((Nat.digits 10 V).length + s₁) * (10 ^ w' - 1) := by
    rw [hX, ofDigits_append', ofDigits_append', ofDigits_replicate_zero,
      ofDigits_rep9, Nat.ofDigits_digits]
    rw [List.length_append, List.length_replicate]
    ring
  have hofDX_dvd : 2 ^ a' * 5 ^ b' ∣ Nat.ofDigits 10 X := by
    rw [hofDX]
    apply Nat.dvd_add
    · rw [hV]
      exact ⟨9, by ring⟩
    · apply dvd_mul_of_dvd_left
      apply pow25_dvd_pow10
      omega
  have hofDD : Nat.ofDigits 10 D
      = Nat.ofDigits 10 X + 10 ^ X.length
          * Nat.ofDigits 10 X.reverse := by
    rw [hD]
    rw [ofDigits_append']
  have hXl : X.length = (Nat.digits 10 V).length + s₁ + w' := by
    rw [hX, List.length_append, List.length_append,
      List.length_replicate, List.length_replicate]
  refine ⟨D, hDpal, hD10, hDne, hD0, ?_, ?_, ?_, ?_⟩
  · rw [hofDD]
    apply Nat.dvd_add hofDX_dvd
    apply dvd_mul_of_dvd_left
    apply pow25_dvd_pow10
    omega
  · rw [hD]
    apply dvd3_pow_of_sigma_even X hq4
    rw [hsigX3]
    exact ⟨2 * (c + t), by ring⟩
  · have hceq : rhob a' b' q = c := by
      show ((Nat.digits 10 (9 * 2 ^ a' * 5 ^ b')).sum / 9 + r0b a' b' q)
          / 3 ^ (q - 2) = c
      rw [← hV]
      show (sdV + r₀) / p3 = c
      conv_lhs => rw [hc, mul_comm p3 c]
      exact Nat.mul_div_cancel _ hp3pos
    rw [hceq, hD, List.sum_append, List.sum_reverse, hsigX3]
    ring
  · refine ⟨?_, ?_⟩
    · show r0b a' b' q < 3 ^ (q - 2)
      exact hr₀lt
    · show D.length = 2 * ((Nat.digits 10 V).length + s₁ + r₀) + 2 * p3 * t
      rw [hD, List.length_append, List.length_reverse, hXl, hw']
      ring


set_option maxHeartbeats 800000 in
theorem assemble_eb04 {a v m : ℕ} (ha : 1 ≤ a)
    (hm0 : 1 ≤ m) (hv2 : 2 ≤ v) (hv4 : v ≤ 4) (hm30 : m.Coprime 30)
    (hm11 : m.Coprime 11) (hm101 : m.Coprime 101)
    (hB : 4 * a + 6 ≤ 2 ^ a * 3 ^ (v - 2) * m) :
    ∃ P z : ℕ, P ≠ 0
      ∧ (0 < z → 10 ∣ 2 ^ a * 3 ^ v * m)
      ∧ (Nat.digits 10 P).Palindrome
      ∧ (Nat.digits 10 P).length + z = 2 ^ a * 3 ^ v * m
      ∧ 2 ^ a * 3 ^ v * m ∣ P * 10 ^ z
      ∧ 2 ^ a * 3 ^ v * m ∣ (Nat.digits 10 P).sum := by
  classical
  set z := min a 0 with hz
  have hzae : z = 0 := Nat.min_zero a
  set n := 2 ^ a * 3 ^ v * m with hn
  haveI : NeZero m := ⟨by omega⟩
  have hm3 : m.Coprime 3 := hm30.coprime_dvd_right (by norm_num)
  have hm10 : m.Coprime 10 := hm30.coprime_dvd_right (by norm_num)
  have hm2 : m.Coprime 2 := hm30.coprime_dvd_right (by norm_num)
  have hza : z ≤ a := Nat.min_le_left a 0
  
  set p2 := 2 ^ (a - 1) with hp2
  have hp2pos : 0 < p2 := pow_pos (by norm_num) _
  set c := p2 - m % p2 with hc
  have hmc : p2 ∣ m + c := by
    have hlt : m % p2 < p2 := Nat.mod_lt _ hp2pos
    have h2 := Nat.div_add_mod m p2
    have h3 : p2 * (m / p2 + 1) = p2 * (m / p2) + p2 := Nat.mul_succ _ _
    refine ⟨m / p2 + 1, ?_⟩
    rw [hc]
    omega
  have hcle : c ≤ p2 := Nat.sub_le _ _
  have hc1 : 1 ≤ c := by
    have hlt : m % p2 < p2 := Nat.mod_lt _ hp2pos
    rw [hc]
    omega
  
  set K := m * 3 ^ (v - 2) with hK
  set j := c * 3 ^ (v - 2) with hj
  set M := m with hM
  have hM0 : 0 < M := by
    rw [hM]
    exact Nat.pos_of_ne_zero (NeZero.ne m)
  have h4m : (4 : ℕ).Coprime m := hm2.symm.pow_left 2
  have h3vm : (3 ^ v).Coprime m := hm3.symm.pow_left v
  have hcop43 : (4 * 3 ^ v).Coprime M := by
    rw [hM]
    exact h4m.mul_left h3vm
  
  have hmo : Odd m := by
    have h2 : ¬ (2 : ℕ) ∣ m :=
      (Nat.prime_two.coprime_iff_not_dvd).mp hm2.symm
    rw [← Nat.not_even_iff_odd]
    rintro ⟨c', hc'⟩
    exact h2 ⟨c', by omega⟩
  have hModd : Odd M := by
    rw [hM]
    exact hmo
  have hnd : ¬ (2 : ℕ) ∣ M := by
    rintro ⟨r, hr⟩
    obtain ⟨s, hs⟩ := hModd
    omega
  have hcop2 : M.Coprime (2 ^ (a - 2)) :=
    ((Nat.prime_two.coprime_iff_not_dvd).mpr hnd).symm.pow_right _
  
  obtain ⟨t, htlt, ht2, htdvd⟩ := sigma_t_solve2 (v := v)
    (ρ := rhob a 0 v) (S := K + j) (M := M) (w := a - 2)
    hM0 hcop43 hcop2
  
  have hmin : a = 0 ∨ (0 : ℕ) = 0 := Or.inr rfl
  obtain ⟨D, hDpal, hD10, hDne, hD0, hD25, hD3v, hDσ, hr₀lt, hlenD⟩ :=
    border_pal_q (a' := a) (b' := 0) (q := v)
      (s₁ := a) (t := t)
      hv2 hv4 hmin (le_of_eq (Nat.max_eq_left (Nat.zero_le a)))
  set lenD := D.length with hlenD'
  have hlenN : lenD
      = 2 * ((Nat.digits 10 (9 * 2 ^ a)).length + a + r0b a 0 v)
        + 2 * (3 ^ (v - 2) * t) := by
    rw [hlenD]
    ring
  
  have lenV_le : (Nat.digits 10 (9 * 2 ^ a)).length ≤ a + 2 := by
    have hVpos : (9 * 2 ^ a : ℕ) ≠ 0 := by positivity
    have hb2 := Nat.base_pow_length_digits_le 10 (9 * 2 ^ a) (by norm_num) hVpos
    have hlt : 10 * (9 * 2 ^ a) < 10 ^ (a + 2) := by
      have h1 : (2 : ℕ) ^ a ≤ 10 ^ a := Nat.pow_le_pow_left (by norm_num) _
      calc 10 * (9 * 2 ^ a) = 90 * 2 ^ a := by ring
        _ ≤ 90 * 10 ^ a := Nat.mul_le_mul_left 90 h1
        _ < 100 * 10 ^ a := by omega
        _ = 10 ^ (a + 2) := by ring
    have hpow : 10 ^ ((Nat.digits 10 (9 * 2 ^ a)).length) < 10 ^ (a + 2) :=
      lt_of_le_of_lt hb2 hlt
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 10)).mp hpow
    omega
  have hne : Even n := by
    rw [hn]
    refine ⟨2 ^ (a - 1) * 3 ^ v * m, ?_⟩
    rw [show 2 ^ a = 2 * 2 ^ (a - 1) from by
      rw [← pow_succ', Nat.succ_eq_add_one, Nat.sub_add_cancel ha]]
    ring
  have hzlt : z < n := by
    have ha2 : a < 2 ^ a := Nat.lt_two_pow_self
    have h2n : 2 ^ a ≤ n := by
      rw [hn]
      calc 2 ^ a ≤ 2 ^ a * 3 ^ v :=
            Nat.le_mul_of_pos_right _ (by positivity)
        _ ≤ 2 ^ a * 3 ^ v * m :=
            Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hne2 : Even (n - z) := by
    rw [hzae, Nat.sub_zero]
    exact hne
  set S := 4 * K + 2 * j + 2 * lenD with hS
  have hSeven : Even S := by
    refine ⟨2 * K + j + lenD, ?_⟩
    rw [hS]
    ring
  set X := (n - z) - S with hX
  have hXeven : Even X := by
    obtain ⟨an, han⟩ := hne2
    obtain ⟨as, has⟩ := hSeven
    refine ⟨an - as, ?_⟩
    rw [hX, han, has]
    omega
  set T := X / 2 with hT
  
  have hbound : S + 4 ≤ n := by
    set E := 2 ^ a * 3 ^ (v - 2) * m with hE
    have hvdec : 3 ^ v = 9 * 3 ^ (v - 2) := by
      rw [show (9 : ℕ) = 3 ^ 2 from by norm_num, ← pow_add,
        show 2 + (v - 2) = v from by omega]
    have hE9 : n = 9 * E := by
      rw [hn, hE, hvdec]
      ring
    have g1 : 4 * (m * 3 ^ (v - 2)) ≤ 2 * E := by
      have h2a1 : 4 ≤ 2 * 2 ^ a := by
        have h : (2 : ℕ) ^ 1 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
        norm_num at h ⊢; omega
      calc 4 * (m * 3 ^ (v - 2))
          ≤ (2 * 2 ^ a) * (m * 3 ^ (v - 2)) := Nat.mul_le_mul_right _ h2a1
        _ = 2 * (2 ^ a * 3 ^ (v - 2) * m) := by ring
        _ = 2 * E := by rw [hE]
    have g2 : 2 * (c * 3 ^ (v - 2)) ≤ E := by
      have hc2 : 2 * c ≤ 2 ^ a := by
        calc 2 * c ≤ 2 * 2 ^ (a - 1) :=
              Nat.mul_le_mul_left 2 hcle
          _ = 2 ^ a := by
              rw [← pow_succ', Nat.succ_eq_add_one, Nat.sub_add_cancel ha]
      calc 2 * (c * 3 ^ (v - 2)) = (2 * c) * 3 ^ (v - 2) := by ring
        _ ≤ 2 ^ a * 3 ^ (v - 2) := Nat.mul_le_mul_right _ hc2
        _ ≤ E := by
            rw [hE]
            calc 2 ^ a * 3 ^ (v - 2)
                ≤ (2 ^ a * 3 ^ (v - 2)) * m :=
                  Nat.le_mul_of_pos_right _ (by omega)
              _ = 2 ^ a * 3 ^ (v - 2) * m := by ring
    have h4pow : 4 * 2 ^ (a - 2) ≤ 2 * 2 ^ a := by
      rcases Nat.lt_or_ge a 2 with hlt | hge
      · have e1 : a = 1 := by omega
        rw [e1]; norm_num
      · have e3 : 2 ^ a = 4 * 2 ^ (a - 2) := by
          conv_lhs => rw [← Nat.sub_add_cancel hge]
          rw [pow_add]
          ring
        rw [e3]
        exact Nat.le_mul_of_pos_left _ (by norm_num)
    have g4 : 4 * (3 ^ (v - 2) * t) + 4 * 3 ^ (v - 2) ≤ 2 * E := by
      have ht1 : t + 1 ≤ M * 2 ^ (a - 2) := htlt
      calc 4 * (3 ^ (v - 2) * t) + 4 * 3 ^ (v - 2)
          = 4 * 3 ^ (v - 2) * (t + 1) := by ring
        _ ≤ 4 * 3 ^ (v - 2) * (M * 2 ^ (a - 2)) :=
            Nat.mul_le_mul_left _ ht1
        _ = (4 * 2 ^ (a - 2)) * (3 ^ (v - 2) * M) := by ring
        _ ≤ (2 * 2 ^ a) * (3 ^ (v - 2) * M) :=
            Nat.mul_le_mul_right _ h4pow
        _ = 2 * E := by rw [hE, hM]; ring
    have g5 : 8 * a + 16 ≤ 4 * E := by
      omega
    have hlen3 : 2 * lenD
        ≤ 8 * a + 4 * (3 ^ (v - 2) * t) + 4 * 3 ^ (v - 2) + 12 := by
      rw [hlenN]
      have hlv := lenV_le
      omega
    rw [hS, hK, hj]
    omega
  
  set C := List.replicate j 9 ++ List.replicate T 0
      ++ List.replicate T 0 ++ List.replicate j 9 with hC
  have hCg : C.length = 2 * j + 2 * T := (center_repunit_even_len_sum j T).1
  have hCσ : C.sum = 18 * j := (center_repunit_even_len_sum j T).2
  have hCval3 : 3 ^ v ∣ Nat.ofDigits 10 C :=
    center_repunit_even_dvd3 hv2 ⟨c, by rw [hj]; ring⟩
  have hK1 : 1 ≤ K := by
    rw [hK]
    have : 0 < m * 3 ^ (v - 2) := by positivity
    omega
  have hde_pal : D.reverse = D := hDpal.reverse_eq
  have hKv : 3 ^ (v - 2) ∣ K := by
    rw [hK]
    exact dvd_mul_of_dvd_right (dvd_refl _) m
  obtain ⟨s₀, hs0⟩ := hs0_v4 hv2 hv4 hK1 D hde_pal hD3v C hCval3 hKv
  have hj1 : 1 ≤ j := by
    rw [hj]
    exact Nat.mul_pos hc1 (by positivity)
  have hg3 : 3 ≤ 2 * j + 2 * T := by
    have hX4 : 4 ≤ X := by
      rw [hX, hzae, Nat.sub_zero]
      omega
    rw [hT]
    omega
  have hgev : Even (2 * j + 2 * T) := ⟨j + T, by ring⟩
  have hKcov : m * 3 ^ (v - 4) ≤ 1 + 9 * (K / 2) := by
    have hv40 : v - 4 = 0 := by omega
    rw [hv40, pow_zero, mul_one]
    have hmK : m ≤ K := by
      rw [hK]
      exact Nat.le_mul_of_pos_right _ (by positivity)
    have hKK : K ≤ 1 + 9 * (K / 2) := by
      have h := Nat.div_add_mod K 2
      omega
    omega
  obtain ⟨e', he', hdvdP⟩ := P_dvd_3m81_even hm3 hm10 hm11 hm101 D rfl C hCg hg3 hgev
    hKcov s₀ hs0
  set MID := (List.range (2 * K)).map (pairDigit e') ++ C
      ++ ((List.range (2 * K)).map (pairDigit e')).reverse with hMID
  set P := Nat.ofDigits 10 (D ++ MID ++ D.reverse) with hP
  have hMIDpal : MID.Palindrome := mid_pal e' C (center_repunit_even_pal j T)
  have hMID10 : ∀ x ∈ MID, x < 10 := mid_lt10 e' he' C
    (center_repunit_even_lt10 j T)
  obtain ⟨hP0, hPpal, hPlen, hPσ⟩ := sandwich_spec_gen D MID hDne hD10
    (hD0 hDne) hMIDpal hMID10 rfl rfl
  have hMIDlen : MID.length = 4 * K + C.length := by
    rw [hMID, List.length_append, List.length_append, List.length_reverse,
      List.length_map, List.length_range]
    ring
  obtain ⟨rr, hrr⟩ := hXeven
  have h2T : 2 * T = X := by rw [hT]; omega
  have hlen : (Nat.digits 10 P).length = n - z := by
    rw [hPlen, hMIDlen, hCg]
    omega
  
  have hσP : (Nat.digits 10 P).sum
      = 4 * 3 ^ v * (rhob a 0 v + t) + 18 * (K + j) := by
    rw [hPσ, mid_sum e' he' C, hCσ, hDσ]
    ring
  have h2a : 2 ^ a ∣ (Nat.digits 10 P).sum := by
    rw [hσP]
    apply Nat.dvd_add
    · have h21 : 2 ^ a ∣ 4 * (rhob a 0 v + t) := by
        rcases Nat.lt_or_ge 2 a with h | h
        · obtain ⟨u, hu⟩ := ht2
          have hpa : 2 ^ a = 2 ^ (a - 2) * 4 := by
            rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, ← pow_add,
              show a - 2 + 2 = a from by omega]
          rw [hpa]
          exact ⟨u, by rw [hu]; ring⟩
        · exact dvd_mul_of_dvd_left (show 2 ^ a ∣ 4 from pow_dvd_pow 2 (by omega)) _
      have e1 : 4 * 3 ^ v * (rhob a 0 v + t)
          = 3 ^ v * (4 * (rhob a 0 v + t)) := by ring
      rw [e1]
      exact dvd_mul_of_dvd_right h21 _
    · have h22 : 2 ^ a ∣ 2 * (m + c) := by
        obtain ⟨u, hu⟩ := hmc
        have hpa : 2 ^ a = 2 ^ (a - 1) * 2 := by
          rw [← pow_succ, Nat.sub_add_cancel ha]
        rw [hpa]
        exact ⟨u, by rw [hu]; ring⟩
      have e2 : 18 * (K + j) = (9 * 3 ^ (v - 2)) * (2 * (m + c)) := by
        rw [hK, hj, ← Nat.add_mul]
        ring
      rw [e2]
      exact dvd_mul_of_dvd_right h22 _
  have h3vd : 3 ^ v ∣ (Nat.digits 10 P).sum := by
    rw [hσP]
    apply Nat.dvd_add
    · exact ⟨4 * (rhob a 0 v + t), by ring⟩
    · refine ⟨2 * (m + c), ?_⟩
      rw [hK, hj, ← Nat.add_mul]
      rw [show (3 : ℕ) ^ v = 9 * 3 ^ (v - 2) from by
        rw [show (9 : ℕ) = 3 ^ 2 from by norm_num, ← pow_add,
          show 2 + (v - 2) = v from by omega]]
      ring
  have hMdvd : m ∣ (Nat.digits 10 P).sum := by
    rw [hσP, ← hM]
    exact htdvd
  have hσ : n ∣ (Nat.digits 10 P).sum := by
    have hcop2a : (2 ^ a).Coprime (3 ^ v) :=
      ((by decide : Nat.Coprime 2 3).pow_right v).pow_left a
    have hcopB : (2 ^ a * 3 ^ v).Coprime m :=
      Nat.Coprime.mul_left (hm2.symm.pow_left a) (hm3.symm.pow_left v)
    have hjoin1 := hcop2a.mul_dvd_of_dvd_of_dvd h2a h3vd
    have hjoin2 := hcopB.mul_dvd_of_dvd_of_dvd hjoin1 hMdvd
    rw [hn]
    rwa [show 2 ^ a * 3 ^ v * m = 2 ^ a * 3 ^ v * m from rfl]
  
  have hPd : n ∣ P * 10 ^ z := by
    have h25 : 2 ^ a * 5 ^ 0 ∣ P := by
      have hle_big : max a 0 ≤ lenD := by
        rw [hlenN]
        omega
      have := B_dvd_P (le := lenD) (de := D) (MID := MID) rfl hD25 hle_big
      rwa [hP]
    obtain ⟨w, hw⟩ := hdvdP
    have h3m : 3 ^ v * m ∣ P := ⟨w, by rw [hw]; ring⟩
    have := n_dvd_P_pow10_le (a := a) (b := 0) (v := v) (m := m) (z := 0)
      (a' := a) (b' := 0) (P := P) h25 h3m
      (by omega) (by omega) hm30
    rw [hzae]
    convert this using 2 <;> ring
  refine ⟨P, z, hP0, ?_, hPpal, ?_, hPd, hσ⟩
  · intro hz'
    omega
  · rw [hlen, hzae]
    omega


end A084017
namespace A084017
open Finset List Nat BigOperators Pointwise

set_option maxHeartbeats 800000 in
theorem ofDigits_dvd_of_mem {b k : ℕ} : ∀ (L : List ℕ),
    (∀ d ∈ L, k ∣ d) → k ∣ Nat.ofDigits b L := by
  intro L hL
  induction L with
  | nil => exact dvd_zero _
  | cons d t ih =>
      rw [Nat.ofDigits_cons]
      exact Nat.dvd_add (hL d (by simp))
        (dvd_mul_of_dvd_right (ih (fun x hx => hL x (by simp [hx]))) b)


set_option maxHeartbeats 800000 in
theorem hs0_v1 {le K g : ℕ}
    (de : List ℕ) (hde_pal : de.reverse = de)
    (hde3 : 3 ∣ Nat.ofDigits 10 de)
    (C : List ℕ) (hC3 : 3 ∣ Nat.ofDigits 10 C) :
    ∃ s₀ : ℕ,
      (Nat.ofDigits (10 : ZMod (3 ^ 1)) de
          + Nat.ofDigits (10 : ZMod (3 ^ 1)) de.reverse
              * (10 : ZMod (3 ^ 1)) ^ (le + (4 * K + g)))
        + (10 : ZMod (3 ^ 1)) ^ le
          * (Nat.ofDigits (10 : ZMod (3 ^ 1)) C
              * (10 : ZMod (3 ^ 1)) ^ (2 * K)
            + (9 * ∑ k ∈ Finset.range K, palW (3 ^ 1) (4 * K + g) (2 * k + 1)
              + 81 * (s₀ : ZMod (3 ^ 1)))) = 0 := by
  refine ⟨0, ?_⟩
  have hde0 : Nat.ofDigits (10 : ZMod 3) de = 0 := by
    rw [← cast_ofDigits]
    exact (CharP.cast_eq_zero_iff (ZMod 3) 3 _).mpr hde3
  have hde0' : Nat.ofDigits (10 : ZMod 3) de.reverse = 0 := by
    rw [hde_pal]; exact hde0
  have hC0 : Nat.ofDigits (10 : ZMod 3) C = 0 := by
    rw [← cast_ofDigits]
    exact (CharP.cast_eq_zero_iff (ZMod 3) 3 _).mpr hC3
  have h9 : (9 : ZMod 3) = 0 := by decide
  have h81 : (81 : ZMod 3) = 0 := by decide
  rw [pow_one]
  simp only [Nat.cast_zero]
  rw [hde0, hde0', hC0, h9, h81]
  simp


set_option maxHeartbeats 800000 in
theorem assemble_zbig1 {a b m : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hm0 : 1 ≤ m) (hm30 : m.Coprime 30)
    (hB : 4 * m + 39 + 36 * 2 ^ (a - 2) + (a + b)
        ≤ 2 * (2 ^ a * 5 ^ b * m)) :
    ∃ P z : ℕ, P ≠ 0
      ∧ (0 < z → 10 ∣ 2 ^ a * 5 ^ b * 3 * m)
      ∧ (Nat.digits 10 P).Palindrome
      ∧ (Nat.digits 10 P).length + z = 2 ^ a * 5 ^ b * 3 * m
      ∧ 2 ^ a * 5 ^ b * 3 * m ∣ P * 10 ^ z
      ∧ 2 ^ a * 5 ^ b * 3 * m ∣ (Nat.digits 10 P).sum := by
  classical
  set z := a + b + 1 + (a + b) % 2 with hz
  set n := 2 ^ a * 5 ^ b * 3 * m with hn
  haveI : NeZero m := ⟨by omega⟩
  have hm3 : m.Coprime 3 := hm30.coprime_dvd_right (by norm_num)
  have hm10 : m.Coprime 10 := hm30.coprime_dvd_right (by norm_num)
  have hm2 : m.Coprime 2 := hm30.coprime_dvd_right (by norm_num)
  have hza : a < z := by rw [hz]; omega
  have hzb : b < z := by rw [hz]; omega
  have hzodd : Odd z := by
    refine ⟨(a + b) / 2 + (a + b) % 2, ?_⟩
    rw [hz]
    omega
  have hz0 : 0 < z := by rw [hz]; omega
  have haz : a - z = 0 := Nat.sub_eq_zero_of_le (le_of_lt hza)
  have hbz : b - z = 0 := Nat.sub_eq_zero_of_le (le_of_lt hzb)
  set K := m with hK
  set M := m * 5 ^ b with hM
  set E := 2 ^ a * 5 ^ b * m with hE
  have hE3 : n = 3 * E := by rw [hn, hE]; ring
  have hM0 : 0 < M := by
    rw [hM]
    exact Nat.mul_pos (by omega) (pow_pos (by norm_num) _)
  have h3m : (3 : ℕ).Coprime m := hm3.symm
  have hmo : Odd m := by
    have h2 : ¬ (2 : ℕ) ∣ m :=
      (Nat.prime_two.coprime_iff_not_dvd).mp hm2.symm
    rw [← Nat.not_even_iff_odd]
    rintro ⟨c', hc'⟩
    exact h2 ⟨c', by omega⟩
  have hModd : Odd M := by
    rw [hM]
    exact hmo.mul (Odd.pow (by decide : Odd 5))
  have hnd : ¬ (2 : ℕ) ∣ M := by
    rintro ⟨r, hr⟩
    obtain ⟨s, hs⟩ := hModd
    omega
  
  set t := 2 ^ (a - 2) - rhob 0 0 4 % 2 ^ (a - 2) with ht
  have ht2 : 2 ^ (a - 2) ∣ rhob 0 0 4 + t := by
    have hlt : rhob 0 0 4 % 2 ^ (a - 2) < 2 ^ (a - 2) :=
      Nat.mod_lt _ (by positivity)
    have hdm := Nat.div_add_mod (rhob 0 0 4) (2 ^ (a - 2))
    have hms : 2 ^ (a - 2) * (rhob 0 0 4 / 2 ^ (a - 2) + 1)
        = 2 ^ (a - 2) * (rhob 0 0 4 / 2 ^ (a - 2)) + 2 ^ (a - 2) :=
      Nat.mul_succ _ _
    refine ⟨rhob 0 0 4 / 2 ^ (a - 2) + 1, ?_⟩
    rw [ht]
    omega
  have htle : t ≤ 2 ^ (a - 2) := Nat.sub_le _ _
  
  have h18 : (18 * 3 ^ (1 - 2)).Coprime M := by
    show (18 : ℕ).Coprime M
    have h18' : (18 : ℕ) = 2 * 3 ^ 2 := by norm_num
    rw [h18', hM]
    have h2m : (2 * 3 ^ 2).Coprime m :=
      hm2.symm.mul_left (hm3.symm.pow_left 2)
    have h25b : (2 * 3 ^ 2).Coprime (5 ^ b) := by
      apply Nat.Coprime.mul_left
      · exact ((by decide : Nat.Coprime 2 5).pow_right b)
      · exact ((by decide : Nat.Coprime 3 5).pow_right b).pow_left 2
    exact h2m.mul_right h25b
  have hcop2 : M.Coprime (2 ^ (a - 1)) :=
    ((Nat.prime_two.coprime_iff_not_dvd).mpr hnd).symm.pow_right _
  obtain ⟨c, hc1, hcle, hmc, hcdvd⟩ := sigma_cm_solve (v := 1)
    (ρ' := rhob 0 0 4 + t) (m := m) (M := M) (a := a) hM0 ha h18 hcop2
  have hcdvd' : M ∣ 4 * 81 * (rhob 0 0 4 + t) + 18 * (m + c) := by
    have e : 18 * 3 ^ (1 - 2) = 18 := by norm_num
    rw [e] at hcdvd
    exact hcdvd
  set j := c with hj
  
  have hmin : a - z = 0 ∨ b - z = 0 := Or.inl haz
  obtain ⟨D, hDpal, hD10, hDne, hD0, hD25, hD81, hDσ, hr₀lt, hlenD⟩ :=
    border_pal (a' := a - z) (b' := b - z) (q := 4)
      (s₁ := max (a - z) (b - z)) (t := t)
      (by norm_num) hmin (le_refl _)
  rw [haz, hbz] at hDσ hr₀lt hlenD hD25
  set lenD := D.length with hlenD'
  have hd9 : Nat.digits 10 9 = [9] := by decide
  have hlenN : lenD = 2 * (1 + r0b 0 0 4) + 18 * t := by
    rw [hlenD]
    have hd : (9 : ℕ) * 2 ^ 0 * 5 ^ 0 = 9 := by norm_num
    rw [hd, hd9]
    norm_num
  
  have hne : Even n := by
    rw [hn]
    refine ⟨2 ^ (a - 1) * 5 ^ b * 3 * m, ?_⟩
    rw [show 2 ^ a = 2 * 2 ^ (a - 1) from by
      rw [← Nat.pow_succ', Nat.succ_eq_add_one, Nat.sub_add_cancel ha]]
    ring
  set S := 1 + 4 * K + 2 * j + 2 * lenD with hS
  have hSodd : Odd S := by
    have e1 : Even (4 * K) := ⟨2 * K, by ring⟩
    have e2 : Even (2 * j) := ⟨j, by ring⟩
    have e3 : Even (2 * lenD) := ⟨lenD, by ring⟩
    obtain ⟨w, hw⟩ := (e1.add e2).add e3
    use w
    rw [hS]
    omega
  have g7 : z ≤ 2 ^ a * 5 ^ b := by
    have hzz : z ≤ a + b + 2 := by rw [hz]; omega
    have h1a : a + 1 ≤ 2 ^ a := Nat.lt_two_pow_self
    have h54 : b + 4 ≤ 5 ^ b := by
      have h : ∀ k : ℕ, k + 5 ≤ 5 ^ (k + 1) := by
        intro k
        induction k with
        | zero => norm_num
        | succ k ih =>
            calc k + 1 + 5 ≤ 5 * (k + 5) := by omega
              _ ≤ 5 * 5 ^ (k + 1) := Nat.mul_le_mul_left 5 ih
              _ = 5 ^ (k + 1 + 1) := by ring
      have h2 := h (b - 1)
      rw [Nat.sub_add_cancel hb] at h2
      omega
    have hab2 : a + b + 2 ≤ (a + 1) * (b + 4) := by
      have e : (a + 1) * (b + 4) = a * b + 4 * a + b + 4 := by ring
      rw [e]
      have h0 : 0 ≤ a * b := Nat.zero_le _
      omega
    exact le_trans hzz (le_trans hab2 (Nat.mul_le_mul h1a h54))
  have hzlt : z < n := by
    rw [hE3]
    have hE1 : 0 < E := by rw [hE]; positivity
    have hze : z ≤ E := le_trans g7
      (by rw [hE]; exact Nat.le_mul_of_pos_right _ hm0)
    omega
  have hno : Odd (n - z) := by
    obtain ⟨en, hen⟩ := hne
    obtain ⟨oz, hoz⟩ := hzodd
    refine ⟨en - oz - 1, ?_⟩
    rw [hoz, hen] at hzlt ⊢
    omega
  set X := (n - z) - S with hX
  have hXeven : Even X := by
    obtain ⟨an, han⟩ := hno
    obtain ⟨as, has⟩ := hSodd
    refine ⟨an - as, ?_⟩
    rw [hX, han, has]
    omega
  set T := X / 2 with hT
  
  have hbound : S + z ≤ n := by
    have g1 : 4 * m ≤ E := by
      rw [hE]
      have h10 : 10 ≤ 2 ^ a * 5 ^ b :=
        calc 10 = 2 * 5 := by norm_num
          _ ≤ 2 ^ a * 5 ^ b :=
              Nat.mul_le_mul (Nat.pow_le_pow_right (n := 2) (by norm_num) ha)
                (Nat.pow_le_pow_right (n := 5) (by norm_num) hb)
      calc 4 * m ≤ (2 ^ a * 5 ^ b) * m :=
            Nat.mul_le_mul_right _ (by omega)
        _ = 2 ^ a * 5 ^ b * m := by ring
    have g2 : 2 * j ≤ E := by
      rw [hj]
      have hc2 : 2 * c ≤ 2 ^ a * M := by
        calc 2 * c ≤ 2 * (2 ^ (a - 1) * M) := Nat.mul_le_mul_left 2 hcle
          _ = (2 * 2 ^ (a - 1)) * M := by ring
          _ = 2 ^ a * M := by
              rw [← Nat.pow_succ', Nat.succ_eq_add_one,
                Nat.sub_add_cancel ha]
      calc 2 * c ≤ 2 ^ a * M := hc2
        _ = E := by rw [hE, hM]; ring
    have g4 : 36 * t ≤ 36 * 2 ^ (a - 2) := Nat.mul_le_mul_left 36 htle
    have hlen3 : 2 * lenD ≤ 36 + 36 * 2 ^ (a - 2) := by
      rw [hlenN]
      have hr : r0b 0 0 4 ≤ 8 := by
        have h := hr₀lt
        norm_num at h
        omega
      calc 2 * (2 * (1 + r0b 0 0 4) + 18 * t)
          = 4 * (1 + r0b 0 0 4) + 36 * t := by ring
        _ ≤ 36 + 36 * 2 ^ (a - 2) := by omega
    have hzz2 : z ≤ a + b + 2 := by rw [hz]; omega
    rw [hS, hK, hE3]
    omega
  
  set C := List.replicate j 9 ++ List.replicate T 0 ++ [0]
      ++ List.replicate T 0 ++ List.replicate j 9 with hC
  have hCg : C.length = 2 * j + 2 * T + 1 := (center_repunit_len_sum j T).1
  have hCσ : C.sum = 18 * j := (center_repunit_len_sum j T).2
  have hCval3 : 3 ∣ Nat.ofDigits 10 C := by
    apply ofDigits_dvd_of_mem
    intro d hd
    have hd90 : d = 9 ∨ d = 0 := by
      rw [hC] at hd
      rcases List.mem_append.mp hd with hA | h9last
      · rcases List.mem_append.mp hA with hA | h0b
        · rcases List.mem_append.mp hA with hA | h00
          · rcases List.mem_append.mp hA with h9a | h0a
            · exact Or.inl (List.eq_of_mem_replicate h9a)
            · exact Or.inr (List.eq_of_mem_replicate h0a)
          · exact Or.inr (List.mem_singleton.mp h00)
        · exact Or.inr (List.eq_of_mem_replicate h0b)
      · exact Or.inl (List.eq_of_mem_replicate h9last)
    rcases hd90 with rfl | rfl
    · exact ⟨3, by norm_num⟩
    · exact dvd_zero _
  have hK1 : 1 ≤ K := by rw [hK]; exact hm0
  have hde_pal : D.reverse = D := hDpal.reverse_eq
  have hde81 : 81 ∣ Nat.ofDigits 10 D := by
    have h : ((Nat.ofDigits 10 D : ℕ) : ZMod 81) = 0 := by
      rw [cast_ofDigits]
      exact hD81
    exact (CharP.cast_eq_zero_iff (ZMod 81) 81 _).mp h
  have hde3 : 3 ∣ Nat.ofDigits 10 D := dvd_trans (by norm_num) hde81
  have hj1 : 1 ≤ j := hc1
  have hg3 : 3 ≤ 2 * j + 2 * T + 1 := by omega
  have hgodd : Odd (2 * j + 2 * T + 1) := ⟨j + T, by ring⟩
  have hKcov : m * 3 ^ (1 - 4) ≤ 1 + 9 * (K / 2) := by
    have hv4' : (1 : ℕ) - 4 = 0 := rfl
    rw [hv4', pow_zero, mul_one]
    have hKm : m ≤ K := by rw [hK]
    have hdiv : m / 2 ≤ K / 2 := Nat.div_le_div_right hKm
    have h2m : m ≤ 2 * (m / 2) + 1 := by
      have := Nat.div_add_mod m 2
      omega
    omega
  obtain ⟨s₀, hs0⟩ := hs0_v1 (le := lenD) (K := K)
    (g := 2 * j + 2 * T + 1) D hde_pal hde3 C hCval3
  obtain ⟨e', he', hdvdP⟩ := P_dvd_3m81 (m := m) (v := 1)
    (le := lenD) (K := K) (g := 2 * j + 2 * T + 1)
    hm3 hm10 D rfl C hCg hg3 hgodd hKcov s₀ hs0
  set MID := (List.range (2 * K)).map (pairDigit e') ++ C
      ++ ((List.range (2 * K)).map (pairDigit e')).reverse with hMID
  set P := Nat.ofDigits 10 (D ++ MID ++ D.reverse) with hP
  have hMIDpal : MID.Palindrome := mid_pal e' C (center_repunit_pal j T)
  have hMID10 : ∀ x ∈ MID, x < 10 := mid_lt10 e' he' C
    (center_repunit_lt10 j T)
  obtain ⟨hP0, hPpal, hPlen, hPσ⟩ := sandwich_spec_gen D MID hDne hD10
    (hD0 hDne) hMIDpal hMID10 rfl rfl
  have hMIDlen : MID.length = 4 * K + C.length := by
    rw [hMID, List.length_append, List.length_append, List.length_reverse,
      List.length_map, List.length_range]
    ring
  obtain ⟨rr, hrr⟩ := hXeven
  have h2T : 2 * T = X := by rw [hT]; omega
  have hlen : (Nat.digits 10 P).length = n - z := by
    rw [hPlen, hMIDlen, hCg]
    omega
  
  have hσP : (Nat.digits 10 P).sum
      = 4 * 81 * (rhob 0 0 4 + t) + 18 * (K + j) := by
    rw [hPσ, mid_sum e' he' C, hCσ, hDσ]
    ring
  have h2a : 2 ^ a ∣ (Nat.digits 10 P).sum := by
    rw [hσP]
    apply Nat.dvd_add
    · have h21 : 2 ^ a ∣ 4 * (rhob 0 0 4 + t) := by
        rcases Nat.lt_or_ge 2 a with h | h
        · obtain ⟨u, hu⟩ := ht2
          have hpa : 2 ^ a = 2 ^ (a - 2) * 4 := by
            rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, ← pow_add,
              show a - 2 + 2 = a from by omega]
          rw [hpa]
          exact ⟨u, by rw [hu]; ring⟩
        · exact dvd_mul_of_dvd_left
            (show 2 ^ a ∣ 4 from pow_dvd_pow 2 (by omega)) _
      have e1 : 4 * 81 * (rhob 0 0 4 + t)
          = 81 * (4 * (rhob 0 0 4 + t)) := by ring
      rw [e1]
      obtain ⟨w, hw⟩ := h21
      exact ⟨81 * w, by rw [hw]; ring⟩
    · have h22 : 2 ^ a ∣ 2 * (m + c) := by
        obtain ⟨u, hu⟩ := hmc
        have hpa : 2 ^ a = 2 ^ (a - 1) * 2 := by
          rw [← Nat.pow_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel ha]
        rw [hpa]
        exact ⟨u, by rw [hu]; ring⟩
      have e2 : 18 * (K + j) = 9 * (2 * (m + c)) := by
        rw [hK, hj]
        ring
      rw [e2]
      exact dvd_mul_of_dvd_right h22 _
  have h3vd : 3 ∣ (Nat.digits 10 P).sum := by
    rw [hσP]
    apply Nat.dvd_add
    · exact dvd_mul_of_dvd_left (by norm_num : (3 : ℕ) ∣ 4 * 81) _
    · exact dvd_mul_of_dvd_left (by norm_num : (3 : ℕ) ∣ 18) _
  have hMdvd : m * 5 ^ b ∣ (Nat.digits 10 P).sum := by
    have e : 18 * (K + j) = 18 * (m + c) := by
      rw [hK, hj]
    rw [hσP, e, ← hM]
    exact hcdvd'
  have hσ : n ∣ (Nat.digits 10 P).sum := by
    have hcop2a : (2 ^ a).Coprime 3 :=
      ((by decide : Nat.Coprime 2 3)).pow_left a
    have hcopB : (2 ^ a * 3).Coprime (m * 5 ^ b) := by
      apply Nat.Coprime.mul_right
      · exact Nat.Coprime.mul_left (hm2.symm.pow_left a) hm3.symm
      · exact Nat.Coprime.mul_left
          (((by decide : Nat.Coprime 2 5).pow_right b).pow_left a)
          ((by decide : Nat.Coprime 3 5).pow_right b)
    have hjoin1 := hcop2a.mul_dvd_of_dvd_of_dvd h2a h3vd
    have hjoin2 := hcopB.mul_dvd_of_dvd_of_dvd hjoin1 hMdvd
    rw [hn]
    rwa [show 2 ^ a * 5 ^ b * 3 * m = 2 ^ a * 3 * (m * 5 ^ b)
      from by ring]
  
  have hPd : n ∣ P * 10 ^ z := by
    have h25 : 2 ^ (a - z) * 5 ^ (b - z) ∣ P := by
      have hle_big : max 0 0 ≤ lenD := by simp
      have := B_dvd_P (le := lenD) (de := D) (MID := MID) rfl hD25 hle_big
      rwa [hP, haz, hbz]
    obtain ⟨w, hw⟩ := hdvdP
    have h3mP : 3 ^ 1 * m ∣ P := ⟨w, by rw [hw]; ring⟩
    have h := n_dvd_P_pow10_le (a := a) (b := b) (v := 1) (m := m) (z := z)
      (a' := a - z) (b' := b - z) (P := P) h25 h3mP
      (by rw [haz, Nat.zero_add]; exact le_of_lt hza)
      (by rw [hbz, Nat.zero_add]; exact le_of_lt hzb) hm30
    rw [pow_one, ← hn] at h
    exact h
  refine ⟨P, z, hP0, ?_, hPpal, ?_, hPd, hσ⟩
  · intro _
    rw [hn]
    have h2a' : 2 ^ a = 2 * 2 ^ (a - 1) := by
      rw [← Nat.pow_succ', Nat.succ_eq_add_one, Nat.sub_add_cancel ha]
    have h5b' : 5 ^ b = 5 * 5 ^ (b - 1) := by
      rw [← Nat.pow_succ', Nat.succ_eq_add_one, Nat.sub_add_cancel hb]
    exact ⟨2 ^ (a - 1) * 5 ^ (b - 1) * 3 * m, by rw [h2a', h5b']; ring⟩
  · rw [hlen]
    exact Nat.sub_add_cancel (le_of_lt hzlt)


set_option maxHeartbeats 800000 in
theorem assemble_v01o {b m : ℕ} (hb : 1 ≤ b)
    (hm0 : 1 ≤ m) (hm30 : m.Coprime 30)
    (hB : 4 * m + 8 * b + 41 ≤ 5 ^ b * m) :
    ∃ P z : ℕ, P ≠ 0
      ∧ (0 < z → 10 ∣ 5 ^ b * 3 * m)
      ∧ (Nat.digits 10 P).Palindrome
      ∧ (Nat.digits 10 P).length + z = 5 ^ b * 3 * m
      ∧ 5 ^ b * 3 * m ∣ P * 10 ^ z
      ∧ 5 ^ b * 3 * m ∣ (Nat.digits 10 P).sum := by
  classical
  set z := 0 with hz
  set n := 5 ^ b * 3 * m with hn
  haveI : NeZero m := ⟨by omega⟩
  have hm3 : m.Coprime 3 := hm30.coprime_dvd_right (by norm_num)
  have hm10 : m.Coprime 10 := hm30.coprime_dvd_right (by norm_num)
  have hm2 : m.Coprime 2 := hm30.coprime_dvd_right (by norm_num)
  set K := m with hK
  set M := m * 5 ^ b with hM
  have hE3 : n = 3 * M := by rw [hn, hM]; ring
  have hM0 : 0 < M := by
    rw [hM]
    exact Nat.mul_pos (by omega) (pow_pos (by norm_num) _)
  have hmo : Odd m := by
    have h2 : ¬ (2 : ℕ) ∣ m :=
      (Nat.prime_two.coprime_iff_not_dvd).mp hm2.symm
    rw [← Nat.not_even_iff_odd]
    rintro ⟨c', hc'⟩
    exact h2 ⟨c', by omega⟩
  have hModd : Odd M := by
    rw [hM]
    exact hmo.mul (Odd.pow (by decide : Odd 5))
  have h18 : (18 * 3 ^ (1 - 2)).Coprime M := by
    show (18 : ℕ).Coprime M
    have h18' : (18 : ℕ) = 2 * 3 ^ 2 := by norm_num
    rw [h18', hM]
    have h2m : (2 * 3 ^ 2).Coprime m :=
      hm2.symm.mul_left (hm3.symm.pow_left 2)
    have h25b : (2 * 3 ^ 2).Coprime (5 ^ b) := by
      apply Nat.Coprime.mul_left
      · exact ((by decide : Nat.Coprime 2 5).pow_right b)
      · exact ((by decide : Nat.Coprime 3 5).pow_right b).pow_left 2
    exact h2m.mul_right h25b
  obtain ⟨c, hclt, hcdvd⟩ := sigma_c_solve (v := 1) (ρ := rhob 0 b 4)
    (m := m) (M := M) hM0 h18
  have hcdvd' : M ∣ 4 * 81 * rhob 0 b 4 + 18 * (m + c) := by
    have e : 18 * 3 ^ (1 - 2) = 18 := by norm_num
    rw [e] at hcdvd
    exact hcdvd
  set j := if c = 0 then M else c with hj
  have hjc : (c ≠ 0 ∧ j = c) ∨ (c = 0 ∧ j = M) := by
    rw [hj]
    by_cases hc0 : c = 0
    · rw [if_pos hc0]
      exact Or.inr ⟨hc0, rfl⟩
    · rw [if_neg hc0]
      exact Or.inl ⟨hc0, rfl⟩
  have hjM : M ∣ j - c := by
    rcases hjc with ⟨-, h⟩ | ⟨hc0, h⟩
    · rw [h, Nat.sub_self]
      exact dvd_zero _
    · rw [h, hc0, Nat.sub_zero]
  have hj1 : 1 ≤ j := by
    rcases hjc with ⟨hc0, h⟩ | ⟨-, h⟩
    · rw [h]
      omega
    · rw [h]
      omega
  have hj2 : 2 * j ≤ 2 * M := by
    rcases hjc with ⟨-, h⟩ | ⟨-, h⟩
    · rw [h]; omega
    · rw [h]
  obtain ⟨D, hDpal, hD10, hDne, hD0, hD25, hD81, hDσ, hr₀lt, hlenD⟩ :=
    border_pal (a' := 0) (b' := b) (q := 4) (s₁ := b) (t := 0)
      (by norm_num) (Or.inl rfl) (by simp)
  set lenD := D.length with hlenD'
  have lenV_le : (Nat.digits 10 (9 * 2 ^ 0 * 5 ^ b)).length ≤ b + 2 := by
    have hVpos : (9 * 2 ^ 0 * 5 ^ b : ℕ) ≠ 0 := by positivity
    have hb2 := Nat.base_pow_length_digits_le 10 (9 * 2 ^ 0 * 5 ^ b)
      (by norm_num) hVpos
    have hlt : 10 * (9 * 2 ^ 0 * 5 ^ b) < 10 ^ (b + 2) := by
      have h1 : (5 : ℕ) ^ b ≤ 10 ^ b := Nat.pow_le_pow_left (by norm_num) b
      calc 10 * (9 * 2 ^ 0 * 5 ^ b) = 90 * 5 ^ b := by ring
        _ ≤ 90 * 10 ^ b := Nat.mul_le_mul_left 90 h1
        _ < 100 * 10 ^ b := by omega
        _ = 10 ^ (b + 2) := by ring
    have hpow : 10 ^ ((Nat.digits 10 (9 * 2 ^ 0 * 5 ^ b)).length)
        < 10 ^ (b + 2) := lt_of_le_of_lt hb2 hlt
    have hlt' := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 10)).mp hpow
    omega
  have hlenN : lenD = 2 * ((Nat.digits 10 (9 * 2 ^ 0 * 5 ^ b)).length
      + b + r0b 0 b 4) := by
    have e : 2 * 3 ^ (4 - 2) * 0 = 0 := by ring
    rw [hlenD, e, add_zero]
  
  have hno : Odd (n - z) := by
    have hnodd : Odd n := by
      rw [hn]
      exact ((Odd.pow (by decide : Odd 5)).mul
        (by decide : Odd 3)).mul hmo
    obtain ⟨an, han⟩ := hnodd
    refine ⟨an, ?_⟩
    rw [han]
    omega
  set S := 1 + 4 * K + 2 * j + 2 * lenD with hS
  have hSodd : Odd S := by
    have e1 : Even (4 * K) := ⟨2 * K, by ring⟩
    have e2 : Even (2 * j) := ⟨j, by ring⟩
    have e3 : Even (2 * lenD) := ⟨lenD, by ring⟩
    obtain ⟨w, hw⟩ := (e1.add e2).add e3
    use w
    rw [hS]
    omega
  set X := (n - z) - S with hX
  have hXeven : Even X := by
    obtain ⟨an, han⟩ := hno
    obtain ⟨as, has⟩ := hSodd
    refine ⟨an - as, ?_⟩
    rw [hX, han, has]
    omega
  set T := X / 2 with hT
  
  have hbound : S + z ≤ n := by
    have hd : 2 * lenD ≤ 8 * b + 40 := by
      rw [hlenN]
      have hr : r0b 0 b 4 ≤ 8 := by
        have h := hr₀lt
        norm_num at h
        omega
      calc 2 * (2 * ((Nat.digits 10 (9 * 2 ^ 0 * 5 ^ b)).length
            + b + r0b 0 b 4))
          = 4 * ((Nat.digits 10 (9 * 2 ^ 0 * 5 ^ b)).length
            + b + r0b 0 b 4) := by ring
        _ ≤ 4 * (b + 2 + b + 8) := by omega
        _ = 8 * b + 40 := by ring
    have hB' : 4 * m + 8 * b + 41 ≤ M := by
      have hBB := hB
      rw [hK] at hBB
      rw [hM]
      rwa [mul_comm (5 ^ b) m] at hBB
    rw [hz, hS, hK, hE3]
    omega
  
  set C := List.replicate j 9 ++ List.replicate T 0 ++ [0]
      ++ List.replicate T 0 ++ List.replicate j 9 with hC
  have hCg : C.length = 2 * j + 2 * T + 1 := (center_repunit_len_sum j T).1
  have hCσ : C.sum = 18 * j := (center_repunit_len_sum j T).2
  have hCval3 : 3 ∣ Nat.ofDigits 10 C := by
    apply ofDigits_dvd_of_mem
    intro d hd
    have hd90 : d = 9 ∨ d = 0 := by
      rw [hC] at hd
      rcases List.mem_append.mp hd with hA | h9last
      · rcases List.mem_append.mp hA with hA | h0b
        · rcases List.mem_append.mp hA with hA | h00
          · rcases List.mem_append.mp hA with h9a | h0a
            · exact Or.inl (List.eq_of_mem_replicate h9a)
            · exact Or.inr (List.eq_of_mem_replicate h0a)
          · exact Or.inr (List.mem_singleton.mp h00)
        · exact Or.inr (List.eq_of_mem_replicate h0b)
      · exact Or.inl (List.eq_of_mem_replicate h9last)
    rcases hd90 with rfl | rfl
    · exact ⟨3, by norm_num⟩
    · exact dvd_zero _
  have hK1 : 1 ≤ K := by rw [hK]; exact hm0
  have hde_pal : D.reverse = D := hDpal.reverse_eq
  have hde81 : 81 ∣ Nat.ofDigits 10 D := by
    have h : ((Nat.ofDigits 10 D : ℕ) : ZMod 81) = 0 := by
      rw [cast_ofDigits]
      exact hD81
    exact (CharP.cast_eq_zero_iff (ZMod 81) 81 _).mp h
  have hde3 : 3 ∣ Nat.ofDigits 10 D := dvd_trans (by norm_num) hde81
  have hg3 : 3 ≤ 2 * j + 2 * T + 1 := by omega
  have hgodd : Odd (2 * j + 2 * T + 1) := ⟨j + T, by ring⟩
  have hKcov : m * 3 ^ (1 - 4) ≤ 1 + 9 * (K / 2) := by
    rw [show (1 : ℕ) - 4 = 0 from rfl, pow_zero, mul_one, ← hK]
    omega
  obtain ⟨s₀, hs0⟩ := hs0_v1 (le := lenD) (K := K)
    (g := 2 * j + 2 * T + 1) D hde_pal hde3 C hCval3
  obtain ⟨e', he', hdvdP⟩ := P_dvd_3m81 (m := m) (v := 1)
    (le := lenD) (K := K) (g := 2 * j + 2 * T + 1)
    hm3 hm10 D rfl C hCg hg3 hgodd hKcov s₀ hs0
  set MID := (List.range (2 * K)).map (pairDigit e') ++ C
      ++ ((List.range (2 * K)).map (pairDigit e')).reverse with hMID
  set P := Nat.ofDigits 10 (D ++ MID ++ D.reverse) with hP
  have hMIDpal : MID.Palindrome := mid_pal e' C (center_repunit_pal j T)
  have hMID10 : ∀ x ∈ MID, x < 10 := mid_lt10 e' he' C
    (center_repunit_lt10 j T)
  obtain ⟨hP0, hPpal, hPlen, hPσ⟩ := sandwich_spec_gen D MID hDne hD10
    (hD0 hDne) hMIDpal hMID10 rfl rfl
  have hMIDlen : MID.length = 4 * K + C.length := by
    rw [hMID, List.length_append, List.length_append, List.length_reverse,
      List.length_map, List.length_range]
    ring
  obtain ⟨rr, hrr⟩ := hXeven
  have h2T : 2 * T = X := by rw [hT]; omega
  have hlen : (Nat.digits 10 P).length = n - z := by
    rw [hPlen, hMIDlen, hCg]
    omega
  
  have hσP : (Nat.digits 10 P).sum
      = 4 * 81 * rhob 0 b 4 + 18 * (K + j) := by
    rw [hPσ, mid_sum e' he' C, hCσ, hDσ]
    ring
  have h3vd : 3 ∣ (Nat.digits 10 P).sum := by
    rw [hσP]
    apply Nat.dvd_add
    · exact dvd_mul_of_dvd_left (by norm_num : (3 : ℕ) ∣ 4 * 81) _
    · exact dvd_mul_of_dvd_left (by norm_num : (3 : ℕ) ∣ 18) _
  have hMdvd : M ∣ (Nat.digits 10 P).sum := by
    have e : 18 * (K + j) = 18 * (m + c) + 18 * (j - c) := by
      rcases hjc with ⟨-, h⟩ | ⟨hc0, h⟩
      · rw [h, Nat.sub_self, hK]; ring
      · rw [h, hc0, Nat.sub_zero, hK]; ring
    rw [hσP, e, ← Nat.add_assoc]
    exact Nat.dvd_add hcdvd' (dvd_mul_of_dvd_right hjM 18)
  have hσ : n ∣ (Nat.digits 10 P).sum := by
    have h3M : (3 : ℕ).Coprime M := by
      rw [hM, ← hK]
      exact Nat.Coprime.mul_right hm3.symm
        ((by decide : Nat.Coprime 3 5).pow_right b)
    have hjoin := h3M.mul_dvd_of_dvd_of_dvd h3vd hMdvd
    rw [hE3]
    exact hjoin
  
  have hPd : n ∣ P * 10 ^ z := by
    have h25 : 2 ^ (0 - z) * 5 ^ (b - z) ∣ P := by
      have hle_big : max (0 - z) (b - z) ≤ lenD := by
        rw [hz, hlenN]
        omega
      have hD25' : 2 ^ (0 - z) * 5 ^ (b - z) ∣ Nat.ofDigits 10 D := by
        rw [hz]
        simpa using hD25
      have hBP := B_dvd_P (le := lenD) (de := D) (MID := MID) rfl hD25'
        hle_big
      rwa [hP]
    obtain ⟨w, hw⟩ := hdvdP
    have h3mP : 3 ^ 1 * m ∣ P := ⟨w, by rw [hw]; ring⟩
    have h := n_dvd_P_pow10_le (a := 0) (b := b) (v := 1) (m := m) (z := z)
      (a' := 0 - z) (b' := b - z) (P := P) h25 h3mP
      (by omega) (by omega) hm30
    rw [hz]
    simpa [hn, hz] using h
  refine ⟨P, z, hP0, ?_, hPpal, ?_, hPd, hσ⟩
  · intro hz0
    omega
  · rw [hlen]
    omega


set_option maxHeartbeats 800000 in
theorem assemble_eb01 {a m : ℕ} (ha : 2 ≤ a)
    (hm0 : 1 ≤ m) (hm30 : m.Coprime 30)
    (hm11 : m.Coprime 11) (hm101 : m.Coprime 101)
    (hB : 4 * m + 2 ^ a + 8 * a + 8 + 2 ^ a * m ≤ 3 * (2 ^ a * m)) :
    ∃ P z : ℕ, P ≠ 0
      ∧ (0 < z → 10 ∣ 2 ^ a * 3 * m)
      ∧ (Nat.digits 10 P).Palindrome
      ∧ (Nat.digits 10 P).length + z = 2 ^ a * 3 * m
      ∧ 2 ^ a * 3 * m ∣ P * 10 ^ z
      ∧ 2 ^ a * 3 * m ∣ (Nat.digits 10 P).sum := by
  classical
  set z := 0 with hz
  set n := 2 ^ a * 3 * m with hn
  haveI : NeZero m := ⟨by omega⟩
  have hm3 : m.Coprime 3 := hm30.coprime_dvd_right (by norm_num)
  have hm10 : m.Coprime 10 := hm30.coprime_dvd_right (by norm_num)
  have hm2 : m.Coprime 2 := hm30.coprime_dvd_right (by norm_num)
  
  set p2 := 2 ^ (a - 1) with hp2
  have hp2pos : 0 < p2 := pow_pos (by norm_num) _
  set c := p2 - m % p2 with hc
  have hmc : p2 ∣ m + c := by
    have hlt : m % p2 < p2 := Nat.mod_lt _ hp2pos
    have h2 := Nat.div_add_mod m p2
    have h3 : p2 * (m / p2 + 1) = p2 * (m / p2) + p2 := Nat.mul_succ _ _
    refine ⟨m / p2 + 1, ?_⟩
    rw [hc, h3]
    omega
  have hcle : c ≤ p2 := Nat.sub_le _ _
  have hc1 : 1 ≤ c := by
    have hlt : m % p2 < p2 := Nat.mod_lt _ hp2pos
    rw [hc]
    omega
  
  set K := m with hK
  set j := c with hj
  set M := m with hM
  have hM0 : 0 < M := by
    rw [hM]
    exact Nat.pos_of_ne_zero (NeZero.ne m)
  have h4m : (4 : ℕ).Coprime m := hm2.symm.pow_left 2
  have h9m : (9 : ℕ).Coprime m := hm3.symm.pow_left 2
  have hcop43 : (4 * 3 ^ 2).Coprime M := by
    rw [hM]
    exact h4m.mul_left h9m
  
  have hmo : Odd m := by
    have h2 : ¬ (2 : ℕ) ∣ m :=
      (Nat.prime_two.coprime_iff_not_dvd).mp hm2.symm
    rw [← Nat.not_even_iff_odd]
    rintro ⟨c', hc'⟩
    exact h2 ⟨c', by omega⟩
  have hModd : Odd M := by
    rw [hM]
    exact hmo
  have hnd : ¬ (2 : ℕ) ∣ M := by
    rintro ⟨r, hr⟩
    obtain ⟨s, hs⟩ := hModd
    omega
  have hcop2 : M.Coprime (2 ^ (a - 2)) :=
    ((Nat.prime_two.coprime_iff_not_dvd).mpr hnd).symm.pow_right _
  
  obtain ⟨t, htlt, ht2, htdvd⟩ := sigma_t_solve2 (v := 2)
    (ρ := rhob a 0 2) (S := K + j) (M := M) (w := a - 2)
    hM0 hcop43 hcop2
  
  have hmin : a = 0 ∨ (0 : ℕ) = 0 := Or.inr rfl
  obtain ⟨D, hDpal, hD10, hDne, hD0, hD25, hD3v, hDσ, hr₀lt, hlenD⟩ :=
    border_pal_q (a' := a) (b' := 0) (q := 2)
      (s₁ := a) (t := t)
      (by norm_num) (by norm_num) hmin (le_of_eq (Nat.max_eq_left (Nat.zero_le a)))
  set lenD := D.length with hlenD'
  have hlenN : lenD
      = 2 * ((Nat.digits 10 (9 * 2 ^ a)).length + a + r0b a 0 2)
        + 2 * t := by
    rw [hlenD]
    ring
  
  have lenV_le : (Nat.digits 10 (9 * 2 ^ a)).length ≤ a + 2 := by
    have hVpos : (9 * 2 ^ a : ℕ) ≠ 0 := by positivity
    have hb2 := Nat.base_pow_length_digits_le 10 (9 * 2 ^ a) (by norm_num) hVpos
    have hlt : 10 * (9 * 2 ^ a) < 10 ^ (a + 2) := by
      have h1 : (2 : ℕ) ^ a ≤ 10 ^ a := Nat.pow_le_pow_left (by norm_num) _
      calc 10 * (9 * 2 ^ a) = 90 * 2 ^ a := by ring
        _ ≤ 90 * 10 ^ a := Nat.mul_le_mul_left 90 h1
        _ < 100 * 10 ^ a := by omega
        _ = 10 ^ (a + 2) := by ring
    have hpow : 10 ^ ((Nat.digits 10 (9 * 2 ^ a)).length) < 10 ^ (a + 2) :=
      lt_of_le_of_lt hb2 hlt
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 10)).mp hpow
    omega
  have hne : Even n := by
    rw [hn]
    refine ⟨2 ^ (a - 1) * 3 * m, ?_⟩
    rw [show 2 ^ a = 2 * 2 ^ (a - 1) from by
      rw [← Nat.pow_succ', Nat.succ_eq_add_one,
        Nat.sub_add_cancel (by omega : 1 ≤ a)]]
    ring
  have hzlt : z < n := by
    have ha2 : a < 2 ^ a := Nat.lt_two_pow_self
    have h2n : 2 ^ a ≤ n := by
      rw [hn]
      calc 2 ^ a ≤ 2 ^ a * 3 :=
            Nat.le_mul_of_pos_right _ (by norm_num)
        _ ≤ 2 ^ a * 3 * m :=
            Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne m))
    omega
  have hne2 : Even (n - z) := by
    rw [hz, Nat.sub_zero]
    exact hne
  set S := 4 * K + 2 * j + 2 * lenD with hS
  have hSeven : Even S := by
    refine ⟨2 * K + j + lenD, ?_⟩
    rw [hS]
    ring
  set X := (n - z) - S with hX
  have hXeven : Even X := by
    obtain ⟨an, han⟩ := hne2
    obtain ⟨as, has⟩ := hSeven
    refine ⟨an - as, ?_⟩
    rw [hX, han, has]
    omega
  set T := X / 2 with hT
  
  have hbound : S + 4 ≤ n := by
    set E := 2 ^ a * m with hE
    have hnE : n = 3 * E := by rw [hn, hE]; ring
    have hB' : 4 * K + 2 ^ a + 8 * a + 8 + E ≤ 3 * E := hB
    have hc2 : 2 * c ≤ 2 ^ a := by
      calc 2 * c ≤ 2 * 2 ^ (a - 1) :=
            Nat.mul_le_mul_left 2 hcle
        _ = 2 ^ a := by
            rw [← Nat.pow_succ', Nat.succ_eq_add_one,
              Nat.sub_add_cancel (by omega : 1 ≤ a)]
    have g4 : 4 * t + 12 ≤ E + 8 := by
      have ht1 : t + 1 ≤ M * 2 ^ (a - 2) := htlt
      have h4a : 4 * 2 ^ (a - 2) = 2 ^ a := by
        rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, ← pow_add,
          show 2 + (a - 2) = a from by omega]
      calc 4 * t + 12 = 4 * (t + 1) + 8 := by ring
        _ ≤ 4 * (M * 2 ^ (a - 2)) + 8 := by omega
        _ = M * (4 * 2 ^ (a - 2)) + 8 := by ring
        _ = M * 2 ^ a + 8 := by rw [h4a]
        _ = E + 8 := by rw [hM, hE]; ring
    have hlen3 : 2 * lenD ≤ 8 * a + 4 * t + 8 := by
      rw [hlenN]
      have hr0 : r0b a 0 2 = 0 := by
        have h := hr₀lt
        norm_num at h
        omega
      rw [hr0]
      omega
    rw [hS, hj, hnE]
    omega
  
  set C := List.replicate j 9 ++ List.replicate T 0
      ++ List.replicate T 0 ++ List.replicate j 9 with hC
  have hCg : C.length = 2 * j + 2 * T := (center_repunit_even_len_sum j T).1
  have hCσ : C.sum = 18 * j := (center_repunit_even_len_sum j T).2
  have hCval3 : 3 ∣ Nat.ofDigits 10 C := by
    apply ofDigits_dvd_of_mem
    intro d hd
    have hd90 : d = 9 ∨ d = 0 := by
      rw [hC] at hd
      rcases List.mem_append.mp hd with hABC | h9last
      · rcases List.mem_append.mp hABC with hAB | hT2
        · rcases List.mem_append.mp hAB with h9a | hT1
          · exact Or.inl (List.eq_of_mem_replicate h9a)
          · exact Or.inr (List.eq_of_mem_replicate hT1)
        · exact Or.inr (List.eq_of_mem_replicate hT2)
      · exact Or.inl (List.eq_of_mem_replicate h9last)
    rcases hd90 with rfl | rfl
    · exact ⟨3, by norm_num⟩
    · exact dvd_zero _
  have hK1 : 1 ≤ K := by rw [hK]; exact hm0
  have hde_pal : D.reverse = D := hDpal.reverse_eq
  have hD3 : 3 ∣ Nat.ofDigits 10 D :=
    dvd_trans (by norm_num : (3 : ℕ) ∣ 3 ^ 2) hD3v
  obtain ⟨s₀, hs0⟩ := hs0_v1 (le := lenD) (K := K)
    (g := 2 * j + 2 * T) D hde_pal hD3 C hCval3
  have hj1 : 1 ≤ j := by rw [hj]; exact hc1
  have hg3 : 3 ≤ 2 * j + 2 * T := by
    have hX4 : 4 ≤ X := by
      have hbnd := hbound
      rw [hX]
      omega
    rw [hT]
    omega
  have hgev : Even (2 * j + 2 * T) := ⟨j + T, by ring⟩
  have hKcov : m * 3 ^ (1 - 4) ≤ 1 + 9 * (K / 2) := by
    rw [show (1 : ℕ) - 4 = 0 from rfl, pow_zero, mul_one]
    show K ≤ 1 + 9 * (K / 2)
    omega
  obtain ⟨e', he', hdvdP⟩ := P_dvd_3m81_even hm3 hm10 hm11 hm101 D rfl C hCg hg3 hgev
    hKcov s₀ hs0
  set MID := (List.range (2 * K)).map (pairDigit e') ++ C
      ++ ((List.range (2 * K)).map (pairDigit e')).reverse with hMID
  set P := Nat.ofDigits 10 (D ++ MID ++ D.reverse) with hP
  have hMIDpal : MID.Palindrome := mid_pal e' C (center_repunit_even_pal j T)
  have hMID10 : ∀ x ∈ MID, x < 10 := mid_lt10 e' he' C
    (center_repunit_even_lt10 j T)
  obtain ⟨hP0, hPpal, hPlen, hPσ⟩ := sandwich_spec_gen D MID hDne hD10
    (hD0 hDne) hMIDpal hMID10 rfl rfl
  have hMIDlen : MID.length = 4 * K + C.length := by
    rw [hMID, List.length_append, List.length_append, List.length_reverse,
      List.length_map, List.length_range]
    ring
  obtain ⟨rr, hrr⟩ := hXeven
  have h2T : 2 * T = X := by rw [hT]; omega
  have hlen : (Nat.digits 10 P).length = n - z := by
    rw [hPlen, hMIDlen, hCg]
    omega
  
  have hσP : (Nat.digits 10 P).sum
      = 4 * 3 ^ 2 * (rhob a 0 2 + t) + 18 * (K + j) := by
    rw [hPσ, mid_sum e' he' C, hCσ, hDσ]
    ring
  have h2a : 2 ^ a ∣ (Nat.digits 10 P).sum := by
    rw [hσP]
    apply Nat.dvd_add
    · have h21 : 2 ^ a ∣ 4 * (rhob a 0 2 + t) := by
        rcases Nat.lt_or_ge 2 a with h | h
        · obtain ⟨u, hu⟩ := ht2
          have hpa : 2 ^ a = 2 ^ (a - 2) * 4 := by
            rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, ← pow_add,
              show a - 2 + 2 = a from by omega]
          rw [hpa]
          exact ⟨u, by rw [hu]; ring⟩
        · exact dvd_mul_of_dvd_left
            (show 2 ^ a ∣ 4 from pow_dvd_pow 2 (by omega)) _
      have e1 : 4 * 3 ^ 2 * (rhob a 0 2 + t)
          = 9 * (4 * (rhob a 0 2 + t)) := by ring
      rw [e1]
      exact dvd_mul_of_dvd_right h21 _
    · have h22 : 2 ^ a ∣ 2 * (m + c) := by
        obtain ⟨u, hu⟩ := hmc
        have hpa : 2 ^ a = 2 ^ (a - 1) * 2 := by
          rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ a)]
        rw [hpa]
        exact ⟨u, by rw [hu]; ring⟩
      have e2 : 18 * (K + j) = 9 * (2 * (m + c)) := by
        rw [hK, hj]
        ring
      rw [e2]
      exact dvd_mul_of_dvd_right h22 _
  have h3vd : 3 ∣ (Nat.digits 10 P).sum := by
    rw [hσP]
    apply Nat.dvd_add
    · exact dvd_mul_of_dvd_left (by norm_num : (3 : ℕ) ∣ 4 * 3 ^ 2) _
    · exact dvd_mul_of_dvd_left (by norm_num : (3 : ℕ) ∣ 18) _
  have hMdvd : m ∣ (Nat.digits 10 P).sum := by
    rw [hσP, ← hM]
    exact htdvd
  have hσ : n ∣ (Nat.digits 10 P).sum := by
    have hcop2a : (2 ^ a).Coprime 3 :=
      (by decide : Nat.Coprime 2 3).pow_left a
    have h3m2 : (2 ^ a * 3).Coprime m :=
      Nat.Coprime.mul_left (hm2.symm.pow_left a) hm3.symm
    have hjoin1 := hcop2a.mul_dvd_of_dvd_of_dvd h2a h3vd
    have hjoin2 := h3m2.mul_dvd_of_dvd_of_dvd hjoin1 hMdvd
    rw [hn]
    rwa [show 2 ^ a * 3 * m = 2 ^ a * 3 * m from rfl]
  
  have hPd : n ∣ P * 10 ^ z := by
    have h25 : 2 ^ a * 5 ^ 0 ∣ P := by
      have hle_big : max a 0 ≤ lenD := by
        rw [hlenN]
        omega
      have := B_dvd_P (le := lenD) (de := D) (MID := MID) rfl hD25 hle_big
      rwa [hP]
    obtain ⟨w, hw⟩ := hdvdP
    have h3m : 3 ^ 1 * m ∣ P := ⟨w, by rw [hw]; ring⟩
    have h := n_dvd_P_pow10_le (a := a) (b := 0) (v := 1) (m := m) (z := 0)
      (a' := a) (b' := 0) (P := P) h25 h3m
      (by omega) (by omega) hm30
    rw [hz]
    simpa [hn] using h
  refine ⟨P, z, hP0, ?_, hPpal, ?_, hPd, hσ⟩
  · intro hz'
    omega
  · rw [hlen]
    omega


set_option maxHeartbeats 800000 in
theorem assemble_eb01a {m : ℕ}
    (hm0 : 1 ≤ m) (hm30 : m.Coprime 30)
    (hm11 : m.Coprime 11) (hm101 : m.Coprime 101)
    (hB : 8 * ((m - 1) / 9 + 1) + 18 ≤ 2 * m) :
    ∃ P z : ℕ, P ≠ 0
      ∧ (0 < z → 10 ∣ 2 ^ 1 * 3 * m)
      ∧ (Nat.digits 10 P).Palindrome
      ∧ (Nat.digits 10 P).length + z = 2 ^ 1 * 3 * m
      ∧ 2 ^ 1 * 3 * m ∣ P * 10 ^ z
      ∧ 2 ^ 1 * 3 * m ∣ (Nat.digits 10 P).sum := by
  classical
  set a := 1 with ha
  set z := 0 with hz
  set n := 2 ^ a * 3 * m with hn
  haveI : NeZero m := ⟨by omega⟩
  have hm3 : m.Coprime 3 := hm30.coprime_dvd_right (by norm_num)
  have hm10 : m.Coprime 10 := hm30.coprime_dvd_right (by norm_num)
  have hm2 : m.Coprime 2 := hm30.coprime_dvd_right (by norm_num)
  
  set p2 := 2 ^ (a - 1) with hp2
  have hp2pos : 0 < p2 := pow_pos (by norm_num) _
  set c := p2 - m % p2 with hc
  have hmc : p2 ∣ m + c := by
    have hlt : m % p2 < p2 := Nat.mod_lt _ hp2pos
    have h2 := Nat.div_add_mod m p2
    have h3 : p2 * (m / p2 + 1) = p2 * (m / p2) + p2 := Nat.mul_succ _ _
    refine ⟨m / p2 + 1, ?_⟩
    rw [hc, h3]
    omega
  have hcle : c ≤ p2 := Nat.sub_le _ _
  have hc1 : 1 ≤ c := by
    have hlt : m % p2 < p2 := Nat.mod_lt _ hp2pos
    rw [hc]
    omega
  
  set K := 2 * ((m - 1) / 9 + 1) with hK
  set j := c with hj
  set M := m with hM
  have hM0 : 0 < M := by
    rw [hM]
    exact Nat.pos_of_ne_zero (NeZero.ne m)
  have h4m : (4 : ℕ).Coprime m := hm2.symm.pow_left 2
  have h9m : (9 : ℕ).Coprime m := hm3.symm.pow_left 2
  have hcop43 : (4 * 3 ^ 2).Coprime M := by
    rw [hM]
    exact h4m.mul_left h9m
  
  have hmo : Odd m := by
    have h2 : ¬ (2 : ℕ) ∣ m :=
      (Nat.prime_two.coprime_iff_not_dvd).mp hm2.symm
    rw [← Nat.not_even_iff_odd]
    rintro ⟨c', hc'⟩
    exact h2 ⟨c', by omega⟩
  have hModd : Odd M := by
    rw [hM]
    exact hmo
  have hnd : ¬ (2 : ℕ) ∣ M := by
    rintro ⟨r, hr⟩
    obtain ⟨s, hs⟩ := hModd
    omega
  have hcop2 : M.Coprime (2 ^ (a - 2)) :=
    ((Nat.prime_two.coprime_iff_not_dvd).mpr hnd).symm.pow_right _
  
  obtain ⟨t, htlt, ht2, htdvd⟩ := sigma_t_solve2 (v := 2)
    (ρ := rhob a 0 2) (S := K + j) (M := M) (w := a - 2)
    hM0 hcop43 hcop2
  
  have hmin : a = 0 ∨ (0 : ℕ) = 0 := Or.inr rfl
  obtain ⟨D, hDpal, hD10, hDne, hD0, hD25, hD3v, hDσ, hr₀lt, hlenD⟩ :=
    border_pal_q (a' := a) (b' := 0) (q := 2)
      (s₁ := a) (t := t)
      (by norm_num) (by norm_num) hmin (le_of_eq (Nat.max_eq_left (Nat.zero_le a)))
  set lenD := D.length with hlenD'
  have hlenN : lenD
      = 2 * ((Nat.digits 10 (9 * 2 ^ a)).length + a + r0b a 0 2)
        + 2 * t := by
    rw [hlenD]
    ring
  
  have lenV_le : (Nat.digits 10 (9 * 2 ^ a)).length ≤ a + 2 := by
    have hVpos : (9 * 2 ^ a : ℕ) ≠ 0 := by positivity
    have hb2 := Nat.base_pow_length_digits_le 10 (9 * 2 ^ a) (by norm_num) hVpos
    have hlt : 10 * (9 * 2 ^ a) < 10 ^ (a + 2) := by
      have h1 : (2 : ℕ) ^ a ≤ 10 ^ a := Nat.pow_le_pow_left (by norm_num) _
      calc 10 * (9 * 2 ^ a) = 90 * 2 ^ a := by ring
        _ ≤ 90 * 10 ^ a := Nat.mul_le_mul_left 90 h1
        _ < 100 * 10 ^ a := by omega
        _ = 10 ^ (a + 2) := by ring
    have hpow : 10 ^ ((Nat.digits 10 (9 * 2 ^ a)).length) < 10 ^ (a + 2) :=
      lt_of_le_of_lt hb2 hlt
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 10)).mp hpow
    omega
  have hne : Even n := by
    rw [hn]
    refine ⟨2 ^ (a - 1) * 3 * m, ?_⟩
    rw [show 2 ^ a = 2 * 2 ^ (a - 1) from by
      rw [← Nat.pow_succ', Nat.succ_eq_add_one,
        Nat.sub_add_cancel (by omega : 1 ≤ a)]]
    ring
  have hzlt : z < n := by
    have ha2 : a < 2 ^ a := Nat.lt_two_pow_self
    have h2n : 2 ^ a ≤ n := by
      rw [hn]
      calc 2 ^ a ≤ 2 ^ a * 3 :=
            Nat.le_mul_of_pos_right _ (by norm_num)
        _ ≤ 2 ^ a * 3 * m :=
            Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne m))
    omega
  have hne2 : Even (n - z) := by
    rw [hz, Nat.sub_zero]
    exact hne
  set S := 4 * K + 2 * j + 2 * lenD with hS
  have hSeven : Even S := by
    refine ⟨2 * K + j + lenD, ?_⟩
    rw [hS]
    ring
  set X := (n - z) - S with hX
  have hXeven : Even X := by
    obtain ⟨an, han⟩ := hne2
    obtain ⟨as, has⟩ := hSeven
    refine ⟨an - as, ?_⟩
    rw [hX, han, has]
    omega
  set T := X / 2 with hT
  
  have hbound : S + 4 ≤ n := by
    set E := 2 ^ a * m with hE
    have hnE : n = 3 * E := by rw [hn, hE, ha, pow_one]; ring
    have hE2 : E = 2 * M := by rw [hE, ha, pow_one, ← hM]
    have h4K : 4 * K = 8 * ((M - 1) / 9 + 1) := by rw [hK]; ring
    have hB' : 4 * K + 18 ≤ E := by
      have hBB := hB
      rw [ha] at hBB
      rw [← h4K, ← hE2] at hBB
      exact hBB
    have hc2 : 2 * c ≤ 2 := by
      have hc_eq : c = 1 := by
        show p2 - m % p2 = 1
        rw [hp2, ha]
        simp [Nat.mod_one]
      omega
    have ht1 : t + 1 ≤ M := by
      have h := htlt
      rw [ha] at h
      simp at h
      omega
    have hlen3 : 2 * lenD ≤ 8 * a + 4 * t + 8 := by
      rw [hlenN]
      have hr0 : r0b a 0 2 = 0 := by
        have h := hr₀lt
        norm_num at h
        omega
      rw [hr0]
      omega
    rw [hS, hj, hnE]
    omega
  
  set C := List.replicate j 9 ++ List.replicate T 0
      ++ List.replicate T 0 ++ List.replicate j 9 with hC
  have hCg : C.length = 2 * j + 2 * T := (center_repunit_even_len_sum j T).1
  have hCσ : C.sum = 18 * j := (center_repunit_even_len_sum j T).2
  have hCval3 : 3 ∣ Nat.ofDigits 10 C := by
    apply ofDigits_dvd_of_mem
    intro d hd
    have hd90 : d = 9 ∨ d = 0 := by
      rw [hC] at hd
      rcases List.mem_append.mp hd with hABC | h9last
      · rcases List.mem_append.mp hABC with hAB | hT2
        · rcases List.mem_append.mp hAB with h9a | hT1
          · exact Or.inl (List.eq_of_mem_replicate h9a)
          · exact Or.inr (List.eq_of_mem_replicate hT1)
        · exact Or.inr (List.eq_of_mem_replicate hT2)
      · exact Or.inl (List.eq_of_mem_replicate h9last)
    rcases hd90 with rfl | rfl
    · exact ⟨3, by norm_num⟩
    · exact dvd_zero _
  have hK1 : 1 ≤ K := by
    rw [hK]
    omega
  have hde_pal : D.reverse = D := hDpal.reverse_eq
  have hD3 : 3 ∣ Nat.ofDigits 10 D :=
    dvd_trans (by norm_num : (3 : ℕ) ∣ 3 ^ 2) hD3v
  obtain ⟨s₀, hs0⟩ := hs0_v1 (le := lenD) (K := K)
    (g := 2 * j + 2 * T) D hde_pal hD3 C hCval3
  have hj1 : 1 ≤ j := hc1
  have hg3 : 3 ≤ 2 * j + 2 * T := by
    have hX4 : 4 ≤ X := by
      have hbnd := hbound
      rw [hX]
      omega
    rw [hT]
    omega
  have hgev : Even (2 * j + 2 * T) := ⟨j + T, by ring⟩
  have hKcov : m * 3 ^ (1 - 4) ≤ 1 + 9 * (K / 2) := by
    rw [show (1 : ℕ) - 4 = 0 from rfl, pow_zero, mul_one]
    show M ≤ 1 + 9 * (K / 2)
    have hKhalf : K / 2 = (M - 1) / 9 + 1 := by
      rw [hK]
      omega
    rw [hKhalf]
    omega
  obtain ⟨e', he', hdvdP⟩ := P_dvd_3m81_even hm3 hm10 hm11 hm101 D rfl C hCg hg3 hgev
    hKcov s₀ hs0
  set MID := (List.range (2 * K)).map (pairDigit e') ++ C
      ++ ((List.range (2 * K)).map (pairDigit e')).reverse with hMID
  set P := Nat.ofDigits 10 (D ++ MID ++ D.reverse) with hP
  have hMIDpal : MID.Palindrome := mid_pal e' C (center_repunit_even_pal j T)
  have hMID10 : ∀ x ∈ MID, x < 10 := mid_lt10 e' he' C
    (center_repunit_even_lt10 j T)
  obtain ⟨hP0, hPpal, hPlen, hPσ⟩ := sandwich_spec_gen D MID hDne hD10
    (hD0 hDne) hMIDpal hMID10 rfl rfl
  have hMIDlen : MID.length = 4 * K + C.length := by
    rw [hMID, List.length_append, List.length_append, List.length_reverse,
      List.length_map, List.length_range]
    ring
  obtain ⟨rr, hrr⟩ := hXeven
  have h2T : 2 * T = X := by rw [hT]; omega
  have hlen : (Nat.digits 10 P).length = n - z := by
    rw [hPlen, hMIDlen, hCg]
    omega
  
  have hσP : (Nat.digits 10 P).sum
      = 4 * 3 ^ 2 * (rhob a 0 2 + t) + 18 * (K + j) := by
    rw [hPσ, mid_sum e' he' C, hCσ, hDσ]
    ring
  have h2a : 2 ^ a ∣ (Nat.digits 10 P).sum := by
    rw [hσP]
    apply Nat.dvd_add
    · have h21 : 2 ^ a ∣ 4 * (rhob a 0 2 + t) := by
        rcases Nat.lt_or_ge 2 a with h | h
        · obtain ⟨u, hu⟩ := ht2
          have hpa : 2 ^ a = 2 ^ (a - 2) * 4 := by
            rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, ← pow_add,
              show a - 2 + 2 = a from by omega]
          rw [hpa]
          exact ⟨u, by rw [hu]; ring⟩
        · exact dvd_mul_of_dvd_left
            (show 2 ^ a ∣ 4 from pow_dvd_pow 2 (by omega)) _
      have e1 : 4 * 3 ^ 2 * (rhob a 0 2 + t)
          = 9 * (4 * (rhob a 0 2 + t)) := by ring
      rw [e1]
      exact dvd_mul_of_dvd_right h21 _
    · have h22 : 2 ^ a ∣ 18 * (K + j) := by
        rw [ha, pow_one]
        exact dvd_mul_of_dvd_left (by norm_num : (2 : ℕ) ∣ 18) _
      exact h22
  have h3vd : 3 ∣ (Nat.digits 10 P).sum := by
    rw [hσP]
    apply Nat.dvd_add
    · exact dvd_mul_of_dvd_left (by norm_num : (3 : ℕ) ∣ 4 * 3 ^ 2) _
    · exact dvd_mul_of_dvd_left (by norm_num : (3 : ℕ) ∣ 18) _
  have hMdvd : m ∣ (Nat.digits 10 P).sum := by
    rw [hσP, ← hM]
    exact htdvd
  have hσ : n ∣ (Nat.digits 10 P).sum := by
    have hcop2a : (2 ^ a).Coprime 3 :=
      (by decide : Nat.Coprime 2 3).pow_left a
    have h3m2 : (2 ^ a * 3).Coprime m :=
      Nat.Coprime.mul_left (hm2.symm.pow_left a) hm3.symm
    have hjoin1 := hcop2a.mul_dvd_of_dvd_of_dvd h2a h3vd
    have hjoin2 := h3m2.mul_dvd_of_dvd_of_dvd hjoin1 hMdvd
    rw [hn]
    rwa [show 2 ^ a * 3 * m = 2 ^ a * 3 * m from rfl]
  
  have hPd : n ∣ P * 10 ^ z := by
    have h25 : 2 ^ a * 5 ^ 0 ∣ P := by
      have hle_big : max a 0 ≤ lenD := by
        rw [hlenN]
        omega
      have := B_dvd_P (le := lenD) (de := D) (MID := MID) rfl hD25 hle_big
      rwa [hP]
    obtain ⟨w, hw⟩ := hdvdP
    have h3m : 3 ^ 1 * m ∣ P := ⟨w, by rw [hw]; ring⟩
    have h := n_dvd_P_pow10_le (a := a) (b := 0) (v := 1) (m := m) (z := 0)
      (a' := a) (b' := 0) (P := P) h25 h3m
      (by omega) (by omega) hm30
    rw [hz]
    simpa [hn] using h
  refine ⟨P, z, hP0, ?_, hPpal, ?_, hPd, hσ⟩
  · intro hz'
    omega
  · rw [hlen]
    omega

end A084017



namespace A084017


set_option maxHeartbeats 800000 in
theorem assemble_b00o {m : ℕ}
    (hm0 : 1 ≤ m) (hm30 : m.Coprime 30)
    (hB : 8 * ((m - 1) / 9 + 1) + 41 ≤ m) :
    ∃ P z : ℕ, P ≠ 0
      ∧ (0 < z → 10 ∣ 3 * m)
      ∧ (Nat.digits 10 P).Palindrome
      ∧ (Nat.digits 10 P).length + z = 3 * m
      ∧ 3 * m ∣ P * 10 ^ z
      ∧ 3 * m ∣ (Nat.digits 10 P).sum := by
  classical
  set b := 0 with hb
  set z := 0 with hz
  set n := 3 * m with hn
  haveI : NeZero m := ⟨by omega⟩
  have hm3 : m.Coprime 3 := hm30.coprime_dvd_right (by norm_num)
  have hm10 : m.Coprime 10 := hm30.coprime_dvd_right (by norm_num)
  have hm2 : m.Coprime 2 := hm30.coprime_dvd_right (by norm_num)
  set K := 2 * ((m - 1) / 9 + 1) with hK
  set M := m with hM
  have hE3 : n = 3 * M := hn
  have hM0 : 0 < M := by
    rw [hM]
    exact Nat.pos_of_ne_zero (NeZero.ne m)
  have hmo : Odd m := by
    have h2 : ¬ (2 : ℕ) ∣ m :=
      (Nat.prime_two.coprime_iff_not_dvd).mp hm2.symm
    rw [← Nat.not_even_iff_odd]
    rintro ⟨c', hc'⟩
    exact h2 ⟨c', by omega⟩
  have hModd : Odd M := by
    rw [hM]
    exact hmo
  have h18 : (18 * 3 ^ (1 - 2)).Coprime M := by
    show (18 : ℕ).Coprime M
    have h18' : (18 : ℕ) = 2 * 3 ^ 2 := by norm_num
    rw [h18', hM]
    exact hm2.symm.mul_left (hm3.symm.pow_left 2)
  obtain ⟨c, hclt, hcdvd⟩ := sigma_c_solve (v := 1) (ρ := rhob 0 0 4)
    (m := m) (M := M) hM0 h18
  have hcdvd' : M ∣ 4 * 81 * rhob 0 0 4 + 18 * (m + c) := by
    have e : 18 * 3 ^ (1 - 2) = 18 := by norm_num
    rw [e] at hcdvd
    exact hcdvd
  
  set jr := (c + M - K % M) % M with hjr
  set j := if jr = 0 then M else jr with hj
  have hjc : (jr ≠ 0 ∧ j = jr) ∨ (jr = 0 ∧ j = M) := by
    rw [hj]
    by_cases hc0 : jr = 0
    · rw [if_pos hc0]
      exact Or.inr ⟨hc0, rfl⟩
    · rw [if_neg hc0]
      exact Or.inl ⟨hc0, rfl⟩
  have hj1 : 1 ≤ j := by
    rcases hjc with ⟨hjr0, h⟩ | ⟨-, h⟩
    · rw [h]
      omega
    · rw [h]
      omega
  have hj2 : 2 * j ≤ 2 * M := by
    rcases hjc with ⟨-, h⟩ | ⟨-, h⟩
    · rw [h]
      have hlt : jr < M := by rw [hjr]; exact Nat.mod_lt _ hM0
      omega
    · rw [h]
  
  have hKj : (K + j) ≡ c [MOD M] := by
    rcases hjc with ⟨-, hj'⟩ | ⟨hjr0, hj'⟩
    · rw [hj']
      show (K + jr) % M = c % M
      rw [hjr]
      have h1 : (K + (c + M - K % M) % M) % M
          = (K % M + (c + M - K % M)) % M :=
        ((Nat.ModEq.add Nat.ModEq.rfl (Nat.mod_modEq _ _)).trans
          (Nat.ModEq.add (Nat.mod_modEq _ _) Nat.ModEq.rfl).symm)
      rw [h1]
      rw [Nat.add_comm (K % M) (c + M - K % M),
        Nat.sub_add_cancel (show K % M ≤ c + M by
          have hlt := Nat.mod_lt K hM0
          omega)]
      rw [Nat.add_mod_right]
    · rw [hj']
      show (K + M) % M = c % M
      rw [Nat.add_mod_right]
      have hX : c + M - K % M = M := by
        have hlt1 : 0 < c + M - K % M := by
          have hlt := Nat.mod_lt K hM0
          omega
        have hd : M ∣ c + M - K % M := by
          have hmod0 : (c + M - K % M) % M = 0 := by
            rw [← hjr]
            exact hjr0
          exact Nat.dvd_of_mod_eq_zero hmod0
        obtain ⟨w, hw⟩ := hd
        have hw1 : w = 1 := by
          have hd3 : c + M - K % M < M * 2 := by
            have hlt := Nat.mod_lt K hM0
            omega
          rw [hw] at hd3
          have hw2 : w < 2 := by
            rcases Nat.lt_or_ge w 2 with h | h
            · exact h
            · have : M * 2 ≤ M * w := Nat.mul_le_mul (Nat.le_refl M) h
              omega
          have hw0 : 0 < w := by
            rcases Nat.eq_zero_or_pos w with h | h
            · rw [hw, h] at hlt1
              simp at hlt1
            · exact h
          omega
        rw [hw, hw1]
        exact Nat.mul_one M
      have : K % M = c := by
        have hlt := Nat.mod_lt K hM0
        omega
      rw [this]
      exact (Nat.mod_eq_of_lt hclt).symm
  obtain ⟨D, hDpal, hD10, hDne, hD0, hD25, hD81, hDσ, hr₀lt, hlenD⟩ :=
    border_pal (a' := 0) (b' := 0) (q := 4) (s₁ := 0) (t := 0)
      (by norm_num) (Or.inl rfl) (by omega)
  set lenD := D.length with hlenD'
  have lenV_le : (Nat.digits 10 (9 * 2 ^ 0 * 5 ^ 0)).length ≤ 0 + 2 := by
    have hVpos : (9 * 2 ^ 0 * 5 ^ 0 : ℕ) ≠ 0 := by positivity
    have hb2 := Nat.base_pow_length_digits_le 10 (9 * 2 ^ 0 * 5 ^ 0)
      (by norm_num) hVpos
    have hlt : 10 * (9 * 2 ^ 0 * 5 ^ 0) < 10 ^ (0 + 2) := by
      have h1 : (5 : ℕ) ^ 0 ≤ 10 ^ 0 := Nat.pow_le_pow_left (by norm_num) 0
      calc 10 * (9 * 2 ^ 0 * 5 ^ 0) = 90 * 5 ^ 0 := by ring
        _ ≤ 90 * 10 ^ 0 := Nat.mul_le_mul_left 90 h1
        _ < 100 * 10 ^ 0 := by norm_num
        _ = 10 ^ (0 + 2) := by norm_num
    have hpow : 10 ^ ((Nat.digits 10 (9 * 2 ^ 0 * 5 ^ 0)).length)
        < 10 ^ (0 + 2) := lt_of_le_of_lt hb2 hlt
    have hlt' := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 10)).mp hpow
    omega
  have hlenN : lenD = 2 * ((Nat.digits 10 (9 * 2 ^ 0 * 5 ^ 0)).length
      + 0 + r0b 0 0 4) := by
    have e : 2 * 3 ^ (4 - 2) * 0 = 0 := by ring
    rw [hlenD, e, add_zero]
  
  have hno : Odd (n - z) := by
    have hnodd : Odd n := by
      rw [hn, hM]
      exact ((by decide : Odd 3).mul hmo)
    obtain ⟨an, han⟩ := hnodd
    refine ⟨an, ?_⟩
    rw [han]
    omega
  set S := 1 + 4 * K + 2 * j + 2 * lenD with hS
  have hSodd : Odd S := by
    have e1 : Even (4 * K) := ⟨2 * K, by ring⟩
    have e2 : Even (2 * j) := ⟨j, by ring⟩
    have e3 : Even (2 * lenD) := ⟨lenD, by ring⟩
    obtain ⟨w, hw⟩ := (e1.add e2).add e3
    use w
    rw [hS]
    omega
  set X := (n - z) - S with hX
  have hXeven : Even X := by
    obtain ⟨an, han⟩ := hno
    obtain ⟨as, has⟩ := hSodd
    refine ⟨an - as, ?_⟩
    rw [hX, han, has]
    omega
  set T := X / 2 with hT
  
  have hbound : S + z ≤ n := by
    have hd : 2 * lenD ≤ 40 := by
      rw [hlenN]
      have hr : r0b 0 0 4 ≤ 8 := by
        have h := hr₀lt
        norm_num at h
        omega
      have lv : (Nat.digits 10 (9 * 2 ^ 0 * 5 ^ 0)).length ≤ 2 :=
        lenV_le
      omega
    have h4K : 4 * K = 8 * ((M - 1) / 9 + 1) := by rw [hK]; ring
    have hB' : 4 * K + 41 ≤ M := by
      have hBB := hB
      rw [← h4K] at hBB
      exact hBB
    rw [hz, hS, hE3]
    omega
  
  set C := List.replicate j 9 ++ List.replicate T 0 ++ [0]
      ++ List.replicate T 0 ++ List.replicate j 9 with hC
  have hCg : C.length = 2 * j + 2 * T + 1 := (center_repunit_len_sum j T).1
  have hCσ : C.sum = 18 * j := (center_repunit_len_sum j T).2
  have hCval3 : 3 ∣ Nat.ofDigits 10 C := by
    apply ofDigits_dvd_of_mem
    intro d hd
    have hd90 : d = 9 ∨ d = 0 := by
      rw [hC] at hd
      rcases List.mem_append.mp hd with hA | h9last
      · rcases List.mem_append.mp hA with hA | h0b
        · rcases List.mem_append.mp hA with hA | h00
          · rcases List.mem_append.mp hA with h9a | h0a
            · exact Or.inl (List.eq_of_mem_replicate h9a)
            · exact Or.inr (List.eq_of_mem_replicate h0a)
          · exact Or.inr (List.mem_singleton.mp h00)
        · exact Or.inr (List.eq_of_mem_replicate h0b)
      · exact Or.inl (List.eq_of_mem_replicate h9last)
    rcases hd90 with rfl | rfl
    · exact ⟨3, by norm_num⟩
    · exact dvd_zero _
  have hK1 : 1 ≤ K := by
    rw [hK]
    omega
  have hde_pal : D.reverse = D := hDpal.reverse_eq
  have hde81 : 81 ∣ Nat.ofDigits 10 D := by
    have h : ((Nat.ofDigits 10 D : ℕ) : ZMod 81) = 0 := by
      rw [cast_ofDigits]
      exact hD81
    exact (CharP.cast_eq_zero_iff (ZMod 81) 81 _).mp h
  have hde3 : 3 ∣ Nat.ofDigits 10 D := dvd_trans (by norm_num) hde81
  have hg3 : 3 ≤ 2 * j + 2 * T + 1 := by
    have hbnd := hbound
    omega
  have hgodd : Odd (2 * j + 2 * T + 1) := ⟨j + T, by ring⟩
  have hKcov : m * 3 ^ (1 - 4) ≤ 1 + 9 * (K / 2) := by
    rw [show (1 : ℕ) - 4 = 0 from rfl, pow_zero, mul_one]
    show M ≤ 1 + 9 * (K / 2)
    have hKhalf : K / 2 = (M - 1) / 9 + 1 := by
      rw [hK]
      omega
    rw [hKhalf]
    omega
  obtain ⟨s₀, hs0⟩ := hs0_v1 (le := lenD) (K := K)
    (g := 2 * j + 2 * T + 1) D hde_pal hde3 C hCval3
  obtain ⟨e', he', hdvdP⟩ := P_dvd_3m81 (m := m) (v := 1)
    (le := lenD) (K := K) (g := 2 * j + 2 * T + 1)
    hm3 hm10 D rfl C hCg hg3 hgodd hKcov s₀ hs0
  set MID := (List.range (2 * K)).map (pairDigit e') ++ C
      ++ ((List.range (2 * K)).map (pairDigit e')).reverse with hMID
  set P := Nat.ofDigits 10 (D ++ MID ++ D.reverse) with hP
  have hMIDpal : MID.Palindrome := mid_pal e' C (center_repunit_pal j T)
  have hMID10 : ∀ x ∈ MID, x < 10 := mid_lt10 e' he' C
    (center_repunit_lt10 j T)
  obtain ⟨hP0, hPpal, hPlen, hPσ⟩ := sandwich_spec_gen D MID hDne hD10
    (hD0 hDne) hMIDpal hMID10 rfl rfl
  have hMIDlen : MID.length = 4 * K + C.length := by
    rw [hMID, List.length_append, List.length_append, List.length_reverse,
      List.length_map, List.length_range]
    ring
  obtain ⟨rr, hrr⟩ := hXeven
  have h2T : 2 * T = X := by rw [hT]; omega
  have hlen : (Nat.digits 10 P).length = n - z := by
    rw [hPlen, hMIDlen, hCg]
    omega
  
  have hσP : (Nat.digits 10 P).sum
      = 4 * 81 * rhob 0 0 4 + 18 * (K + j) := by
    rw [hPσ, mid_sum e' he' C, hCσ, hDσ]
    ring
  have h3vd : 3 ∣ (Nat.digits 10 P).sum := by
    rw [hσP]
    apply Nat.dvd_add
    · exact dvd_mul_of_dvd_left (by norm_num : (3 : ℕ) ∣ 4 * 81) _
    · exact dvd_mul_of_dvd_left (by norm_num : (3 : ℕ) ∣ 18) _
  have hMdvd : M ∣ (Nat.digits 10 P).sum := by
    rw [hσP]
    have hmc_eq : (m + c) ≡ c [MOD M] := by
      have h0m : (m : ℕ) ≡ 0 [MOD M] := by
        show m % M = 0
        rw [← hM]
        exact Nat.mod_self M
      simpa using Nat.ModEq.add h0m (Nat.ModEq.rfl : c ≡ c [MOD M])
    have htarget : (K + j) ≡ (m + c) [MOD M] := hKj.trans hmc_eq.symm
    have hmod := Nat.ModEq.add
      (Nat.ModEq.rfl : 4 * 81 * rhob 0 0 4 ≡ 4 * 81 * rhob 0 0 4 [MOD M])
      (Nat.ModEq.mul_left 18 htarget)
    exact Nat.modEq_zero_iff_dvd.mp
      (hmod.trans (Nat.modEq_zero_iff_dvd.mpr hcdvd'))
  have hσ : n ∣ (Nat.digits 10 P).sum := by
    have h3M : (3 : ℕ).Coprime M := by
      rw [hM]
      exact hm3.symm
    have hjoin := h3M.mul_dvd_of_dvd_of_dvd h3vd hMdvd
    rw [hE3]
    exact hjoin
  
  have hPd : n ∣ P * 10 ^ z := by
    have h25 : 2 ^ 0 * 5 ^ 0 ∣ P := by
      have hle_big : max 0 0 ≤ lenD := by
        omega
      have hBP := B_dvd_P (le := lenD) (de := D) (MID := MID) rfl hD25
        hle_big
      rwa [hP]
    obtain ⟨w, hw⟩ := hdvdP
    have h3mP : 3 ^ 1 * m ∣ P := ⟨w, by rw [hw]; ring⟩
    have h := n_dvd_P_pow10_le (a := 0) (b := 0) (v := 1) (m := m) (z := 0)
      (a' := 0) (b' := 0) (P := P) h25 h3mP
      (by omega) (by omega) hm30
    rw [hz]
    simpa [hn] using h
  refine ⟨P, z, hP0, ?_, hPpal, ?_, hPd, hσ⟩
  · intro hz0
    omega
  · rw [hlen]
    omega


set_option maxHeartbeats 800000 in
def residualCase (a b v m : ℕ) : Prop :=
  v = 0
  ∨ (1 ≤ a ∧ b = 0 ∧ (11 ∣ m ∨ 101 ∣ m))
  ∨ (a = 0 ∧ 2 ≤ v ∧ v ≤ 4
      ∧ ¬ (8 * b + 44 ≤ 5 ^ b * m * 3 ^ (v - 2)) ∧ (b ≠ 0 ∨ m ≠ 1))
  ∨ (1 ≤ a ∧ 1 ≤ b ∧ 2 ≤ v ∧ v ≤ 4
      ∧ ¬ (36 * 2 ^ (a - 2) ≤ 2 * (2 ^ a * 5 ^ b * 3 ^ (v - 2) * m)))
  ∨ (1 ≤ a ∧ b = 0 ∧ 2 ≤ v ∧ v ≤ 4
      ∧ ¬ (4 * a + 6 ≤ 2 ^ a * 3 ^ (v - 2) * m))
  ∨ (1 ≤ a ∧ 1 ≤ b ∧ v = 1
      ∧ ¬ (4 * m + 39 + 36 * 2 ^ (a - 2) + (a + b)
          ≤ 2 * (2 ^ a * 5 ^ b * m)))
  ∨ (a = 0 ∧ 1 ≤ b ∧ v = 1 ∧ ¬ (4 * m + 8 * b + 41 ≤ 5 ^ b * m))
  ∨ (a = 0 ∧ b = 0 ∧ v = 1 ∧ ¬ (8 * ((m - 1) / 9 + 1) + 41 ≤ m))
  ∨ (2 ≤ a ∧ b = 0 ∧ v = 1
      ∧ ¬ (4 * m + 2 ^ a + 8 * a + 8 + 2 ^ a * m ≤ 3 * (2 ^ a * m)))
  ∨ (a = 1 ∧ b = 0 ∧ v = 1 ∧ ¬ (8 * ((m - 1) / 9 + 1) + 18 ≤ 2 * m))


set_option maxHeartbeats 800000 in
theorem A084017_of_residue (n : ℕ) (hn : n ≠ 0)
    (hres : ∀ a b v m : ℕ, n = 2 ^ a * 5 ^ b * 3 ^ v * m →
      m.Coprime 30 → residualCase a b v m →
      ∃ P z : ℕ, P ≠ 0
        ∧ (0 < z → 10 ∣ n)
        ∧ (Nat.digits 10 P).Palindrome
        ∧ (Nat.digits 10 P).length + z = n
        ∧ n ∣ P * 10 ^ z
        ∧ n ∣ (Nat.digits 10 P).sum) :
    ∃ P z : ℕ, P ≠ 0
      ∧ (0 < z → 10 ∣ n)
      ∧ (Nat.digits 10 P).Palindrome
      ∧ (Nat.digits 10 P).length + z = n
      ∧ n ∣ P * 10 ^ z
      ∧ n ∣ (Nat.digits 10 P).sum := by
  classical
  obtain ⟨a, b, v, m, hnd, hm30, _h2, _h5, _h3⟩ := decomp235 n hn
  have hm0 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0] at hm30
      exact absurd hm30 (by decide)
    · exact h0
  subst hnd
  by_cases hv0 : v = 0
  · exact hres a b v m rfl hm30 (Or.inl hv0)
  have hvD : v = 1 ∨ (2 ≤ v ∧ v ≤ 4) ∨ 5 ≤ v := by omega
  rcases hvD with rfl | ⟨hv2, hv4⟩ | hv5
  · 
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · rcases Nat.eq_zero_or_pos b with rfl | hb
      · 
        by_cases hB : 8 * ((m - 1) / 9 + 1) + 41 ≤ m
        · simpa using assemble_b00o hm0 hm30 hB
        · exact hres 0 0 1 m rfl hm30
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inl ⟨rfl, rfl, rfl, hB⟩))))))))
      · 
        by_cases hB : 4 * m + 8 * b + 41 ≤ 5 ^ b * m
        · simpa using assemble_v01o hb hm0 hm30 hB
        · exact hres 0 b 1 m rfl hm30
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inl ⟨rfl, hb, rfl, hB⟩)))))))
    · rcases Nat.eq_zero_or_pos b with rfl | hb
      · 
        by_cases hbad : 11 ∣ m ∨ 101 ∣ m
        · exact hres a 0 1 m rfl hm30
            (Or.inr (Or.inl ⟨ha, rfl, hbad⟩))
        · push_neg at hbad
          have hm11 : m.Coprime 11 :=
            (((by norm_num : Nat.Prime 11).coprime_iff_not_dvd).mpr
              hbad.1).symm
          have hm101 : m.Coprime 101 :=
            (((by norm_num : Nat.Prime 101).coprime_iff_not_dvd).mpr
              hbad.2).symm
          rcases Nat.lt_or_ge a 2 with ha1 | ha2
          · 
            have ha1' : a = 1 := by omega
            subst ha1'
            by_cases hB : 8 * ((m - 1) / 9 + 1) + 18 ≤ 2 * m
            · simpa using assemble_eb01a hm0 hm30 hm11 hm101 hB
            · exact hres 1 0 1 m rfl hm30
                (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr ⟨rfl, rfl, rfl, hB⟩)))))))))
          · 
            by_cases hB : 4 * m + 2 ^ a + 8 * a + 8 + 2 ^ a * m
                ≤ 3 * (2 ^ a * m)
            · simpa using assemble_eb01 ha2 hm0 hm30 hm11 hm101 hB
            · exact hres a 0 1 m rfl hm30
                (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inl ⟨ha2, rfl, rfl, hB⟩)))))))))
      · 
        by_cases hB : 4 * m + 39 + 36 * 2 ^ (a - 2) + (a + b)
            ≤ 2 * (2 ^ a * 5 ^ b * m)
        · simpa using assemble_zbig1 ha hb hm0 hm30 hB
        · exact hres a b 1 m rfl hm30
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inl ⟨ha, hb, rfl, hB⟩))))))
  · 
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · 
      by_cases h3p : b = 0 ∧ m = 1
      · obtain ⟨rfl, rfl⟩ := h3p
        simpa using assemble_3pow hv2
      · push_neg at h3p
        by_cases hB : 8 * b + 44 ≤ 5 ^ b * m * 3 ^ (v - 2)
        · simpa using assemble_v4o hm30 hv2 hv4 hB
        · have hne : b ≠ 0 ∨ m ≠ 1 := by
            by_cases hb0 : b = 0
            · exact Or.inr (h3p hb0)
            · exact Or.inl hb0
          exact hres 0 b v m rfl hm30
            (Or.inr (Or.inr (Or.inl ⟨rfl, hv2, hv4, hB, hne⟩)))
    · rcases Nat.eq_zero_or_pos b with rfl | hb
      · 
        by_cases hbad : 11 ∣ m ∨ 101 ∣ m
        · exact hres a 0 v m rfl hm30
            (Or.inr (Or.inl ⟨ha, rfl, hbad⟩))
        · push_neg at hbad
          have hm11 : m.Coprime 11 :=
            (((by norm_num : Nat.Prime 11).coprime_iff_not_dvd).mpr
              hbad.1).symm
          have hm101 : m.Coprime 101 :=
            (((by norm_num : Nat.Prime 101).coprime_iff_not_dvd).mpr
              hbad.2).symm
          by_cases hB : 4 * a + 6 ≤ 2 ^ a * 3 ^ (v - 2) * m
          · simpa using assemble_eb04 ha hm0 hv2 hv4 hm30 hm11 hm101 hB
          · exact hres a 0 v m rfl hm30
              (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inl ⟨ha, rfl, hv2, hv4, hB⟩)))))
      · 
        by_cases hB : 36 * 2 ^ (a - 2)
            ≤ 2 * (2 ^ a * 5 ^ b * 3 ^ (v - 2) * m)
        · simpa using assemble_zbig4 ha hb hm0 hv2 hv4 hm30 hB
        · exact hres a b v m rfl hm30
            (Or.inr (Or.inr (Or.inr
              (Or.inl ⟨ha, hb, hv2, hv4, hB⟩))))
  · 
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · rcases Nat.eq_zero_or_pos b with rfl | hb
      · 
        rcases eq_or_ne m 1 with rfl | hm1
        · have hv2' : 2 ≤ v := by omega
          simpa using assemble_3pow hv2'
        · have hm2 : 2 ≤ m := by omega
          simpa using assemble_v5 (b := 0) hm30 hv5 (Or.inl hm2)
      · 
        have hm : 2 ≤ m ∨ m = 1 ∧ 1 ≤ b := by
          rcases Nat.lt_or_ge m 2 with h | h
          · have hm1 : m = 1 := by omega
            exact Or.inr ⟨hm1, hb⟩
          · exact Or.inl h
        simpa using assemble_v5 (b := b) hm30 hv5 hm
    · rcases Nat.eq_zero_or_pos b with rfl | hb
      · 
        by_cases hbad : 11 ∣ m ∨ 101 ∣ m
        · exact hres a 0 v m rfl hm30
            (Or.inr (Or.inl ⟨ha, rfl, hbad⟩))
        · push_neg at hbad
          have hm11 : m.Coprime 11 :=
            (((by norm_num : Nat.Prime 11).coprime_iff_not_dvd).mpr
              hbad.1).symm
          have hm101 : m.Coprime 101 :=
            (((by norm_num : Nat.Prime 101).coprime_iff_not_dvd).mpr
              hbad.2).symm
          simpa using assemble_even0 ha hm0 hv5 hm30 hm11 hm101
      · 
        simpa using assemble_zbig ha hb hm0 hv5 hm30























variable {m : ℕ} [NeZero m]
variable {M : ℕ} [NeZero M]






end A084017


end A084017src

section A084017R2src





namespace A084017
open Finset List Nat BigOperators Pointwise


end A084017


namespace A084017
open Finset List Nat BigOperators Pointwise


end A084017


namespace A084017
open Finset List Nat BigOperators Pointwise
variable {M : ℕ} [NeZero M]


end A084017


namespace A084017
open Finset List Nat BigOperators Pointwise


end A084017

end A084017R2src

section SpecA084017src




end SpecA084017src

section PinnedTensrc





namespace PinnedTen
open Finset List Nat BigOperators Pointwise
open A084017






end PinnedTen

end PinnedTensrc


end OMA.A084017Port

theorem OMA.solution : OMA.R_oeis_a084017_R1_H1_R1.H4 := by
  intro n hres hn
  exact OMA.A084017Port.A084017.A084017_of_residue n hn hres
