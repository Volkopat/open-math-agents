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




theorem digit_sum_interval (t R : ℕ) (hR : R ≤ 9 * t) :
    ∃ d : ℕ → ℕ, (∀ i, d i ≤ 9) ∧ (∀ i, t ≤ i → d i = 0)
      ∧ (Finset.range t).sum d = R := by
  induction t generalizing R with
  | zero =>
    interval_cases R
    exact ⟨fun _ => 0, fun i => by simp, fun i _ => rfl, by simp⟩
  | succ t ih =>
    set d0 := min 9 R
    have hrest : R - d0 ≤ 9 * t := by
      by_cases h9 : 9 ≤ R
      · have : d0 = 9 := min_eq_left h9
        omega
      · have : d0 = R := min_eq_right (by omega)
        omega
    rcases ih (R - d0) hrest with ⟨e, he1, he2, he3⟩
    refine ⟨Function.update e t d0, ?_, ?_, ?_⟩
    · intro i
      by_cases hi : i = t
      · subst hi; simp [Function.update_self, d0]
      · rw [Function.update_of_ne hi]; exact he1 i
    · intro i hi
      have hi0 : i ≠ t := by omega
      rw [Function.update_of_ne hi0]
      exact he2 i (by omega)
    · rw [Finset.sum_range_succ, Function.update_self]
      have : (Finset.range t).sum (Function.update e t d0)
          = (Finset.range t).sum e := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Function.update_of_ne (by
          have := Finset.mem_range.mp hi; omega)]
      rw [this, he3]
      have hle : d0 ≤ R := Nat.min_le_right _ _
      omega


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


theorem exists_free_block (t R : ℕ) (hR : R ≤ 9 * t) :
    ∃ F : List ℕ, F.length = t ∧ (∀ x ∈ F, x ≤ 9) ∧ F.sum = R := by
  obtain ⟨d, hd9, _, hdsum⟩ := digit_sum_interval t R hR
  refine ⟨(List.range t).map d, by simp, ?_, ?_⟩
  · intro x hx
    rw [List.mem_map] at hx
    obtain ⟨i, _, rfl⟩ := hx
    exact hd9 i
  · have hsum : ((List.range t).map d).sum
        = (Finset.range t).sum d := by
      rw [Finset.sum_list_map_count]
      apply Finset.sum_congr (List.toFinset_range t)
      intro x hx
      rw [List.count_eq_one_of_mem List.nodup_range
            (List.mem_range.mpr (Finset.mem_range.mp hx)), one_smul]
    rw [hsum, hdsum]

def twt (m L k : ℕ) : ZMod m := palW m L (2 * k) - palW m L (2 * k + 1)


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


end A084017


namespace A084017
open Finset List Nat BigOperators Pointwise


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


end A084017

namespace A084017
open Finset List Nat BigOperators Pointwise


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


end A084017


namespace A084017
open Finset List Nat BigOperators Pointwise


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


end A084017
namespace A084017
open Finset List Nat BigOperators Pointwise

set_option maxHeartbeats 800000 in
theorem hs0_v0 {le K g : ℕ} (de : List ℕ) (C : List ℕ) :
    ∃ s₀ : ℕ,
      (Nat.ofDigits (10 : ZMod (3 ^ 0)) de
          + Nat.ofDigits (10 : ZMod (3 ^ 0)) de.reverse
              * (10 : ZMod (3 ^ 0)) ^ (le + (4 * K + g)))
        + (10 : ZMod (3 ^ 0)) ^ le
          * (Nat.ofDigits (10 : ZMod (3 ^ 0)) C
              * (10 : ZMod (3 ^ 0)) ^ (2 * K)
            + (9 * ∑ k ∈ Finset.range K, palW (3 ^ 0) (4 * K + g) (2 * k + 1)
              + 81 * (s₀ : ZMod (3 ^ 0)))) = 0 := by
  refine ⟨0, ?_⟩
  rw [pow_zero]
  exact Subsingleton.elim _ _

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


end A084017



namespace A084017


set_option maxHeartbeats 800000 in
def tz (x : ℕ) : ℕ := ((Nat.digits 10 x).takeWhile (· = 0)).length


set_option maxHeartbeats 800000 in
theorem tz_zero_of_not_dvd {n : ℕ} (h : ¬ 10 ∣ n) : tz n = 0 := by
  have hmod : n % 10 ≠ 0 := fun e => h (Nat.dvd_of_mod_eq_zero e)
  unfold tz
  cases hd : Nat.digits 10 n with
  | nil => rfl
  | cons d ds =>
    have hn0 : 0 < n := Nat.pos_of_ne_zero (fun e => by
      rw [e, Nat.digits_zero] at hd
      exact nomatch hd)
    have hdmod : n % 10 = d := by
      have hdd := Nat.digits_def' (b := 10) (by norm_num) hn0
      rw [hd] at hdd
      exact (List.cons.inj hdd).1.symm
    rw [List.takeWhile_cons]
    have hd0 : d ≠ 0 := fun e => hmod (hdmod.trans e)
    simp [hd0]


set_option maxHeartbeats 800000 in
theorem not10_2a3vm {a v m : ℕ} (hm30 : m.Coprime 30) :
    ¬ 10 ∣ 2 ^ a * 3 ^ v * m := by
  intro h
  have h5 : 5 ∣ 2 ^ a * 3 ^ v * m :=
    dvd_trans (by norm_num : (5 : ℕ) ∣ 10) h
  rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 5)).mp h5
      with h5a | h5m
  · rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 5)).mp h5a
        with h52 | h53
    · exact absurd (Nat.Prime.dvd_of_dvd_pow
        (by norm_num : Nat.Prime 5) h52) (by decide)
    · exact absurd (Nat.Prime.dvd_of_dvd_pow
        (by norm_num : Nat.Prime 5) h53) (by decide)
  · have hcop : m.Coprime 5 :=
      hm30.coprime_dvd_right (by norm_num : (5 : ℕ) ∣ 30)
    have hg : (5 : ℕ) ∣ Nat.gcd m 5 := Nat.dvd_gcd h5m (dvd_refl 5)
    rw [hcop] at hg
    exact absurd hg (by decide)


set_option maxHeartbeats 800000 in
abbrev witSpec (n z : ℕ) (L : List ℕ) : Prop :=
  (∀ x ∈ L, x < 10) ∧ L ≠ [] ∧ L.getLast? ≠ some 0
    ∧ L.Palindrome ∧ L.length + z = n
    ∧ z = tz n ∧ n ∣ Nat.ofDigits 10 L * 10 ^ z ∧ n ∣ L.sum


set_option maxHeartbeats 800000 in
abbrev finGoal (n : ℕ) : Prop :=
  ∃ P z : ℕ, P ≠ 0
    ∧ z = tz n
    ∧ (Nat.digits 10 P).Palindrome
    ∧ (Nat.digits 10 P).length + z = n
    ∧ n ∣ P * 10 ^ z
    ∧ n ∣ (Nat.digits 10 P).sum


set_option maxHeartbeats 800000 in
abbrev relaxedGoal (n : ℕ) : Prop :=
  ∃ P z : ℕ, P ≠ 0
    ∧ (0 < z → 10 ∣ n)
    ∧ (Nat.digits 10 P).Palindrome
    ∧ (Nat.digits 10 P).length + z = n
    ∧ n ∣ P * 10 ^ z
    ∧ n ∣ (Nat.digits 10 P).sum


set_option maxHeartbeats 800000 in
theorem finGoal_of_relaxed {n : ℕ} (h10 : ¬ 10 ∣ n) :
    relaxedGoal n → finGoal n := by
  rintro ⟨P, z, hP, hz10, hpal, hlen, hdvd, hσ⟩
  have hz0 : z = 0 := by
    rcases Nat.eq_zero_or_pos z with e | hp
    · exact e
    · exact absurd (hz10 hp) h10
  subst hz0
  refine ⟨P, 0, hP, (tz_zero_of_not_dvd h10).symm, hpal, ?_, ?_, hσ⟩
  · simpa using hlen
  · simpa using hdvd






















variable {m : ℕ} [NeZero m]
variable {M : ℕ} [NeZero M]


set_option maxHeartbeats 800000 in
theorem bnd72 (m : ℕ) : 72 * ((m - 1) / 9 + 1) ≤ 8 * (m - 1) + 72 := by
  have h := Nat.div_add_mod (m - 1) 9
  omega


set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
def witTabOpen : List (ℕ × ℕ × List ℕ) := [
  (22, 0, [2,0,0,0,0,0,0,0,0,0,9,9,0,0,0,0,0,0,0,0,0,2]),
  (44, 0, [4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,9,9,9,9,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4]),
  (66, 0, [4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,9,9,9,9,9,9,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4]),
  (14, 0, [2,8,1,3,0,0,0,0,0,0,3,1,8,2]),
  (19, 0, [6,9,5,6,1,0,0,0,0,3,0,0,0,0,1,6,5,9,6]),
  (26, 0, [2,9,2,9,9,9,3,0,0,9,0,0,0,0,0,0,9,0,0,3,9,9,9,2,9,2]),
  (28, 0, [2,3,1,9,9,9,5,0,0,9,0,0,9,0,0,9,0,0,9,0,0,5,9,9,9,1,3,2]),
  (34, 0, [6,9,9,9,9,9,9,9,9,9,3,9,3,0,0,0,0,0,0,0,0,3,9,3,9,9,9,9,9,9,9,9,9,6]),
  (37, 0, [2,9,9,9,9,5,0,0,0,0,5,0,0,0,0,5,0,0,5,0,0,5,0,0,0,0,5,0,0,0,0,5,9,9,9,9,2]),
  (38, 0, [2,9,5,9,2,9,9,9,9,9,6,0,9,0,9,0,0,9,9,9,9,0,0,9,0,9,0,6,9,9,9,9,9,2,9,5,9,2]),
  (46, 0, [6,5,1,0,0,9,9,9,9,9,9,9,9,0,9,0,9,9,9,0,9,0,9,9,0,9,0,9,9,9,0,9,0,9,9,9,9,9,9,9,9,0,0,1,5,6]),
  (7, 0, [1,0,3,6,3,0,1]),
  (11, 0, [1,0,1,0,9,0,9,0,1,0,1]),
  (13, 0, [1,0,0,0,2,7,6,7,2,0,0,0,1]),
  (17, 0, [2,7,5,9,0,0,0,0,5,0,0,0,0,9,5,7,2]),
  (23, 0, [6,8,1,9,0,0,0,0,0,9,0,3,0,9,0,0,0,0,0,9,1,8,6]),
  (29, 0, [2,9,7,9,9,9,9,0,0,9,0,0,9,0,1,0,9,0,0,9,0,0,9,9,9,9,7,9,2]),
  (31, 0, [6,9,3,9,9,9,9,9,3,1,0,0,0,0,9,3,9,0,0,0,0,1,3,9,9,9,9,9,3,9,6]),
  (41, 0, [2,9,9,9,9,9,0,0,0,0,6,0,0,0,0,0,0,5,0,3,1,3,0,5,0,0,0,0,0,0,6,0,0,0,0,9,9,9,9,9,2]),
  (43, 0, [2,9,7,9,9,9,9,9,9,9,9,0,0,9,9,0,9,9,9,9,4,5,4,9,9,9,9,0,9,9,0,0,9,9,9,9,9,9,9,9,7,9,2]),
  (47, 0, [6,9,7,6,9,9,9,9,9,9,9,9,9,0,9,0,9,9,9,0,9,0,9,3,9,0,9,0,9,9,9,0,9,0,9,9,9,9,9,9,9,9,9,6,7,9,6]),
  (49, 0, [6,7,9,9,8,9,9,9,9,9,9,9,3,0,0,0,0,0,0,0,9,0,7,0,3,0,7,0,9,0,0,0,0,0,0,0,3,9,9,9,9,9,9,9,8,9,9,7,6]),
  (59, 0, [2,9,9,9,9,9,9,9,9,9,9,9,9,9,9,0,9,9,9,9,9,9,8,0,8,6,0,0,0,5,0,0,0,6,8,0,8,9,9,9,9,9,9,0,9,9,9,9,9,9,9,9,9,9,9,9,9,9,2]),
  (67, 0, [2,9,8,9,9,9,9,9,4,0,0,0,0,0,0,0,0,0,0,5,0,0,9,0,0,0,9,0,0,9,0,0,0,1,0,0,0,9,0,0,9,0,0,0,9,0,0,5,0,0,0,0,0,0,0,0,0,0,4,9,9,9,9,9,8,9,2]),
  (83, 0, [4,0,9,2,9,9,2,0,0,9,9,9,9,9,9,9,9,9,9,9,9,9,9,0,9,9,9,9,9,0,9,9,9,9,7,0,0,0,0,0,0,0,0,0,0,0,0,0,7,9,9,9,9,0,9,9,9,9,9,0,9,9,9,9,9,9,9,9,9,9,9,9,9,9,0,0,2,9,9,2,9,0,4])
  ]


set_option maxHeartbeats 800000 in
def witLO (n : ℕ) : ℕ × List ℕ :=
  match witTabOpen.find? (fun t => t.1 == n) with
  | some (_, z, L) => (z, L)
  | none => (0, [])


set_option maxHeartbeats 800000 in
theorem wit_sound_of {n : ℕ}
    (h : decide (witSpec n (witLO n).1 (witLO n).2) = true) :
    finGoal n := by
  obtain ⟨h10, hne, hgl, hpal, hlen, hz10, hdvd, hσ⟩ :=
    of_decide_eq_true h
  have hlast : ∀ h' : (witLO n).2 ≠ [], ((witLO n).2).getLast h' ≠ 0 := by
    intro h' hh
    apply hgl
    rw [List.getLast?_eq_getLast_of_ne_nil h']
    rw [hh]
  have hdig : Nat.digits 10 (Nat.ofDigits 10 (witLO n).2) = (witLO n).2 :=
    Nat.digits_ofDigits 10 (by norm_num) _ h10 hlast
  refine ⟨Nat.ofDigits 10 (witLO n).2, (witLO n).1, ?_, hz10, ?_, ?_, ?_, ?_⟩
  · intro h0
    rw [h0, Nat.digits_zero] at hdig
    exact hne hdig.symm
  · rw [hdig]; exact hpal
  · rw [hdig]; exact hlen
  · exact hdvd
  · rw [hdig]; exact hσ


set_option maxHeartbeats 800000 in
def residualHard (a b v m : ℕ) : Prop :=
  1 ≤ a ∧ b = 0 ∧ (11 ∣ m ∨ 101 ∣ m)





end A084017


end A084017src

section A084017R2src





namespace A084017
open Finset List Nat BigOperators Pointwise


theorem ofDigits_cons' {α : Type*} [Semiring α] (b : α) (d : ℕ)
    (L : List ℕ) :
    Nat.ofDigits b (d :: L) = (d : α) + b * Nat.ofDigits b L := rfl


theorem ofDigits_neg1_rev (L : List ℕ) :
    Nat.ofDigits (-1 : ZMod 11) L.reverse
      = (-1 : ZMod 11) ^ (L.length + 1)
          * Nat.ofDigits (-1 : ZMod 11) L := by
  induction L with
  | nil => simp [Nat.ofDigits]
  | cons x L ih =>
    rw [List.reverse_cons, ofDigits_append', List.length_reverse,
      ofDigits_singleton', ih, List.length_cons, ofDigits_cons']
    have hpow : (-1 : ZMod 11) ^ (L.length + 2) = (-1) ^ L.length := by
      rw [pow_add]
      have h2 : (-1 : ZMod 11) ^ 2 = 1 := by norm_num
      rw [h2, mul_one]
    rw [show L.length + 1 + 1 = L.length + 2 from rfl, hpow, pow_succ]
    ring


theorem ofDigits_palPair11 (A : List ℕ) :
    Nat.ofDigits (10 : ZMod 11) (A ++ A.reverse) = 0 := by
  have h10 : (10 : ZMod 11) = -1 := by decide
  rw [h10, ofDigits_append', ofDigits_neg1_rev]
  have e : (-1 : ZMod 11) ^ A.length
        * ((-1 : ZMod 11) ^ (A.length + 1)
            * Nat.ofDigits (-1 : ZMod 11) A)
      = -Nat.ofDigits (-1 : ZMod 11) A := by
    rw [← mul_assoc, ← pow_add,
      show A.length + (A.length + 1) = 2 * A.length + 1 from by ring,
      pow_succ, pow_mul]
    have h2 : (-1 : ZMod 11) ^ 2 = 1 := by norm_num
    rw [h2, one_pow, one_mul]
    ring
  rw [e, add_neg_cancel]


theorem ofDigits_evenPal11 {L : List ℕ} (hL : L.Palindrome)
    (hEv : Even L.length) :
    Nat.ofDigits (10 : ZMod 11) L = 0 := by
  set n := L.length / 2 with hn
  have hnn : n + n = L.length := by
    obtain ⟨c, hc⟩ := hEv; omega
  have hsplit : L = L.take n ++ (L.take n).reverse := by
    have e1 : L.drop n = (L.take n).reverse := by
      have e2 : L.reverse.take n = (L.drop (L.length - n)).reverse :=
        List.take_reverse
      rw [hL.reverse_eq] at e2
      have hLmn : L.length - n = n := by omega
      rw [hLmn] at e2
      rw [e2]
      exact (List.reverse_reverse _).symm
    have e3 : L = L.take n ++ L.drop n := (List.take_append_drop n L).symm
    rw [e1] at e3
    exact e3
  conv_lhs => rw [hsplit]
  exact ofDigits_palPair11 _


theorem palW_mod11 {L i : ℕ} (hEv : Even L) (hi : i < L) :
    palW 11 L i = 0 := by
  unfold palW
  have h10 : (10 : ZMod 11) = -1 := by decide
  rw [h10]
  obtain ⟨c, hc⟩ := hEv
  rcases Nat.even_or_odd i with he | ho
  · have ho' : Odd (L - 1 - i) := by
      obtain ⟨k, hk⟩ := he
      exact ⟨c - k - 1, by omega⟩
    rw [he.neg_one_pow, ho'.neg_one_pow]
    norm_num
  · have he' : Even (L - 1 - i) := by
      obtain ⟨k, hk⟩ := ho
      exact ⟨c - k - 1, by omega⟩
    rw [ho.neg_one_pow, he'.neg_one_pow]
    norm_num


theorem ofDigits_append_zero {α : Type*} [Semiring α] (b : α) (D : List ℕ) :
    Nat.ofDigits b (D ++ [0]) = Nat.ofDigits b D := by
  rw [ofDigits_append', ofDigits_singleton']
  simp


end A084017


namespace A084017
open Finset List Nat BigOperators Pointwise


theorem repunit99_dvd (s : ℕ) : 99 ∣ 10 ^ (2 * s) - 1 := by
  have h : (10 : ℕ) ^ (2 * s) ≡ 1 [MOD 99] := by
    have h10 : (10 : ℕ) ^ 2 ≡ 1 [MOD 99] := by decide
    have := Nat.ModEq.pow s h10
    rwa [← pow_mul, one_pow] at this
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp h.symm


theorem repunit99_mul (s : ℕ) :
    99 * ((10 ^ (2 * s) - 1) / 99) = 10 ^ (2 * s) - 1 :=
  Nat.mul_div_cancel' (repunit99_dvd s)


theorem repunit_eq_11_mul_repunit99 (s : ℕ) :
    (10 ^ (2 * s) - 1) / 9 = 11 * ((10 ^ (2 * s) - 1) / 99) := by
  have h := repunit99_mul s
  have h' := nine_mul_repunit (2 * s)
  omega


theorem repunit99_succ (s : ℕ) :
    (10 ^ (2 * (s + 1)) - 1) / 99 = 100 * ((10 ^ (2 * s) - 1) / 99) + 1 := by
  have h99 := repunit99_mul s
  have h99' := repunit99_mul (s + 1)
  have e : 10 ^ (2 * (s + 1)) - 1
      = 100 * (10 ^ (2 * s) - 1) + 99 := by
    have hp : 1 ≤ 10 ^ (2 * s) := Nat.one_le_pow _ _ (by norm_num)
    rw [show 2 * (s + 1) = 2 * s + 2 from by ring, pow_add,
      show (10 : ℕ) ^ 2 = 100 from by norm_num]
    omega
  omega


theorem repunit99_coprime100 {s : ℕ} (hs : 1 ≤ s) :
    Nat.Coprime ((10 ^ (2 * s) - 1) / 99) 100 := by
  obtain ⟨s, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  rw [repunit99_succ]
  have h : (100 : ℕ).Coprime (1 + ((10 ^ (2 * s) - 1) / 99) * 100) :=
    (Nat.coprime_add_mul_right_right 100 1 _).mpr (Nat.coprime_one_right 100)
  have e : 100 * ((10 ^ (2 * s) - 1) / 99) + 1
      = 1 + ((10 ^ (2 * s) - 1) / 99) * 100 := by ring
  rw [e]
  exact h.symm


theorem repunit99_gcd (a b : ℕ) :
    Nat.gcd ((10 ^ (2 * a) - 1) / 99) ((10 ^ (2 * b) - 1) / 99)
      = (10 ^ (2 * Nat.gcd a b) - 1) / 99 := by
  have h99a := repunit99_mul a
  have h99b := repunit99_mul b
  have h99g := repunit99_mul (Nat.gcd a b)
  have h := Nat.gcd_mul_left 99 ((10 ^ (2 * a) - 1) / 99)
    ((10 ^ (2 * b) - 1) / 99)
  rw [h99a, h99b] at h
  have e : Nat.gcd (10 ^ (2 * a) - 1) (10 ^ (2 * b) - 1)
      = 10 ^ (2 * Nat.gcd a b) - 1 := by
    rw [Nat.pow_sub_one_gcd_pow_sub_one, Nat.gcd_mul_left]
  rw [e, ← h99g] at h
  exact (Nat.mul_left_cancel (by norm_num : 0 < 99) h).symm


theorem repunit99_one : (10 ^ (2 * 1) - 1) / 99 = 1 := by norm_num


end A084017


namespace A084017
open Finset List Nat BigOperators Pointwise
variable {M : ℕ} [NeZero M]


theorem gadget_extract3_q11 {K g : ℕ} (hM10 : M.Coprime 10) (h11M : 11 ∣ M)
    (hg : 4 ≤ g) (hg4 : g % 4 = 0)
    (hK : M ≤ 1 + 9 * (K / 2)) (t : ZMod M)
    (ht : (ZMod.castHom h11M (ZMod 11)) t = 0) :
    ∃ e : ℕ → ℕ, (∀ k, e k ≤ 9)
      ∧ (∑ k ∈ Finset.range K, (e k : ZMod M)
          * (((10 : ℕ) ^ (2 * k)
              * ((10 ^ (4 * K + g - 2 - 4 * k) - 1) / 9) : ℕ) : ZMod M))
          = t := by
  set L := 4 * K + g with hL
  set r := K / 2 with hr
  set M₁ := M / 11 with hM₁
  have hM11' : M = 11 * M₁ := (Nat.mul_div_cancel' h11M).symm
  have hM₁pos : 0 < M₁ := by
    have h1 : 11 ≤ M := Nat.le_of_dvd (NeZero.pos M) h11M
    omega
  haveI : NeZero M₁ := ⟨by omega⟩
  
  set u : ℕ → ℕ := fun i =>
    if i < K then 10 ^ (2 * i) * ((10 ^ (L - 2 - 4 * i) - 1) / 99) else 1 with hu
  set w : ℕ → ZMod M₁ := fun i => (u i : ZMod M₁) with hw
  
  
  have hgcd : ∀ i, Nat.gcd (Nat.gcd (u (2 * i)) (u (2 * i + 1))) M₁ = 1 := by
    intro i
    by_cases hi : 2 * i + 1 < K
    · rw [hu]; dsimp only
      rw [if_pos (by omega : 2 * i < K), if_pos hi]
      obtain ⟨c, hc⟩ : ∃ c, g = 4 * c := ⟨g / 4, by omega⟩
      have hDev1 : 2 ∣ L - 2 - 4 * (2 * i) := by
        refine ⟨2 * K + 2 * c - 1 - 4 * i, ?_⟩
        rw [hL]
        omega
      have hDev2 : 2 ∣ L - 2 - 4 * (2 * i + 1) := by
        refine ⟨2 * K + 2 * c - 1 - 2 * (2 * i + 1), ?_⟩
        rw [hL]
        omega
      have hD1 : 1 ≤ L - 2 - 4 * (2 * i) := by rw [hL]; omega
      have hD2 : 1 ≤ L - 2 - 4 * (2 * i + 1) := by rw [hL]; omega
      have he3 : ∀ d : ℕ, 2 ∣ d → (10 ^ d - 1) / 99
          = (10 ^ (2 * (d / 2)) - 1) / 99 := fun d hd => by
        obtain ⟨s, rfl⟩ := hd
        rw [show 2 * s / 2 = s from by omega]
      
      have hs1 : (L - 2 - 4 * (2 * i)) / 2
          = (L - 2 - 4 * (2 * i + 1)) / 2 + 2 := by
        obtain ⟨x1, hx1⟩ := hDev1
        obtain ⟨x2, hx2⟩ := hDev2
        omega
      have hsodd : Odd ((L - 2 - 4 * (2 * i + 1)) / 2) := by
        refine ⟨K + c - 2 - 2 * i, ?_⟩
        have e : L - 2 - 4 * (2 * i + 1)
            = 2 * (2 * K + 2 * c - 3 - 4 * i) := by
          rw [hL]; omega
        rw [e, show 2 * (2 * K + 2 * c - 3 - 4 * i) / 2
            = 2 * K + 2 * c - 3 - 4 * i from by omega]
        omega
      have hgg : Nat.gcd (10 ^ (2 * (2 * i))
          * ((10 ^ (L - 2 - 4 * (2 * i)) - 1) / 99))
          (10 ^ (2 * (2 * i + 1))
            * ((10 ^ (L - 2 - 4 * (2 * i + 1)) - 1) / 99))
          = 10 ^ (4 * i) * ((10 ^ (2 * Nat.gcd
              ((L - 2 - 4 * (2 * i)) / 2)
              ((L - 2 - 4 * (2 * i + 1)) / 2)) - 1) / 99) := by
        have e1 : 2 * (2 * i + 1) = 4 * i + 2 := by ring
        have e2 : 2 * (2 * i) = 4 * i := by ring
        rw [e1, e2, pow_add, Nat.mul_assoc, Nat.gcd_mul_left]
        have hDs1 : 1 ≤ (L - 2 - 4 * (2 * i)) / 2 := by omega
        rw [he3 _ hDev1]
        have hc10 : Nat.Coprime
            ((10 ^ (2 * ((L - 2 - 4 * (2 * i)) / 2)) - 1) / 99) (10 ^ 2) :=
          repunit99_coprime100 hDs1
        rw [show Nat.gcd ((10 ^ (2 * ((L - 2 - 4 * (2 * i)) / 2)) - 1) / 99)
            (10 ^ 2 * ((10 ^ (L - 2 - 4 * (2 * i + 1)) - 1) / 99))
            = Nat.gcd (10 ^ 2 * ((10 ^ (L - 2 - 4 * (2 * i + 1)) - 1) / 99))
              ((10 ^ (2 * ((L - 2 - 4 * (2 * i)) / 2)) - 1) / 99)
            from Nat.gcd_comm _ _]
        rw [Nat.Coprime.gcd_mul_left_cancel
          ((10 ^ (L - 2 - 4 * (2 * i + 1)) - 1) / 99) hc10.symm]
        rw [Nat.gcd_comm, he3 _ hDev2, repunit99_gcd]
      rw [hgg]
      have hg1 : Nat.gcd ((L - 2 - 4 * (2 * i)) / 2)
          ((L - 2 - 4 * (2 * i + 1)) / 2) = 1 := by
        rw [hs1, Nat.gcd_self_add_left]
        obtain ⟨c2, hc2⟩ := hsodd
        rw [hc2, Nat.gcd_comm]
        exact Nat.coprime_iff_gcd_eq_one.mp
          (Nat.coprime_two_right.mpr ⟨c2, rfl⟩)
      rw [hg1, repunit99_one, mul_one, Nat.gcd_comm]
      have hM10₁ : M₁.Coprime 10 :=
        Nat.Coprime.coprime_dvd_left ⟨11, by omega⟩ hM10
      exact Nat.coprime_iff_gcd_eq_one.mp (hM10₁.pow_right (4 * i))
    · rw [hu]; dsimp only
      rw [if_neg (by omega : ¬ 2 * i + 1 < K)]
      simp
  have haw : ∀ i, w i = (u i : ZMod M₁) := fun i => rfl
  have hS0 : (0 : ZMod M₁) ∈ ({0} : Finset (ZMod M₁)) :=
    Finset.mem_singleton_self 0
  have hcard : ({0} : Finset (ZMod M₁)).card = 1 := Finset.card_singleton 0
  have hM₁le : M₁ ≤ 1 + 9 * (K / 2) := by
    have h := hK
    omega
  have hcover : ({0} : Finset (ZMod M₁))
      + ∑ i ∈ Finset.range (2 * r), seg (w i) 9 = Finset.univ :=
    covers_univ (m := M₁) haw hgcd hS0 (r := r) (by rw [hcard]; omega)
  
  have h11tv : 11 ∣ t.val := by
    have hc : ((t.val : ℕ) : ZMod 11)
        = (ZMod.castHom h11M (ZMod 11)) t := by
      have h2 : t = ((t.val : ℕ) : ZMod M) :=
        ((ZMod.natCast_val t).trans (ZMod.cast_id _ _)).symm
      conv_rhs => rw [h2]
      rw [map_natCast]
    rw [← hc] at ht
    exact (CharP.cast_eq_zero_iff (ZMod 11) 11 _).mp ht
  set t₁ : ℕ := t.val / 11 with ht₁
  have htt : 11 * t₁ = t.val := Nat.mul_div_cancel' h11tv
  have hcover_t : ((t₁ : ℕ) : ZMod M₁) ∈ ({0} : Finset (ZMod M₁))
      + ∑ i ∈ Finset.range (2 * r), seg (w i) 9 := by
    rw [hcover]; exact Finset.mem_univ _
  rw [Finset.mem_add] at hcover_t
  obtain ⟨s, hs, c', hc', hsum⟩ := hcover_t
  rw [Finset.mem_singleton] at hs
  obtain ⟨d, hd, hcx⟩ := mem_sum_seg hc'
  
  have hsum₁ : ∑ k ∈ Finset.range (2 * r), (d k : ZMod M₁) * w k
      = ((t₁ : ℕ) : ZMod M₁) := by
    rw [← hcx, ← hsum, hs, zero_add]
  
  refine ⟨fun k => if k < 2 * r then d k else 0, ?_, ?_⟩
  · intro k
    by_cases hk : k < 2 * r
    · simp only [hk, ite_true]; exact hd k
    · simp only [hk, ite_false]; exact Nat.zero_le 9
  · 
    have hai : ∀ k, k < K →
        (10 : ℕ) ^ (2 * k) * ((10 ^ (L - 2 - 4 * k) - 1) / 9)
          = 11 * (10 ^ (2 * k) * ((10 ^ (L - 2 - 4 * k) - 1) / 99)) := by
      intro k hk
      have hD : 2 ∣ L - 2 - 4 * k := by
        obtain ⟨c, hc⟩ : ∃ c, g = 4 * c := ⟨g / 4, by omega⟩
        refine ⟨2 * K + 2 * c - 1 - 2 * k, ?_⟩
        rw [hL]
        omega
      obtain ⟨s', hs'⟩ := hD
      have e : L - 2 - 4 * k = 2 * s' := by omega
      rw [e, repunit_eq_11_mul_repunit99, ← e]
      ring
    
    have hsub : ∑ k ∈ Finset.range K,
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
    have hcast : (∑ k ∈ Finset.range (2 * r), (d k : ZMod M)
        * (((10 : ℕ) ^ (2 * k)
            * ((10 ^ (4 * K + g - 2 - 4 * k) - 1) / 9) : ℕ) : ZMod M))
        = ((11 * ∑ k ∈ Finset.range (2 * r),
            d k * (10 ^ (2 * k) * ((10 ^ (4 * K + g - 2 - 4 * k) - 1) / 99))
          : ℕ) : ZMod M) := by
      conv_rhs => rw [Nat.cast_mul, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      rw [hai k (by omega)]
      push_cast
      ring
    rw [hcast]
    
    have hSval : 11 * ∑ k ∈ Finset.range (2 * r),
        d k * (10 ^ (2 * k) * ((10 ^ (4 * K + g - 2 - 4 * k) - 1) / 99))
        ≡ 11 * t₁ [MOD M] := by
      have hme : ((∑ k ∈ Finset.range (2 * r),
          d k * (10 ^ (2 * k) * ((10 ^ (4 * K + g - 2 - 4 * k) - 1) / 99))
          : ℕ) : ZMod M₁) = ((t₁ : ℕ) : ZMod M₁) := by
        rw [Nat.cast_sum]
        rw [← hsum₁]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [Finset.mem_range] at hk
        rw [Nat.cast_mul, hw, hu]; dsimp only
        rw [if_pos (by omega : k < K)]
      have hv1 : (∑ k ∈ Finset.range (2 * r),
          d k * (10 ^ (2 * k) * ((10 ^ (4 * K + g - 2 - 4 * k) - 1) / 99)))
          ≡ t₁ [MOD M₁] := by
        have hv2 : ((∑ k ∈ Finset.range (2 * r),
            d k * (10 ^ (2 * k) * ((10 ^ (4 * K + g - 2 - 4 * k) - 1) / 99))
            : ℕ) : ZMod M₁).val
            = ((t₁ : ℕ) : ZMod M₁).val := congrArg ZMod.val hme
        rw [ZMod.val_natCast, ZMod.val_natCast] at hv2
        rw [Nat.ModEq, hv2]
      have hmul := Nat.ModEq.mul_left' 11 hv1
      rwa [← hM11'] at hmul
    have hcast2 : ((11 * ∑ k ∈ Finset.range (2 * r),
        d k * (10 ^ (2 * k) * ((10 ^ (4 * K + g - 2 - 4 * k) - 1) / 99))
        : ℕ) : ZMod M) = ((11 * t₁ : ℕ) : ZMod M) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hSval
    rw [hcast2, htt, ZMod.natCast_val, ZMod.cast_id]


theorem gadget_extract3_g4 {K g : ℕ} (hM10 : M.Coprime 10)
    (hM11 : ¬ (11 : ℕ) ∣ M)
    (hg : 4 ≤ g) (hg4 : g % 4 = 0)
    (hK : M ≤ 1 + 9 * (K / 2)) (t : ZMod M) :
    ∃ e : ℕ → ℕ, (∀ k, e k ≤ 9)
      ∧ (∑ k ∈ Finset.range K, (e k : ZMod M)
          * (((10 : ℕ) ^ (2 * k)
              * ((10 ^ (4 * K + g - 2 - 4 * k) - 1) / 9) : ℕ) : ZMod M))
          = t := by
  set L := 4 * K + g with hL
  set r := K / 2 with hr
  set a : ℕ → ℕ := fun i =>
    if i < K then 10 ^ (2 * i) * ((10 ^ (L - 2 - 4 * i) - 1) / 9) else 1 with ha
  set w : ℕ → ZMod M := fun i => (a i : ZMod M) with hw
  have hDg : ∀ i, 2 * i + 1 < K
      → Nat.gcd (L - 2 - 4 * (2 * i)) (L - 2 - 4 * (2 * i + 1)) = 2 := by
    intro i hi
    obtain ⟨c, hc⟩ : ∃ c, g = 4 * c := ⟨g / 4, by omega⟩
    have hD2 : L - 2 - 4 * (2 * i) = (L - 2 - 4 * (2 * i + 1)) + 4 := by omega
    rw [hD2, Nat.gcd_self_add_left]
    have hmod4 : (L - 2 - 4 * (2 * i + 1)) % 4 = 2 := by rw [hL]; omega
    rw [Nat.gcd_rec, hmod4]
    decide
  have haw : ∀ i, w i = (a i : ZMod M) := fun i => rfl
  have hM11' : M.Coprime 11 :=
    (((by norm_num : Nat.Prime 11).coprime_iff_not_dvd).mpr hM11).symm
  have hgcd : ∀ i, Nat.gcd (Nat.gcd (a (2 * i)) (a (2 * i + 1))) M = 1 := by
    intro i
    by_cases hi : 2 * i + 1 < K
    · rw [ha]; dsimp only
      rw [if_pos (by omega : 2 * i < K), if_pos hi]
      have hD1 : 1 ≤ L - 2 - 4 * (2 * i) := by rw [hL]; omega
      have hD2 : 1 ≤ L - 2 - 4 * (2 * i + 1) := by rw [hL]; omega
      have hg : Nat.gcd (10 ^ (2 * (2 * i))
          * ((10 ^ (L - 2 - 4 * (2 * i)) - 1) / 9))
          (10 ^ (2 * (2 * i + 1))
            * ((10 ^ (L - 2 - 4 * (2 * i + 1)) - 1) / 9))
          = 10 ^ (4 * i) * ((10 ^ Nat.gcd (L - 2 - 4 * (2 * i))
              (L - 2 - 4 * (2 * i + 1)) - 1) / 9) := by
        have e1 : 2 * (2 * i + 1) = 4 * i + 2 := by ring
        have e2 : 2 * (2 * i) = 4 * i := by ring
        rw [e1, e2, pow_add, Nat.mul_assoc, Nat.gcd_mul_left]
        have hc10 : Nat.Coprime ((10 ^ (L - 2 - 4 * (2 * i)) - 1) / 9)
            (10 ^ 2) :=
          (repunit_coprime10 hD1).pow_right 2
        rw [show Nat.gcd ((10 ^ (L - 2 - 4 * (2 * i)) - 1) / 9)
            (10 ^ 2 * ((10 ^ (L - 2 - 4 * (2 * i + 1)) - 1) / 9))
            = Nat.gcd (10 ^ 2 * ((10 ^ (L - 2 - 4 * (2 * i + 1)) - 1) / 9))
              ((10 ^ (L - 2 - 4 * (2 * i)) - 1) / 9) from Nat.gcd_comm _ _]
        rw [Nat.Coprime.gcd_mul_left_cancel
          ((10 ^ (L - 2 - 4 * (2 * i + 1)) - 1) / 9) hc10.symm]
        rw [Nat.gcd_comm, repunit_gcd]
      rw [hg, Nat.Coprime.gcd_mul_left_cancel _ (hM10.pow_right (4 * i)).symm]
      rw [hDg i hi, show ((10 ^ 2 - 1) / 9 : ℕ) = 11 from by norm_num,
        Nat.gcd_comm]
      exact Nat.coprime_iff_gcd_eq_one.mp hM11'
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


theorem extract3_target81_R2 {m v K g : ℕ} [NeZero m]
    (hm3 : m.Coprime 3) (hm10 : m.Coprime 10)
    (hg : 4 ≤ g) (hg4 : g % 4 = 0)
    (hK : m * 3 ^ (v - 4) ≤ 1 + 9 * (K / 2)) (t : ZMod m)
    (ht : ∀ h : 11 ∣ m, (ZMod.castHom h (ZMod 11)) t = 0)
    (s₀ : ℕ) :
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
  
  have h11_iff : 11 ∣ M ↔ 11 ∣ m := by
    rw [hM]
    have hc : Nat.Coprime 11 (3 ^ (v - 4)) :=
      Nat.Coprime.pow_right _ (by decide : Nat.Coprime 11 3)
    exact ⟨fun h => hc.dvd_of_dvd_mul_right h,
      fun h => dvd_mul_of_dvd_left h _⟩
  by_cases h11M : 11 ∣ M
  · 
    have htrep11 : (ZMod.castHom h11M (ZMod 11)) (↑trep : ZMod M) = 0 := by
      
      have h11m : 11 ∣ m := h11_iff.mp h11M
      have hcastt : (ZMod.castHom h11M (ZMod 11)) (↑trep : ZMod M)
          = ((trep : ℕ) : ZMod 11) := by
        rw [map_natCast]
      rw [hcastt]
      rw [htrep, Nat.cast_add, Nat.cast_mul]
      have hm0 : ((m : ℕ) : ZMod 11) = 0 :=
        (CharP.cast_eq_zero_iff (ZMod 11) 11 _).mpr h11m
      rw [hm0, zero_mul, add_zero]
      have htv : ((t.val : ℕ) : ZMod 11)
          = (ZMod.castHom h11m (ZMod 11)) t := by
        have h2 : t = ((t.val : ℕ) : ZMod m) :=
          ((ZMod.natCast_val t).trans (ZMod.cast_id _ _)).symm
        conv_rhs => rw [h2]
        rw [map_natCast]
      rw [htv]
      exact ht h11m
    obtain ⟨e, he, hsum⟩ := gadget_extract3_q11 hM10 h11M hg hg4
      (by omega : M ≤ 1 + 9 * (K / 2)) (↑trep : ZMod M) htrep11
    · 
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
  · 
    obtain ⟨e, he, hsum⟩ := gadget_extract3_g4 hM10 h11M hg hg4 hK
      (↑trep : ZMod M)
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


theorem P_dvd_3m81_R2 {m v le K g : ℕ} [NeZero m]
    (hm3 : m.Coprime 3) (hm10 : m.Coprime 10)
    (de : List ℕ) (hle : de.length = le)
    (hde11 : Nat.ofDigits (10 : ZMod 11) de = 0)
    (hde11r : Nat.ofDigits (10 : ZMod 11) de.reverse = 0)
    (C : List ℕ) (hC : C.length = g)
    (hC11 : Nat.ofDigits (10 : ZMod 11) C = 0)
    (hg : 4 ≤ g) (hg4 : g % 4 = 0)
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
  
  have htcond : ∀ h : 11 ∣ m, (ZMod.castHom h (ZMod 11)) t = 0 := by
    intro h
    rw [ht, map_mul, map_neg]
    have hcastE : (ZMod.castHom h (ZMod 11))
        (E + (10 : ZMod m) ^ le * X) = 0 := by
      rw [map_add, hE, hX, map_add, castHom_ofDigits, map_mul,
        castHom_ofDigits, map_pow, castHom_ten, map_mul, map_pow,
        castHom_ten, map_add, map_mul, castHom_ofDigits, map_pow,
        castHom_ten, map_mul, castHom_nine, map_sum]
      have hpal : ∀ k ∈ Finset.range K,
          (ZMod.castHom h (ZMod 11)) (palW m (4 * K + g) (2 * k + 1))
            = palW 11 (4 * K + g) (2 * k + 1) :=
        fun k _ => castHom_palW h (4 * K + g) (2 * k + 1)
      rw [Finset.sum_congr rfl hpal]
      have hsum0 : ∑ k ∈ Finset.range K, palW 11 (4 * K + g) (2 * k + 1)
          = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        apply palW_mod11
        · exact ⟨2 * K + g / 2, by
            obtain ⟨c, hc⟩ : ∃ c, g = 4 * c := ⟨g / 4, by omega⟩
            omega⟩
        · rw [Finset.mem_range] at hk; omega
      rw [hde11, hde11r, hC11, hsum0]
      simp
    rw [hcastE]
    simp
  obtain ⟨e', he', T, hTsum, hTm, hT3⟩ :=
    extract3_target81_R2 hm3 hm10 hg hg4 hKcov t htcond s₀
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


theorem hs0_v4' {v le K g : ℕ} (hv2 : 2 ≤ v) (hv4 : v ≤ 4) (hK1 : 1 ≤ K)
    (de : List ℕ)
    (hde3v : 3 ^ v ∣ Nat.ofDigits 10 de)
    (hde3vr : 3 ^ v ∣ Nat.ofDigits 10 de.reverse)
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
    rw [← cast_ofDigits]
    exact (CharP.cast_eq_zero_iff (ZMod (3 ^ v)) (3 ^ v) _).mpr hde3vr
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


theorem hs0_v1' {le K g : ℕ}
    (de : List ℕ)
    (hde3 : 3 ∣ Nat.ofDigits 10 de)
    (hde3r : 3 ∣ Nat.ofDigits 10 de.reverse)
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
    rw [← cast_ofDigits]
    exact (CharP.cast_eq_zero_iff (ZMod 3) 3 _).mpr hde3r
  have hC0 : Nat.ofDigits (10 : ZMod 3) C = 0 := by
    rw [← cast_ofDigits]
    exact (CharP.cast_eq_zero_iff (ZMod 3) 3 _).mpr hC3
  have h9 : (9 : ZMod 3) = 0 := by decide
  have h81 : (81 : ZMod 3) = 0 := by decide
  rw [pow_one]
  simp only [Nat.cast_zero]
  rw [hde0, hde0', hC0, h9, h81]
  simp


theorem hs0_solver' {v le K g : ℕ} (hv : 5 ≤ v) (hK1 : 1 ≤ K)
    (de : List ℕ)
    (hde81 : 81 ∣ Nat.ofDigits 10 de)
    (hde81r : 81 ∣ Nat.ofDigits 10 de.reverse)
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
  obtain ⟨eb', heb'⟩ := hde81r
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
  set rest : ℕ := (eb + eb' * 10 ^ (le + (4 * K + g)))
      + 10 ^ le * (cb * 10 ^ (2 * K) + wb) with hrest
  have hunit : IsUnit (((10 ^ le : ℕ) : ZMod (3 ^ (v - 4)))) := by
    rw [ZMod.isUnit_iff_coprime]
    exact ((by decide : Nat.Coprime 10 3).pow_right (v - 4)).pow_left le
  set s₀z : ZMod (3 ^ (v - 4)) :=
    -↑rest * ((10 ^ le : ℕ) : ZMod (3 ^ (v - 4)))⁻¹ with hs₀z
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
  
  have hLHS : (Nat.ofDigits (10 : ZMod (3 ^ v)) de
      + Nat.ofDigits (10 : ZMod (3 ^ v)) de.reverse
          * (10 : ZMod (3 ^ v)) ^ (le + (4 * K + g)))
    + (10 : ZMod (3 ^ v)) ^ le
      * (Nat.ofDigits (10 : ZMod (3 ^ v)) C
          * (10 : ZMod (3 ^ v)) ^ (2 * K)
        + (9 * ∑ k ∈ Finset.range K, palW (3 ^ v) (4 * K + g) (2 * k + 1)
          + 81 * (s₀ : ZMod (3 ^ v))))
      = ((81 * (rest + 10 ^ le * s₀) : ℕ) : ZMod (3 ^ v)) := by
    simp only [← cast_ofDigits]
    rw [heb, heb', hcb]
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
  refine ⟨s₀, ?_⟩
  rw [hLHS]
  have h81 : (81 : ℕ) * (rest + 10 ^ le * s₀) = 3 ^ v * w' := by
    rw [hw']
    rw [show (81 : ℕ) = 3 ^ 4 from by norm_num, ← mul_assoc, ← pow_add,
      show 4 + (v - 4) = v from by omega]
  rw [h81]
  exact (CharP.cast_eq_zero_iff (ZMod (3 ^ v)) (3 ^ v) _).mpr (dvd_mul_right _ _)




theorem assemble_v0e_R2 {a m : ℕ} (ha : 1 ≤ a) (hm0 : 1 ≤ m)
    (hm30 : m.Coprime 30)
    (hB : 72 * a + 72 * ((m - 1) / 9 + 1) + 99 ≤ 8 * (2 ^ a) * m)
    (de : List ℕ) (le : ℕ) (hle : de.length = le)
    (hde10 : ∀ x ∈ de, x < 10) (hdene : de ≠ [])
    (hde0 : ∀ h : de ≠ [], de.head h ≠ 0)
    (hde2a : 2 ^ a * 5 ^ 0 ∣ Nat.ofDigits 10 de)
    (hleb : le ≤ 4 * a + 5) (hlea : a ≤ le)
    (hde11 : Nat.ofDigits (10 : ZMod 11) de = 0)
    (hde11r : Nat.ofDigits (10 : ZMod 11) de.reverse = 0)
    (hpar : 4 ∣ 2 ^ a * m - 2 * le) :
    ∃ P z : ℕ, P ≠ 0
      ∧ (0 < z → 10 ∣ 2 ^ a * m)
      ∧ (Nat.digits 10 P).Palindrome
      ∧ (Nat.digits 10 P).length + z = 2 ^ a * m
      ∧ 2 ^ a * m ∣ P * 10 ^ z
      ∧ 2 ^ a * m ∣ (Nat.digits 10 P).sum := by
  classical
  set n := 2 ^ a * m with hn
  have : NeZero m := ⟨by omega⟩
  have hm3 : m.Coprime 3 := hm30.coprime_dvd_right (by norm_num)
  have hm10 : m.Coprime 10 := hm30.coprime_dvd_right (by norm_num)
  set K := 2 * ((m - 1) / 9 + 1) with hK
  have h2a : 2 ^ a = 2 * 2 ^ (a - 1) := by
    rw [← Nat.pow_succ', Nat.succ_eq_add_one,
      Nat.sub_add_cancel (by omega : 1 ≤ a)]
  have hneven : Even n := by
    refine ⟨2 ^ (a - 1) * m, ?_⟩
    rw [hn, h2a]
    ring
  have hnpos : 0 < n := by rw [hn]; positivity
  have hB' : 72 * a + 72 * ((m - 1) / 9 + 1) + 99 ≤ 8 * n := by
    rw [hn, ← Nat.mul_assoc]
    exact hB
  have h36K : 36 * K = 72 * ((m - 1) / 9 + 1) := by rw [hK]; ring
  have hkey : 18 * le + 36 * K ≤ 8 * n - 9 := by omega
  set base := 2 * de.sum + 18 * K with hbase
  set g := n - (2 * le + 4 * K) with hg
  have hcap : n ≤ 9 * g + 1 := by omega
  have hg4 : g % 4 = 0 := by
    obtain ⟨c, hc⟩ := Nat.dvd_sub hpar (Nat.dvd_mul_right 4 K)
    rw [hg, hn, ← Nat.sub_sub, hc]
    omega
  have hn2 : 2 ≤ n := by
    rw [hn, h2a, mul_assoc]
    have h : 1 ≤ 2 ^ (a - 1) * m :=
      Nat.mul_le_mul (Nat.one_le_pow _ _ (by norm_num)) hm0
    omega
  have hg4le : 4 ≤ g := by omega
  have hgev : Even g := by
    obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero hg4
    exact ⟨2 * c, by omega⟩
  set qσ := (base + n - 1) / n with hqσ
  set σ₀ := n * qσ with hσ₀
  have hσ₀ge : base ≤ σ₀ := by
    have hdm := Nat.div_add_mod (base + n - 1) n
    have hmlt : (base + n - 1) % n < n := Nat.mod_lt _ hnpos
    rw [hσ₀, hqσ]
    omega
  have hσ₀lt : σ₀ - base ≤ n - 1 := by
    have hdm := Nat.div_add_mod (base + n - 1) n
    have hmlt : (base + n - 1) % n < n := Nat.mod_lt _ hnpos
    rw [hσ₀, hqσ]
    omega
  set v := σ₀ - base with hv
  have hvle : v ≤ 9 * g := by omega
  have hve : Even v := by
    have hσ₀e : Even σ₀ := by
      obtain ⟨w, hw⟩ := hneven
      refine ⟨w * qσ, ?_⟩
      rw [hσ₀, hw]
      ring
    have hbe : Even base := by
      refine ⟨de.sum + 9 * K, ?_⟩
      rw [hbase]
      omega
    obtain ⟨x, hx⟩ := hσ₀e
    obtain ⟨y, hy⟩ := hbe
    refine ⟨x - y, ?_⟩
    rw [hv]
    omega
  set R := v / 2 with hR
  have h2R : 2 * R = v := by
    obtain ⟨w, hw⟩ := hve
    omega
  obtain ⟨F, hFlen, hF9, hFsum⟩ :=
    exists_free_block (g / 2) R (by
      obtain ⟨w, hw⟩ := hgev
      omega)
  set C := F ++ F.reverse with hC
  have hCpal : C.Palindrome := by
    rw [hC]
    exact List.Palindrome.append_reverse F
  have hC10 : ∀ x ∈ C, x < 10 := by
    intro x hx
    rw [hC] at hx
    rcases List.mem_append.mp hx with hx | hx
    · have := hF9 x hx
      omega
    · have := hF9 x (List.mem_reverse.mp hx)
      omega
  have hCg : C.length = g := by
    rw [hC, List.length_append, hFlen, List.length_reverse]
    obtain ⟨w, hw⟩ := hgev
    omega
  have hCσ : C.sum = v := by
    rw [hC, List.sum_append, List.sum_reverse, hFsum]
    omega
  have hC11 : Nat.ofDigits (10 : ZMod 11) C = 0 := by
    rw [hC]
    exact ofDigits_palPair11 F
  have hKcov : m * 3 ^ (0 - 4) ≤ 1 + 9 * (K / 2) := by
    have hK2 : K / 2 = (m - 1) / 9 + 1 := by
      rw [hK]
      exact Nat.mul_div_cancel_left _ (by norm_num : (0:ℕ) < 2)
    have hdm := Nat.div_add_mod (m - 1) 9
    have hmlt : (m - 1) % 9 < 9 := Nat.mod_lt _ (by norm_num)
    have h0m : 0 - 4 = 0 := rfl
    rw [h0m, pow_zero, mul_one, hK2]
    omega
  obtain ⟨s₀, hs0⟩ := hs0_v0 (le := le) (K := K) (g := g) de C
  obtain ⟨e', he', hdvdP⟩ :=
    P_dvd_3m81_R2 (v := 0) (le := le) (K := K) (g := g)
      hm3 hm10 de hle hde11 hde11r C hCg hC11 hg4le hg4 hKcov s₀ hs0
  set MID := (List.range (2 * K)).map (pairDigit e') ++ C
      ++ ((List.range (2 * K)).map (pairDigit e')).reverse with hMID
  have hMIDpal : MID.Palindrome := mid_pal e' C hCpal
  have hMID10 : ∀ x ∈ MID, x < 10 := mid_lt10 e' he' C hC10
  have hMIDlen : MID.length = 4 * K + g := by
    rw [hMID, List.length_append, List.length_append,
      List.length_reverse, List.length_map, List.length_range, hCg]
    ring
  have hMIDσ : MID.sum = 18 * K + C.sum := mid_sum e' he' C
  obtain ⟨hP0, hPpal, hPlen, hPσ⟩ := sandwich_spec_gen de MID
    hdene hde10 (hde0 hdene) hMIDpal hMID10 rfl rfl
  have h25P : 2 ^ a * 5 ^ 0 ∣ Nat.ofDigits 10
      (de ++ MID ++ de.reverse) :=
    B_dvd_P (le := le) hle hde2a (by omega)
  set P := Nat.ofDigits 10 (de ++ MID ++ de.reverse) with hP
  have hmP : 3 ^ 0 * m ∣ P := by simpa using hdvdP
  have hnP : n ∣ P := by
    have h := n_dvd_P_pow10_le (a := a) (b := 0) (v := 0) (m := m)
      (z := 0) (a' := a) (b' := 0) (P := P) h25P hmP
      (by omega) (by omega) hm30
    have h' : 2 ^ a * m ∣ P := by simpa using h
    rw [hn]
    exact h'
  have hσ : (Nat.digits 10 P).sum = σ₀ := by
    rw [hPσ, hMIDσ, hCσ]
    omega
  refine ⟨P, 0, hP0, fun h => (Nat.lt_irrefl 0 h).elim, hPpal,
    ?_, ?_, ?_⟩
  · rw [hPlen, hMIDlen, hle]
    omega
  · simpa using hnP
  · rw [hσ, hσ₀]
    rw [hn]
    exact dvd_mul_right _ _


theorem v0e_R2_capacity {a m : ℕ} (ha : 1 ≤ a) (hm30 : m.Coprime 30)
    (hbad : 11 ∣ m ∨ 101 ∣ m)
    (hsm : ¬ ((a = 1 ∧ m = 11) ∨ (a = 2 ∧ m = 11))) :
    72 * a + 72 * ((m - 1) / 9 + 1) + 99 ≤ 8 * (2 ^ a) * m := by
  have hm0 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0] at hm30
      exact absurd hm30 (by decide)
    · exact h0
  have hm11 : 11 ≤ m := by
    rcases hbad with h | h
    · exact Nat.le_of_dvd hm0 h
    · exact le_trans (by norm_num) (Nat.le_of_dvd hm0 h)
  have hb := bnd72 m
  rcases Nat.lt_or_ge a 3 with ha3 | ha3
  · have ha12 : a = 1 ∨ a = 2 := by omega
    rcases ha12 with rfl | rfl
    · have hmB : 30 ≤ m := by
        by_contra hlt
        have hlt' : m < 30 := Nat.not_le.mp hlt
        interval_cases m <;>
          first
            | exact absurd hm30 (by decide)
            | exact absurd hbad (by decide)
            | exact absurd (Or.inl ⟨rfl, rfl⟩) hsm
      rw [pow_one]
      omega
    · have hmB : 13 ≤ m := by
        by_contra hlt
        have hlt' : m < 13 := Nat.not_le.mp hlt
        interval_cases m <;>
          first
            | exact absurd hm30 (by decide)
            | exact absurd hbad (by decide)
            | exact absurd (Or.inr ⟨rfl, rfl⟩) hsm
      rw [show (2 : ℕ) ^ 2 = 4 from by norm_num]
      omega
  · have h9 : 72 * a + 251 ≤ 616 * 2 ^ (a - 3) := by
      induction a, ha3 using Nat.le_induction with
      | base => norm_num
      | succ n hn ih =>
          rw [show n + 1 - 3 = n - 3 + 1 by omega, pow_succ]
          omega
    have hp : 1 ≤ 2 ^ a := Nat.one_le_pow _ _ (by norm_num)
    have h2a3 : (2:ℕ) ^ a = 8 * 2 ^ (a - 3) := by
      conv_lhs => rw [show a = a - 3 + 3 by omega]
      rw [pow_add]
      ring
    have h88 : 88 * (2 ^ a - 1) ≤ 8 * (2 ^ a - 1) * m := by
      calc 88 * (2 ^ a - 1) = 8 * (2 ^ a - 1) * 11 := by ring
        _ ≤ 8 * (2 ^ a - 1) * m := Nat.mul_le_mul_left _ hm11
    have hfin : 72 * a + 163 ≤ 88 * (2 ^ a - 1) := by
      rw [h2a3]
      omega
    have hlast : 8 * (2 ^ a - 1) * m + 8 * m = 8 * 2 ^ a * m := by
      have h2a' : 2 ^ a = 2 ^ a - 1 + 1 := by omega
      calc 8 * (2 ^ a - 1) * m + 8 * m
          = 8 * m * ((2 ^ a - 1) + 1) := by ring
        _ = 8 * m * 2 ^ a := by rw [← h2a']
        _ = 8 * 2 ^ a * m := by ring
    calc 72 * a + 72 * ((m - 1) / 9 + 1) + 99
        ≤ 72 * a + (8 * (m - 1) + 72) + 99 := by omega
      _ = 72 * a + 163 + 8 * m := by omega
      _ ≤ 88 * (2 ^ a - 1) + 8 * m := by omega
      _ ≤ 8 * (2 ^ a - 1) * m + 8 * m := by omega
      _ = 8 * 2 ^ a * m := hlast


theorem hard_closed_v0 {a m : ℕ} (ha : 1 ≤ a) (hm30 : m.Coprime 30)
    (hbad : 11 ∣ m ∨ 101 ∣ m) : finGoal (2 ^ a * m) := by
  have hm0 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0] at hm30
      exact absurd hm30 (by decide)
    · exact h0
  have hm11 : 11 ≤ m := by
    rcases hbad with h | h
    · exact Nat.le_of_dvd hm0 h
    · exact le_trans (by norm_num) (Nat.le_of_dvd hm0 h)
  by_cases hsm : (a = 1 ∧ m = 11) ∨ (a = 2 ∧ m = 11)
  · rcases hsm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact wit_sound_of rfl
    · exact wit_sound_of rfl
  obtain ⟨D, hDpal, hD10, hDne, hD0, hD25, _hD3v, _hDσ, hr₀lt, hlenD⟩ :=
    border_pal_q (a' := a) (b' := 0) (q := 2) (s₁ := a) (t := 0)
      (by norm_num) (by norm_num) (Or.inr rfl)
      (le_of_eq (Nat.max_eq_left (Nat.zero_le a)))
  set lenD := D.length with hlenD'
  have hr0z : r0b a 0 2 = 0 := by
    have h := hr₀lt
    norm_num at h
    omega
  have hlenN : lenD
      = 2 * ((Nat.digits 10 (9 * 2 ^ a)).length + a) := by
    have h := hlenD
    rw [hr0z] at h
    norm_num at h ⊢
    omega
  have lenV_le : (Nat.digits 10 (9 * 2 ^ a)).length ≤ a + 2 := by
    have hVpos : (9 * 2 ^ a : ℕ) ≠ 0 := by positivity
    have hb2 := Nat.base_pow_length_digits_le 10 (9 * 2 ^ a)
      (by norm_num) hVpos
    have hlt : 10 * (9 * 2 ^ a) < 10 ^ (a + 2) := by
      have h1 : (2 : ℕ) ^ a ≤ 10 ^ a :=
        Nat.pow_le_pow_left (by norm_num) _
      calc 10 * (9 * 2 ^ a) = 90 * 2 ^ a := by ring
        _ ≤ 90 * 10 ^ a := Nat.mul_le_mul_left 90 h1
        _ < 100 * 10 ^ a := by omega
        _ = 10 ^ (a + 2) := by
            rw [pow_add]
            ring
    have hpow : 10 ^ ((Nat.digits 10 (9 * 2 ^ a)).length)
        < 10 ^ (a + 2) := lt_of_le_of_lt hb2 hlt
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 10)).mp hpow
    omega
  have hlenDb : lenD ≤ 4 * a + 4 := by omega
  have hcap := v0e_R2_capacity ha hm30 hbad hsm
  have hDeven : Even lenD := by
    rw [hlenN]
    exact ⟨(Nat.digits 10 (9 * 2 ^ a)).length + a, by ring⟩
  have hde11D : Nat.ofDigits (10 : ZMod 11) D = 0 :=
    ofDigits_evenPal11 hDpal (by rw [← hlenD']; exact hDeven)
  have hde11Dr : Nat.ofDigits (10 : ZMod 11) D.reverse = 0 := by
    rw [hDpal.reverse_eq]
    exact hde11D
  by_cases ha1 : a = 1
  · 
    have hde2a : 2 ^ a * 5 ^ 0 ∣ Nat.ofDigits 10 (D ++ [0]) := by
      rw [ofDigits_append_zero]
      exact hD25
    have hde10 : ∀ x ∈ D ++ [0], x < 10 := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hD10 x hx
      · rw [List.mem_singleton] at hx
        omega
    have hdene : D ++ [0] ≠ [] := by
      intro h
      exact hDne (List.append_eq_nil_iff.mp h).1
    have hde0 : ∀ h : D ++ [0] ≠ [], (D ++ [0]).head h ≠ 0 := by
      intro h
      rcases D with _ | ⟨d, ds⟩
      · exact absurd rfl hDne
      · exact hD0 hDne
    have hde11 : Nat.ofDigits (10 : ZMod 11) (D ++ [0]) = 0 := by
      rw [ofDigits_append_zero]
      exact hde11D
    have hde11r : Nat.ofDigits (10 : ZMod 11) (D ++ [0]).reverse = 0 := by
      rw [List.reverse_append, List.reverse_singleton,
        List.singleton_append, ofDigits_cons', hDpal.reverse_eq]
      simp [hde11D]
    have hpar : 4 ∣ 2 ^ a * m - 2 * (lenD + 1) := by
      have hmo : Odd m := by
        have h2 : ¬ (2 : ℕ) ∣ m :=
          (Nat.prime_two.coprime_iff_not_dvd).mp
            (hm30.coprime_dvd_right (by norm_num : (2:ℕ) ∣ 30)).symm
        rw [← Nat.not_even_iff_odd]
        rintro ⟨c, hc⟩
        exact h2 ⟨c, by omega⟩
      have hlm : lenD + 1 ≤ m := by
        rw [ha1] at hlenDb
        omega
      obtain ⟨c, hc⟩ := hDeven
      obtain ⟨w, hw⟩ := hmo
      rw [ha1, pow_one]
      refine ⟨w - c, ?_⟩
      omega
    exact finGoal_of_relaxed
      (by simpa using not10_2a3vm (a := a) (v := 0) (m := m) hm30)
      (assemble_v0e_R2 ha hm0 hm30 hcap (D ++ [0]) (lenD + 1)
        (by simp [← hlenD']) hde10 hdene hde0 hde2a
        (by omega) (by omega) hde11 hde11r hpar)
  · have ha2 : 2 ≤ a := by omega
    have hpar : 4 ∣ 2 ^ a * m - 2 * lenD := by
      have h2a : 2 ^ a = 4 * 2 ^ (a - 2) := by
        conv_lhs => rw [show a = a - 2 + 2 by omega]
        rw [pow_add]
        ring
      obtain ⟨w, hw⟩ := hDeven
      have hwb : w ≤ 2 ^ (a - 2) * m := by
        have hwle : w ≤ 2 * a + 2 := by omega
        have hXm : 11 * 2 ^ (a - 2) ≤ 2 ^ (a - 2) * m := by
          rw [mul_comm 11]
          exact Nat.mul_le_mul_left _ hm11
        have h11 : 2 * a + 2 ≤ 11 * 2 ^ (a - 2) := by
          have hlt : a - 2 < 2 ^ (a - 2) := Nat.lt_two_pow_self
          omega
        exact le_trans hwle (le_trans h11 hXm)
      rw [h2a, show 4 * 2 ^ (a - 2) * m
          = 4 * (2 ^ (a - 2) * m) from by ring]
      refine ⟨2 ^ (a - 2) * m - w, ?_⟩
      omega
    exact finGoal_of_relaxed
      (by simpa using not10_2a3vm (a := a) (v := 0) (m := m) hm30)
      (assemble_v0e_R2 ha hm0 hm30 hcap D lenD hlenD'.symm
        hD10 hDne hD0 hD25 (by omega) (by omega) hde11D hde11Dr hpar)


theorem wit66 : finGoal 66 := by
  classical
  set F : List ℕ := [6, 9, 9, 9] ++ List.replicate 29 0 with hF
  set L := F ++ F.reverse with hL
  set P := Nat.ofDigits 10 L with hP
  have hF10 : ∀ x ∈ F, x < 10 := by
    intro x hx
    rw [hF] at hx
    simp only [List.mem_append, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, List.mem_replicate, ne_eq, or_false] at hx
    rcases hx with (h | h | h | h) | h <;> omega
  have hL10 : ∀ x ∈ L, x < 10 := by
    intro x hx
    rw [hL] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hF10 x hx
    · exact hF10 x (List.mem_reverse.mp hx)
  have hFne : F ≠ [] := by rw [hF]; simp
  have hLne : L ≠ [] := by
    rw [hL]
    intro h
    exact hFne (List.append_eq_nil_iff.mp h).1
  have hlast? : L.getLast? = some 6 := by
    rw [hL, List.getLast?_append, List.getLast?_reverse]
    have hhd : F.head? = some 6 := by rw [hF]; rfl
    rw [hhd]
    simp
  have hlast : ∀ h : L ≠ [], L.getLast h ≠ 0 := by
    intro h hh
    rw [List.getLast?_eq_getLast_of_ne_nil h] at hlast?
    rw [hh] at hlast?
    exact absurd (Option.some.inj hlast?) (by decide)
  have hdig : Nat.digits 10 P = L :=
    Nat.digits_ofDigits 10 (by norm_num) _ hL10 hlast
  have hP0 : P ≠ 0 := by
    intro h0
    rw [h0, Nat.digits_zero] at hdig
    exact hLne hdig.symm
  have h2 : 2 ∣ P := by
    have hLcons : L = 6
        :: (([9, 9, 9] ++ List.replicate 29 0) ++ F.reverse) := by
      rw [hL, hF]
      simp only [List.append_assoc, List.cons_append]
    rw [hP, hLcons, Nat.ofDigits_cons]
    exact ⟨3 + 5 * Nat.ofDigits 10 _, by ring⟩
  have h3 : 3 ∣ P := by
    rw [hP]
    apply ofDigits_dvd_of_mem
    intro d hd
    have hd6 : d = 6 ∨ d = 9 ∨ d = 0 := by
      have hdF : d ∈ F := by
        have hd' := hd
        rw [hL] at hd'
        rcases List.mem_append.mp hd' with h | h
        · exact h
        · exact List.mem_reverse.mp h
      rw [hF] at hdF
      simp only [List.mem_append, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, List.mem_replicate, ne_eq, or_false] at hdF
      rcases hdF with (h | h | h | h) | h <;> omega
    rcases hd6 with rfl | rfl | rfl <;> norm_num
  have h11 : 11 ∣ P := by
    have h := ofDigits_palPair11 F
    rw [← hL] at h
    rw [hP]
    rw [← cast_ofDigits] at h
    exact (CharP.cast_eq_zero_iff (ZMod 11) 11 _).mp h
  have h6 : 6 ∣ P :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 2 3) h2 h3
  have h66 : 66 ∣ P := by
    have h := Nat.Coprime.mul_dvd_of_dvd_of_dvd
      (by decide : Nat.Coprime 6 11) h6 h11
    simpa using h
  have hLsum : L.sum = 66 := by
    rw [hL, List.sum_append, List.sum_reverse, hF]
    simp [List.sum_replicate]
  refine ⟨P, 0, hP0, (by decide : (0 : ℕ) = tz 66), ?_, ?_, ?_, ?_⟩
  · rw [hdig, hL]
    exact List.Palindrome.of_reverse_eq (by
      rw [List.reverse_append, List.reverse_reverse])
  · rw [hdig, hL, List.length_append, List.length_reverse, hF]
    simp
  · simpa using h66
  · rw [hdig, hLsum]


theorem assemble_sandwich_R2 {a v m le K j T : ℕ} (ha : 1 ≤ a)
    (hm0 : 1 ≤ m) (hm30 : m.Coprime 30)
    (hT : 2 * T = 2 ^ a * 3 ^ v * m - (4 * K + 2 * j + 2 * le))
    (hbound : 4 * K + 2 * j + 2 * le + 4 ≤ 2 ^ a * 3 ^ v * m)
    (hj1 : 1 ≤ j)
    (hKcov : m * 3 ^ (v - 4) ≤ 1 + 9 * (K / 2))
    (de : List ℕ) (hle : de.length = le)
    (hde10 : ∀ x ∈ de, x < 10) (hdene : de ≠ [])
    (hde0 : ∀ h : de ≠ [], de.head h ≠ 0)
    (hde2a : 2 ^ a * 5 ^ 0 ∣ Nat.ofDigits 10 de)
    (hde11 : Nat.ofDigits (10 : ZMod 11) de = 0)
    (hde11r : Nat.ofDigits (10 : ZMod 11) de.reverse = 0)
    (hpar : 4 ∣ 2 ^ a * 3 ^ v * m - 2 * le)
    (hlea : a ≤ le)
    (C : List ℕ) (hCdef : C = List.replicate j 9 ++ List.replicate T 0
        ++ List.replicate T 0 ++ List.replicate j 9)
    (s₀ : ℕ) (hs0 : (Nat.ofDigits (10 : ZMod (3 ^ v)) de
        + Nat.ofDigits (10 : ZMod (3 ^ v)) de.reverse
            * (10 : ZMod (3 ^ v)) ^ (le + (4 * K + (2 * j + 2 * T))))
      + (10 : ZMod (3 ^ v)) ^ le
        * (Nat.ofDigits (10 : ZMod (3 ^ v)) C
            * (10 : ZMod (3 ^ v)) ^ (2 * K)
          + (9 * ∑ k ∈ Finset.range K,
              palW (3 ^ v) (4 * K + (2 * j + 2 * T)) (2 * k + 1)
            + 81 * (s₀ : ZMod (3 ^ v)))) = 0)
    (hσdiv : 2 ^ a * 3 ^ v * m ∣ 2 * de.sum + 18 * (K + j)) :
    finGoal (2 ^ a * 3 ^ v * m) := by
  classical
  haveI : NeZero m := ⟨by omega⟩
  have hm3 : m.Coprime 3 := hm30.coprime_dvd_right (by norm_num)
  have hm10 : m.Coprime 10 := hm30.coprime_dvd_right (by norm_num)
  set n := 2 ^ a * 3 ^ v * m with hn
  have hCg : C.length = 2 * j + 2 * T := by
    rw [hCdef]
    exact (center_repunit_even_len_sum j T).1
  have hCσ : C.sum = 18 * j := by
    rw [hCdef]
    exact (center_repunit_even_len_sum j T).2
  have hCpal : C.Palindrome := by
    rw [hCdef]
    exact center_repunit_even_pal j T
  have hC10 : ∀ x ∈ C, x < 10 := by
    rw [hCdef]
    exact center_repunit_even_lt10 j T
  have hC11 : Nat.ofDigits (10 : ZMod 11) C = 0 := by
    rw [hCdef]
    have hFe : List.replicate j 9 ++ List.replicate T 0
        ++ List.replicate T 0 ++ List.replicate j 9
        = (List.replicate j 9 ++ List.replicate T 0)
          ++ (List.replicate j 9 ++ List.replicate T 0).reverse := by
      rw [List.reverse_append, List.reverse_replicate,
        List.reverse_replicate, ← List.append_assoc]
    rw [hFe]
    exact ofDigits_palPair11 _
  have hg4 : (2 * j + 2 * T) % 4 = 0 := by
    have hgs : 2 * j + 2 * T = n - 2 * le - 4 * K := by
      rw [hn]
      omega
    obtain ⟨c, hc⟩ := hpar
    rw [hgs]
    omega
  have hg4le : 4 ≤ 2 * j + 2 * T := by omega
  obtain ⟨e', he', hdvdP⟩ := P_dvd_3m81_R2 (v := v) (le := le) (K := K)
    (g := 2 * j + 2 * T) hm3 hm10 de hle hde11 hde11r C hCg hC11
    hg4le hg4 hKcov s₀ hs0
  set MID := (List.range (2 * K)).map (pairDigit e') ++ C
      ++ ((List.range (2 * K)).map (pairDigit e')).reverse with hMID
  have hMIDpal : MID.Palindrome := mid_pal e' C hCpal
  have hMID10 : ∀ x ∈ MID, x < 10 := mid_lt10 e' he' C hC10
  have hMIDlen : MID.length = 4 * K + (2 * j + 2 * T) := by
    rw [hMID, List.length_append, List.length_append,
      List.length_reverse, List.length_map, List.length_range, hCg]
    ring
  have hMIDσ : MID.sum = 18 * K + C.sum := mid_sum e' he' C
  obtain ⟨hP0, hPpal, hPlen, hPσ⟩ := sandwich_spec_gen de MID
    hdene hde10 (hde0 hdene) hMIDpal hMID10 rfl rfl
  have h25P : 2 ^ a * 5 ^ 0 ∣ Nat.ofDigits 10
      (de ++ MID ++ de.reverse) :=
    B_dvd_P (le := le) hle hde2a (by omega)
  set P := Nat.ofDigits 10 (de ++ MID ++ de.reverse) with hP
  have hmP : 3 ^ v * m ∣ P := by
    obtain ⟨w, hw⟩ := hdvdP
    exact ⟨w, by rw [hw]; ring⟩
  have hnP : n ∣ P := by
    have h := n_dvd_P_pow10_le (a := a) (b := 0) (v := v) (m := m)
      (z := 0) (a' := a) (b' := 0) (P := P) h25P hmP
      (by omega) (by omega) hm30
    have h' : 2 ^ a * 3 ^ v * m ∣ P := by simpa using h
    rw [hn]
    exact h'
  have hσ : (Nat.digits 10 P).sum = 2 * de.sum + 18 * (K + j) := by
    rw [hPσ, hMIDσ, hCσ]
    have hrev : de.reverse.sum = de.sum := List.sum_reverse _
    omega
  refine ⟨P, 0, hP0,
    (tz_zero_of_not_dvd (hn.symm ▸ not10_2a3vm hm30)).symm, hPpal,
    ?_, ?_, ?_⟩
  · rw [hPlen, hMIDlen, hle]
    omega
  · simpa using hnP
  · rw [hσ, hn]
    exact hσdiv


theorem eb01a_R2_capacity {m : ℕ} (hm : 25 ≤ m) :
    8 * ((m - 1) / 9 + 1) + 20 ≤ 2 * m := by
  have hdm := Nat.div_add_mod (m - 1) 9
  have hlt : (m - 1) % 9 < 9 := Nat.mod_lt _ (by norm_num)
  have h9 : 9 * ((m - 1) / 9 + 1) ≤ m + 8 := by omega
  omega


theorem assemble_eb01a_R2 {m : ℕ} (hm0 : 1 ≤ m) (hm30 : m.Coprime 30)
    (hB : 8 * ((m - 1) / 9 + 1) + 20 ≤ 2 * m) :
    finGoal (2 ^ 1 * 3 ^ 1 * m) := by
  classical
  set n := 2 ^ 1 * 3 ^ 1 * m with hn
  haveI : NeZero m := ⟨by omega⟩
  have hm3 : m.Coprime 3 := hm30.coprime_dvd_right (by norm_num)
  have hm10 : m.Coprime 10 := hm30.coprime_dvd_right (by norm_num)
  have hm2 : m.Coprime 2 := hm30.coprime_dvd_right (by norm_num)
  
  set K := 2 * ((m - 1) / 9 + 1) with hK
  set j := 1 with hj
  set M := m with hM
  have hM0 : 0 < M := by rw [hM]; omega
  have h4m : (4 : ℕ).Coprime m := hm2.symm.pow_left 2
  have h9m : (9 : ℕ).Coprime m := hm3.symm.pow_left 2
  have hcop43 : (4 * 3 ^ 2).Coprime M := by
    rw [hM]
    exact h4m.mul_left h9m
  have hnd : ¬ (2 : ℕ) ∣ M := by
    rw [hM]
    rintro ⟨r, hr⟩
    exact (Nat.prime_two.coprime_iff_not_dvd).mp hm2.symm ⟨r, hr⟩
  have hcop2 : M.Coprime (2 ^ (1 - 2)) :=
    ((Nat.prime_two.coprime_iff_not_dvd).mpr hnd).symm.pow_right _
  obtain ⟨t, htlt, ht2, htdvd⟩ := sigma_t_solve2 (v := 2)
    (ρ := rhob 1 0 2) (S := K + j) (M := M) (w := 1 - 2)
    hM0 hcop43 hcop2
  have ht1 : t + 1 ≤ M := by
    have h := htlt
    norm_num at h
    omega
  obtain ⟨D, hDpal, hD10, hDne, hD0, hD25, hD3v, hDσ, hr₀lt, hlenD⟩ :=
    border_pal_q (a' := 1) (b' := 0) (q := 2) (s₁ := 1) (t := t)
      (by norm_num) (by norm_num) (Or.inr rfl)
      (le_of_eq (Nat.max_eq_left (Nat.zero_le 1)))
  set lenD := D.length with hlenD'
  have hr0z : r0b 1 0 2 = 0 := by
    have h := hr₀lt
    norm_num at h
    omega
  have hlenN : lenD = 2 * ((Nat.digits 10 (9 * 2 ^ 1)).length + 1)
      + 2 * t := by
    have h := hlenD
    rw [hr0z] at h
    norm_num at h ⊢
    omega
  have lenV_le : (Nat.digits 10 (9 * 2 ^ 1)).length ≤ 3 := by
    norm_num
  have hlenDb : lenD ≤ 2 * m + 6 := by
    rw [hlenN]
    have h := ht1
    rw [hM] at h
    omega
  have hDeven : Even lenD := by
    rw [hlenN]
    exact ⟨(Nat.digits 10 (9 * 2 ^ 1)).length + 1 + t, by ring⟩
  have hde11D : Nat.ofDigits (10 : ZMod 11) D = 0 :=
    ofDigits_evenPal11 hDpal (by rw [← hlenD']; exact hDeven)
  set de := D ++ [0] with hde
  set le := lenD + 1 with hle'
  have hle : de.length = le := by
    rw [hde, hle', List.length_append, List.length_singleton, hlenD']
  have hde10 : ∀ x ∈ de, x < 10 := by
    intro x hx
    rw [hde] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hD10 x hx
    · rw [List.mem_singleton] at hx
      omega
  have hdene : de ≠ [] := by
    rw [hde]
    intro h
    exact hDne (List.append_eq_nil_iff.mp h).1
  have hde0 : ∀ h : de ≠ [], de.head h ≠ 0 := by
    intro h
    rw [hde] at h
    rcases D with _ | ⟨d, ds⟩
    · exact absurd rfl hDne
    · exact hD0 hDne
  have hde2a : 2 ^ 1 * 5 ^ 0 ∣ Nat.ofDigits 10 de := by
    rw [hde, ofDigits_append_zero]
    exact hD25
  have hde11 : Nat.ofDigits (10 : ZMod 11) de = 0 := by
    rw [hde, ofDigits_append_zero]
    exact hde11D
  have hde11r : Nat.ofDigits (10 : ZMod 11) de.reverse = 0 := by
    rw [hde, List.reverse_append, List.reverse_singleton,
      List.singleton_append, ofDigits_cons', hDpal.reverse_eq]
    simp [hde11D]
  have hde3 : 3 ∣ Nat.ofDigits 10 de := by
    rw [hde, ofDigits_append_zero]
    exact dvd_trans (by norm_num : (3 : ℕ) ∣ 3 ^ 2) hD3v
  have hde3r : 3 ∣ Nat.ofDigits 10 de.reverse := by
    rw [hde, List.reverse_append, List.reverse_singleton,
      List.singleton_append, Nat.ofDigits_cons, hDpal.reverse_eq]
    simp only [Nat.cast_zero, zero_add]
    exact dvd_mul_of_dvd_right
      (dvd_trans (by norm_num : (3 : ℕ) ∣ 3 ^ 2) hD3v) 10
  have hpar : 4 ∣ 2 ^ 1 * 3 ^ 1 * m - 2 * le := by
    have hmo : Odd m := by
      have h2 : ¬ (2 : ℕ) ∣ m :=
        (Nat.prime_two.coprime_iff_not_dvd).mp hm2.symm
      rw [← Nat.not_even_iff_odd]
      rintro ⟨c', hc'⟩
      exact h2 ⟨c', by omega⟩
    obtain ⟨w', hw'⟩ := hmo
    obtain ⟨w, hw⟩ := hDeven
    have hlm : lenD + 1 ≤ 3 * m := by omega
    rw [hle']
    refine ⟨(3 * m - (lenD + 1)) / 2, ?_⟩
    omega
  
  set S := 4 * K + 2 * j + 2 * le with hS
  have hSeven : Even S := ⟨2 * K + j + le, by rw [hS]; ring⟩
  have hne : Even n := by
    rw [hn]
    exact ⟨3 * m, by ring⟩
  set X := n - S with hX
  have hXeven : Even X := by
    obtain ⟨an, han⟩ := hne
    obtain ⟨as, has⟩ := hSeven
    refine ⟨an - as, ?_⟩
    rw [hX, han, has]
    omega
  set T := X / 2 with hT'
  have hbound : 4 * K + 2 * j + 2 * le + 4 ≤ n := by
    set E := 2 * m with hE
    have hnE : n = 3 * E := by rw [hn, hE]; ring
    have h4K : 4 * K = 8 * ((m - 1) / 9 + 1) := by rw [hK]; ring
    have hB' : 4 * K + 20 ≤ E := by
      rw [hE, h4K]
      exact hB
    have hlen3 : 2 * lenD ≤ 4 * t + 16 := by
      rw [hlenN]
      omega
    rw [hj, hle', hnE]
    omega
  have h2T : 2 * T = X := by
    rw [hT']
    omega
  have hT : 2 * T = n - (4 * K + 2 * j + 2 * le) := by
    rw [h2T, hX, hS]
  have hKcov : m * 3 ^ (1 - 4) ≤ 1 + 9 * (K / 2) := by
    have hdm := Nat.div_add_mod (m - 1) 9
    have hlt : (m - 1) % 9 < 9 := Nat.mod_lt _ (by norm_num)
    have hK2 : K / 2 = (m - 1) / 9 + 1 := by
      rw [hK]
      exact Nat.mul_div_cancel_left _ (by norm_num)
    rw [show (1 : ℕ) - 4 = 0 from rfl, pow_zero, mul_one, hK2]
    omega
  set C := List.replicate j 9 ++ List.replicate T 0
      ++ List.replicate T 0 ++ List.replicate j 9 with hCdef
  have hCval3 : 3 ∣ Nat.ofDigits 10 C := by
    apply ofDigits_dvd_of_mem
    intro d hd
    rw [hCdef] at hd
    rcases List.mem_append.mp hd with hABC | h9last
    · rcases List.mem_append.mp hABC with hAB | hT2
      · rcases List.mem_append.mp hAB with h9a | hT1
        · rw [List.eq_of_mem_replicate h9a]
          exact ⟨3, by norm_num⟩
        · rw [List.eq_of_mem_replicate hT1]
          exact dvd_zero _
      · rw [List.eq_of_mem_replicate hT2]
        exact dvd_zero _
    · rw [List.eq_of_mem_replicate h9last]
      exact ⟨3, by norm_num⟩
  obtain ⟨s₀, hs0⟩ := hs0_v1' (le := le) (K := K)
    (g := 2 * j + 2 * T) de hde3 hde3r C hCval3
  have hσdiv : 2 ^ 1 * 3 ^ 1 * m ∣ 2 * de.sum + 18 * (K + j) := by
    have hdeσ : de.sum = D.sum := by
      rw [hde, List.sum_append, List.sum_singleton]
      simp
    have hσe : 2 * de.sum + 18 * (K + j)
        = 4 * 3 ^ 2 * (rhob 1 0 2 + t) + 18 * (K + j) := by
      rw [hdeσ, hDσ]
      ring
    rw [hσe]
    have h2 : 2 ∣ 4 * 3 ^ 2 * (rhob 1 0 2 + t) + 18 * (K + j) :=
      ⟨2 * 3 ^ 2 * (rhob 1 0 2 + t) + 9 * (K + j), by ring⟩
    have h3 : 3 ∣ 4 * 3 ^ 2 * (rhob 1 0 2 + t) + 18 * (K + j) :=
      ⟨4 * 3 * (rhob 1 0 2 + t) + 6 * (K + j), by ring⟩
    have h6 : 6 ∣ 4 * 3 ^ 2 * (rhob 1 0 2 + t) + 18 * (K + j) :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 2 3)
        h2 h3
    have hm6 : (6 : ℕ).Coprime m := Nat.Coprime.mul_left hm2.symm hm3.symm
    have hσ6m : 6 * m ∣ 4 * 3 ^ 2 * (rhob 1 0 2 + t) + 18 * (K + j) :=
      hm6.mul_dvd_of_dvd_of_dvd h6 (by rw [← hM]; exact htdvd)
    have e : 2 ^ 1 * 3 ^ 1 * m = 6 * m := by norm_num
    rw [e]
    exact hσ6m
  exact assemble_sandwich_R2 (a := 1) (v := 1) (le := le) (K := K)
    (j := j) (T := T) (by norm_num) hm0 hm30 hT hbound (by omega)
    hKcov de hle hde10 hdene hde0 hde2a hde11 hde11r hpar (by omega)
    C hCdef s₀ hs0 hσdiv


theorem eb01_R2_capacity {a m : ℕ} (ha : 2 ≤ a) (hm : 11 ≤ m) :
    4 * m + 2 ^ a + 8 * a + 8 + 2 ^ a * m ≤ 3 * (2 ^ a * m) := by
  have h24 : (4 : ℕ) ≤ 2 ^ a :=
    Nat.pow_le_pow_right (n := 2) (by norm_num) ha
  have h2a : a < 2 ^ a := Nat.lt_two_pow_self
  have g1 : 4 * m ≤ 2 ^ a * m := Nat.mul_le_mul_right m h24
  have g2 : 2 ^ a + 8 * a + 8 ≤ 2 ^ a * m := by
    calc 2 ^ a + 8 * a + 8 ≤ 9 * 2 ^ a := by omega
      _ ≤ m * 2 ^ a :=
          Nat.mul_le_mul_right (2 ^ a) (by omega)
      _ = 2 ^ a * m := by ring
  omega


theorem assemble_eb01_R2 {a m : ℕ} (ha : 2 ≤ a) (hm0 : 1 ≤ m)
    (hm30 : m.Coprime 30)
    (hB : 4 * m + 2 ^ a + 8 * a + 8 + 2 ^ a * m ≤ 3 * (2 ^ a * m)) :
    finGoal (2 ^ a * 3 * m) := by
  classical
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
  have hM0 : 0 < M := by rw [hM]; omega
  have h4m : (4 : ℕ).Coprime m := hm2.symm.pow_left 2
  have h9m : (9 : ℕ).Coprime m := hm3.symm.pow_left 2
  have hcop43 : (4 * 3 ^ 2).Coprime M := by
    rw [hM]
    exact h4m.mul_left h9m
  have hnd : ¬ (2 : ℕ) ∣ M := by
    rw [hM]
    rintro ⟨r, hr⟩
    exact (Nat.prime_two.coprime_iff_not_dvd).mp hm2.symm ⟨r, hr⟩
  have hcop2 : M.Coprime (2 ^ (a - 2)) :=
    ((Nat.prime_two.coprime_iff_not_dvd).mpr hnd).symm.pow_right _
  obtain ⟨t, htlt, ht2, htdvd⟩ := sigma_t_solve2 (v := 2)
    (ρ := rhob a 0 2) (S := K + j) (M := M) (w := a - 2)
    hM0 hcop43 hcop2
  obtain ⟨D, hDpal, hD10, hDne, hD0, hD25, hD3v, hDσ, hr₀lt, hlenD⟩ :=
    border_pal_q (a' := a) (b' := 0) (q := 2) (s₁ := a) (t := t)
      (by norm_num) (by norm_num) (Or.inr rfl)
      (le_of_eq (Nat.max_eq_left (Nat.zero_le a)))
  set lenD := D.length with hlenD'
  have hr0z : r0b a 0 2 = 0 := by
    have h := hr₀lt
    norm_num at h
    omega
  have hlenN : lenD
      = 2 * ((Nat.digits 10 (9 * 2 ^ a)).length + a) + 2 * t := by
    have h := hlenD
    rw [hr0z] at h
    norm_num at h ⊢
    omega
  have lenV_le : (Nat.digits 10 (9 * 2 ^ a)).length ≤ a + 2 := by
    have hVpos : (9 * 2 ^ a : ℕ) ≠ 0 := by positivity
    have hb2 := Nat.base_pow_length_digits_le 10 (9 * 2 ^ a)
      (by norm_num) hVpos
    have hlt : 10 * (9 * 2 ^ a) < 10 ^ (a + 2) := by
      have h1 : (2 : ℕ) ^ a ≤ 10 ^ a := Nat.pow_le_pow_left (by norm_num) _
      calc 10 * (9 * 2 ^ a) = 90 * 2 ^ a := by ring
        _ ≤ 90 * 10 ^ a := Nat.mul_le_mul_left 90 h1
        _ < 100 * 10 ^ a := by omega
        _ = 10 ^ (a + 2) := by ring
    have hpow : 10 ^ ((Nat.digits 10 (9 * 2 ^ a)).length)
        < 10 ^ (a + 2) := lt_of_le_of_lt hb2 hlt
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 10)).mp hpow
    omega
  have hDeven : Even lenD := by
    rw [hlenN]
    exact ⟨(Nat.digits 10 (9 * 2 ^ a)).length + a + t, by ring⟩
  have hde11 : Nat.ofDigits (10 : ZMod 11) D = 0 :=
    ofDigits_evenPal11 hDpal (by rw [← hlenD']; exact hDeven)
  have hde11r : Nat.ofDigits (10 : ZMod 11) D.reverse = 0 := by
    rw [hDpal.reverse_eq]
    exact hde11
  have hde3 : 3 ∣ Nat.ofDigits 10 D :=
    dvd_trans (by norm_num : (3 : ℕ) ∣ 3 ^ 2) hD3v
  have hde3r : 3 ∣ Nat.ofDigits 10 D.reverse := by
    rw [hDpal.reverse_eq]
    exact hde3
  have hpar : 4 ∣ 2 ^ a * 3 * m - 2 * lenD := by
    have h4n : 4 ∣ 2 ^ a * 3 * m := by
      have h4a : (4 : ℕ) ∣ 2 ^ a := by
        have h := pow_dvd_pow 2 ha
        norm_num at h
        exact h
      rw [mul_assoc]
      exact dvd_mul_of_dvd_left h4a _
    have h4l : 4 ∣ 2 * lenD := by
      obtain ⟨w, hw⟩ := hDeven
      exact ⟨w, by omega⟩
    exact Nat.dvd_sub h4n h4l
  set S := 4 * K + 2 * j + 2 * lenD with hS
  have hSeven : Even S := ⟨2 * K + j + lenD, by rw [hS]; ring⟩
  have hne : Even n := by
    rw [hn]
    refine ⟨2 ^ (a - 1) * 3 * m, ?_⟩
    rw [show 2 ^ a = 2 * 2 ^ (a - 1) from by
      rw [← Nat.pow_succ', Nat.succ_eq_add_one,
        Nat.sub_add_cancel (by omega : 1 ≤ a)]]
    ring
  set X := n - S with hX
  have hXeven : Even X := by
    obtain ⟨an, han⟩ := hne
    obtain ⟨as, has⟩ := hSeven
    refine ⟨an - as, ?_⟩
    rw [hX, han, has]
    omega
  set T := X / 2 with hT'
  have hbound : 4 * K + 2 * j + 2 * lenD + 4 ≤ n := by
    set E := 2 ^ a * m with hE
    have hnE : n = 3 * E := by rw [hn, hE]; ring
    have hB' : 4 * K + 2 ^ a + 8 * a + 8 + E ≤ 3 * E := by
      rw [hK, hE]
      exact hB
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
      have hlv := lenV_le
      omega
    rw [hK, hj, hnE]
    omega
  have h2T : 2 * T = X := by
    rw [hT']
    omega
  have hT : 2 * T = n - (4 * K + 2 * j + 2 * lenD) := by
    rw [h2T, hX, hS]
  have hKcov : m * 3 ^ (1 - 4) ≤ 1 + 9 * (K / 2) := by
    rw [show (1 : ℕ) - 4 = 0 from rfl, pow_zero, mul_one, hK]
    have hdm := Nat.div_add_mod m 2
    omega
  set C := List.replicate j 9 ++ List.replicate T 0
      ++ List.replicate T 0 ++ List.replicate j 9 with hCdef
  have hCval3 : 3 ∣ Nat.ofDigits 10 C := by
    apply ofDigits_dvd_of_mem
    intro d hd
    rw [hCdef] at hd
    rcases List.mem_append.mp hd with hABC | h9last
    · rcases List.mem_append.mp hABC with hAB | hT2
      · rcases List.mem_append.mp hAB with h9a | hT1
        · rw [List.eq_of_mem_replicate h9a]
          exact ⟨3, by norm_num⟩
        · rw [List.eq_of_mem_replicate hT1]
          exact dvd_zero _
      · rw [List.eq_of_mem_replicate hT2]
        exact dvd_zero _
    · rw [List.eq_of_mem_replicate h9last]
      exact ⟨3, by norm_num⟩
  obtain ⟨s₀, hs0⟩ := hs0_v1' (le := lenD) (K := K)
    (g := 2 * j + 2 * T) D hde3 hde3r C hCval3
  have hσdiv : 2 ^ a * 3 * m ∣ 2 * D.sum + 18 * (K + j) := by
    have hσe : 2 * D.sum + 18 * (K + j)
        = 4 * 3 ^ 2 * (rhob a 0 2 + t) + 18 * (K + j) := by
      rw [hDσ]
      ring
    rw [hσe]
    have h2a : 2 ^ a ∣ 4 * 3 ^ 2 * (rhob a 0 2 + t) + 18 * (K + j) := by
      apply Nat.dvd_add
      · have h21 : 2 ^ a ∣ 4 * (rhob a 0 2 + t) := by
          obtain ⟨u, hu⟩ := ht2
          have hpa : 2 ^ a = 2 ^ (a - 2) * 4 := by
            rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, ← pow_add,
              show a - 2 + 2 = a from by omega]
          rw [hpa]
          exact ⟨u, by rw [hu]; ring⟩
        have e1 : 4 * 3 ^ 2 * (rhob a 0 2 + t)
            = 3 ^ 2 * (4 * (rhob a 0 2 + t)) := by ring
        rw [e1]
        exact dvd_mul_of_dvd_right h21 _
      · have h22 : 2 ^ a ∣ 2 * (m + c) := by
          obtain ⟨u, hu⟩ := hmc
          rw [hp2] at hu
          have hpa : 2 ^ a = 2 ^ (a - 1) * 2 := by
            rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ a)]
          rw [hpa]
          exact ⟨u, by rw [hu]; ring⟩
        have e2 : 18 * (K + j) = 9 * (2 * (m + c)) := by
          rw [hK, hj]
          ring
        rw [e2]
        exact dvd_mul_of_dvd_right h22 _
    have h3 : 3 ∣ 4 * 3 ^ 2 * (rhob a 0 2 + t) + 18 * (K + j) := by
      apply Nat.dvd_add
      · exact ⟨4 * 3 * (rhob a 0 2 + t), by ring⟩
      · exact ⟨6 * (K + j), by ring⟩
    have hMdvd : m ∣ 4 * 3 ^ 2 * (rhob a 0 2 + t) + 18 * (K + j) := by
      rw [← hM]
      exact htdvd
    have hcop2a : (2 ^ a).Coprime 3 :=
      ((by decide : Nat.Coprime 2 3).pow_left a)
    have hjoin1 := hcop2a.mul_dvd_of_dvd_of_dvd h2a h3
    have hcopB : (2 ^ a * 3).Coprime m := by
      have h2m : m.Coprime (2 ^ a) := hm2.pow_right a
      have h3m : m.Coprime 3 := hm3
      exact (h2m.mul_right h3m).symm
    have hjoin2 := hcopB.mul_dvd_of_dvd_of_dvd hjoin1 hMdvd
    exact hjoin2
  exact assemble_sandwich_R2 (a := a) (v := 1) (le := lenD) (K := K)
    (j := j) (T := T) (by omega) hm0 hm30 hT hbound hc1
    hKcov D hlenD'.symm hD10 hDne hD0 hD25 hde11 hde11r hpar
    (by omega) C hCdef s₀ hs0 hσdiv


theorem hard_closed_v1 {a m : ℕ} (ha : 1 ≤ a) (hm30 : m.Coprime 30)
    (hbad : 11 ∣ m ∨ 101 ∣ m) : finGoal (2 ^ a * 3 * m) := by
  have hm0 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0] at hm30
      exact absurd hm30 (by decide)
    · exact h0
  have hmb : 11 ≤ m := by
    rcases hbad with h | h
    · exact Nat.le_of_dvd hm0 h
    · exact le_trans (by norm_num) (Nat.le_of_dvd hm0 h)
  rcases Nat.lt_or_ge a 2 with ha1 | ha2
  · have ha1' : a = 1 := by omega
    subst ha1'
    by_cases hm11 : m = 11
    · subst hm11
      simpa using wit66
    · have hm25 : 25 ≤ m := by
        rcases hbad with h | h
        · obtain ⟨q, hq⟩ := h
          rcases Nat.lt_or_ge q 7 with hq7 | hq7
          · exfalso
            rw [hq] at hm0 hm11 hm30
            interval_cases q
            · exact absurd hm0 (by decide)
            · exact hm11 (by omega)
            · exact absurd hm30 (by decide)
            · exact absurd hm30 (by decide)
            · exact absurd hm30 (by decide)
            · exact absurd hm30 (by decide)
            · exact absurd hm30 (by decide)
          · have : 77 ≤ 11 * q := by
              calc 77 = 11 * 7 := by norm_num
                _ ≤ 11 * q := Nat.mul_le_mul_left 11 hq7
            rw [hq]
            omega
        · obtain ⟨q, hq⟩ := h
          rw [hq]
          have hq1 : 1 ≤ q := Nat.pos_of_ne_zero (fun h => by
            rw [h] at hq
            omega)
          calc 25 ≤ 101 := by norm_num
            _ ≤ 101 * q := Nat.le_mul_of_pos_right _ hq1
      exact assemble_eb01a_R2 hm0 hm30 (eb01a_R2_capacity hm25)
  · exact assemble_eb01_R2 ha2 hm0 hm30 (eb01_R2_capacity ha2 hmb)


theorem hard_closed_v234 {a v m : ℕ} (ha : 1 ≤ a) (hm0 : 1 ≤ m)
    (hv2 : 2 ≤ v) (hv4 : v ≤ 4) (hm30 : m.Coprime 30)
    (hbad : 11 ∣ m ∨ 101 ∣ m) : finGoal (2 ^ a * 3 ^ v * m) := by
  classical
  set n := 2 ^ a * 3 ^ v * m with hn
  haveI : NeZero m := ⟨by omega⟩
  have hm3 : m.Coprime 3 := hm30.coprime_dvd_right (by norm_num)
  have hm10 : m.Coprime 10 := hm30.coprime_dvd_right (by norm_num)
  have hm2 : m.Coprime 2 := hm30.coprime_dvd_right (by norm_num)
  have hmb : 11 ≤ m := by
    rcases hbad with h | h
    · exact Nat.le_of_dvd hm0 h
    · exact le_trans (by norm_num) (Nat.le_of_dvd hm0 h)
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
  set K := m * 3 ^ (v - 2) with hK
  set j := c * 3 ^ (v - 2) with hj
  set M := m with hM
  have hM0 : 0 < M := by rw [hM]; omega
  have h4m : (4 : ℕ).Coprime m := hm2.symm.pow_left 2
  have h3vm : (3 ^ v).Coprime m := hm3.symm.pow_left v
  have hcop43 : (4 * 3 ^ v).Coprime M := by
    rw [hM]
    exact h4m.mul_left h3vm
  have hnd : ¬ (2 : ℕ) ∣ M := by
    rw [hM]
    rintro ⟨r, hr⟩
    exact (Nat.prime_two.coprime_iff_not_dvd).mp hm2.symm ⟨r, hr⟩
  have hcop2 : M.Coprime (2 ^ (a - 2)) :=
    ((Nat.prime_two.coprime_iff_not_dvd).mpr hnd).symm.pow_right _
  obtain ⟨t, htlt, ht2, htdvd⟩ := sigma_t_solve2 (v := v)
    (ρ := rhob a 0 v) (S := K + j) (M := M) (w := a - 2)
    hM0 hcop43 hcop2
  have hmin : a = 0 ∨ (0 : ℕ) = 0 := Or.inr rfl
  obtain ⟨D, hDpal, hD10, hDne, hD0, hD25, hD3v, hDσ, hr₀lt, hlenD⟩ :=
    border_pal_q (a' := a) (b' := 0) (q := v) (s₁ := a) (t := t)
      hv2 hv4 hmin (le_of_eq (Nat.max_eq_left (Nat.zero_le a)))
  set lenD := D.length with hlenD'
  have hlenN : lenD
      = 2 * ((Nat.digits 10 (9 * 2 ^ a)).length + a + r0b a 0 v)
        + 2 * (3 ^ (v - 2) * t) := by
    have h := hlenD
    rw [show 9 * 2 ^ a * 5 ^ 0 = 9 * 2 ^ a from by simp] at h
    rw [h]
    ring
  have lenV_le : (Nat.digits 10 (9 * 2 ^ a)).length ≤ a + 2 := by
    have hVpos : (9 * 2 ^ a : ℕ) ≠ 0 := by positivity
    have hb2 := Nat.base_pow_length_digits_le 10 (9 * 2 ^ a)
      (by norm_num) hVpos
    have hlt : 10 * (9 * 2 ^ a) < 10 ^ (a + 2) := by
      have h1 : (2 : ℕ) ^ a ≤ 10 ^ a := Nat.pow_le_pow_left (by norm_num) _
      calc 10 * (9 * 2 ^ a) = 90 * 2 ^ a := by ring
        _ ≤ 90 * 10 ^ a := Nat.mul_le_mul_left 90 h1
        _ < 100 * 10 ^ a := by omega
        _ = 10 ^ (a + 2) := by ring
    have hpow : 10 ^ ((Nat.digits 10 (9 * 2 ^ a)).length)
        < 10 ^ (a + 2) := lt_of_le_of_lt hb2 hlt
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 10)).mp hpow
    omega
  have hDeven : Even lenD := by
    rw [hlenN]
    exact ⟨(Nat.digits 10 (9 * 2 ^ a)).length + a + r0b a 0 v
      + 3 ^ (v - 2) * t, by ring⟩
  have hde11D : Nat.ofDigits (10 : ZMod 11) D = 0 :=
    ofDigits_evenPal11 hDpal (by rw [← hlenD']; exact hDeven)
  have hde11Dr : Nat.ofDigits (10 : ZMod 11) D.reverse = 0 := by
    rw [hDpal.reverse_eq]
    exact hde11D
  set de := if a = 1 then D ++ [0] else D with hde
  set le := if a = 1 then lenD + 1 else lenD with hle'
  have hle : de.length = le := by
    rw [hde, hle']
    split_ifs with h1
    · rw [List.length_append, List.length_singleton, ← hlenD']
    · rw [← hlenD']
  have hle_le : le ≤ lenD + 1 := by
    rw [hle']
    split_ifs
    · omega
    · omega
  have hde10 : ∀ x ∈ de, x < 10 := by
    rw [hde]
    split_ifs with h1
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hD10 x hx
      · rw [List.mem_singleton] at hx
        omega
    · exact hD10
  have hdene : de ≠ [] := by
    rw [hde]
    split_ifs with h1
    · intro h
      exact hDne (List.append_eq_nil_iff.mp h).1
    · exact hDne
  have hde0 : ∀ h : de ≠ [], de.head h ≠ 0 := by
    rw [hde]
    split_ifs with h1
    · intro h
      rcases D with _ | ⟨d, ds⟩
      · exact absurd rfl hDne
      · exact hD0 hDne
    · exact hD0
  have hde2a : 2 ^ a * 5 ^ 0 ∣ Nat.ofDigits 10 de := by
    rw [hde]
    split_ifs with h1
    · rw [ofDigits_append_zero]
      exact hD25
    · exact hD25
  have hde11 : Nat.ofDigits (10 : ZMod 11) de = 0 := by
    rw [hde]
    split_ifs with h1
    · rw [ofDigits_append_zero]
      exact hde11D
    · exact hde11D
  have hde11r : Nat.ofDigits (10 : ZMod 11) de.reverse = 0 := by
    rw [hde]
    split_ifs with h1
    · rw [List.reverse_append, List.reverse_singleton,
        List.singleton_append, ofDigits_cons', hDpal.reverse_eq]
      simp [hde11D]
    · rw [hDpal.reverse_eq]
      exact hde11D
  have hde3v : 3 ^ v ∣ Nat.ofDigits 10 de := by
    rw [hde]
    split_ifs with h1
    · rw [ofDigits_append_zero]
      exact hD3v
    · exact hD3v
  have hde3r : 3 ^ v ∣ Nat.ofDigits 10 de.reverse := by
    rw [hde]
    split_ifs with h1
    · rw [List.reverse_append, List.reverse_singleton,
        List.singleton_append, Nat.ofDigits_cons, hDpal.reverse_eq]
      simp only [Nat.cast_zero, zero_add]
      exact dvd_mul_of_dvd_right hD3v 10
    · rw [hDpal.reverse_eq]
      exact hD3v
  have hpar : 4 ∣ 2 ^ a * 3 ^ v * m - 2 * le := by
    by_cases h1 : a = 1
    · have hle1 : le = lenD + 1 := by
        rw [hle', if_pos h1]
      rw [hle1, h1, pow_one]
      have hmo : Odd (3 ^ v * m) := by
        have hm : Odd m := by
          have h2 : ¬ (2 : ℕ) ∣ m :=
            (Nat.prime_two.coprime_iff_not_dvd).mp hm2.symm
          rw [← Nat.not_even_iff_odd]
          rintro ⟨c', hc'⟩
          exact h2 ⟨c', by omega⟩
        exact Odd.mul (Odd.pow (by decide : Odd 3)) hm
      obtain ⟨w', hw'⟩ := hmo
      obtain ⟨w, hw⟩ := hDeven
      have hvdec : 3 ^ v = 9 * 3 ^ (v - 2) := by
        rw [show (9 : ℕ) = 3 ^ 2 from by norm_num, ← pow_add,
          show 2 + (v - 2) = v from by omega]
      have htl : t + 1 ≤ m := by
        have h := htlt
        rw [hM, h1] at h
        have h20 : (2 : ℕ) ^ (1 - 2) = 1 := by norm_num
        rw [h20, mul_one] at h
        exact h
      have htY : 3 ^ (v - 2) * t + 3 ^ (v - 2) ≤ 3 ^ (v - 2) * m := by
        have h2 := Nat.mul_le_mul_left (3 ^ (v - 2)) htl
        rw [Nat.mul_succ] at h2
        exact h2
      have hlen1 : lenD
          = 2 * ((Nat.digits 10 (9 * 2 ^ 1)).length + 1 + r0b 1 0 v)
            + 2 * (3 ^ (v - 2) * t) := by
        have h := hlenN
        rw [h1] at h
        exact h
      have hlv1 : (Nat.digits 10 (9 * 2 ^ 1)).length ≤ 3 := by
        have h := lenV_le
        rw [h1] at h
        omega
      have hr01 : r0b 1 0 v + 1 ≤ 3 ^ (v - 2) := by
        have h := hr₀lt
        rw [h1] at h
        exact h
      have hY2 : 11 ≤ 3 ^ (v - 2) * m := by
        calc 11 ≤ m := hmb
          _ ≤ 3 ^ (v - 2) * m :=
              Nat.le_mul_of_pos_left _ (by positivity)
      have hlm : lenD + 1 ≤ 3 ^ v * m := by
        rw [hvdec, hlen1,
          show 9 * 3 ^ (v - 2) * m = 9 * (3 ^ (v - 2) * m) from by ring]
        omega
      refine ⟨(3 ^ v * m - (lenD + 1)) / 2, ?_⟩
      rw [show 2 * 3 ^ v * m = 2 * (3 ^ v * m) from by ring]
      omega
    · have ha2 : 2 ≤ a := by omega
      have hle2 : le = lenD := by
        rw [hle', if_neg h1]
      rw [hle2]
      have h4n : 4 ∣ 2 ^ a * 3 ^ v * m := by
        have h4a : (4 : ℕ) ∣ 2 ^ a := by
          have h := pow_dvd_pow 2 ha2
          norm_num at h
          exact h
        rw [mul_assoc]
        exact dvd_mul_of_dvd_left h4a _
      have h4l : 4 ∣ 2 * lenD := by
        obtain ⟨w, hw⟩ := hDeven
        exact ⟨w, by omega⟩
      exact Nat.dvd_sub h4n h4l
  set S := 4 * K + 2 * j + 2 * le with hS
  have hSeven : Even S := ⟨2 * K + j + le, by rw [hS]; ring⟩
  have hne : Even n := by
    rw [hn]
    refine ⟨2 ^ (a - 1) * 3 ^ v * m, ?_⟩
    rw [show 2 ^ a = 2 * 2 ^ (a - 1) from by
      rw [← Nat.pow_succ', Nat.succ_eq_add_one,
        Nat.sub_add_cancel ha]]
    ring
  set X := n - S with hX
  have hXeven : Even X := by
    obtain ⟨an, han⟩ := hne
    obtain ⟨as, has⟩ := hSeven
    refine ⟨an - as, ?_⟩
    rw [hX, han, has]
    omega
  set T := X / 2 with hT'
  have hbound : 4 * K + 2 * j + 2 * le + 4 ≤ n := by
    set E := 2 ^ a * 3 ^ (v - 2) * m with hE
    have hvdec : 3 ^ v = 9 * 3 ^ (v - 2) := by
      rw [show (9 : ℕ) = 3 ^ 2 from by norm_num, ← pow_add,
        show 2 + (v - 2) = v from by omega]
    have hE9 : n = 9 * E := by
      rw [hn, hE, hvdec]
      ring
    have g1 : 4 * (m * 3 ^ (v - 2)) ≤ 2 * E := by
      have h2a1 : 4 ≤ 2 * 2 ^ a := by
        have h : (2 : ℕ) ^ 1 ≤ 2 ^ a :=
          Nat.pow_le_pow_right (by norm_num) ha
        norm_num at h ⊢
        omega
      calc 4 * (m * 3 ^ (v - 2))
          ≤ (2 * 2 ^ a) * (m * 3 ^ (v - 2)) :=
            Nat.mul_le_mul_right _ h2a1
        _ = 2 * (2 ^ a * 3 ^ (v - 2) * m) := by ring
        _ = 2 * E := by rw [hE]
    have g2 : 2 * (c * 3 ^ (v - 2)) ≤ E := by
      have hc2 : 2 * c ≤ 2 ^ a := by
        calc 2 * c ≤ 2 * 2 ^ (a - 1) :=
              Nat.mul_le_mul_left 2 hcle
          _ = 2 ^ a := by
              rw [← Nat.pow_succ', Nat.succ_eq_add_one,
                Nat.sub_add_cancel ha]
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
    have hlen3 : 2 * le
        ≤ 8 * a + 4 * (3 ^ (v - 2) * t) + 4 * 3 ^ (v - 2) + 14 := by
      have hlv := lenV_le
      have hr0 : r0b a 0 v + 1 ≤ 3 ^ (v - 2) := hr₀lt
      have hlel := hle_le
      rw [hlenN] at hlel
      omega
    rw [hK, hj, hE9]
    have hB' : 8 * a + 18 ≤ 4 * E := by
      have h2a1 : a ≤ 2 ^ a := le_of_lt Nat.lt_two_pow_self
      have hEm : 4 * (2 ^ a * m) ≤ 4 * E := by
        apply Nat.mul_le_mul_left 4
        rw [hE]
        exact Nat.mul_le_mul_right m
          (Nat.le_mul_of_pos_right _ (by positivity))
      have h44 : 8 * a + 18 ≤ 44 * a := by omega
      have h44b : 44 * a ≤ 44 * 2 ^ a := Nat.mul_le_mul_left 44 h2a1
      have hE2 : 44 * 2 ^ a ≤ 4 * (2 ^ a * m) := by
        calc 44 * 2 ^ a = 4 * (2 ^ a * 11) := by ring
          _ ≤ 4 * (2 ^ a * m) :=
              Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left (2 ^ a) hmb)
      omega
    omega
  have h2T : 2 * T = X := by
    rw [hT']
    omega
  have hT : 2 * T = n - (4 * K + 2 * j + 2 * le) := by
    rw [h2T, hX, hS]
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
  set C := List.replicate j 9 ++ List.replicate T 0
      ++ List.replicate T 0 ++ List.replicate j 9 with hCdef
  have hCval3 : 3 ^ v ∣ Nat.ofDigits 10 C :=
    center_repunit_even_dvd3 hv2 ⟨c, by rw [hj]; ring⟩
  have hK1 : 1 ≤ K := by
    rw [hK]
    have : 0 < m * 3 ^ (v - 2) := by positivity
    omega
  have hKv : 3 ^ (v - 2) ∣ K := by
    rw [hK]
    exact dvd_mul_of_dvd_right (dvd_refl _) m
  obtain ⟨s₀, hs0⟩ := hs0_v4' (le := le) (K := K)
    (g := 2 * j + 2 * T) hv2 hv4 hK1 de hde3v hde3r C hCval3 hKv
  have hdeσ : de.sum = 2 * 3 ^ v * (rhob a 0 v + t) := by
    rw [hde]
    split_ifs with h1
    · rw [List.sum_append, List.sum_singleton]
      have h := hDσ
      omega
    · exact hDσ
  have hσdiv : 2 ^ a * 3 ^ v * m ∣ 2 * de.sum + 18 * (K + j) := by
    have hσe : 2 * de.sum + 18 * (K + j)
        = 4 * 3 ^ v * (rhob a 0 v + t) + 18 * (K + j) := by
      rw [hdeσ]
      ring
    rw [hσe]
    have h2a : 2 ^ a ∣ 4 * 3 ^ v * (rhob a 0 v + t) + 18 * (K + j) := by
      apply Nat.dvd_add
      · have h21 : 2 ^ a ∣ 4 * (rhob a 0 v + t) := by
          rcases Nat.lt_or_ge 2 a with h | h
          · obtain ⟨u, hu⟩ := ht2
            have hpa : 2 ^ a = 2 ^ (a - 2) * 4 := by
              rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, ← pow_add,
                show a - 2 + 2 = a from by omega]
            rw [hpa]
            exact ⟨u, by rw [hu]; ring⟩
          · exact dvd_mul_of_dvd_left
              (show 2 ^ a ∣ 4 from by
                have h' := pow_dvd_pow 2 (by omega : a ≤ 2)
                norm_num at h'
                exact h') _
        have e1 : 4 * 3 ^ v * (rhob a 0 v + t)
            = 3 ^ v * (4 * (rhob a 0 v + t)) := by ring
        rw [e1]
        exact dvd_mul_of_dvd_right h21 _
      · have h22 : 2 ^ a ∣ 2 * (m + c) := by
          obtain ⟨u, hu⟩ := hmc
          rw [hp2] at hu
          have hpa : 2 ^ a = 2 ^ (a - 1) * 2 := by
            rw [← pow_succ, Nat.sub_add_cancel ha]
          rw [hpa]
          exact ⟨u, by rw [hu]; ring⟩
        have e2 : 18 * (K + j) = (9 * 3 ^ (v - 2)) * (2 * (m + c)) := by
          rw [hK, hj, ← Nat.add_mul]
          ring
        rw [e2]
        exact dvd_mul_of_dvd_right h22 _
    have h3vd : 3 ^ v ∣ 4 * 3 ^ v * (rhob a 0 v + t) + 18 * (K + j) := by
      apply Nat.dvd_add
      · exact ⟨4 * (rhob a 0 v + t), by ring⟩
      · refine ⟨2 * (m + c), ?_⟩
        rw [hK, hj, ← Nat.add_mul]
        rw [show (3 : ℕ) ^ v = 9 * 3 ^ (v - 2) from by
          rw [show (9 : ℕ) = 3 ^ 2 from by norm_num, ← pow_add,
            show 2 + (v - 2) = v from by omega]]
        ring
    have hMdvd : m ∣ 4 * 3 ^ v * (rhob a 0 v + t) + 18 * (K + j) := by
      rw [← hM]
      exact htdvd
    have hcop2a : (2 ^ a).Coprime (3 ^ v) :=
      ((by decide : Nat.Coprime 2 3).pow_right v).pow_left a
    have hcopB : (2 ^ a * 3 ^ v).Coprime m :=
      Nat.Coprime.mul_left (hm2.symm.pow_left a) (hm3.symm.pow_left v)
    have hjoin1 := hcop2a.mul_dvd_of_dvd_of_dvd h2a h3vd
    exact hcopB.mul_dvd_of_dvd_of_dvd hjoin1 hMdvd
  have hlea : a ≤ le := by
    rw [hle']
    split_ifs with h1
    · rw [h1]
      omega
    · rw [hlenN]
      have hlv := lenV_le
      omega
  have hj1 : 1 ≤ j := by
    rw [hj]
    exact Nat.mul_pos hc1 (by positivity)
  exact assemble_sandwich_R2 (a := a) (v := v) (le := le) (K := K)
    (j := j) (T := T) ha hm0 hm30 hT hbound hj1 hKcov de hle hde10
    hdene hde0 hde2a hde11 hde11r hpar hlea C hCdef s₀ hs0 hσdiv


theorem hard_closed_v5 {a v m : ℕ} (ha : 1 ≤ a) (hm0 : 1 ≤ m)
    (hv5 : 5 ≤ v) (hm30 : m.Coprime 30)
    (hbad : 11 ∣ m ∨ 101 ∣ m) : finGoal (2 ^ a * 3 ^ v * m) := by
  classical
  set n := 2 ^ a * 3 ^ v * m with hn
  haveI : NeZero m := ⟨by omega⟩
  have hm3 : m.Coprime 3 := hm30.coprime_dvd_right (by norm_num)
  have hm10 : m.Coprime 10 := hm30.coprime_dvd_right (by norm_num)
  have hm2 : m.Coprime 2 := hm30.coprime_dvd_right (by norm_num)
  have hmb : 11 ≤ m := by
    rcases hbad with h | h
    · exact Nat.le_of_dvd hm0 h
    · exact le_trans (by norm_num) (Nat.le_of_dvd hm0 h)
  have hv2 : 2 ≤ v := by omega
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
  set K := m * 3 ^ (v - 2) with hK
  set j := c * 3 ^ (v - 2) with hj
  set M := m with hM
  have hM0 : 0 < M := by rw [hM]; omega
  have h4m : (4 : ℕ).Coprime m := hm2.symm.pow_left 2
  have h3vm : (3 ^ v).Coprime m := hm3.symm.pow_left v
  have hcop43 : (4 * 3 ^ v).Coprime M := by
    rw [hM]
    exact h4m.mul_left h3vm
  have hnd : ¬ (2 : ℕ) ∣ M := by
    rw [hM]
    rintro ⟨r, hr⟩
    exact (Nat.prime_two.coprime_iff_not_dvd).mp hm2.symm ⟨r, hr⟩
  have hcop2 : M.Coprime (2 ^ (a - 2)) :=
    ((Nat.prime_two.coprime_iff_not_dvd).mpr hnd).symm.pow_right _
  obtain ⟨t, htlt, ht2, htdvd⟩ := sigma_t_solve2 (v := v)
    (ρ := rhob a 0 v) (S := K + j) (M := M) (w := a - 2)
    hM0 hcop43 hcop2
  have hmin : a = 0 ∨ (0 : ℕ) = 0 := Or.inr rfl
  obtain ⟨D, hDpal, hD10, hDne, hD0, hD25, hD81, hDσ, hr₀lt, hlenD⟩ :=
    border_pal (a' := a) (b' := 0) (q := v) (s₁ := a) (t := t)
      (by omega) hmin (le_of_eq (Nat.max_eq_left (Nat.zero_le a)))
  set lenD := D.length with hlenD'
  have hlenN : lenD
      = 2 * ((Nat.digits 10 (9 * 2 ^ a)).length + a + r0b a 0 v)
        + 2 * (3 ^ (v - 2) * t) := by
    have h := hlenD
    rw [show 9 * 2 ^ a * 5 ^ 0 = 9 * 2 ^ a from by simp] at h
    rw [h]
    ring
  have lenV_le : (Nat.digits 10 (9 * 2 ^ a)).length ≤ a + 2 := by
    have hVpos : (9 * 2 ^ a : ℕ) ≠ 0 := by positivity
    have hb2 := Nat.base_pow_length_digits_le 10 (9 * 2 ^ a)
      (by norm_num) hVpos
    have hlt : 10 * (9 * 2 ^ a) < 10 ^ (a + 2) := by
      have h1 : (2 : ℕ) ^ a ≤ 10 ^ a := Nat.pow_le_pow_left (by norm_num) _
      calc 10 * (9 * 2 ^ a) = 90 * 2 ^ a := by ring
        _ ≤ 90 * 10 ^ a := Nat.mul_le_mul_left 90 h1
        _ < 100 * 10 ^ a := by omega
        _ = 10 ^ (a + 2) := by ring
    have hpow : 10 ^ ((Nat.digits 10 (9 * 2 ^ a)).length)
        < 10 ^ (a + 2) := lt_of_le_of_lt hb2 hlt
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 10)).mp hpow
    omega
  have hDeven : Even lenD := by
    rw [hlenN]
    exact ⟨(Nat.digits 10 (9 * 2 ^ a)).length + a + r0b a 0 v
      + 3 ^ (v - 2) * t, by ring⟩
  have hde11D : Nat.ofDigits (10 : ZMod 11) D = 0 :=
    ofDigits_evenPal11 hDpal (by rw [← hlenD']; exact hDeven)
  have hde11Dr : Nat.ofDigits (10 : ZMod 11) D.reverse = 0 := by
    rw [hDpal.reverse_eq]
    exact hde11D
  set de := if a = 1 then D ++ [0] else D with hde
  set le := if a = 1 then lenD + 1 else lenD with hle'
  have hle : de.length = le := by
    rw [hde, hle']
    split_ifs with h1
    · rw [List.length_append, List.length_singleton, ← hlenD']
    · rw [← hlenD']
  have hle_le : le ≤ lenD + 1 := by
    rw [hle']
    split_ifs
    · omega
    · omega
  have hde10 : ∀ x ∈ de, x < 10 := by
    rw [hde]
    split_ifs with h1
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hD10 x hx
      · rw [List.mem_singleton] at hx
        omega
    · exact hD10
  have hdene : de ≠ [] := by
    rw [hde]
    split_ifs with h1
    · intro h
      exact hDne (List.append_eq_nil_iff.mp h).1
    · exact hDne
  have hde0 : ∀ h : de ≠ [], de.head h ≠ 0 := by
    rw [hde]
    split_ifs with h1
    · intro h
      rcases D with _ | ⟨d, ds⟩
      · exact absurd rfl hDne
      · exact hD0 hDne
    · exact hD0
  have hde2a : 2 ^ a * 5 ^ 0 ∣ Nat.ofDigits 10 de := by
    rw [hde]
    split_ifs with h1
    · rw [ofDigits_append_zero]
      exact hD25
    · exact hD25
  have hde11 : Nat.ofDigits (10 : ZMod 11) de = 0 := by
    rw [hde]
    split_ifs with h1
    · rw [ofDigits_append_zero]
      exact hde11D
    · exact hde11D
  have hde11r : Nat.ofDigits (10 : ZMod 11) de.reverse = 0 := by
    rw [hde]
    split_ifs with h1
    · rw [List.reverse_append, List.reverse_singleton,
        List.singleton_append, ofDigits_cons', hDpal.reverse_eq]
      simp [hde11D]
    · rw [hDpal.reverse_eq]
      exact hde11D
  have hD81n : 81 ∣ Nat.ofDigits 10 D := by
    have h : ((Nat.ofDigits 10 D : ℕ) : ZMod 81) = 0 := by
      rw [cast_ofDigits]
      exact hD81
    exact (CharP.cast_eq_zero_iff (ZMod 81) 81 _).mp h
  have hde81 : 81 ∣ Nat.ofDigits 10 de := by
    rw [hde]
    split_ifs with h1
    · rw [ofDigits_append_zero]
      exact hD81n
    · exact hD81n
  have hde81r : 81 ∣ Nat.ofDigits 10 de.reverse := by
    rw [hde]
    split_ifs with h1
    · rw [List.reverse_append, List.reverse_singleton,
        List.singleton_append, Nat.ofDigits_cons, hDpal.reverse_eq]
      simp only [Nat.cast_zero, zero_add]
      exact dvd_mul_of_dvd_right hD81n 10
    · rw [hDpal.reverse_eq]
      exact hD81n
  have hpar : 4 ∣ 2 ^ a * 3 ^ v * m - 2 * le := by
    by_cases h1 : a = 1
    · have hle1 : le = lenD + 1 := by
        rw [hle', if_pos h1]
      rw [hle1, h1, pow_one]
      have hmo : Odd (3 ^ v * m) := by
        have hm : Odd m := by
          have h2 : ¬ (2 : ℕ) ∣ m :=
            (Nat.prime_two.coprime_iff_not_dvd).mp hm2.symm
          rw [← Nat.not_even_iff_odd]
          rintro ⟨c', hc'⟩
          exact h2 ⟨c', by omega⟩
        exact Odd.mul (Odd.pow (by decide : Odd 3)) hm
      obtain ⟨w', hw'⟩ := hmo
      obtain ⟨w, hw⟩ := hDeven
      have hvdec : 3 ^ v = 9 * 3 ^ (v - 2) := by
        rw [show (9 : ℕ) = 3 ^ 2 from by norm_num, ← pow_add,
          show 2 + (v - 2) = v from by omega]
      have htl : t + 1 ≤ m := by
        have h := htlt
        rw [hM, h1] at h
        have h20 : (2 : ℕ) ^ (1 - 2) = 1 := by norm_num
        rw [h20, mul_one] at h
        exact h
      have htY : 3 ^ (v - 2) * t + 3 ^ (v - 2) ≤ 3 ^ (v - 2) * m := by
        have h2 := Nat.mul_le_mul_left (3 ^ (v - 2)) htl
        rw [Nat.mul_succ] at h2
        exact h2
      have hlen1 : lenD
          = 2 * ((Nat.digits 10 (9 * 2 ^ 1)).length + 1 + r0b 1 0 v)
            + 2 * (3 ^ (v - 2) * t) := by
        have h := hlenN
        rw [h1] at h
        exact h
      have hlv1 : (Nat.digits 10 (9 * 2 ^ 1)).length ≤ 3 := by
        have h := lenV_le
        rw [h1] at h
        omega
      have hr01 : r0b 1 0 v + 1 ≤ 3 ^ (v - 2) := by
        have h := hr₀lt
        rw [h1] at h
        exact h
      have hY2 : 11 ≤ 3 ^ (v - 2) * m := by
        calc 11 ≤ m := hmb
          _ ≤ 3 ^ (v - 2) * m :=
              Nat.le_mul_of_pos_left _ (by positivity)
      have hlm : lenD + 1 ≤ 3 ^ v * m := by
        rw [hvdec, hlen1,
          show 9 * 3 ^ (v - 2) * m = 9 * (3 ^ (v - 2) * m) from by ring]
        omega
      refine ⟨(3 ^ v * m - (lenD + 1)) / 2, ?_⟩
      rw [show 2 * 3 ^ v * m = 2 * (3 ^ v * m) from by ring]
      omega
    · have ha2 : 2 ≤ a := by omega
      have hle2 : le = lenD := by
        rw [hle', if_neg h1]
      rw [hle2]
      have h4n : 4 ∣ 2 ^ a * 3 ^ v * m := by
        have h4a : (4 : ℕ) ∣ 2 ^ a := by
          have h := pow_dvd_pow 2 ha2
          norm_num at h
          exact h
        rw [mul_assoc]
        exact dvd_mul_of_dvd_left h4a _
      have h4l : 4 ∣ 2 * lenD := by
        obtain ⟨w, hw⟩ := hDeven
        exact ⟨w, by omega⟩
      exact Nat.dvd_sub h4n h4l
  set S := 4 * K + 2 * j + 2 * le with hS
  have hSeven : Even S := ⟨2 * K + j + le, by rw [hS]; ring⟩
  have hne : Even n := by
    rw [hn]
    refine ⟨2 ^ (a - 1) * 3 ^ v * m, ?_⟩
    rw [show 2 ^ a = 2 * 2 ^ (a - 1) from by
      rw [← Nat.pow_succ', Nat.succ_eq_add_one,
        Nat.sub_add_cancel ha]]
    ring
  set X := n - S with hX
  have hXeven : Even X := by
    obtain ⟨an, han⟩ := hne
    obtain ⟨as, has⟩ := hSeven
    refine ⟨an - as, ?_⟩
    rw [hX, han, has]
    omega
  set T := X / 2 with hT'
  have hbound : 4 * K + 2 * j + 2 * le + 4 ≤ n := by
    set E := 2 ^ a * 3 ^ (v - 2) * m with hE
    have hvdec : 3 ^ v = 9 * 3 ^ (v - 2) := by
      rw [show (9 : ℕ) = 3 ^ 2 from by norm_num, ← pow_add,
        show 2 + (v - 2) = v from by omega]
    have hE9 : n = 9 * E := by
      rw [hn, hE, hvdec]
      ring
    have g1 : 4 * (m * 3 ^ (v - 2)) ≤ 2 * E := by
      have h2a1 : 4 ≤ 2 * 2 ^ a := by
        have h : (2 : ℕ) ^ 1 ≤ 2 ^ a :=
          Nat.pow_le_pow_right (by norm_num) ha
        norm_num at h ⊢
        omega
      calc 4 * (m * 3 ^ (v - 2))
          ≤ (2 * 2 ^ a) * (m * 3 ^ (v - 2)) :=
            Nat.mul_le_mul_right _ h2a1
        _ = 2 * (2 ^ a * 3 ^ (v - 2) * m) := by ring
        _ = 2 * E := by rw [hE]
    have g2 : 2 * (c * 3 ^ (v - 2)) ≤ E := by
      have hc2 : 2 * c ≤ 2 ^ a := by
        calc 2 * c ≤ 2 * 2 ^ (a - 1) :=
              Nat.mul_le_mul_left 2 hcle
          _ = 2 ^ a := by
              rw [← Nat.pow_succ', Nat.succ_eq_add_one,
                Nat.sub_add_cancel ha]
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
    have hlen3 : 2 * le
        ≤ 8 * a + 4 * (3 ^ (v - 2) * t) + 4 * 3 ^ (v - 2) + 14 := by
      have hlv := lenV_le
      have hr0 : r0b a 0 v + 1 ≤ 3 ^ (v - 2) := hr₀lt
      have hlel := hle_le
      rw [hlenN] at hlel
      omega
    have hE2 : 18 ≤ 2 * E := by
      rw [hE]
      have hu4 : 27 ≤ 3 ^ (v - 2) := by
        have h : (3 : ℕ) ^ 3 ≤ 3 ^ (v - 2) :=
          Nat.pow_le_pow_right (by norm_num) (by omega : 3 ≤ v - 2)
        norm_num at h ⊢; exact h
      have h2a2 : 2 ≤ 2 ^ a := by
        have h : (2 : ℕ) ^ 1 ≤ 2 ^ a :=
          Nat.pow_le_pow_right (by norm_num) ha
        norm_num at h ⊢; exact h
      have h1 : 2 * 27 * 11 ≤ 2 ^ a * 3 ^ (v - 2) * m :=
        Nat.mul_le_mul (Nat.mul_le_mul h2a2 hu4) hmb
      omega
    rw [hK, hj, hE9]
    omega
  have h2T : 2 * T = X := by
    rw [hT']
    omega
  have hT : 2 * T = n - (4 * K + 2 * j + 2 * le) := by
    rw [h2T, hX, hS]
  have hKcov : m * 3 ^ (v - 4) ≤ 1 + 9 * (K / 2) := by
    have hpow : 3 ^ (v - 2) = 9 * 3 ^ (v - 4) := by
      rw [show (9 : ℕ) = 3 ^ 2 from by norm_num, ← pow_add,
        show 2 + (v - 4) = v - 2 from by omega]
    have hF : 0 < m * 3 ^ (v - 4) := by positivity
    rw [hK, hpow]
    have e : m * (9 * 3 ^ (v - 4)) = 9 * (m * 3 ^ (v - 4)) := by ring
    rw [e]
    omega
  set C := List.replicate j 9 ++ List.replicate T 0
      ++ List.replicate T 0 ++ List.replicate j 9 with hCdef
  have hCval3 : 3 ^ v ∣ Nat.ofDigits 10 C :=
    center_repunit_even_dvd3 hv2 ⟨c, by rw [hj]; ring⟩
  have hC81 : 81 ∣ Nat.ofDigits 10 C :=
    dvd_trans (pow_dvd_pow 3 (by omega : 4 ≤ v)) hCval3
  have hK1 : 1 ≤ K := by
    rw [hK]
    have : 0 < m * 3 ^ (v - 2) := by positivity
    omega
  have hK9 : 9 ∣ K := by
    rw [hK]
    exact dvd_mul_of_dvd_right (pow_dvd_pow 3 (by omega : 2 ≤ v - 2)) m
  obtain ⟨s₀, hs0⟩ := hs0_solver' (le := le) (K := K)
    (g := 2 * j + 2 * T) hv5 hK1 de hde81 hde81r C hC81 hK9
  have hdeσ : de.sum = 2 * 3 ^ v * (rhob a 0 v + t) := by
    rw [hde]
    split_ifs with h1
    · rw [List.sum_append, List.sum_singleton]
      have h := hDσ
      omega
    · exact hDσ
  have hσdiv : 2 ^ a * 3 ^ v * m ∣ 2 * de.sum + 18 * (K + j) := by
    have hσe : 2 * de.sum + 18 * (K + j)
        = 4 * 3 ^ v * (rhob a 0 v + t) + 18 * (K + j) := by
      rw [hdeσ]
      ring
    rw [hσe]
    have h2a : 2 ^ a ∣ 4 * 3 ^ v * (rhob a 0 v + t) + 18 * (K + j) := by
      apply Nat.dvd_add
      · have h21 : 2 ^ a ∣ 4 * (rhob a 0 v + t) := by
          rcases Nat.lt_or_ge 2 a with h | h
          · obtain ⟨u, hu⟩ := ht2
            have hpa : 2 ^ a = 2 ^ (a - 2) * 4 := by
              rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, ← pow_add,
                show a - 2 + 2 = a from by omega]
            rw [hpa]
            exact ⟨u, by rw [hu]; ring⟩
          · exact dvd_mul_of_dvd_left
              (show 2 ^ a ∣ 4 from by
                have h' := pow_dvd_pow 2 (by omega : a ≤ 2)
                norm_num at h'
                exact h') _
        have e1 : 4 * 3 ^ v * (rhob a 0 v + t)
            = 3 ^ v * (4 * (rhob a 0 v + t)) := by ring
        rw [e1]
        exact dvd_mul_of_dvd_right h21 _
      · have h22 : 2 ^ a ∣ 2 * (m + c) := by
          obtain ⟨u, hu⟩ := hmc
          rw [hp2] at hu
          have hpa : 2 ^ a = 2 ^ (a - 1) * 2 := by
            rw [← pow_succ, Nat.sub_add_cancel ha]
          rw [hpa]
          exact ⟨u, by rw [hu]; ring⟩
        have e2 : 18 * (K + j) = (9 * 3 ^ (v - 2)) * (2 * (m + c)) := by
          rw [hK, hj, ← Nat.add_mul]
          ring
        rw [e2]
        exact dvd_mul_of_dvd_right h22 _
    have h3vd : 3 ^ v ∣ 4 * 3 ^ v * (rhob a 0 v + t) + 18 * (K + j) := by
      apply Nat.dvd_add
      · exact ⟨4 * (rhob a 0 v + t), by ring⟩
      · refine ⟨2 * (m + c), ?_⟩
        rw [hK, hj, ← Nat.add_mul]
        rw [show (3 : ℕ) ^ v = 9 * 3 ^ (v - 2) from by
          rw [show (9 : ℕ) = 3 ^ 2 from by norm_num, ← pow_add,
            show 2 + (v - 2) = v from by omega]]
        ring
    have hMdvd : m ∣ 4 * 3 ^ v * (rhob a 0 v + t) + 18 * (K + j) := by
      rw [← hM]
      exact htdvd
    have hcop2a : (2 ^ a).Coprime (3 ^ v) :=
      ((by decide : Nat.Coprime 2 3).pow_right v).pow_left a
    have hcopB : (2 ^ a * 3 ^ v).Coprime m :=
      Nat.Coprime.mul_left (hm2.symm.pow_left a) (hm3.symm.pow_left v)
    have hjoin1 := hcop2a.mul_dvd_of_dvd_of_dvd h2a h3vd
    exact hcopB.mul_dvd_of_dvd_of_dvd hjoin1 hMdvd
  have hlea : a ≤ le := by
    rw [hle']
    split_ifs with h1
    · rw [h1]
      omega
    · rw [hlenN]
      have hlv := lenV_le
      omega
  have hj1 : 1 ≤ j := by
    rw [hj]
    exact Nat.mul_pos hc1 (by positivity)
  exact assemble_sandwich_R2 (a := a) (v := v) (le := le) (K := K)
    (j := j) (T := T) ha hm0 hm30 hT hbound hj1 hKcov de hle hde10
    hdene hde0 hde2a hde11 hde11r hpar hlea C hCdef s₀ hs0 hσdiv


theorem hard_closed {a b v m : ℕ} (hm30 : m.Coprime 30)
    (hh : residualHard a b v m) :
    finGoal (2 ^ a * 5 ^ b * 3 ^ v * m) := by
  obtain ⟨ha, hb0, hbad⟩ := hh
  subst hb0
  have hm0 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0] at hm30
      exact absurd hm30 (by decide)
    · exact h0
  rcases Nat.eq_zero_or_pos v with rfl | hvpos
  · simpa only [pow_zero, mul_one, one_mul] using
      hard_closed_v0 ha hm30 hbad
  · rcases Nat.lt_or_ge v 2 with hv1 | hv2
    · have hv : v = 1 := by omega
      subst hv
      simpa only [pow_one, pow_zero, mul_one, one_mul] using
        hard_closed_v1 ha hm30 hbad
    · rcases Nat.lt_or_ge v 5 with hv4 | hv5
      · simpa only [pow_zero, mul_one] using
          hard_closed_v234 ha hm0 hv2 (by omega) hm30 hbad
      · simpa only [pow_zero, mul_one] using
          hard_closed_v5 ha hm0 hv5 hm30 hbad


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

theorem OMA.solution : OMA.R_oeis_a084017_R1_H1_R1.H1 := by
  intro a b v m hm30 hh
  exact OMA.A084017Port.A084017.hard_closed hm30 hh
