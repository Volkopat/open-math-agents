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
theorem dvd10_of_tz_pos {n : ℕ} (h : 0 < tz n) : 10 ∣ n := by
  by_contra hn
  rw [tz_zero_of_not_dvd hn] at h
  exact Nat.lt_irrefl 0 h


set_option maxHeartbeats 800000 in
abbrev witSpec (n z : ℕ) (L : List ℕ) : Prop :=
  (∀ x ∈ L, x < 10) ∧ L ≠ [] ∧ L.getLast? ≠ some 0
    ∧ L.Palindrome ∧ L.length + z = n
    ∧ z = tz n ∧ n ∣ Nat.ofDigits 10 L * 10 ^ z ∧ n ∣ L.sum


set_option maxHeartbeats 800000 in
def residualOpen (a b v m : ℕ) : Prop :=
  v = 0 ∨ (1 ≤ a ∧ b = 0 ∧ (11 ∣ m ∨ 101 ∣ m))


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
theorem relaxed_of_finGoal {n : ℕ} : finGoal n → relaxedGoal n := by
  rintro ⟨P, z, hP, hz10, hpal, hlen, hdvd, hσ⟩
  exact ⟨P, z, hP, fun hz => dvd10_of_tz_pos (hz10 ▸ hz), hpal,
    hlen, hdvd, hσ⟩





















set_option maxHeartbeats 800000 in
theorem digits_sum_le (N : ℕ) :
    (Nat.digits 10 N).sum ≤ 9 * (Nat.digits 10 N).length := by
  have h : ∀ x ∈ Nat.digits 10 N, x ≤ 9 := fun x hx =>
    Nat.lt_succ_iff.mp (Nat.digits_lt_base (by norm_num) hx)
  have hs := List.sum_le_card_nsmul (Nat.digits 10 N) 9 h
  rwa [nsmul_eq_mul, Nat.mul_comm] at hs

set_option maxHeartbeats 800000 in
theorem digits_sum_le_self (N : ℕ) :
    (Nat.digits 10 N).sum ≤ N := by
  have hL : ∀ L : List ℕ, L.sum ≤ Nat.ofDigits 10 L := by
    intro L
    induction L with
    | nil => simp [Nat.ofDigits]
    | cons a t ih =>
      rw [List.sum_cons]
      show a + t.sum ≤ a + 10 * Nat.ofDigits 10 t
      omega
  calc (Nat.digits 10 N).sum ≤ Nat.ofDigits 10 (Nat.digits 10 N) := hL _
    _ = N := Nat.ofDigits_digits 10 N

set_option maxHeartbeats 800000 in
theorem list_sum_map_range (d : ℕ → ℕ) (k : ℕ) :
    ((List.range k).map d).sum = (Finset.range k).sum d := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]
    simp

set_option maxHeartbeats 800000 in
theorem five_not_dvd_pow2 (a : ℕ) : ¬ (5:ℕ) ∣ 2 ^ a := by
  have hc : Nat.Coprime 5 2 := by norm_num
  have hc2 := hc.pow_right a
  exact (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 5)).mp hc2

set_option maxHeartbeats 800000 in
theorem pow5_mod10 {b : ℕ} (hb : 1 ≤ b) : 5 ^ b % 10 = 5 := by
  obtain ⟨t, ht⟩ : Odd (5 ^ (b - 1)) := (by norm_num : Odd (5:ℕ)).pow
  have h5b : 5 ^ b = 10 * t + 5 := by
    calc 5 ^ b = 5 ^ (b - 1 + 1) := by congr 1; omega
      _ = 5 ^ (b - 1) * 5 := pow_succ _ _
      _ = (2 * t + 1) * 5 := by rw [ht]
      _ = 10 * t + 5 := by ring
  rw [h5b]
  omega

set_option maxHeartbeats 800000 in
theorem two_mul_le_pow2 {a : ℕ} (ha : 2 ≤ a) : 2 * a ≤ 2 ^ a := by
  induction a, ha using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hp : (2:ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ']
    rw [hp]
    omega

set_option maxHeartbeats 800000 in
theorem pow2_ge_a1 {a : ℕ} (ha : 3 ≤ a) : a ≤ 2 ^ (a - 1) := by
  induction a, ha using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hp : (2:ℕ) ^ (k + 1 - 1) = 2 * 2 ^ (k - 1) := by
      rw [show k + 1 - 1 = k - 1 + 1 from by omega, pow_succ']
    rw [hp]
    omega

set_option maxHeartbeats 800000 in
theorem pow2_ge_9a7 {a : ℕ} (ha : 3 ≤ a) : 9 * a ≤ 7 * 2 ^ (a - 1) := by
  induction a, ha using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hp : (2:ℕ) ^ (k + 1 - 1) = 2 * 2 ^ (k - 1) := by
      rw [show k + 1 - 1 = k - 1 + 1 from by omega, pow_succ']
    rw [hp]
    omega

set_option maxHeartbeats 800000 in
theorem pow5_ge_18b {b : ℕ} (hb : 2 ≤ b) : 18 * b + 1 ≤ 3 * 5 ^ b := by
  induction b, hb using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hp : (5:ℕ) ^ (k + 1) = 5 * 5 ^ k := by rw [pow_succ']
    rw [hp]
    omega

set_option maxHeartbeats 800000 in
theorem pow5_ge_2b1 {b : ℕ} (hb : 1 ≤ b) : 2 * b + 1 ≤ 5 ^ b := by
  induction b, hb using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hp : (5:ℕ) ^ (k + 1) = 5 * 5 ^ k := by rw [pow_succ']
    rw [hp]
    omega


set_option maxHeartbeats 800000 in
theorem ofDigits_prefix_eq (V s : ℕ) (rest : List ℕ)
    (hl : (Nat.digits 10 V).length ≤ s) :
    Nat.ofDigits 10 ((Nat.digits 10 V
        ++ List.replicate (s - (Nat.digits 10 V).length) 0) ++ rest)
      = V + 10 ^ s * Nat.ofDigits 10 rest := by
  rw [Nat.ofDigits_append, Nat.ofDigits_append_replicate_zero,
    Nat.ofDigits_digits]
  have hX : (Nat.digits 10 V
      ++ List.replicate (s - (Nat.digits 10 V).length) 0).length = s := by
    rw [List.length_append, List.length_replicate]
    omega
  rw [hX]


set_option maxHeartbeats 800000 in
theorem mirror_spec (A MID : List ℕ) (hA : A ≠ [])
    (hA10 : ∀ x ∈ A, x < 10) (hA0 : A.head hA ≠ 0)
    (hMID : MID.Palindrome) (hM10 : ∀ x ∈ MID, x < 10) :
    Nat.ofDigits 10 (A ++ MID ++ A.reverse) ≠ 0
      ∧ (Nat.digits 10
          (Nat.ofDigits 10 (A ++ MID ++ A.reverse))).Palindrome
      ∧ (Nat.digits 10 (Nat.ofDigits 10 (A ++ MID ++ A.reverse))).length
          = 2 * A.length + MID.length
      ∧ (Nat.digits 10 (Nat.ofDigits 10 (A ++ MID ++ A.reverse))).sum
          = 2 * A.sum + MID.sum :=
  sandwich_spec_gen A MID hA hA10 hA0 hMID hM10 rfl rfl


set_option maxHeartbeats 800000 in
theorem assemble_v0_m1_ab {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ∃ P z : ℕ, P ≠ 0 ∧ (0 < z → 10 ∣ 2 ^ a * 5 ^ b)
      ∧ (Nat.digits 10 P).Palindrome
      ∧ (Nat.digits 10 P).length + z = 2 ^ a * 5 ^ b
      ∧ 2 ^ a * 5 ^ b ∣ P * 10 ^ z
      ∧ 2 ^ a * 5 ^ b ∣ (Nat.digits 10 P).sum := by
  set n := 2 ^ a * 5 ^ b with hn
  have hn10 : 10 ≤ n := by
    rw [hn]
    calc (10:ℕ) = 2 ^ 1 * 5 ^ 1 := by norm_num
      _ ≤ 2 ^ a * 5 ^ b :=
          Nat.mul_le_mul (pow_le_pow_right' (by norm_num) ha)
            (pow_le_pow_right' (by norm_num) hb)
  set z := 2 * ((Nat.max a b + 1) / 2) with hz
  have hz2 : 2 ∣ z := ⟨(Nat.max a b + 1) / 2, rfl⟩
  have hzmax : Nat.max a b ≤ z := by
    have := Nat.div_add_mod (Nat.max a b + 1) 2
    omega
  have hzub : z ≤ Nat.max a b + 1 := by
    have := Nat.div_add_mod (Nat.max a b + 1) 2
    omega
  have hn2 : 2 ∣ n := by
    rw [hn]
    exact dvd_mul_of_dvd_left (by simpa using pow_dvd_pow (2:ℕ) ha) _
  have hzn : z + 2 ≤ n := by
    have h2a : a + 1 ≤ 2 ^ a := Nat.lt_pow_self (by norm_num)
    have h5b : b + 1 ≤ 5 ^ b := Nat.lt_pow_self (by norm_num)
    have hprod : (a + 1) * (b + 1) ≤ n := by
      rw [hn]; exact Nat.mul_le_mul h2a h5b
    have hexp : (a + 1) * (b + 1) = a * b + a + b + 1 := by ring
    have hmax : Nat.max a b ≤ a * b := Nat.max_le.mpr
      ⟨Nat.le_mul_of_pos_right a hb, Nat.le_mul_of_pos_left b ha⟩
    omega
  set t := (n - z) / 2 with ht
  have htpos : 1 ≤ t := by rw [ht]; omega
  have ht2 : 2 * t = n - z := by
    obtain ⟨q, hq⟩ : 2 ∣ n - z := by
      obtain ⟨u, hu⟩ := hn2
      obtain ⟨w, hw⟩ := hz2
      refine ⟨u - w, ?_⟩
      rw [hu, hw, Nat.mul_sub]
    rw [ht]
    omega
  set S := n / 2 with hS
  have hS2 : 2 * S = n := by
    obtain ⟨u, hu⟩ := hn2
    rw [hS]
    omega
  have hSt : S ≤ 9 * t := by
    have h9z : 9 * z ≤ 8 * n := by
      have h2a : 2 * a ≤ 2 ^ a := by
        rcases Nat.lt_or_ge a 2 with h | h
        · interval_cases a; norm_num
        · exact two_mul_le_pow2 h
      have hbb : b ≤ 5 ^ b := Nat.le_of_lt (Nat.lt_pow_self (by norm_num))
      have hmax : Nat.max a b ≤ a * b := Nat.max_le.mpr
        ⟨Nat.le_mul_of_pos_right a hb, Nat.le_mul_of_pos_left b ha⟩
      have hn2ab : 2 * (a * b) ≤ n := by
        rw [hn]
        calc 2 * (a * b) = (2 * a) * b := by ring
          _ ≤ 2 ^ a * 5 ^ b := Nat.mul_le_mul h2a hbb
      have hn3 : 3 ≤ n := by
        have h2 : (2:ℕ) ≤ 2 ^ a := by
          calc (2:ℕ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ a := pow_le_pow_right' (by norm_num) ha
        have h5 : (5:ℕ) ≤ 5 ^ b := by
          calc (5:ℕ) = 5 ^ 1 := by norm_num
            _ ≤ 5 ^ b := pow_le_pow_right' (by norm_num) hb
        calc 3 ≤ 2 * 5 := by norm_num
          _ ≤ 2 ^ a * 5 ^ b := Nat.mul_le_mul h2 h5
      omega
    rw [hS, ht]
    omega
  obtain ⟨d, hd9, hd0, hdS⟩ :=
    digit_sum_interval (t - 1) (S - min 9 S) (by
      have h1 : min 9 S ≤ S := Nat.min_le_right _ _
      have h2 : 1 ≤ t := htpos
      omega)
  set F := (List.range (t - 1)).map d with hF
  set A := min 9 S :: F with hA
  set L := A ++ A.reverse with hL
  set P := Nat.ofDigits 10 L with hP
  have hAne : A ≠ [] := by rw [hA]; exact List.cons_ne_nil _ _
  have hA10 : ∀ x ∈ A, x < 10 := by
    intro x hx
    rw [hA, List.mem_cons] at hx
    rcases hx with rfl | hx
    · omega
    · rw [hF, List.mem_map] at hx
      obtain ⟨i, _, rfl⟩ := hx
      have := hd9 i
      omega
  have hA0 : A.head hAne ≠ 0 := by
    have hS1 : 1 ≤ S := by rw [hS]; omega
    have hhead : A.head hAne = min 9 S := rfl
    rw [hhead]
    omega
  obtain ⟨hP0, hPpal, hPlen, hPσ⟩ := mirror_spec A [] hAne hA10 hA0
    (List.Palindrome.of_reverse_eq (by simp)) (by simp)
  simp only [List.append_nil, List.length_nil, List.sum_nil, add_zero]
    at hP0 hPpal hPlen hPσ
  have hAlen : A.length = t := by
    rw [hA, List.length_cons, hF, List.length_map, List.length_range]
    omega
  have hAσ : A.sum = S := by
    rw [hA, List.sum_cons, hF, list_sum_map_range, hdS]
    have h1 : min 9 S ≤ S := Nat.min_le_right _ _
    omega
  refine ⟨P, z, hP0, ?_, hPpal, ?_, ?_, ?_⟩
  · intro _
    rw [hn]
    have h2 : 2 ∣ 2 ^ a := by simpa using pow_dvd_pow (2:ℕ) ha
    have h5 : 5 ∣ 5 ^ b := by simpa using pow_dvd_pow (5:ℕ) hb
    exact Nat.mul_dvd_mul h2 h5
  · rw [hP, hL, hPlen, hAlen]
    omega
  · rw [hP]
    rw [hn]
    exact Nat.dvd_trans (pow25_dvd_pow10 hzmax) (dvd_mul_left (10 ^ z) P)
  · rw [hP, hL, hPσ, hAσ, hS2]


set_option maxHeartbeats 800000 in
theorem assemble_v0_m1_0b {b : ℕ} (hb : 1 ≤ b) :
    ∃ P z : ℕ, P ≠ 0 ∧ (0 < z → 10 ∣ 5 ^ b)
      ∧ (Nat.digits 10 P).Palindrome
      ∧ (Nat.digits 10 P).length + z = 5 ^ b
      ∧ 5 ^ b ∣ P * 10 ^ z
      ∧ 5 ^ b ∣ (Nat.digits 10 P).sum := by
  rcases Nat.lt_or_ge b 2 with hb1 | hb1
  · have hb' : b = 1 := by omega
    subst hb'
    exact ⟨52125, 0, by norm_num, by omega, by decide, by decide,
      by decide, by decide⟩
  · have hb2 : 2 ≤ b := hb1
    set n := 5 ^ b with hn
    have hnodd : Odd n := (by norm_num : Odd (5:ℕ)).pow
    set lenV := (Nat.digits 10 (5 ^ b)).length with hlenV
    set sigV := (Nat.digits 10 (5 ^ b)).sum with hsigV
    have hlenVle : lenV ≤ b := by
      rw [hlenV, Nat.digits_length_le_iff (by norm_num)]
      exact Nat.pow_lt_pow_left (by norm_num : (5:ℕ) < 10)
        (by omega : b ≠ 0)
    have hlenV1 : 1 ≤ lenV := by
      rw [hlenV]
      exact List.length_pos_of_ne_nil
        (Nat.digits_ne_nil_iff_ne_zero.mpr (pow_pos (by norm_num) b).ne')
    have hV5 : 5 ^ b % 10 = 5 := pow5_mod10 hb
    set t := (n - 1) / 2 with ht
    have ht2 : 2 * t = n - 1 := by
      obtain ⟨u, hu⟩ := hnodd
      rw [ht]
      omega
    have htb : b ≤ t := by
      have := pow5_ge_2b1 hb
      rw [ht, hn]
      omega
    set σA := (3 * n - 1) / 2 with hσA
    have hσle : sigV ≤ σA := by
      have h1 : sigV ≤ 9 * lenV := by
        rw [hsigV, hlenV]
        exact digits_sum_le _
      have h18 : 18 * b + 1 ≤ 3 * 5 ^ b := pow5_ge_18b hb2
      rw [hσA, hn]
      omega
    obtain ⟨d, hd9, hd0, hdS⟩ :=
      digit_sum_interval (t - b) (σA - sigV) (by
        have h9b : 9 * b + 4 ≤ 3 * n := by
          rw [hn]
          have := pow5_ge_18b hb2
          omega
        rw [ht, hσA]
        omega)
    set F := (List.range (t - b)).map d with hF
    set ds := Nat.digits 10 (5 ^ b / 10) with hds
    have hd5 : Nat.digits 10 (5 ^ b) = 5 ^ b % 10 :: ds :=
      Nat.digits_def' (by norm_num) (pow_pos (by norm_num) b)
    have hdlen : ds.length = lenV - 1 := by
      have hcl := congrArg List.length hd5
      rw [List.length_cons, ← hlenV] at hcl
      omega
    have hdsum : (Nat.digits 10 (5 ^ b)).sum = 5 ^ b % 10 + ds.sum := by
      rw [hd5, List.sum_cons]
    set W := (ds ++ List.replicate (b - lenV) 0) ++ F with hW
    set A := 5 ^ b % 10 :: W with hA
    set L := A ++ [1] ++ A.reverse with hL
    set P := Nat.ofDigits 10 L with hP
    have hAeq : A = (Nat.digits 10 (5 ^ b)
        ++ List.replicate (b - lenV) 0) ++ F := by
      rw [hA, hd5, hW]
      simp only [List.append_assoc, List.cons_append]
    have hAne : A ≠ [] := by rw [hA]; exact List.cons_ne_nil _ _
    have hA10 : ∀ x ∈ A, x < 10 := by
      intro x hx
      rw [hA, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Nat.mod_lt _ (by norm_num)
      · rw [hW, List.mem_append] at hx
        rcases hx with hx | hx
        · rw [List.mem_append] at hx
          rcases hx with hx | hx
          · rw [hds] at hx
            exact Nat.digits_lt_base (by norm_num) hx
          · rw [List.mem_replicate] at hx
            rcases hx with ⟨_, rfl⟩
            norm_num
        · rw [hF, List.mem_map] at hx
          obtain ⟨i, _, rfl⟩ := hx
          have := hd9 i
          omega
    have hA0 : A.head hAne ≠ 0 := by
      show 5 ^ b % 10 ≠ 0
      rw [hV5]
      norm_num
    obtain ⟨hP0, hPpal, hPlen, hPσ⟩ := mirror_spec A [1] hAne hA10 hA0
      (List.Palindrome.of_reverse_eq (by simp))
      (by intro x hx; rw [List.mem_singleton] at hx; subst hx; norm_num)
    simp only [List.length_singleton, List.sum_singleton]
      at hPlen hPσ
    have hAlen : A.length = t := by
      rw [hA, List.length_cons, hW, List.length_append, List.length_append,
        List.length_replicate, hF, List.length_map, List.length_range]
      omega
    have hAσ : A.sum = σA := by
      rw [hA, List.sum_cons, hW, List.sum_append, List.sum_append,
        List.sum_replicate, nsmul_eq_mul, mul_zero, add_zero, hF,
        list_sum_map_range, hdS]
      omega
    have hPde : P = 5 ^ b + 10 ^ b * Nat.ofDigits 10 F
        + 10 ^ t * Nat.ofDigits 10 ([1] ++ A.reverse) := by
      rw [hP, hL, Nat.ofDigits_append, Nat.ofDigits_append, hAlen,
        Nat.ofDigits_singleton, List.length_append, hAlen,
        List.length_singleton, hAeq, hlenV,
        ofDigits_prefix_eq (5 ^ b) b F hlenVle,
        List.singleton_append, Nat.ofDigits_cons, pow_succ']
      ring
    have h5bP : 5 ^ b ∣ P := by
      rw [hPde]
      apply Nat.dvd_add
      · apply Nat.dvd_add
        · exact dvd_refl _
        · exact dvd_mul_of_dvd_left
            (by simpa using @pow25_dvd_pow10 0 b b (by omega))
            _
      · exact dvd_mul_of_dvd_left
          (by simpa using @pow25_dvd_pow10 0 b t (by omega))
          _
    have hσP : (Nat.digits 10 P).sum = 3 * n := by
      rw [hP, hL, hPσ, hAσ, hσA]
      obtain ⟨u, hu⟩ := hnodd
      omega
    refine ⟨P, 0, hP0, by omega, hPpal, ?_, ?_, ?_⟩
    · rw [hP, hL, hPlen, hAlen]
      omega
    · simpa using h5bP
    · rw [hσP, hn]
      exact dvd_mul_of_dvd_right (dvd_refl n) 3


set_option maxHeartbeats 800000 in
theorem assemble_v0_m1_a0 {a : ℕ} (ha : 1 ≤ a) :
    ∃ P z : ℕ, P ≠ 0 ∧ (0 < z → 10 ∣ 2 ^ a)
      ∧ (Nat.digits 10 P).Palindrome
      ∧ (Nat.digits 10 P).length + z = 2 ^ a
      ∧ 2 ^ a ∣ P * 10 ^ z
      ∧ 2 ^ a ∣ (Nat.digits 10 P).sum := by
  rcases Nat.lt_or_ge a 3 with ha2 | ha2
  · interval_cases a
    · exact ⟨22, 0, by norm_num, by omega, by decide, by decide,
        by decide, by decide⟩
    · exact ⟨4004, 0, by norm_num, by omega, by decide, by decide,
        by decide, by decide⟩
  · have ha3 : 3 ≤ a := ha2
    set n := 2 ^ a with hn
    set lenV := (Nat.digits 10 (2 ^ a)).length with hlenV
    set sigV := (Nat.digits 10 (2 ^ a)).sum with hsigV
    have hlenVle : lenV ≤ a := by
      rw [hlenV, Nat.digits_length_le_iff (by norm_num)]
      exact Nat.pow_lt_pow_left (by norm_num : (2:ℕ) < 10)
        (by omega : a ≠ 0)
    have hlenV1 : 1 ≤ lenV := by
      rw [hlenV]
      exact List.length_pos_of_ne_nil
        (Nat.digits_ne_nil_iff_ne_zero.mpr (pow_pos (by norm_num) a).ne')
    have hV2 : 2 ^ a % 10 ≠ 0 := by
      intro h10
      have hdvd : (10:ℕ) ∣ 2 ^ a := Nat.dvd_of_mod_eq_zero h10
      exact five_not_dvd_pow2 a
        (dvd_trans (by norm_num : (5:ℕ) ∣ 10) hdvd)
    set t := 2 ^ (a - 1) with ht
    have h2t : 2 * t = n := by
      rw [ht, hn, ← pow_succ']
      congr 1
      omega
    have hta : a ≤ t := by rw [ht]; exact pow2_ge_a1 ha3
    have hσle : sigV ≤ 2 ^ a := by
      rw [hsigV]
      exact digits_sum_le_self (2 ^ a)
    obtain ⟨d, hd9, hd0, hdS⟩ :=
      digit_sum_interval (t - a) (2 ^ a - sigV) (by
        have h9a : 9 * a ≤ 7 * 2 ^ (a - 1) := pow2_ge_9a7 ha3
        have h2a : 2 ^ a = 2 * 2 ^ (a - 1) := by
          rw [← pow_succ']
          congr 1
          omega
        rw [ht]
        omega)
    set F := (List.range (t - a)).map d with hF
    set ds := Nat.digits 10 (2 ^ a / 10) with hds
    have hd2 : Nat.digits 10 (2 ^ a) = 2 ^ a % 10 :: ds :=
      Nat.digits_def' (by norm_num) (pow_pos (by norm_num) a)
    have hdlen : ds.length = lenV - 1 := by
      have hcl := congrArg List.length hd2
      rw [List.length_cons, ← hlenV] at hcl
      omega
    have hdsum : (Nat.digits 10 (2 ^ a)).sum = 2 ^ a % 10 + ds.sum := by
      rw [hd2, List.sum_cons]
    set W := (ds ++ List.replicate (a - lenV) 0) ++ F with hW
    set A := 2 ^ a % 10 :: W with hA
    set L := A ++ A.reverse with hL
    set P := Nat.ofDigits 10 L with hP
    have hAeq : A = (Nat.digits 10 (2 ^ a)
        ++ List.replicate (a - lenV) 0) ++ F := by
      rw [hA, hd2, hW]
      simp only [List.append_assoc, List.cons_append]
    have hAne : A ≠ [] := by rw [hA]; exact List.cons_ne_nil _ _
    have hA10 : ∀ x ∈ A, x < 10 := by
      intro x hx
      rw [hA, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Nat.mod_lt _ (by norm_num)
      · rw [hW, List.mem_append] at hx
        rcases hx with hx | hx
        · rw [List.mem_append] at hx
          rcases hx with hx | hx
          · rw [hds] at hx
            exact Nat.digits_lt_base (by norm_num) hx
          · rw [List.mem_replicate] at hx
            rcases hx with ⟨_, rfl⟩
            norm_num
        · rw [hF, List.mem_map] at hx
          obtain ⟨i, _, rfl⟩ := hx
          have := hd9 i
          omega
    have hA0 : A.head hAne ≠ 0 := by
      show 2 ^ a % 10 ≠ 0
      exact hV2
    obtain ⟨hP0, hPpal, hPlen, hPσ⟩ := mirror_spec A [] hAne hA10 hA0
      (List.Palindrome.of_reverse_eq (by simp)) (by simp)
    simp only [List.append_nil, List.length_nil, List.sum_nil, add_zero]
      at hP0 hPpal hPlen hPσ
    have hAlen : A.length = t := by
      rw [hA, List.length_cons, hW, List.length_append, List.length_append,
        List.length_replicate, hF, List.length_map, List.length_range]
      omega
    have hAσ : A.sum = 2 ^ a := by
      rw [hA, List.sum_cons, hW, List.sum_append, List.sum_append,
        List.sum_replicate, nsmul_eq_mul, mul_zero, add_zero, hF,
        list_sum_map_range, hdS]
      omega
    have hPde : P = 2 ^ a + 10 ^ a * Nat.ofDigits 10 F
        + 10 ^ t * Nat.ofDigits 10 A.reverse := by
      rw [hP, hL, Nat.ofDigits_append, hAlen, hAeq, hlenV,
        ofDigits_prefix_eq (2 ^ a) a F hlenVle]
    have h2aP : 2 ^ a ∣ P := by
      rw [hPde]
      apply Nat.dvd_add
      · apply Nat.dvd_add
        · exact dvd_refl _
        · exact dvd_mul_of_dvd_left
            (by simpa using @pow25_dvd_pow10 a 0 a (by omega))
            _
      · exact dvd_mul_of_dvd_left
          (by simpa using @pow25_dvd_pow10 a 0 t (by omega))
          _
    have hσP : (Nat.digits 10 P).sum = 2 ^ (a + 1) := by
      rw [hP, hL, hPσ, hAσ, pow_succ']
    refine ⟨P, 0, hP0, by omega, hPpal, ?_, ?_, ?_⟩
    · rw [hP, hL, hPlen, hAlen]
      omega
    · simpa using h2aP
    · rw [hσP, hn]
      exact pow_dvd_pow 2 (by omega)


set_option maxHeartbeats 800000 in
theorem assemble_v0_m1 (a b : ℕ) :
    ∃ P z : ℕ, P ≠ 0 ∧ (0 < z → 10 ∣ 2 ^ a * 5 ^ b)
      ∧ (Nat.digits 10 P).Palindrome
      ∧ (Nat.digits 10 P).length + z = 2 ^ a * 5 ^ b
      ∧ 2 ^ a * 5 ^ b ∣ P * 10 ^ z
      ∧ 2 ^ a * 5 ^ b ∣ (Nat.digits 10 P).sum := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · rcases Nat.eq_zero_or_pos b with hb | hb
    · subst ha; subst hb
      exact ⟨1, 0, by norm_num, by omega, by decide, by decide,
        by decide, by decide⟩
    · subst ha
      simp only [pow_zero, one_mul]
      exact assemble_v0_m1_0b hb
  · rcases Nat.eq_zero_or_pos b with hb | hb
    · subst hb
      simp only [pow_zero, mul_one]
      exact assemble_v0_m1_a0 ha
    · exact assemble_v0_m1_ab ha hb


set_option maxHeartbeats 800000 in
theorem center_free_pal (F : List ℕ) (c : ℕ) :
    (F ++ [c] ++ F.reverse).Palindrome := by
  apply List.Palindrome.of_reverse_eq
  rw [List.reverse_append, List.reverse_append, List.reverse_reverse,
    List.reverse_singleton, ← List.append_assoc]


set_option maxHeartbeats 800000 in
theorem assemble_v0o {b m : ℕ} (hb : 1 ≤ b) (hm0 : 1 ≤ m)
    (hm30 : m.Coprime 30)
    (hB : 72 * b + 72 * ((m - 1) / 9 + 1) + 81 ≤ 8 * (5 ^ b) * m) :
    ∃ P z : ℕ, P ≠ 0
      ∧ (0 < z → 10 ∣ 5 ^ b * m)
      ∧ (Nat.digits 10 P).Palindrome
      ∧ (Nat.digits 10 P).length + z = 5 ^ b * m
      ∧ 5 ^ b * m ∣ P * 10 ^ z
      ∧ 5 ^ b * m ∣ (Nat.digits 10 P).sum := by
  classical
  set n := 5 ^ b * m with hn
  have : NeZero m := ⟨by omega⟩
  have hm3 : m.Coprime 3 := hm30.coprime_dvd_right (by norm_num)
  have hm10 : m.Coprime 10 := hm30.coprime_dvd_right (by norm_num)
  have hm2 : m.Coprime 2 := hm30.coprime_dvd_right (by norm_num)
  set K := 2 * ((m - 1) / 9 + 1) with hK
  
  obtain ⟨D, _hDpal, hD10, hDne, hD0, hD25, _hD3v, _hDσ, hr₀lt,
    hlenD⟩ := border_pal_q (a' := 0) (b' := b) (q := 2) (s₁ := b)
      (t := 0) (by norm_num) (by norm_num) (Or.inl rfl)
      (le_of_eq (Nat.max_eq_right (Nat.zero_le b)))
  set lenD := D.length with hlenD'
  have hr0z : r0b 0 b 2 = 0 := by
    have h := hr₀lt
    norm_num at h
    exact h
  have hlenN : lenD
      = 2 * ((Nat.digits 10 (9 * 5 ^ b)).length + b) := by
    have h := hlenD
    rw [hr0z] at h
    norm_num at h ⊢
    omega
  
  have lenV_le : (Nat.digits 10 (9 * 5 ^ b)).length ≤ b + 2 := by
    have hVpos : (9 * 5 ^ b : ℕ) ≠ 0 := by positivity
    have hb2 := Nat.base_pow_length_digits_le 10 (9 * 5 ^ b)
      (by norm_num) hVpos
    have hlt : 10 * (9 * 5 ^ b) < 10 ^ (b + 2) := by
      have h1 : (5 : ℕ) ^ b ≤ 10 ^ b :=
        Nat.pow_le_pow_left (by norm_num) _
      calc 10 * (9 * 5 ^ b) = 90 * 5 ^ b := by ring
        _ ≤ 90 * 10 ^ b := Nat.mul_le_mul_left 90 h1
        _ < 100 * 10 ^ b := by omega
        _ = 10 ^ (b + 2) := by ring
    have hpow : 10 ^ ((Nat.digits 10 (9 * 5 ^ b)).length)
        < 10 ^ (b + 2) := lt_of_le_of_lt hb2 hlt
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 10)).mp hpow
    omega
  have hlenDb : lenD ≤ 4 * b + 4 := by omega
  have hnodd : Odd n := by
    have hmo : Odd m := by
      have h2 : ¬ (2 : ℕ) ∣ m :=
        (Nat.prime_two.coprime_iff_not_dvd).mp hm2.symm
      rw [← Nat.not_even_iff_odd]
      rintro ⟨c', hc'⟩
      exact h2 ⟨c', by omega⟩
    rw [hn]
    exact ((by decide : Odd (5 : ℕ)).pow).mul hmo
  have hnpos : 0 < n := by rw [hn]; positivity
  have hB' : 72 * b + 72 * ((m - 1) / 9 + 1) + 81 ≤ 8 * n := by
    rw [hn, ← Nat.mul_assoc]
    exact hB
  have h36K : 36 * K = 72 * ((m - 1) / 9 + 1) := by rw [hK]; ring
  have hkey : 18 * lenD + 36 * K ≤ 8 * n - 9 := by omega
  set base := 2 * D.sum + 18 * K with hbase
  set g := n - (2 * lenD + 4 * K) with hg
  
  have hcap : n ≤ 9 * g + 1 := by omega
  have hg3 : 3 ≤ g := by omega
  have hgodd : Odd g := by
    obtain ⟨w, hw⟩ := hnodd
    refine ⟨w - (lenD + 2 * K), ?_⟩
    rw [hg]
    omega
  
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
  set R := min (v / 2) (9 * (g / 2)) with hR
  set c := v - 2 * R with hc
  have h2Rc : 2 * R + c = v := by
    have : R ≤ v / 2 := Nat.min_le_left _ _
    omega
  have hc9 : c ≤ 9 := by
    obtain ⟨w, hw⟩ := hgodd
    rcases min_choice (v / 2) (9 * (g / 2)) with hRv | hRv
    · omega
    · omega
  have hRle : R ≤ 9 * (g / 2) := Nat.min_le_right _ _
  obtain ⟨F, hFlen, hF9, hFsum⟩ :=
    exists_free_block (g / 2) R hRle
  set C := F ++ [c] ++ F.reverse with hC
  have hCpal : C.Palindrome := center_free_pal F c
  have hC10 : ∀ x ∈ C, x < 10 := by
    intro x hx
    rw [hC] at hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · have := hF9 x hx
        omega
      · rw [List.mem_singleton] at hx
        omega
    · have := hF9 x (List.mem_reverse.mp hx)
      omega
  have hCg : C.length = g := by
    obtain ⟨w, hw⟩ := hgodd
    rw [hC, List.length_append, List.length_append, hFlen,
      List.length_singleton, List.length_reverse]
    omega
  have hCσ : C.sum = v := by
    rw [hC, List.sum_append, List.sum_append, List.sum_reverse,
      hFsum, List.sum_singleton]
    omega
  have hKcov : m * 3 ^ (0 - 4) ≤ 1 + 9 * (K / 2) := by
    have hK2 : K / 2 = (m - 1) / 9 + 1 := by
      rw [hK]
      exact Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)
    have hdm := Nat.div_add_mod (m - 1) 9
    have hmlt : (m - 1) % 9 < 9 := Nat.mod_lt _ (by norm_num)
    have h0m : 0 - 4 = 0 := rfl
    rw [h0m, pow_zero, mul_one, hK2]
    omega
  obtain ⟨s₀, hs0⟩ := hs0_v0 (le := lenD) (K := K) (g := g) D C
  obtain ⟨e', he', hdvdP⟩ :=
    P_dvd_3m81 (v := 0) (le := lenD) (K := K) (g := g)
      hm3 hm10 D hlenD'.symm C hCg hg3 hgodd hKcov s₀ hs0
  set MID := (List.range (2 * K)).map (pairDigit e') ++ C
      ++ ((List.range (2 * K)).map (pairDigit e')).reverse with hMID
  have hMIDpal : MID.Palindrome := mid_pal e' C hCpal
  have hMID10 : ∀ x ∈ MID, x < 10 := mid_lt10 e' he' C hC10
  have hMIDlen : MID.length = 4 * K + g := by
    rw [hMID, List.length_append, List.length_append,
      List.length_reverse, List.length_map, List.length_range, hCg]
    ring
  have hMIDσ : MID.sum = 18 * K + C.sum := mid_sum e' he' C
  obtain ⟨hP0, hPpal, hPlen, hPσ⟩ := sandwich_spec_gen D MID
    hDne hD10 (hD0 hDne) hMIDpal hMID10 rfl rfl
  have h25P : 2 ^ 0 * 5 ^ b ∣ Nat.ofDigits 10
      (D ++ MID ++ D.reverse) :=
    B_dvd_P (le := lenD) hlenD'.symm hD25 (by omega)
  set P := Nat.ofDigits 10 (D ++ MID ++ D.reverse) with hP
  have hmP : 3 ^ 0 * m ∣ P := by simpa using hdvdP
  have hnP : n ∣ P := by
    have h := n_dvd_P_pow10_le (a := 0) (b := b) (v := 0) (m := m)
      (z := 0) (a' := 0) (b' := b) (P := P) h25P hmP
      (by omega) (by omega) hm30
    have h' : 5 ^ b * m ∣ P := by simpa using h
    rw [hn]
    exact h'
  have hσ : (Nat.digits 10 P).sum = σ₀ := by
    rw [hPσ, hMIDσ, hCσ]
    omega
  refine ⟨P, 0, hP0, fun h => (Nat.lt_irrefl 0 h).elim, hPpal,
    ?_, ?_, ?_⟩
  · rw [hPlen, hMIDlen]
    omega
  · simpa using hnP
  · rw [hσ, hσ₀]
    rw [hn]
    exact dvd_mul_right _ _


set_option maxHeartbeats 800000 in
theorem assemble_v0z {a b m : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hm0 : 1 ≤ m) (hm30 : m.Coprime 30)
    (hB : 9 * (a + b + 2) + 72 * ((m - 1) / 9 + 1) + 63
      ≤ 8 * (2 ^ a) * (5 ^ b) * m) :
    ∃ P z : ℕ, P ≠ 0
      ∧ (0 < z → 10 ∣ 2 ^ a * 5 ^ b * m)
      ∧ (Nat.digits 10 P).Palindrome
      ∧ (Nat.digits 10 P).length + z = 2 ^ a * 5 ^ b * m
      ∧ 2 ^ a * 5 ^ b * m ∣ P * 10 ^ z
      ∧ 2 ^ a * 5 ^ b * m ∣ (Nat.digits 10 P).sum := by
  classical
  set z := a + b + 1 + (a + b) % 2 with hz
  set n := 2 ^ a * 5 ^ b * m with hn
  have : NeZero m := ⟨by omega⟩
  have hm3 : m.Coprime 3 := hm30.coprime_dvd_right (by norm_num)
  have hm10 : m.Coprime 10 := hm30.coprime_dvd_right (by norm_num)
  set K := 2 * ((m - 1) / 9 + 1) with hK
  
  have hzodd : Odd z := by
    refine ⟨(a + b + 1) / 2, ?_⟩
    rw [hz]
    omega
  have haz : a < z := by rw [hz]; omega
  have hbz : b < z := by rw [hz]; omega
  have hzpos : 0 < z := by omega
  have h10n : 10 ∣ 2 ^ a * 5 ^ b * m := by
    have h2a : 2 ^ a = 2 * 2 ^ (a - 1) := by
      rw [← Nat.pow_succ', Nat.succ_eq_add_one,
        Nat.sub_add_cancel (by omega : 1 ≤ a)]
    have h5b : 5 ^ b = 5 * 5 ^ (b - 1) := by
      rw [← Nat.pow_succ', Nat.succ_eq_add_one,
        Nat.sub_add_cancel (by omega : 1 ≤ b)]
    rw [h2a, h5b]
    exact ⟨2 ^ (a - 1) * 5 ^ (b - 1) * m, by ring⟩
  
  have hneven : Even n := by
    have h2a : 2 ^ a = 2 * 2 ^ (a - 1) := by
      rw [← Nat.pow_succ', Nat.succ_eq_add_one,
        Nat.sub_add_cancel (by omega : 1 ≤ a)]
    refine ⟨2 ^ (a - 1) * 5 ^ b * m, ?_⟩
    rw [hn, h2a]
    ring
  have hzn : z ≤ n := by
    have h1 : a + 1 ≤ 2 ^ a := by
      refine Nat.le_induction (by norm_num) ?_ a ha
      intro k _ ih
      have e : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      rw [e]
      omega
    have h2 : b + 1 ≤ 5 ^ b := by
      refine Nat.le_induction (by norm_num) ?_ b hb
      intro k _ ih
      have e : 5 ^ (k + 1) = 5 * 5 ^ k := by ring
      rw [e]
      omega
    have h3 : 2 ^ a + 5 ^ b ≤ 2 ^ a * 5 ^ b :=
      Nat.add_le_mul (by omega) (by omega)
    have h4 : 2 ^ a * 5 ^ b ≤ n := by
      rw [hn]
      exact Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hnzodd : Odd (n - z) := by
    obtain ⟨an, han⟩ := hneven
    obtain ⟨az, haz'⟩ := hzodd
    refine ⟨an - az - 1, ?_⟩
    omega
  
  obtain ⟨D, _hDpal, hD10, hDne, hD0, hD25, _hD3v, _hDσ, hr₀lt,
    hlenD⟩ := border_pal_q (a' := 0) (b' := 0) (q := 2) (s₁ := 0)
      (t := 0) (by norm_num) (by norm_num) (Or.inl rfl)
      (le_of_eq (Nat.max_eq_right (Nat.zero_le 0)))
  set lenD := D.length with hlenD'
  have hr0z : r0b 0 0 2 = 0 := by
    have h := hr₀lt
    norm_num at h
    exact h
  have hlenN : lenD = 2 := by
    have h := hlenD
    rw [hr0z] at h
    norm_num at h ⊢
    omega
  have hB' : 9 * (a + b + 2) + 72 * ((m - 1) / 9 + 1) + 63
      ≤ 8 * n := by
    rw [hn, ← Nat.mul_assoc, ← Nat.mul_assoc]
    exact hB
  have h36K : 36 * K = 72 * ((m - 1) / 9 + 1) := by rw [hK]; ring
  have hkey : 9 * z + 18 * lenD + 36 * K ≤ 8 * n - 9 := by
    rw [hlenN]
    omega
  set base := 2 * D.sum + 18 * K with hbase
  set g := (n - z) - (2 * lenD + 4 * K) with hg
  have hcap : n ≤ 9 * g + 1 := by omega
  have hg3 : 3 ≤ g := by omega
  have hgodd : Odd g := by
    obtain ⟨w, hw⟩ := hnzodd
    refine ⟨w - (lenD + 2 * K), ?_⟩
    rw [hg]
    omega
  have hnpos : 0 < n := by rw [hn]; positivity
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
  set R := min (v / 2) (9 * (g / 2)) with hR
  set c := v - 2 * R with hc
  have h2Rc : 2 * R + c = v := by
    have : R ≤ v / 2 := Nat.min_le_left _ _
    omega
  have hc9 : c ≤ 9 := by
    obtain ⟨w, hw⟩ := hgodd
    rcases min_choice (v / 2) (9 * (g / 2)) with hRv | hRv
    · omega
    · omega
  have hRle : R ≤ 9 * (g / 2) := Nat.min_le_right _ _
  obtain ⟨F, hFlen, hF9, hFsum⟩ :=
    exists_free_block (g / 2) R hRle
  set C := F ++ [c] ++ F.reverse with hC
  have hCpal : C.Palindrome := center_free_pal F c
  have hC10 : ∀ x ∈ C, x < 10 := by
    intro x hx
    rw [hC] at hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · have := hF9 x hx
        omega
      · rw [List.mem_singleton] at hx
        omega
    · have := hF9 x (List.mem_reverse.mp hx)
      omega
  have hCg : C.length = g := by
    rw [hC, List.length_append, List.length_append, hFlen,
      List.length_singleton, List.length_reverse]
    omega
  have hCσ : C.sum = v := by
    rw [hC, List.sum_append, List.sum_append, List.sum_reverse,
      hFsum, List.sum_singleton]
    omega
  have hKcov : m * 3 ^ (0 - 4) ≤ 1 + 9 * (K / 2) := by
    have hK2 : K / 2 = (m - 1) / 9 + 1 := by
      rw [hK]
      exact Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)
    have hdm := Nat.div_add_mod (m - 1) 9
    have hmlt : (m - 1) % 9 < 9 := Nat.mod_lt _ (by norm_num)
    have h0m : 0 - 4 = 0 := rfl
    rw [h0m, pow_zero, mul_one, hK2]
    omega
  obtain ⟨s₀, hs0⟩ := hs0_v0 (le := lenD) (K := K) (g := g) D C
  obtain ⟨e', he', hdvdP⟩ :=
    P_dvd_3m81 (v := 0) (le := lenD) (K := K) (g := g)
      hm3 hm10 D hlenD'.symm C hCg hg3 hgodd hKcov s₀ hs0
  set MID := (List.range (2 * K)).map (pairDigit e') ++ C
      ++ ((List.range (2 * K)).map (pairDigit e')).reverse with hMID
  have hMIDpal : MID.Palindrome := mid_pal e' C hCpal
  have hMID10 : ∀ x ∈ MID, x < 10 := mid_lt10 e' he' C hC10
  have hMIDlen : MID.length = 4 * K + g := by
    rw [hMID, List.length_append, List.length_append,
      List.length_reverse, List.length_map, List.length_range, hCg]
    ring
  have hMIDσ : MID.sum = 18 * K + C.sum := mid_sum e' he' C
  obtain ⟨hP0, hPpal, hPlen, hPσ⟩ := sandwich_spec_gen D MID
    hDne hD10 (hD0 hDne) hMIDpal hMID10 rfl rfl
  have h25P : 2 ^ 0 * 5 ^ 0 ∣ Nat.ofDigits 10
      (D ++ MID ++ D.reverse) :=
    B_dvd_P (le := lenD) hlenD'.symm hD25 (by omega)
  set P := Nat.ofDigits 10 (D ++ MID ++ D.reverse) with hP
  have hmP : 3 ^ 0 * m ∣ P := by simpa using hdvdP
  have hnP : n ∣ P * 10 ^ z := by
    have h := n_dvd_P_pow10_le (a := a) (b := b) (v := 0) (m := m)
      (z := z) (a' := 0) (b' := 0) (P := P) h25P hmP
      (by omega) (by omega) hm30
    have h' : 2 ^ a * 5 ^ b * m ∣ P * 10 ^ z := by simpa using h
    rw [hn]
    exact h'
  have hσ : (Nat.digits 10 P).sum = σ₀ := by
    rw [hPσ, hMIDσ, hCσ]
    omega
  refine ⟨P, z, hP0, fun _ => h10n, hPpal, ?_, ?_, ?_⟩
  · rw [hPlen, hMIDlen]
    omega
  · rwa [hn] at hnP
  · rw [hσ, hσ₀, hn]
    exact dvd_mul_right _ _


set_option maxHeartbeats 800000 in
theorem assemble_v0e {a m : ℕ} (ha : 1 ≤ a) (hm0 : 1 ≤ m)
    (hm30 : m.Coprime 30)
    (hm11 : m.Coprime 11) (hm101 : m.Coprime 101)
    (hB : 72 * a + 72 * ((m - 1) / 9 + 1) + 81 ≤ 8 * (2 ^ a) * m) :
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
  
  obtain ⟨D, _hDpal, hD10, hDne, hD0, hD25, _hD3v, _hDσ, hr₀lt,
    hlenD⟩ := border_pal_q (a' := a) (b' := 0) (q := 2) (s₁ := a)
      (t := 0) (by norm_num) (by norm_num) (Or.inr rfl)
      (le_of_eq (Nat.max_eq_left (Nat.zero_le a)))
  set lenD := D.length with hlenD'
  have hr0z : r0b a 0 2 = 0 := by
    have h := hr₀lt
    norm_num at h
    exact h
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
        _ = 10 ^ (a + 2) := by ring
    have hpow : 10 ^ ((Nat.digits 10 (9 * 2 ^ a)).length)
        < 10 ^ (a + 2) := lt_of_le_of_lt hb2 hlt
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 10)).mp hpow
    omega
  have hlenDb : lenD ≤ 4 * a + 4 := by omega
  have hneven : Even n := by
    have h2a : 2 ^ a = 2 * 2 ^ (a - 1) := by
      rw [← Nat.pow_succ', Nat.succ_eq_add_one,
        Nat.sub_add_cancel (by omega : 1 ≤ a)]
    refine ⟨2 ^ (a - 1) * m, ?_⟩
    rw [hn, h2a]
    ring
  have hnpos : 0 < n := by rw [hn]; positivity
  have hB' : 72 * a + 72 * ((m - 1) / 9 + 1) + 81 ≤ 8 * n := by
    rw [hn, ← Nat.mul_assoc]
    exact hB
  have h36K : 36 * K = 72 * ((m - 1) / 9 + 1) := by rw [hK]; ring
  have hkey : 18 * lenD + 36 * K ≤ 8 * n - 9 := by omega
  set base := 2 * D.sum + 18 * K with hbase
  set g := n - (2 * lenD + 4 * K) with hg
  have hcap : n ≤ 9 * g + 1 := by omega
  have hg3 : 3 ≤ g := by omega
  have hgev : Even g := by
    obtain ⟨w, hw⟩ := hneven
    refine ⟨w - (lenD + 2 * K), ?_⟩
    rw [hg]
    omega
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
      refine ⟨D.sum + 9 * K, ?_⟩
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
  have hKcov : m * 3 ^ (0 - 4) ≤ 1 + 9 * (K / 2) := by
    have hK2 : K / 2 = (m - 1) / 9 + 1 := by
      rw [hK]
      exact Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)
    have hdm := Nat.div_add_mod (m - 1) 9
    have hmlt : (m - 1) % 9 < 9 := Nat.mod_lt _ (by norm_num)
    have h0m : 0 - 4 = 0 := rfl
    rw [h0m, pow_zero, mul_one, hK2]
    omega
  obtain ⟨s₀, hs0⟩ := hs0_v0 (le := lenD) (K := K) (g := g) D C
  obtain ⟨e', he', hdvdP⟩ :=
    P_dvd_3m81_even (v := 0) (le := lenD) (K := K) (g := g)
      hm3 hm10 hm11 hm101 D hlenD'.symm C hCg hg3 hgev hKcov s₀ hs0
  set MID := (List.range (2 * K)).map (pairDigit e') ++ C
      ++ ((List.range (2 * K)).map (pairDigit e')).reverse with hMID
  have hMIDpal : MID.Palindrome := mid_pal e' C hCpal
  have hMID10 : ∀ x ∈ MID, x < 10 := mid_lt10 e' he' C hC10
  have hMIDlen : MID.length = 4 * K + g := by
    rw [hMID, List.length_append, List.length_append,
      List.length_reverse, List.length_map, List.length_range, hCg]
    ring
  have hMIDσ : MID.sum = 18 * K + C.sum := mid_sum e' he' C
  obtain ⟨hP0, hPpal, hPlen, hPσ⟩ := sandwich_spec_gen D MID
    hDne hD10 (hD0 hDne) hMIDpal hMID10 rfl rfl
  have h25P : 2 ^ a * 5 ^ 0 ∣ Nat.ofDigits 10
      (D ++ MID ++ D.reverse) :=
    B_dvd_P (le := lenD) hlenD'.symm hD25 (by omega)
  set P := Nat.ofDigits 10 (D ++ MID ++ D.reverse) with hP
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
  · rw [hPlen, hMIDlen]
    omega
  · simpa using hnP
  · rw [hσ, hσ₀]
    rw [hn]
    exact dvd_mul_right _ _


set_option maxHeartbeats 800000 in
theorem assemble_v000 {m : ℕ} (hm0 : 1 ≤ m) (hm30 : m.Coprime 30)
    (hmod : m % 9 = 1) (h55 : 55 ≤ m) :
    ∃ P z : ℕ, P ≠ 0
      ∧ (0 < z → 10 ∣ m)
      ∧ (Nat.digits 10 P).Palindrome
      ∧ (Nat.digits 10 P).length + z = m
      ∧ m ∣ P * 10 ^ z
      ∧ m ∣ (Nat.digits 10 P).sum := by
  classical
  have : NeZero m := ⟨by omega⟩
  have hm3 : m.Coprime 3 := hm30.coprime_dvd_right (by norm_num)
  have hm10 : m.Coprime 10 := hm30.coprime_dvd_right (by norm_num)
  have hm2 : m.Coprime 2 := hm30.coprime_dvd_right (by norm_num)
  
  have hq : m - 1 = 9 * (m / 9) := by
    have hdm := Nat.div_add_mod m 9
    omega
  set K := 2 * (m / 9) with hK
  have h18K : 18 * K = 4 * (m - 1) := by
    rw [hK]
    omega
  obtain ⟨D, _hDpal, hD10, hDne, hD0, _hD25, _hD3v, hDσ, hr₀lt,
    hlenD⟩ := border_pal_q (a' := 0) (b' := 0) (q := 2) (s₁ := 0)
      (t := 0) (by norm_num) (by norm_num) (Or.inl rfl)
      (le_of_eq (Nat.max_eq_right (Nat.zero_le 0)))
  set lenD := D.length with hlenD'
  have hr0z : r0b 0 0 2 = 0 := by
    have h := hr₀lt
    norm_num at h
    exact h
  have hlenN : lenD = 2 := by
    have h := hlenD
    rw [hr0z] at h
    norm_num at h ⊢
    omega
  have hnodd : Odd m := by
    have h2 : ¬ (2 : ℕ) ∣ m :=
      (Nat.prime_two.coprime_iff_not_dvd).mp hm2.symm
    rw [← Nat.not_even_iff_odd]
    rintro ⟨c', hc'⟩
    exact h2 ⟨c', by omega⟩
  set g := m - (2 * lenD + 4 * K) with hg
  have hg3 : 3 ≤ g := by omega
  have hgodd : Odd g := by
    obtain ⟨w, hw⟩ := hnodd
    refine ⟨w - (lenD + 2 * K), ?_⟩
    rw [hg]
    omega
  
  set v := m - 32 with hv
  have hvle : v ≤ 9 * g := by omega
  set R := (v - 5) / 2 with hR
  set c := 5 with hc
  have h2Rc : 2 * R + c = v := by
    obtain ⟨w, hw⟩ := hnodd
    omega
  have hRle : R ≤ 9 * (g / 2) := by
    obtain ⟨w, hw⟩ := hgodd
    omega
  obtain ⟨F, hFlen, hF9, hFsum⟩ :=
    exists_free_block (g / 2) R hRle
  set C := F ++ [c] ++ F.reverse with hC
  have hCpal : C.Palindrome := center_free_pal F c
  have hC10 : ∀ x ∈ C, x < 10 := by
    intro x hx
    rw [hC] at hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · have := hF9 x hx
        omega
      · rw [List.mem_singleton] at hx
        omega
    · have := hF9 x (List.mem_reverse.mp hx)
      omega
  have hCg : C.length = g := by
    rw [hC, List.length_append, List.length_append, hFlen,
      List.length_singleton, List.length_reverse]
    omega
  have hCσ : C.sum = v := by
    rw [hC, List.sum_append, List.sum_append, List.sum_reverse,
      hFsum, List.sum_singleton]
    omega
  have hKcov : m * 3 ^ (0 - 4) ≤ 1 + 9 * (K / 2) := by
    have hK2 : K / 2 = m / 9 := by
      rw [hK]
      exact Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)
    have h0m : 0 - 4 = 0 := rfl
    rw [h0m, pow_zero, mul_one, hK2]
    omega
  obtain ⟨s₀, hs0⟩ := hs0_v0 (le := lenD) (K := K) (g := g) D C
  obtain ⟨e', he', hdvdP⟩ :=
    P_dvd_3m81 (v := 0) (le := lenD) (K := K) (g := g)
      hm3 hm10 D hlenD'.symm C hCg hg3 hgodd hKcov s₀ hs0
  set MID := (List.range (2 * K)).map (pairDigit e') ++ C
      ++ ((List.range (2 * K)).map (pairDigit e')).reverse with hMID
  have hMIDpal : MID.Palindrome := mid_pal e' C hCpal
  have hMID10 : ∀ x ∈ MID, x < 10 := mid_lt10 e' he' C hC10
  have hMIDlen : MID.length = 4 * K + g := by
    rw [hMID, List.length_append, List.length_append,
      List.length_reverse, List.length_map, List.length_range, hCg]
    ring
  have hMIDσ : MID.sum = 18 * K + C.sum := mid_sum e' he' C
  obtain ⟨hP0, hPpal, hPlen, hPσ⟩ := sandwich_spec_gen D MID
    hDne hD10 (hD0 hDne) hMIDpal hMID10 rfl rfl
  set P := Nat.ofDigits 10 (D ++ MID ++ D.reverse) with hP
  have hmP : m ∣ P := by simpa using hdvdP
  have hρ : rhob 0 0 2 = 1 := by decide
  have hD18 : D.sum = 18 := by rw [hDσ, hρ]; norm_num
  have hσ : (Nat.digits 10 P).sum = 5 * m := by
    rw [hPσ, hMIDσ, hCσ, hD18, hv]
    omega
  refine ⟨P, 0, hP0, fun h => (Nat.lt_irrefl 0 h).elim, hPpal,
    ?_, ?_, ?_⟩
  · rw [hPlen, hMIDlen]
    omega
  · simpa using hmP
  · rw [hσ]
    exact ⟨5, by ring⟩




variable {m : ℕ} [NeZero m]
variable {M : ℕ} [NeZero M]


set_option maxHeartbeats 800000 in
def pairDigitS (s e : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i % 2 = 0 then e (i / 2) else s (i / 2) - e (i / 2)

set_option maxHeartbeats 800000 in
theorem pairDigitS_even (s e : ℕ → ℕ) (k : ℕ) :
    pairDigitS s e (2 * k) = e k := by
  unfold pairDigitS
  rw [show (2 * k) % 2 = 0 by omega, show (2 * k) / 2 = k by omega]
  simp

set_option maxHeartbeats 800000 in
theorem pairDigitS_odd (s e : ℕ → ℕ) (k : ℕ) :
    pairDigitS s e (2 * k + 1) = s k - e k := by
  unfold pairDigitS
  rw [show (2 * k + 1) % 2 = 1 by omega,
    show (2 * k + 1) / 2 = k by omega]
  simp


set_option maxHeartbeats 800000 in
theorem pair_covers_c {S : Finset (ZMod m)} {a b : ℕ} {w₁ w₂ : ZMod m}
    {c : ℕ}
    (ha : w₁ = (a : ZMod m)) (hb : w₂ = (b : ZMod m))
    (hgcd : Nat.gcd (Nat.gcd a b) m = 1) (hS0 : (0 : ZMod m) ∈ S) :
    min (S.card + c) m ≤ (S + seg w₁ c + seg w₂ c).card := by
  set T₁ := S + seg w₁ c with hT1
  set T₂ := T₁ + seg w₂ c with hT2
  have hST1 : S ⊆ T₁ := subset_add_of_zero_mem (zero_mem_seg w₁ c)
  have hT1T2 : T₁ ⊆ T₂ := subset_add_of_zero_mem (zero_mem_seg w₂ c)
  by_cases hbig : S.card + c ≤ T₁.card
  · calc min (S.card + c) m ≤ S.card + c := min_le_left _ _
      _ ≤ T₂.card := le_trans hbig (Finset.card_le_card hT1T2)
  · push_neg at hbig
    have hbig' : (S + seg w₁ c).card < S.card + c := by rwa [hT1] at hbig
    have hw1 : T₁ + {w₁} = T₁ := by
      rw [hT1]
      exact segk_invariant hbig'
    by_cases hbig2 : T₁.card + c ≤ T₂.card
    · have hs : S.card ≤ T₁.card := Finset.card_le_card hST1
      calc min (S.card + c) m ≤ S.card + c := min_le_left _ _
        _ ≤ T₁.card + c := by omega
        _ ≤ T₂.card := hbig2
    · push_neg at hbig2
      have hbig2' : (T₁ + seg w₂ c).card < T₁.card + c := by
        rwa [hT2] at hbig2
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
theorem zero_mem_sum_seg_c (w : ℕ → ZMod m) (c : ℕ → ℕ) (r : ℕ) :
    (0 : ZMod m) ∈ ∑ i ∈ Finset.range r, seg (w i) (c i) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ]
    exact (zero_add (0 : ZMod m)) ▸
      Finset.add_mem_add ih (zero_mem_seg (w r) (c r))


set_option maxHeartbeats 800000 in
theorem min_add_le_min_c {x y m c : ℕ} (h : min x m ≤ y) :
    min (x + c) m ≤ min (y + c) m := by
  rcases Nat.lt_or_ge x m with hc | hc
  · rw [min_eq_left (le_of_lt hc)] at h
    exact le_min (by omega) (min_le_right _ _)
  · rw [min_eq_right hc] at h
    rw [min_eq_right (by omega : m ≤ y + c)]
    exact min_le_right _ _


set_option maxHeartbeats 800000 in
theorem pair_covers_iter_c {S : Finset (ZMod m)} {w : ℕ → ZMod m}
    {a : ℕ → ℕ} {c : ℕ → ℕ}
    (ha : ∀ i, w i = (a i : ZMod m))
    (hgcd : ∀ i, Nat.gcd (Nat.gcd (a (2 * i)) (a (2 * i + 1))) m = 1)
    (hS0 : (0 : ZMod m) ∈ S) (r : ℕ) :
    min (S.card + ∑ j ∈ Finset.range r, c j) m ≤
      (S + ∑ i ∈ Finset.range (2 * r), seg (w i) (c (i / 2))).card := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ]
    have h2r : 2 * (r + 1) = 2 * r + 1 + 1 := by ring
    rw [h2r, Finset.sum_range_succ, Finset.sum_range_succ]
    rw [show 2 * r / 2 = r by omega, show (2 * r + 1) / 2 = r by omega]
    rw [← add_assoc, ← add_assoc, ← add_assoc]
    have hT0 : (0 : ZMod m) ∈
        S + ∑ i ∈ Finset.range (2 * r), seg (w i) (c (i / 2)) :=
      (zero_add (0 : ZMod m)) ▸
        Finset.add_mem_add hS0
          (zero_mem_sum_seg_c w (fun i => c (i / 2)) (2 * r))
    have hstep := pair_covers_c (c := c r) (ha (2 * r)) (ha (2 * r + 1))
      (hgcd r) hT0
    exact (min_add_le_min_c ih).trans hstep


set_option maxHeartbeats 800000 in
theorem covers_univ_c {S : Finset (ZMod m)} {w : ℕ → ZMod m} {a : ℕ → ℕ}
    {c : ℕ → ℕ}
    (ha : ∀ i, w i = (a i : ZMod m))
    (hgcd : ∀ i, Nat.gcd (Nat.gcd (a (2 * i)) (a (2 * i + 1))) m = 1)
    (hS0 : (0 : ZMod m) ∈ S) {r : ℕ}
    (hr : m ≤ S.card + ∑ j ∈ Finset.range r, c j) :
    S + ∑ i ∈ Finset.range (2 * r), seg (w i) (c (i / 2)) = Finset.univ := by
  have h := pair_covers_iter_c (c := c) ha hgcd hS0 r
  rw [min_eq_right hr] at h
  exact Finset.eq_univ_of_card _ (by
    rw [ZMod.card]
    exact le_antisymm
      (le_trans (Finset.card_le_univ _) (le_of_eq (ZMod.card m))) h)


set_option maxHeartbeats 800000 in
theorem mem_sum_seg_c {w : ℕ → ZMod m} {cc : ℕ → ℕ} {r : ℕ} {x : ZMod m}
    (hx : x ∈ ∑ i ∈ Finset.range r, seg (w i) (cc i)) :
    ∃ d : ℕ → ℕ, (∀ i, d i ≤ cc i)
      ∧ x = ∑ i ∈ Finset.range r, (d i : ZMod m) * w i := by
  induction r generalizing x with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty, mem_zero] at hx
    exact ⟨fun _ => 0, fun _ => Nat.zero_le _, by simpa using hx⟩
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


set_option maxHeartbeats 800000 in
theorem gadget_extract3_var {K g : ℕ} (hM10 : M.Coprime 10)
    (hg3 : 3 ≤ g) (hgodd : Odd g) (c : ℕ → ℕ)
    (hK : M ≤ 1 + ∑ j ∈ Finset.range (K / 2), c j) (t : ZMod M) :
    ∃ e : ℕ → ℕ, (∀ k, e k ≤ c (k / 2))
      ∧ (∑ k ∈ Finset.range K, (e k : ZMod M)
          * (((10 : ℕ) ^ (2 * k)
              * ((10 ^ (4 * K + g - 2 - 4 * k) - 1) / 9) : ℕ) : ZMod M))
        = t := by
  set L := 4 * K + g with hL
  set r := K / 2 with hr
  set a : ℕ → ℕ := fun i =>
    if i < K then 10 ^ (2 * i) * ((10 ^ (L - 2 - 4 * i) - 1) / 9) else 1
    with ha
  set w : ℕ → ZMod M := fun i => (a i : ZMod M) with hw
  have hDg : ∀ i, 2 * i + 1 < K
      → Nat.gcd (L - 2 - 4 * (2 * i)) (L - 2 - 4 * (2 * i + 1)) = 1 := by
    intro i hi
    obtain ⟨c', hc'⟩ := hgodd
    have hD1pos : 1 ≤ L - 2 - 4 * (2 * i + 1) := by
      rw [hL]; omega
    have hD2 : L - 2 - 4 * (2 * i) = (L - 2 - 4 * (2 * i + 1)) + 4 := by
      omega
    have hodd : Odd (L - 2 - 4 * (2 * i + 1)) := by
      refine ⟨2 * K + c' - 4 * i - 3, ?_⟩
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
      have hgd : Nat.gcd 4 (L - 2 - 4 * (2 * i + 1))
          ∣ L - 2 - 4 * (2 * i + 1) := Nat.gcd_dvd_right _ _
      rw [h2] at hgd
      obtain ⟨c'', hc''⟩ := hodd
      omega
    · exfalso
      have hgd : Nat.gcd 4 (L - 2 - 4 * (2 * i + 1))
          ∣ L - 2 - 4 * (2 * i + 1) := Nat.gcd_dvd_right _ _
      rw [h4'] at hgd
      obtain ⟨c'', hc''⟩ := hodd
      omega
  have haw : ∀ i, w i = (a i : ZMod M) := fun i => rfl
  have hgcd : ∀ i, Nat.gcd (Nat.gcd (a (2 * i)) (a (2 * i + 1))) M = 1 := by
    intro i
    by_cases hi : 2 * i + 1 < K
    · rw [ha]; dsimp only
      rw [if_pos (by omega : 2 * i < K), if_pos hi]
      have hD1 : 1 ≤ L - 2 - 4 * (2 * i) := by rw [hL]; omega
      have hD2 : 1 ≤ L - 2 - 4 * (2 * i + 1) := by rw [hL]; omega
      have hg : Nat.gcd
          (10 ^ (2 * (2 * i)) * ((10 ^ (L - 2 - 4 * (2 * i)) - 1) / 9))
          (10 ^ (2 * (2 * i + 1))
            * ((10 ^ (L - 2 - 4 * (2 * i + 1)) - 1) / 9))
          = 10 ^ (4 * i) := by
        have e1 : 2 * (2 * i + 1) = 4 * i + 2 := by ring
        have e2 : 2 * (2 * i) = 4 * i := by ring
        rw [e1, e2, pow_add, Nat.mul_assoc, Nat.gcd_mul_left]
        have hc10 : Nat.Coprime
            ((10 ^ (L - 2 - 4 * (2 * i)) - 1) / 9) (10 ^ 2) :=
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
  have hS0 : (0 : ZMod M) ∈ ({0} : Finset (ZMod M)) :=
    Finset.mem_singleton_self 0
  have hcard : ({0} : Finset (ZMod M)).card = 1 := Finset.card_singleton 0
  have hcover : ({0} : Finset (ZMod M))
      + ∑ i ∈ Finset.range (2 * r), seg (w i) (c (i / 2)) = Finset.univ :=
    covers_univ_c (m := M) haw hgcd hS0 (r := r) (by rw [hcard]; exact hK)
  have ht : t ∈ ({0} : Finset (ZMod M))
      + ∑ i ∈ Finset.range (2 * r), seg (w i) (c (i / 2)) := by
    rw [hcover]; exact Finset.mem_univ t
  rw [Finset.mem_add] at ht
  obtain ⟨s', hs', c', hc', hsum⟩ := ht
  rw [Finset.mem_singleton] at hs'
  obtain ⟨d, hd, hcx⟩ := mem_sum_seg_c hc'
  refine ⟨fun k => if k < 2 * r then d k else 0, ?_, ?_⟩
  · intro k
    by_cases hk : k < 2 * r
    · simp only [hk, ite_true]; exact hd k
    · simp only [hk, ite_false]; exact Nat.zero_le _
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
    rw [← hcx, ← hsum, hs', zero_add]


set_option maxHeartbeats 800000 in
theorem castHom_nat {q m' : ℕ} (h : m' ∣ q) (n : ℕ) :
    (ZMod.castHom h (ZMod m')) (n : ZMod q) = n := by
  have hh := map_natCast (ZMod.castHom h (ZMod m')) n
  simpa using hh


set_option maxHeartbeats 800000 in
theorem extract3_target81_var {m v K g : ℕ} [NeZero m]
    (hm3 : m.Coprime 3) (hm10 : m.Coprime 10)
    (hg3 : 3 ≤ g) (hgodd : Odd g) (c : ℕ → ℕ)
    (hK : m * 3 ^ (v - 4) ≤ 1 + ∑ j ∈ Finset.range (K / 2), c j)
    (t : ZMod m) (s₀ : ℕ) :
    ∃ e : ℕ → ℕ, (∀ k, e k ≤ c (k / 2))
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
    gadget_extract3_var hM10 hg3 hgodd c hK (↑trep : ZMod M)
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
theorem sum_pair_weights_gen_var {m K L : ℕ} (s e : ℕ → ℕ)
    (he : ∀ k, e k ≤ s k) :
    ∑ i ∈ Finset.range (2 * K),
        (pairDigitS s e i : ZMod m) * palW m L i
    = ∑ k ∈ Finset.range K,
        ((s k : ZMod m) * palW m L (2 * k + 1)
        + (e k : ZMod m) * (palW m L (2 * k)
            - palW m L (2 * k + 1))) := by
  rw [sum_range_pair
    (fun i => (pairDigitS s e i : ZMod m) * palW m L i) K]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [pairDigitS_even, pairDigitS_odd]
  rw [Nat.cast_sub (he k)]
  push_cast
  ring


set_option maxHeartbeats 800000 in
theorem ofDigits_pair_center_var {m K g : ℕ} (s e : ℕ → ℕ)
    (he : ∀ k, e k ≤ s k) (C : List ℕ) (hC : C.length = g) :
    Nat.ofDigits (10 : ZMod m)
      ((List.range (2 * K)).map (pairDigitS s e) ++ C
        ++ ((List.range (2 * K)).map (pairDigitS s e)).reverse)
    = Nat.ofDigits (10 : ZMod m) C * (10 : ZMod m) ^ (2 * K)
      + ∑ k ∈ Finset.range K,
          ((s k : ZMod m) * palW m (4 * K + g) (2 * k + 1)
          + (e k : ZMod m)
            * (palW m (4 * K + g) (2 * k)
              - palW m (4 * K + g) (2 * k + 1))) := by
  have hlen : ((List.range (2 * K)).map (pairDigitS s e)).length
      = 2 * K := by
    rw [List.length_map, List.length_range]
  rw [ofDigits_append', ofDigits_append', hlen,
    List.length_append, hlen, hC]
  rw [ofDigits_zmod_range, ofDigits_zmod_rev]
  rw [Finset.mul_sum]
  have hterm : ∀ i ∈ Finset.range (2 * K),
      (10 : ZMod m) ^ (2 * K + g)
          * ((pairDigitS s e i : ZMod m) * 10 ^ (2 * K - 1 - i))
      = (pairDigitS s e i : ZMod m)
          * (10 : ZMod m) ^ (4 * K + g - 1 - i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    calc (10 : ZMod m) ^ (2 * K + g)
          * ((pairDigitS s e i : ZMod m) * 10 ^ (2 * K - 1 - i))
        = (pairDigitS s e i : ZMod m)
            * ((10 : ZMod m) ^ (2 * K + g) * 10 ^ (2 * K - 1 - i)) := by
          ring
      _ = (pairDigitS s e i : ZMod m)
            * (10 : ZMod m) ^ (2 * K + g + (2 * K - 1 - i)) := by
          rw [← pow_add]
      _ = (pairDigitS s e i : ZMod m)
            * (10 : ZMod m) ^ (4 * K + g - 1 - i) := by
          rw [show 2 * K + g + (2 * K - 1 - i)
              = 4 * K + g - 1 - i by omega]
  have hsum : ∑ i ∈ Finset.range (2 * K),
        (pairDigitS s e i : ZMod m) * (10 : ZMod m) ^ i
      + ∑ i ∈ Finset.range (2 * K), (10 : ZMod m) ^ (2 * K + g)
          * ((pairDigitS s e i : ZMod m) * 10 ^ (2 * K - 1 - i))
      = ∑ i ∈ Finset.range (2 * K),
          (pairDigitS s e i : ZMod m) * palW m (4 * K + g) i := by
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
  rw [sum_pair_weights_gen_var s e he]


set_option maxHeartbeats 800000 in
theorem gadget_val_m_var {m le K g : ℕ} (de : List ℕ)
    (hle : de.length = le) (s e : ℕ → ℕ) (he : ∀ k, e k ≤ s k)
    (C : List ℕ) (hC : C.length = g) :
    Nat.ofDigits (10 : ZMod m)
      (de ++ (((List.range (2 * K)).map (pairDigitS s e) ++ C)
          ++ ((List.range (2 * K)).map (pairDigitS s e)).reverse)
        ++ de.reverse)
    = (Nat.ofDigits (10 : ZMod m) de
        + Nat.ofDigits (10 : ZMod m) de.reverse
            * (10 : ZMod m) ^ (le + (4 * K + g)))
      + (10 : ZMod m) ^ le
          * (Nat.ofDigits (10 : ZMod m) C * (10 : ZMod m) ^ (2 * K)
            + ∑ k ∈ Finset.range K,
                ((s k : ZMod m) * palW m (4 * K + g) (2 * k + 1)
                + (e k : ZMod m)
                    * (palW m (4 * K + g) (2 * k)
                      - palW m (4 * K + g) (2 * k + 1)))) := by
  set G := (List.range (2 * K)).map (pairDigitS s e) with hG
  set X := (G ++ C) ++ G.reverse with hX
  have hGl : G.length = 2 * K := by
    rw [hG, List.length_map, List.length_range]
  have hXl : X.length = 4 * K + g := by
    rw [hX, List.length_append, List.length_append, hGl,
      List.length_reverse, hGl, hC]; ring
  have hlen : (de ++ X).length = le + (4 * K + g) := by
    rw [List.length_append, hle, hXl]
  rw [ofDigits_append', ofDigits_append', hlen]
  have hInner :=
    ofDigits_pair_center_var (m := m) (K := K) (g := g) s e he C hC
  rw [← hG] at hInner
  rw [hX, hInner, hle]
  ring


set_option maxHeartbeats 800000 in
theorem P_dvd_3m81_var {m v le K g : ℕ} [NeZero m]
    (hm3 : m.Coprime 3) (hm10 : m.Coprime 10)
    (de : List ℕ) (hle : de.length = le)
    (C : List ℕ) (hC : C.length = g)
    (hg3 : 3 ≤ g) (hgodd : Odd g)
    (c s : ℕ → ℕ) (hsc : ∀ k, s k = c (k / 2))
    (hKcov : m * 3 ^ (v - 4) ≤ 1 + ∑ j ∈ Finset.range (K / 2), c j)
    (s₀ : ℕ)
    (hs0 : (Nat.ofDigits (10 : ZMod (3 ^ v)) de
        + Nat.ofDigits (10 : ZMod (3 ^ v)) de.reverse
            * (10 : ZMod (3 ^ v)) ^ (le + (4 * K + g)))
      + (10 : ZMod (3 ^ v)) ^ le
        * (Nat.ofDigits (10 : ZMod (3 ^ v)) C
            * (10 : ZMod (3 ^ v)) ^ (2 * K)
          + (∑ k ∈ Finset.range K, (s k : ZMod (3 ^ v))
                * palW (3 ^ v) (4 * K + g) (2 * k + 1)
            + 81 * (s₀ : ZMod (3 ^ v)))) = 0) :
    ∃ e' : ℕ → ℕ, (∀ k, e' k ≤ s k)
      ∧ m * 3 ^ v ∣ Nat.ofDigits 10
          (de ++ (((List.range (2 * K)).map (pairDigitS s e') ++ C)
            ++ ((List.range (2 * K)).map (pairDigitS s e')).reverse)
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
      + ∑ k ∈ Finset.range K, (s k : ZMod m)
          * palW m (4 * K + g) (2 * k + 1) with hX
  set t : ZMod m := -(E + (10 : ZMod m) ^ le * X)
      * ((10 : ZMod m) ^ le * 81)⁻¹ with ht
  obtain ⟨e', he', T, hTsum, hTm, hT3⟩ :=
    extract3_target81_var hm3 hm10 hg3 hgodd c hKcov t s₀
  refine ⟨e', fun k => (hsc k).symm ▸ he' k, ?_⟩
  have hPq : (Nat.ofDigits (10 : ZMod q)
      (de ++ (((List.range (2 * K)).map (pairDigitS s e') ++ C)
          ++ ((List.range (2 * K)).map (pairDigitS s e')).reverse)
          ++ de.reverse))
      = (Nat.ofDigits (10 : ZMod q) de
          + Nat.ofDigits (10 : ZMod q) de.reverse
              * (10 : ZMod q) ^ (le + (4 * K + g)))
        + (10 : ZMod q) ^ le
            * (Nat.ofDigits (10 : ZMod q) C * (10 : ZMod q) ^ (2 * K)
              + ∑ k ∈ Finset.range K,
                  ((s k : ZMod q) * palW q (4 * K + g) (2 * k + 1)
                  + (e' k : ZMod q)
                      * (palW q (4 * K + g) (2 * k)
                        - palW q (4 * K + g) (2 * k + 1)))) :=
    gadget_val_m_var de hle s e' (fun k => (hsc k).symm ▸ he' k) C hC
  simp only [twt] at hTsum
  have hsumq : ∑ k ∈ Finset.range K,
      ((s k : ZMod q) * palW q (4 * K + g) (2 * k + 1)
        + (e' k : ZMod q)
            * (palW q (4 * K + g) (2 * k) - palW q (4 * K + g) (2 * k + 1)))
      = (∑ k ∈ Finset.range K, (s k : ZMod q)
            * palW q (4 * K + g) (2 * k + 1)) + T := by
    rw [Finset.sum_add_distrib, hTsum]
  rw [hsumq] at hPq
  have hPm : (Nat.ofDigits (10 : ZMod m)
      (de ++ (((List.range (2 * K)).map (pairDigitS s e') ++ C)
          ++ ((List.range (2 * K)).map (pairDigitS s e')).reverse)
          ++ de.reverse)) = 0 := by
    have hcast := congrArg (ZMod.castHom (Nat.dvd_mul_right m (3 ^ v))
      (ZMod m)) hPq
    rw [castHom_ofDigits] at hcast
    rw [map_add, map_add, castHom_ofDigits, map_mul, castHom_ofDigits,
      map_pow, castHom_ten] at hcast
    rw [map_mul, map_pow, castHom_ten] at hcast
    rw [map_add, map_mul, castHom_ofDigits, map_pow, castHom_ten] at hcast
    rw [map_add] at hcast
    have hs' : (ZMod.castHom (Nat.dvd_mul_right m (3 ^ v)) (ZMod m))
        (∑ k ∈ Finset.range K, (s k : ZMod q)
            * palW q (4 * K + g) (2 * k + 1))
        = ∑ k ∈ Finset.range K, (s k : ZMod m)
            * palW m (4 * K + g) (2 * k + 1) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [map_mul, castHom_nat _ _, castHom_palW _ _ _]
    rw [hs', hTm] at hcast
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
          + (∑ k ∈ Finset.range K, (s k : ZMod m)
                * palW m (4 * K + g) (2 * k + 1)
            + 81 * t))
        = E + (10 : ZMod m) ^ le * X + ((10 : ZMod m) ^ le * 81) * t
        from by rw [hX]; ring]
    rw [htz]
    ring
  have hP3 : (Nat.ofDigits (10 : ZMod (3 ^ v))
      (de ++ (((List.range (2 * K)).map (pairDigitS s e') ++ C)
          ++ ((List.range (2 * K)).map (pairDigitS s e')).reverse)
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
        (∑ k ∈ Finset.range K, (s k : ZMod q)
            * palW q (4 * K + g) (2 * k + 1))
        = ∑ k ∈ Finset.range K, (s k : ZMod (3 ^ v))
            * palW (3 ^ v) (4 * K + g) (2 * k + 1) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [map_mul, castHom_nat _ _, castHom_palW _ _ _]
    rw [hsp, hT3] at hcast
    rw [hcast]
    linear_combination hs0
  have hdm : m ∣ Nat.ofDigits 10
      (de ++ (((List.range (2 * K)).map (pairDigitS s e') ++ C)
          ++ ((List.range (2 * K)).map (pairDigitS s e')).reverse)
          ++ de.reverse) := by
    rw [← CharP.cast_eq_zero_iff (ZMod m) m _]
    rw [cast_ofDigits]
    exact hPm
  have hd3 : 3 ^ v ∣ Nat.ofDigits 10
      (de ++ (((List.range (2 * K)).map (pairDigitS s e') ++ C)
          ++ ((List.range (2 * K)).map (pairDigitS s e')).reverse)
          ++ de.reverse) := by
    rw [← CharP.cast_eq_zero_iff (ZMod (3 ^ v)) (3 ^ v) _]
    rw [cast_ofDigits]
    exact hP3
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (hm3.pow_right v) hdm hd3


set_option maxHeartbeats 800000 in
theorem hs0_v0_var {le K g : ℕ} (de : List ℕ) (C : List ℕ) (s : ℕ → ℕ) :
    ∃ s₀ : ℕ,
      (Nat.ofDigits (10 : ZMod (3 ^ 0)) de
          + Nat.ofDigits (10 : ZMod (3 ^ 0)) de.reverse
              * (10 : ZMod (3 ^ 0)) ^ (le + (4 * K + g)))
        + (10 : ZMod (3 ^ 0)) ^ le
          * (Nat.ofDigits (10 : ZMod (3 ^ 0)) C
              * (10 : ZMod (3 ^ 0)) ^ (2 * K)
            + (∑ k ∈ Finset.range K, (s k : ZMod (3 ^ 0))
                  * palW (3 ^ 0) (4 * K + g) (2 * k + 1)
              + 81 * (s₀ : ZMod (3 ^ 0)))) = 0 := by
  refine ⟨0, ?_⟩
  rw [pow_zero]
  exact Subsingleton.elim _ _


set_option maxHeartbeats 800000 in
theorem mid_pal_var {K : ℕ} (s e : ℕ → ℕ) (C : List ℕ)
    (hC : C.Palindrome) :
    ((List.range (2 * K)).map (pairDigitS s e) ++ C
      ++ ((List.range (2 * K)).map (pairDigitS s e)).reverse).Palindrome := by
  apply List.Palindrome.of_reverse_eq
  rw [List.reverse_append, List.reverse_append, List.reverse_reverse,
    hC.reverse_eq, List.append_assoc]


set_option maxHeartbeats 800000 in
theorem mid_lt10_var {K : ℕ} (s e : ℕ → ℕ) (hs : ∀ k, s k ≤ 9)
    (he : ∀ k, e k ≤ s k) (C : List ℕ) (hC : ∀ x ∈ C, x < 10) :
    ∀ x ∈ (List.range (2 * K)).map (pairDigitS s e) ++ C
      ++ ((List.range (2 * K)).map (pairDigitS s e)).reverse, x < 10 := by
  have hpd : ∀ i, pairDigitS s e i < 10 := by
    intro i
    unfold pairDigitS
    by_cases h : i % 2 = 0
    · rw [if_pos h]
      have hs' := hs (i / 2)
      have he' := he (i / 2)
      omega
    · rw [if_neg h]
      have hs' := hs (i / 2)
      have he' := he (i / 2)
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
theorem pairDigitS_sum (s e : ℕ → ℕ) (he : ∀ k, e k ≤ s k) (K : ℕ) :
    ((List.range (2 * K)).map (pairDigitS s e)).sum
      = ∑ k ∈ Finset.range K, s k := by
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
    rw [pairDigitS_even, pairDigitS_odd, Finset.sum_range_succ]
    have := he k
    omega


set_option maxHeartbeats 800000 in
theorem mid_sum_var {K : ℕ} (s e : ℕ → ℕ) (he : ∀ k, e k ≤ s k)
    (C : List ℕ) :
    ((List.range (2 * K)).map (pairDigitS s e) ++ C
      ++ ((List.range (2 * K)).map (pairDigitS s e)).reverse).sum
      = 2 * (∑ k ∈ Finset.range K, s k) + C.sum := by
  rw [List.sum_append, List.sum_append, List.sum_reverse,
    pairDigitS_sum s e he]
  ring


set_option maxHeartbeats 800000 in
theorem assemble_v000_ne1 {m : ℕ} (hm0 : 1 ≤ m) (hm30 : m.Coprime 30)
    (hmod : m % 9 ≠ 1) (hk : 13 ≤ (m - 1) / 9 + m % 9) :
    ∃ P z : ℕ, P ≠ 0
      ∧ (0 < z → 10 ∣ m)
      ∧ (Nat.digits 10 P).Palindrome
      ∧ (Nat.digits 10 P).length + z = m
      ∧ m ∣ P * 10 ^ z
      ∧ m ∣ (Nat.digits 10 P).sum := by
  classical
  have : NeZero m := ⟨by omega⟩
  have hm3 : m.Coprime 3 := hm30.coprime_dvd_right (by norm_num)
  have hm10 : m.Coprime 10 := hm30.coprime_dvd_right (by norm_num)
  have hm2 : m.Coprime 2 := hm30.coprime_dvd_right (by norm_num)
  have hρ2 : 2 ≤ m % 9 := by
    have hlt : m % 9 < 9 := Nat.mod_lt _ (by norm_num)
    have h3 : ¬ (3 : ℕ) ∣ m :=
      ((by norm_num : Nat.Prime 3).coprime_iff_not_dvd).mp hm3.symm
    have hm9 : m % 9 % 3 ≠ 0 := by
      rw [Nat.mod_mod_of_dvd _ (by norm_num : (3:ℕ) ∣ 9)]
      intro hh
      exact h3 (Nat.dvd_of_mod_eq_zero hh)
    omega
  set q := (m - 1) / 9 with hq
  have hm9k : m = 9 * q + m % 9 := by rw [hq]; omega
  set K := 2 * (q + 1) with hK
  set c : ℕ → ℕ := fun j => if j < q then 9 else m % 9 - 1 with hc
  have hsumc : ∑ j ∈ Finset.range (q + 1), c j = m - 1 := by
    have hcj : ∀ j ∈ Finset.range q, c j = 9 := by
      intro j hj
      rw [Finset.mem_range] at hj
      simp only [hc]
      exact if_pos hj
    have h1 : ∑ j ∈ Finset.range q, c j = 9 * q := by
      rw [Finset.sum_congr rfl hcj, Finset.sum_const,
        Finset.card_range, smul_eq_mul, mul_comm]
    have h2 : c q = m % 9 - 1 := by
      simp only [hc]
      exact if_neg (by omega : ¬ q < q)
    rw [Finset.sum_range_succ, h1, h2]
    omega
  set s : ℕ → ℕ := fun i => c (i / 2) with hs
  have hsc : ∀ k, s k = c (k / 2) := fun k => by simp only [hs]
  have hs9 : ∀ k, s k ≤ 9 := by
    intro k
    simp only [hs, hc]
    rcases Nat.lt_or_ge (k / 2) q with h | h
    · rw [if_pos h]
    · rw [if_neg (by omega : ¬ k / 2 < q)]
      omega
  have hsums : ∑ k ∈ Finset.range K, s k = 2 * (m - 1) := by
    rw [hK, sum_range_pair s (q + 1)]
    have hpair : ∀ j, s (2 * j) + s (2 * j + 1) = 2 * c j := by
      intro j
      simp only [hs]
      rw [show (2 * j) / 2 = j by omega,
        show (2 * j + 1) / 2 = j by omega]
      ring
    rw [Finset.sum_congr rfl (fun j _ => hpair j), ← Finset.mul_sum,
      hsumc]
  set g := m - (2 + 4 * K) with hg
  have hmodd : m % 2 = 1 := by
    have h2 : ¬ (2 : ℕ) ∣ m :=
      (Nat.prime_two.coprime_iff_not_dvd).mp hm2.symm
    omega
  have hg3 : 3 ≤ g := by omega
  have hgodd : Odd g := by
    have hg2 : g % 2 = 1 := by rw [hg, hK]; omega
    refine ⟨g / 2, ?_⟩
    omega
  obtain ⟨F, hFlen, hF9, hFsum⟩ :=
    exists_free_block (g / 2) 0 (Nat.zero_le _)
  set C := F ++ [2] ++ F.reverse with hC
  have hCpal : C.Palindrome := center_free_pal F 2
  have hC10 : ∀ x ∈ C, x < 10 := by
    intro x hx
    rw [hC] at hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · have := hF9 x hx
        omega
      · rw [List.mem_singleton] at hx
        omega
    · have := hF9 x (List.mem_reverse.mp hx)
      omega
  have hCg : C.length = g := by
    obtain ⟨w, hw⟩ := hgodd
    rw [hC, List.length_append, List.length_append, hFlen,
      List.length_singleton, List.length_reverse]
    omega
  have hCσ : C.sum = 2 := by
    rw [hC]
    simp [List.sum_append, List.sum_reverse, List.sum_singleton, hFsum]
  have hKcov : m * 3 ^ (0 - 4) ≤ 1 + ∑ j ∈ Finset.range (K / 2), c j := by
    have hK2 : K / 2 = q + 1 := by
      rw [hK]
      exact Nat.mul_div_cancel_left _ (by norm_num : (0:ℕ) < 2)
    have h0m : 0 - 4 = 0 := rfl
    rw [h0m, pow_zero, mul_one, hK2, hsumc]
    omega
  obtain ⟨s₀, hs0⟩ := hs0_v0_var (le := 1) (K := K) (g := g) [1] C s
  obtain ⟨e', he', hdvdP⟩ :=
    P_dvd_3m81_var (v := 0) (le := 1) (K := K) (g := g)
      hm3 hm10 [1] rfl C hCg hg3 hgodd c s hsc hKcov s₀ hs0
  set MID := (List.range (2 * K)).map (pairDigitS s e') ++ C
      ++ ((List.range (2 * K)).map (pairDigitS s e')).reverse with hMID
  have hMIDpal : MID.Palindrome := mid_pal_var s e' C hCpal
  have hMID10 : ∀ x ∈ MID, x < 10 := mid_lt10_var s e' hs9 he' C hC10
  have hMIDlen : MID.length = 4 * K + g := by
    rw [hMID, List.length_append, List.length_append,
      List.length_reverse, List.length_map, List.length_range, hCg]
    ring
  have hMIDσ : MID.sum = 2 * (∑ k ∈ Finset.range K, s k) + C.sum :=
    mid_sum_var s e' he' C
  obtain ⟨hP0, hPpal, hPlen, hPσ⟩ := sandwich_spec_gen [1] MID
    (by simp) (by decide) (by decide) hMIDpal hMID10 rfl rfl
  set P := Nat.ofDigits 10 ([1] ++ MID ++ [1].reverse) with hP
  have hmP : m ∣ P := by simpa using hdvdP
  have hD1s : ([1] : List ℕ).sum = 1 := by simp
  have hD1l : ([1] : List ℕ).length = 1 := by simp
  have hσ : (Nat.digits 10 P).sum = 4 * m := by
    rw [hPσ, hMIDσ, hCσ, hsums, hD1s]
    omega
  refine ⟨P, 0, hP0, fun h => (Nat.lt_irrefl 0 h).elim, hPpal,
    ?_, ?_, ?_⟩
  · rw [hPlen, hMIDlen, hD1l]
    omega
  · simpa using hmP
  · rw [hσ]
    exact ⟨4, by ring⟩




set_option maxHeartbeats 800000 in
theorem cop30_ge7 {m : ℕ} (hm30 : m.Coprime 30) (hm0 : 1 ≤ m)
    (h1 : m ≠ 1) : 7 ≤ m := by
  have h2 : ¬ (2 : ℕ) ∣ m :=
    (Nat.prime_two.coprime_iff_not_dvd).mp
      (hm30.coprime_dvd_right (by norm_num : (2:ℕ) ∣ 30)).symm
  have h3 : ¬ (3 : ℕ) ∣ m :=
    ((by norm_num : Nat.Prime 3).coprime_iff_not_dvd).mp
      (hm30.coprime_dvd_right (by norm_num : (3:ℕ) ∣ 30)).symm
  have h5 : ¬ (5 : ℕ) ∣ m :=
    ((by norm_num : Nat.Prime 5).coprime_iff_not_dvd).mp
      (hm30.coprime_dvd_right (by norm_num : (5:ℕ) ∣ 30)).symm
  by_contra hlt
  push_neg at hlt
  interval_cases m <;>
    first
      | exact absurd rfl h1
      | exact absurd (by decide) h2
      | exact absurd (by decide) h3
      | exact absurd (by decide) h5


set_option maxHeartbeats 800000 in
theorem bnd72 (m : ℕ) : 72 * ((m - 1) / 9 + 1) ≤ 8 * (m - 1) + 72 := by
  have h := Nat.div_add_mod (m - 1) 9
  omega


set_option maxHeartbeats 800000 in
theorem pow5_lin_v0 (b : ℕ) (hb : 1 ≤ b) :
    72 * b + 145 ≤ 224 * 5 ^ (b - 1) := by
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.eq_zero_or_pos b with rfl | hb'
    · norm_num
    · have ih' := ih hb'
      rw [show b + 1 - 1 = b - 1 + 1 from by omega, pow_succ]
      have hx : 1 ≤ 5 ^ (b - 1) := Nat.one_le_pow _ _ (by norm_num)
      omega


set_option maxHeartbeats 800000 in
theorem pow2_lin9 (a : ℕ) (ha : 1 ≤ a) :
    9 * a + 81 ≤ 112 * 2 ^ (a - 1) := by
  induction a with
  | zero => omega
  | succ a ih =>
    rcases Nat.eq_zero_or_pos a with rfl | ha'
    · norm_num
    · have ih' := ih ha'
      rw [show a + 1 - 1 = a - 1 + 1 from by omega, pow_succ]
      have hx : 1 ≤ 2 ^ (a - 1) := Nat.one_le_pow _ _ (by norm_num)
      omega


set_option maxHeartbeats 800000 in
theorem pow5_lin9 (b : ℕ) (hb : 1 ≤ b) :
    9 * b + 72 ≤ 112 * 5 ^ (b - 1) := by
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.eq_zero_or_pos b with rfl | hb'
    · norm_num
    · have ih' := ih hb'
      rw [show b + 1 - 1 = b - 1 + 1 from by omega, pow_succ]
      have hx : 1 ≤ 5 ^ (b - 1) := Nat.one_le_pow _ _ (by norm_num)
      omega


set_option maxHeartbeats 800000 in
theorem pow2_lin_shift2 (n : ℕ) :
    72 * (n + 3) + 145 ≤ 392 * 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    have hx : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
    omega


set_option maxHeartbeats 800000 in
theorem v0o_capacity {b m : ℕ} (hb : 1 ≤ b) (hm7 : 7 ≤ m) :
    72 * b + 72 * ((m - 1) / 9 + 1) + 81 ≤ 8 * (5 ^ b) * m := by
  have hk := bnd72 m
  have hstep := pow5_lin_v0 b hb
  have hx : 1 ≤ 5 ^ (b - 1) := Nat.one_le_pow _ _ (by norm_num)
  have h5 : 5 ^ b = 5 * 5 ^ (b - 1) := by
    conv_lhs => rw [show b = b - 1 + 1 by omega]
    rw [pow_succ']
  rw [h5]
  have h8 : 8 * m ≤ 8 * m * 5 ^ (b - 1) := Nat.le_mul_of_pos_right _ hx
  have h224 : 224 ≤ 32 * m := by
    calc (224 : ℕ) = 32 * 7 := by norm_num
      _ ≤ 32 * m := Nat.mul_le_mul_left _ hm7
  have h32 : 224 * 5 ^ (b - 1) ≤ 32 * m * 5 ^ (b - 1) := by
    calc 224 * 5 ^ (b - 1) ≤ (32 * m) * 5 ^ (b - 1) :=
        Nat.mul_le_mul h224 (le_refl _)
      _ = 32 * m * 5 ^ (b - 1) := by ring
  have hsplit : 8 * (5 * 5 ^ (b - 1)) * m
      = 8 * m * 5 ^ (b - 1) + 32 * m * 5 ^ (b - 1) := by ring
  rw [hsplit]
  omega


set_option maxHeartbeats 800000 in
theorem v0z_capacity {a b m : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hm7 : 7 ≤ m) :
    9 * (a + b + 2) + 72 * ((m - 1) / 9 + 1) + 63
      ≤ 8 * (2 ^ a) * (5 ^ b) * m := by
  have hk := bnd72 m
  have hu : 1 ≤ 2 ^ (a - 1) := Nat.one_le_pow _ _ (by norm_num)
  have hw : 1 ≤ 5 ^ (b - 1) := Nat.one_le_pow _ _ (by norm_num)
  have hpa := pow2_lin9 a ha
  have hpb := pow5_lin9 b hb
  have h2a : 2 ^ a = 2 * 2 ^ (a - 1) := by
    conv_lhs => rw [show a = a - 1 + 1 by omega]
    rw [pow_succ']
  have h5b : 5 ^ b = 5 * 5 ^ (b - 1) := by
    conv_lhs => rw [show b = b - 1 + 1 by omega]
    rw [pow_succ']
  rw [h2a, h5b]
  have hsp : 8 * (2 * 2 ^ (a - 1)) * (5 * 5 ^ (b - 1)) * m
      = 8 * m * (2 ^ (a - 1) * 5 ^ (b - 1))
        + 72 * m * (2 ^ (a - 1) * 5 ^ (b - 1)) := by ring
  rw [hsp]
  have h1 : 8 * m ≤ 8 * m * (2 ^ (a - 1) * 5 ^ (b - 1)) :=
    Nat.le_mul_of_pos_right _ (Nat.mul_pos hu hw)
  have h9 : 9 * a + 9 * b + 145
      ≤ 224 * (2 ^ (a - 1) * 5 ^ (b - 1)) := by
    have e1 : 9 * a + 81 ≤ 112 * (2 ^ (a - 1) * 5 ^ (b - 1)) :=
      le_trans hpa (Nat.mul_le_mul_left _
        (Nat.le_mul_of_pos_right _ hw))
    have e2 : 9 * b + 72 ≤ 112 * (2 ^ (a - 1) * 5 ^ (b - 1)) :=
      le_trans hpb (Nat.mul_le_mul_left _
        (Nat.le_mul_of_pos_left _ hu))
    omega
  have h224m : 224 ≤ 72 * m := by
    calc (224 : ℕ) ≤ 72 * 4 := by norm_num
      _ ≤ 72 * m := Nat.mul_le_mul_left _ (by omega : 4 ≤ m)
  have h2 : 224 * (2 ^ (a - 1) * 5 ^ (b - 1))
      ≤ 72 * m * (2 ^ (a - 1) * 5 ^ (b - 1)) := by
    calc 224 * (2 ^ (a - 1) * 5 ^ (b - 1))
        ≤ (72 * m) * (2 ^ (a - 1) * 5 ^ (b - 1)) :=
        Nat.mul_le_mul h224m (le_refl _)
      _ = 72 * m * (2 ^ (a - 1) * 5 ^ (b - 1)) := by ring
  omega


set_option maxHeartbeats 800000 in
theorem v0e_capacity1 {m : ℕ} (hm29 : 29 ≤ m) :
    72 * 1 + 72 * ((m - 1) / 9 + 1) + 81 ≤ 8 * (2 ^ 1) * m := by
  have hk := bnd72 m
  norm_num
  omega


set_option maxHeartbeats 800000 in
theorem v0e_capacity2 {m : ℕ} (hm13 : 13 ≤ m) :
    72 * 2 + 72 * ((m - 1) / 9 + 1) + 81 ≤ 8 * (2 ^ 2) * m := by
  have hk := bnd72 m
  norm_num
  omega


set_option maxHeartbeats 800000 in
theorem v0e_capacity3 {a m : ℕ} (ha3 : 3 ≤ a) (hm7 : 7 ≤ m) :
    72 * a + 72 * ((m - 1) / 9 + 1) + 81 ≤ 8 * (2 ^ a) * m := by
  have hk := bnd72 m
  have hlin : 72 * a + 145 ≤ 392 * 2 ^ (a - 3) := by
    have h := pow2_lin_shift2 (a - 3)
    rwa [Nat.sub_add_cancel ha3] at h
  have h2a3 : 2 ^ a = 8 * 2 ^ (a - 3) := by
    conv_lhs => rw [show a = a - 3 + 3 by omega]
    rw [pow_add]; ring
  have hx3 : 1 ≤ 2 ^ (a - 3) := Nat.one_le_pow _ _ (by norm_num)
  have ha1 : 1 ≤ 2 ^ a := Nat.one_le_pow _ _ (by norm_num)
  have h2m : 7 * 2 ^ (a - 3) ≤ 2 ^ a - 1 := by rw [h2a3]; omega
  have hsp : 8 * 2 ^ a * m = 8 * m + 8 * m * (2 ^ a - 1) := by
    have hp : 2 ^ a = (2 ^ a - 1) + 1 := by omega
    conv_lhs => rw [hp]
    ring
  have h1 : 392 * 2 ^ (a - 3) ≤ 8 * m * (2 ^ a - 1) := by
    have h56 : 56 * 7 * 2 ^ (a - 3) ≤ 8 * m * (2 ^ a - 1) := by
      calc 56 * 7 * 2 ^ (a - 3) = 8 * 7 * (7 * 2 ^ (a - 3)) := by ring
        _ ≤ 8 * m * (2 ^ a - 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hm7) h2m
    calc 392 * 2 ^ (a - 3) = 56 * 7 * 2 ^ (a - 3) := by ring
      _ ≤ _ := h56
  rw [hsp]
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

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in

set_option maxHeartbeats 800000 in
theorem hres_open_00r1 {n : ℕ} (m : ℕ) (hn : n = m)
    (hm30 : m.Coprime 30) (hm7 : 7 ≤ m) (hmod : m % 9 = 1)
    (hmB : m < 55) : finGoal n := by
  subst n
  interval_cases m <;>
    first
      | exact absurd hm30 (by decide)
      | exact absurd hmod (by decide)
      | exact wit_sound_of rfl

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in

set_option maxHeartbeats 800000 in
theorem hres_open_00r8 {n : ℕ} (m : ℕ) (hn : n = m)
    (hm30 : m.Coprime 30) (hm7 : 7 ≤ m) (hmod : m % 9 ≠ 1)
    (hK : ¬ (13 ≤ (m - 1) / 9 + m % 9)) : finGoal n := by
  subst n
  have hmB : m ≤ 117 := by omega
  interval_cases m <;>
    first
      | exact absurd hm30 (by decide)
      | exact absurd (by decide) hmod
      | exact absurd (by decide) hK
      | exact wit_sound_of rfl

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in

set_option maxHeartbeats 800000 in
theorem hres_open_v0e1 {n : ℕ} (m : ℕ)
    (hn : n = 2 ^ 1 * 5 ^ 0 * 3 ^ 0 * m)
    (hm30 : m.Coprime 30) (hm7 : 7 ≤ m) (hb11 : ¬ (11 : ℕ) ∣ m)
    (hmB : m ≤ 28) : finGoal n := by
  subst hn
  interval_cases m <;>
    first
      | exact absurd hm30 (by decide)
      | exact absurd (by decide) hb11
      | exact wit_sound_of rfl

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in

set_option maxHeartbeats 800000 in
theorem hres_open_v0e2 {n : ℕ} (m : ℕ)
    (hn : n = 2 ^ 2 * 5 ^ 0 * 3 ^ 0 * m)
    (hm30 : m.Coprime 30) (hm7 : 7 ≤ m) (hb11 : ¬ (11 : ℕ) ∣ m)
    (hmB : m ≤ 12) : finGoal n := by
  subst hn
  interval_cases m <;>
    first
      | exact absurd hm30 (by decide)
      | exact absurd (by decide) hb11
      | exact wit_sound_of rfl


set_option maxHeartbeats 800000 in
theorem hres_open {n : ℕ} (a b v m : ℕ)
    (hn : n = 2 ^ a * 5 ^ b * 3 ^ v * m)
    (hm30 : m.Coprime 30) (ho : residualOpen a b v m)
    (hhard : ∀ a b v m : ℕ, m.Coprime 30 →
      residualHard a b v m → finGoal (2 ^ a * 5 ^ b * 3 ^ v * m)) :
    relaxedGoal n := by
  have hm0 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0] at hm30
      exact absurd hm30 (by decide)
    · exact h0
  subst hn
  rcases ho with hv0 | hR2
  · subst hv0
    by_cases hm1 : m = 1
    · subst hm1
      simpa only [pow_zero, mul_one, one_mul] using assemble_v0_m1 a b
    · have hm7 : 7 ≤ m := cop30_ge7 hm30 hm0 hm1
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · rcases Nat.eq_zero_or_pos b with rfl | hb
        · 
          by_cases hmod : m % 9 = 1
          · by_cases h55 : 55 ≤ m
            · simpa only [pow_zero, mul_one, one_mul] using
                assemble_v000 hm0 hm30 hmod h55
            · exact relaxed_of_finGoal
                (hres_open_00r1 m (by simp) hm30 hm7 hmod (by omega))
          · by_cases hK : 13 ≤ (m - 1) / 9 + m % 9
            · simpa only [pow_zero, mul_one, one_mul] using
                assemble_v000_ne1 hm0 hm30 hmod hK
            · exact relaxed_of_finGoal
                (hres_open_00r8 m (by simp) hm30 hm7 hmod hK)
        · 
          simpa only [pow_zero, mul_one, one_mul] using
            assemble_v0o hb hm0 hm30 (v0o_capacity hb hm7)
      · rcases Nat.eq_zero_or_pos b with rfl | hb
        · 
          by_cases hbad : 11 ∣ m ∨ 101 ∣ m
          · exact relaxed_of_finGoal
              (hhard a 0 0 m hm30 ⟨ha, rfl, hbad⟩)
          · push_neg at hbad
            have hm11 : m.Coprime 11 :=
              (((by norm_num : Nat.Prime 11).coprime_iff_not_dvd).mpr
                hbad.1).symm
            have hm101 : m.Coprime 101 :=
              (((by norm_num : Nat.Prime 101).coprime_iff_not_dvd).mpr
                hbad.2).symm
            by_cases ha3 : 3 ≤ a
            · simpa only [pow_zero, mul_one, one_mul] using
                assemble_v0e ha hm0 hm30 hm11 hm101
                (v0e_capacity3 ha3 hm7)
            · have ha2 : a ≤ 2 := by omega
              interval_cases a
              · by_cases hm29 : 29 ≤ m
                · simpa only [pow_zero, mul_one, one_mul] using
                    assemble_v0e (a := 1) (by norm_num)
                    hm0 hm30 hm11 hm101 (v0e_capacity1 hm29)
                · exact relaxed_of_finGoal
                    (hres_open_v0e1 m (by simp) hm30 hm7 hbad.1
                      (by omega))
              · by_cases hm13 : 13 ≤ m
                · simpa only [pow_zero, mul_one, one_mul] using
                    assemble_v0e (a := 2) (by norm_num)
                    hm0 hm30 hm11 hm101 (v0e_capacity2 hm13)
                · exact relaxed_of_finGoal
                    (hres_open_v0e2 m rfl hm30 hm7 hbad.1 (by omega))
        · 
          simpa only [pow_zero, mul_one, one_mul] using
            assemble_v0z ha hb hm0 hm30
            (v0z_capacity ha hb hm7)
  · obtain ⟨ha, hb0, hbad⟩ := hR2
    subst hb0
    exact relaxed_of_finGoal
      (hhard a 0 v m hm30 ⟨ha, rfl, hbad⟩)


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

theorem OMA.solution : OMA.R_oeis_a084017_R1_H1_R1.H2 := by
  intro h1 n a b v m hnd hm30 ho
  exact OMA.A084017Port.A084017.hres_open a b v m hnd hm30 ho h1
