-- split of proofs/oeis-a084017.lean (1 068 065 B > 512 KiB lint) via the reductions mechanism
import OMAReductions.R_oeis_a084017_R1
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


theorem pal_mod81 : ∀ (A : List ℕ) (c : ℕ),
    Nat.ofDigits (10 : ZMod 81) (A ++ [c] ++ A.reverse)
      = (1 + 9 * ((A.length : ℕ) : ZMod 81))
          * (2 * ((A.sum : ℕ) : ZMod 81) + (c : ZMod 81)) := by
  intro A; induction A with
  | nil => intro c; simp [Nat.ofDigits]
  | cons a A' ih =>
    intro c
    have h1 : (a :: A') ++ [c] ++ (a :: A').reverse
        = a :: ((A' ++ [c] ++ A'.reverse) ++ [a]) := by
      simp [List.reverse_cons]
    rw [h1]
    rw [show a :: ((A' ++ [c] ++ A'.reverse) ++ [a])
        = [a] ++ ((A' ++ [c] ++ A'.reverse) ++ [a]) from rfl]
    rw [ofDigits_append', ofDigits_singleton', List.length_singleton,
      pow_one,
      show (A' ++ [c] ++ A'.reverse) ++ [a]
        = A' ++ [c] ++ A'.reverse ++ [a] from rfl,
      ofDigits_append', ofDigits_singleton', ih]
    have hlen : ((A' ++ [c] ++ A'.reverse).length : ℕ)
        = 2 * A'.length + 1 := by
      simp [List.length_append]; omega
    rw [hlen]
    have hpow : (10 : ZMod 81) ^ (2 * A'.length + 2)
        = 1 + 9 * ((2 * A'.length + 2 : ℕ) : ZMod 81) := by
      rw [ten_pow_mod81]
      congr 1
      exact nine_mul_cast_mod9 _
    have h2 : (10 : ZMod 81) ^ (2 * A'.length + 2)
        = 10 * 10 ^ (2 * A'.length + 1) := pow_succ' _ _
    have hpow2 :
        (10 : ZMod 81) * (10 ^ (2 * A'.length + 1) * (a : ZMod 81))
          = 10 ^ (2 * A'.length + 2) * (a : ZMod 81) := by
      rw [← mul_assoc, ← h2]
    rw [mul_add, hpow2, hpow, List.sum_cons, List.length_cons]
    push_cast
    have h81 : (81 : ZMod 81) = 0 := by decide
    linear_combination
      (2 * ((A'.length : ℕ) : ZMod 81)
          * (List.map Nat.cast A').sum
        + ((A'.length : ℕ) : ZMod 81) * ((c : ℕ) : ZMod 81))
        * h81


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


theorem dvd3_pow_of_sigma_odd (A : List ℕ) (c : ℕ) {v : ℕ}
    (hv : v ≤ 4) (hσ : 3 ^ v ∣ 2 * A.sum + c) :
    3 ^ v ∣ Nat.ofDigits 10 (A ++ [c] ++ A.reverse) := by
  haveI : NeZero (3 ^ v) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hdiv : 3 ^ v ∣ 81 :=
    ⟨3 ^ (4 - v), by
      rw [← pow_add, show v + (4 - v) = 4 by omega]; norm_num⟩
  have hmod : Nat.ofDigits 10 (A ++ [c] ++ A.reverse)
      ≡ (2 * A.sum + c) * (1 + 9 * A.length) [MOD 81] := by
    have h := pal_mod81 A c
    rw [← ofDigits_cast] at h
    rw [mul_comm] at h
    have hcast : ((1 + 9 * A.length : ℕ) : ZMod 81)
        = 1 + 9 * (A.length : ZMod 81) := by push_cast; ring
    rw [← hcast] at h
    have hcast2 : ((2 * A.sum + c : ℕ) : ZMod 81)
        = 2 * ((A.sum : ℕ) : ZMod 81) + (c : ZMod 81) := by
      push_cast; ring
    rw [← hcast2, ← Nat.cast_mul] at h
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h
  have hmodv : Nat.ofDigits 10 (A ++ [c] ++ A.reverse)
      ≡ (2 * A.sum + c) * (1 + 9 * A.length) [MOD 3 ^ v] :=
    Nat.ModEq.of_dvd hdiv hmod
  have hS0 : (2 * A.sum + c) * (1 + 9 * A.length) ≡ 0 [MOD 3 ^ v] :=
    Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left hσ _)
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
end A084017
namespace A084017
open Finset List Nat BigOperators Pointwise

end A084017



namespace A084017


set_option maxHeartbeats 800000 in
def tz (x : ℕ) : ℕ := ((Nat.digits 10 x).takeWhile (· = 0)).length


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
theorem not10_5b3vm {b v m : ℕ} (hm30 : m.Coprime 30) :
    ¬ 10 ∣ 5 ^ b * 3 ^ v * m := by
  intro h
  have h2 : 2 ∣ 5 ^ b * 3 ^ v * m :=
    dvd_trans (by norm_num : (2 : ℕ) ∣ 10) h
  rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 2)).mp h2
      with h25 | h2m
  · rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 2)).mp h25
        with h25b | h23
    · exact absurd (Nat.Prime.dvd_of_dvd_pow
        (by norm_num : Nat.Prime 2) h25b) (by decide)
    · exact absurd (Nat.Prime.dvd_of_dvd_pow
        (by norm_num : Nat.Prime 2) h23) (by decide)
  · have hcop : m.Coprime 2 :=
      hm30.coprime_dvd_right (by norm_num : (2 : ℕ) ∣ 30)
    have hg : (2 : ℕ) ∣ Nat.gcd m 2 := Nat.dvd_gcd h2m (dvd_refl 2)
    rw [hcop] at hg
    exact absurd hg (by decide)





















set_option maxHeartbeats 800000 in
theorem digits_sum_le (N : ℕ) :
    (Nat.digits 10 N).sum ≤ 9 * (Nat.digits 10 N).length := by
  have h : ∀ x ∈ Nat.digits 10 N, x ≤ 9 := fun x hx =>
    Nat.lt_succ_iff.mp (Nat.digits_lt_base (by norm_num) hx)
  have hs := List.sum_le_card_nsmul (Nat.digits 10 N) 9 h
  rwa [nsmul_eq_mul, Nat.mul_comm] at hs

set_option maxHeartbeats 800000 in
theorem five_not_dvd_pow2 (a : ℕ) : ¬ (5:ℕ) ∣ 2 ^ a := by
  have hc : Nat.Coprime 5 2 := by norm_num
  have hc2 := hc.pow_right a
  exact (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 5)).mp hc2

variable {m : ℕ} [NeZero m]
variable {M : ℕ} [NeZero M]






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


end A084017

end A084017R2src

section SpecA084017src




abbrev SpecPropA084017N (n : ℕ) : Prop :=
  ∃ P z : ℕ, P ≠ 0
    ∧ z = ((Nat.digits 10 n).takeWhile (· = 0)).length
    ∧ (Nat.digits 10 P).Palindrome
    ∧ (Nat.digits 10 P).length + z = n
    ∧ n ∣ P * 10 ^ z
    ∧ n ∣ (Nat.digits 10 P).sum

end SpecA084017src

section PinnedTensrc





namespace PinnedTen
open Finset List Nat BigOperators Pointwise
open A084017






theorem ofDigits_takeWhile_zero (b : ℕ) (l : List ℕ) :
    Nat.ofDigits b (l.takeWhile (· = 0)) = 0 := by
  induction l with
  | nil => simp [Nat.ofDigits]
  | cons d t ih =>
    rw [List.takeWhile_cons]
    by_cases hd : d = 0
    · simp [hd, Nat.ofDigits_cons, ih]
    · simp [hd, Nat.ofDigits]


theorem takeWhile_replicate_zero (k : ℕ) (l : List ℕ) :
    ((List.replicate k 0) ++ l).takeWhile (· = 0)
      = List.replicate k 0 ++ l.takeWhile (· = 0) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp [List.replicate_succ, List.cons_append, List.takeWhile_cons, ih]


theorem pow10_le_tz {n k : ℕ} (hn : n ≠ 0) (h : 10 ^ k ∣ n) :
    k ≤ tz n := by
  rcases k with _ | k
  · exact Nat.zero_le _
  obtain ⟨c, hc⟩ := h
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with e | hp
    · rw [e, mul_zero] at hc
      exact absurd hc hn
    · exact hp
  have hd : Nat.digits 10 n
      = List.replicate (k + 1) 0 ++ Nat.digits 10 c := by
    rw [hc, Nat.digits_base_pow_mul (b := 10) (k := k + 1) (m := c)
      (by norm_num) hc0]
  show k + 1 ≤ ((Nat.digits 10 n).takeWhile (· = 0)).length
  rw [hd, takeWhile_replicate_zero, List.length_append,
    List.length_replicate]
  omega


theorem pow10_dvd_of_tz {n : ℕ} : 10 ^ tz n ∣ n := by
  refine ⟨Nat.ofDigits 10 ((Nat.digits 10 n).dropWhile (· = 0)), ?_⟩
  calc n = Nat.ofDigits 10 (Nat.digits 10 n) :=
        (Nat.ofDigits_digits 10 n).symm
    _ = Nat.ofDigits 10 ((Nat.digits 10 n).takeWhile (· = 0)
          ++ (Nat.digits 10 n).dropWhile (· = 0)) := by
        rw [List.takeWhile_append_dropWhile]
    _ = Nat.ofDigits 10 ((Nat.digits 10 n).takeWhile (· = 0))
          + 10 ^ ((Nat.digits 10 n).takeWhile (· = 0)).length
            * Nat.ofDigits 10 ((Nat.digits 10 n).dropWhile (· = 0)) :=
        ofDigits_append' _ _ _
    _ = 10 ^ tz n
          * Nat.ofDigits 10 ((Nat.digits 10 n).dropWhile (· = 0)) := by
        rw [ofDigits_takeWhile_zero, zero_add]
        rfl







theorem P_dvd_3m81_pinned {m v le K g : ℕ} [NeZero m]
    (hm3 : m.Coprime 3) (hm10 : m.Coprime 10)
    (de : List ℕ) (hle : de.length = le)
    (C : List ℕ) (hC : C.length = g)
    (hP0_11 : ∀ h : 11 ∣ m, (ZMod.castHom h (ZMod 11))
      ((Nat.ofDigits (10 : ZMod m) de
          + Nat.ofDigits (10 : ZMod m) de.reverse
              * (10 : ZMod m) ^ (le + (4 * K + g)))
        + (10 : ZMod m) ^ le
          * (Nat.ofDigits (10 : ZMod m) C * (10 : ZMod m) ^ (2 * K)
            + 9 * ∑ k ∈ Finset.range K, palW m (4 * K + g) (2 * k + 1)))
        = 0)
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
      rw [hE, hX]
      exact hP0_11 h
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
    have htz' : ((10 : ZMod m) ^ le * 81) * t
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
    rw [htz']
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






theorem hs0_lhs {v le K g : ℕ} (de C : List ℕ)
    (hle : de.length = le) (hCg : C.length = g) (s₀ : ℕ) :
    (Nat.ofDigits (10 : ZMod (3 ^ v)) de
      + Nat.ofDigits (10 : ZMod (3 ^ v)) de.reverse
          * (10 : ZMod (3 ^ v)) ^ (le + (4 * K + g)))
    + (10 : ZMod (3 ^ v)) ^ le
      * (Nat.ofDigits (10 : ZMod (3 ^ v)) C
          * (10 : ZMod (3 ^ v)) ^ (2 * K)
        + (9 * ∑ k ∈ Finset.range K, palW (3 ^ v) (4 * K + g) (2 * k + 1)
          + 81 * (s₀ : ZMod (3 ^ v))))
    = ((Nat.ofDigits 10
        (de ++ (((List.range (2 * K)).map (pairDigit (fun _ => 0)) ++ C)
          ++ ((List.range (2 * K)).map (pairDigit (fun _ => 0))).reverse)
          ++ de.reverse) : ℕ) : ZMod (3 ^ v))
        + (10 : ZMod (3 ^ v)) ^ le * 81 * (s₀ : ZMod (3 ^ v)) := by
  rw [cast_ofDigits,
      gadget_val_m (m := 3 ^ v) de hle (fun _ => 0)
        (fun _ => Nat.zero_le 9) C hCg]
  simp only [Nat.cast_zero, zero_mul, add_zero]
  rw [← Finset.mul_sum]
  push_cast
  ring


theorem hs0_of_dvd3 {v le K g : ℕ} (de C : List ℕ)
    (hle : de.length = le) (hCg : C.length = g)
    (hP0 : 3 ^ v ∣ Nat.ofDigits 10
      (de ++ (((List.range (2 * K)).map (pairDigit (fun _ => 0)) ++ C)
        ++ ((List.range (2 * K)).map (pairDigit (fun _ => 0))).reverse)
        ++ de.reverse)) :
    (Nat.ofDigits (10 : ZMod (3 ^ v)) de
      + Nat.ofDigits (10 : ZMod (3 ^ v)) de.reverse
          * (10 : ZMod (3 ^ v)) ^ (le + (4 * K + g)))
    + (10 : ZMod (3 ^ v)) ^ le
      * (Nat.ofDigits (10 : ZMod (3 ^ v)) C
          * (10 : ZMod (3 ^ v)) ^ (2 * K)
        + (9 * ∑ k ∈ Finset.range K, palW (3 ^ v) (4 * K + g) (2 * k + 1)
          + 81 * ((0 : ℕ) : ZMod (3 ^ v)))) = 0 := by
  rw [hs0_lhs de C hle hCg 0]
  rw [Nat.cast_zero, mul_zero, add_zero]
  rw [CharP.cast_eq_zero_iff (ZMod (3 ^ v)) (3 ^ v) _]
  exact hP0


theorem hs0_of_dvd81 {v le K g : ℕ} (hv : 5 ≤ v) (de C : List ℕ)
    (hle : de.length = le) (hCg : C.length = g)
    (hP0 : 81 ∣ Nat.ofDigits 10
      (de ++ (((List.range (2 * K)).map (pairDigit (fun _ => 0)) ++ C)
        ++ ((List.range (2 * K)).map (pairDigit (fun _ => 0))).reverse)
        ++ de.reverse)) :
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
  set P0 := Nat.ofDigits 10
    (de ++ (((List.range (2 * K)).map (pairDigit (fun _ => 0)) ++ C)
      ++ ((List.range (2 * K)).map (pairDigit (fun _ => 0))).reverse)
      ++ de.reverse) with hP0def
  set Q := P0 / 81 with hQ
  have h81Q : 81 * Q = P0 := Nat.mul_div_cancel' hP0
  set s₀ : ℕ := (-(Q : ZMod (3 ^ (v - 4)))
      * ((10 : ZMod (3 ^ (v - 4))) ^ le)⁻¹).val with hs₀
  refine ⟨s₀, ?_⟩
  have hsc : (s₀ : ZMod (3 ^ (v - 4)))
      = -(Q : ZMod (3 ^ (v - 4)))
          * ((10 : ZMod (3 ^ (v - 4))) ^ le)⁻¹ := by
    rw [hs₀, ZMod.natCast_val, ZMod.cast_id]
  have hunit : IsUnit ((10 : ZMod (3 ^ (v - 4))) ^ le) := by
    apply IsUnit.pow
    apply (ZMod.isUnit_iff_coprime 10 (3 ^ (v - 4))).mpr
    exact (by decide : Nat.Coprime 10 3).pow_right _
  have h1 : (10 : ZMod (3 ^ (v - 4))) ^ le
      * ((10 : ZMod (3 ^ (v - 4))) ^ le)⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ hunit
  have hkey : ((Q + 10 ^ le * s₀ : ℕ) : ZMod (3 ^ (v - 4))) = 0 := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, hsc]
    push_cast
    have e : (10 : ZMod (3 ^ (v - 4))) ^ le
        * (-(Q : ZMod (3 ^ (v - 4)))
            * ((10 : ZMod (3 ^ (v - 4))) ^ le)⁻¹)
        = -((Q : ZMod (3 ^ (v - 4)))
          * ((10 : ZMod (3 ^ (v - 4))) ^ le
            * ((10 : ZMod (3 ^ (v - 4))) ^ le)⁻¹)) := by ring
    rw [e, h1, mul_one]
    exact add_neg_cancel _
  have hdvd : 3 ^ (v - 4) ∣ Q + 10 ^ le * s₀ :=
    (CharP.cast_eq_zero_iff (ZMod (3 ^ (v - 4))) (3 ^ (v - 4)) _).mp hkey
  have h3v : 3 ^ v ∣ 81 * (Q + 10 ^ le * s₀) := by
    have hvd : 81 * 3 ^ (v - 4) = 3 ^ v := by
      rw [show (81:ℕ) = 3 ^ 4 from by norm_num, ← pow_add]
      congr 1
      omega
    rw [← hvd]
    exact Nat.mul_dvd_mul_left _ hdvd
  rw [hs0_lhs de C hle hCg s₀]
  rw [← hP0def, ← h81Q]
  have hgoal : ((81 * Q : ℕ) : ZMod (3 ^ v))
      + (10 : ZMod (3 ^ v)) ^ le * 81 * (s₀ : ZMod (3 ^ v))
      = ((81 * (Q + 10 ^ le * s₀) : ℕ) : ZMod (3 ^ v)) := by
    push_cast
    ring
  rw [hgoal, CharP.cast_eq_zero_iff (ZMod (3 ^ v)) (3 ^ v) _]
  exact h3v







theorem dvd3_pow_sandwich_even {v : ℕ} (hv : v ≤ 4) (de G F : List ℕ)
    (hσ : 3 ^ v ∣ 2 * (de ++ G ++ F).sum) :
    3 ^ v ∣ Nat.ofDigits 10
      (de ++ ((G ++ (F ++ F.reverse)) ++ G.reverse) ++ de.reverse) := by
  have hsplit : de ++ ((G ++ (F ++ F.reverse)) ++ G.reverse) ++ de.reverse
      = (de ++ G ++ F) ++ (de ++ G ++ F).reverse := by
    simp [List.append_assoc, List.reverse_append]
  rw [hsplit]
  exact dvd3_pow_of_sigma_even _ hv hσ


theorem dvd3_pow_sandwich_odd {v : ℕ} (hv : v ≤ 4) (de G F : List ℕ)
    (hσ : 3 ^ v ∣ 2 * (de ++ G ++ F).sum) :
    3 ^ v ∣ Nat.ofDigits 10
      (de ++ ((G ++ (F ++ [0] ++ F.reverse)) ++ G.reverse)
        ++ de.reverse) := by
  have hsplit : de ++ ((G ++ (F ++ [0] ++ F.reverse)) ++ G.reverse)
        ++ de.reverse
      = (de ++ G ++ F) ++ [0] ++ (de ++ G ++ F).reverse := by
    simp [List.append_assoc, List.reverse_append]
  rw [hsplit]
  exact dvd3_pow_of_sigma_odd _ 0 hv (by simpa using hσ)


theorem succ_le_pow2 (k : ℕ) : k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ]
    omega


theorem z_le_pow10_pred {z : ℕ} (hz : 1 ≤ z) : z ≤ 10 ^ (z - 1) := by
  have h2 : z ≤ 2 ^ (z - 1) := by
    have h := succ_le_pow2 (z - 1)
    rwa [Nat.sub_add_cancel hz] at h
  exact h2.trans (Nat.pow_le_pow_left (by norm_num : (2:ℕ) ≤ 10) _)


theorem two_sigma_le_nine (e : ℕ) :
    2 * (Nat.digits 10 e).sum ≤ 9 * e := by
  rcases Nat.eq_zero_or_pos e with he | he
  · rw [he]; simp
  have hlen9 : (Nat.digits 10 e).sum ≤ 9 * (Nat.digits 10 e).length :=
    digits_sum_le e
  rcases Nat.lt_or_ge (Nat.digits 10 e).length 2 with hl1 | hl2
  · have hle1 : (Nat.digits 10 e).length = 1 := by
      have h0 : (Nat.digits 10 e).length ≠ 0 := by
        intro h0
        have hdn := (Nat.digits_ne_nil_iff_ne_zero (b := 10)).mpr
          (show e ≠ 0 by omega)
        exact hdn (List.length_eq_zero_iff.mp h0)
      omega
    have hlt10 : e < 10 :=
      (Nat.digits_length_le_iff (b := 10) (k := 1) (by norm_num) e).mp
        (by rw [hle1])
    have hsum : (Nat.digits 10 e).sum = e := by
      have hd : Nat.digits 10 e = [e % 10] := by
        have hcons := Nat.digits_eq_cons_digits_div (b := 10)
          (by norm_num) (show e ≠ 0 by omega)
        have hd10 : e / 10 = 0 := Nat.div_eq_of_lt hlt10
        rw [hcons, hd10, Nat.digits_zero]
      rw [hd, List.sum_singleton, Nat.mod_eq_of_lt hlt10]
    rw [hsum]
    omega
  · have hpos : 0 < (Nat.digits 10 e).length := by
      have hdn := (Nat.digits_ne_nil_iff_ne_zero (b := 10)).mpr
        (show e ≠ 0 by omega)
      exact Nat.pos_of_ne_zero (fun h0 => hdn (List.length_eq_zero_iff.mp h0))
    have h10le : 10 ^ ((Nat.digits 10 e).length - 1) ≤ e := by
      exact (Nat.lt_digits_length_iff (b := 10) (n := e) (by norm_num)).mp
        (by omega)
    have h2len : 2 * (Nat.digits 10 e).length
        ≤ 10 ^ ((Nat.digits 10 e).length - 1) := by
      obtain ⟨k, hk⟩ : ∃ k, (Nat.digits 10 e).length = k + 2 :=
        ⟨(Nat.digits 10 e).length - 2, by omega⟩
      rw [hk]
      have hkk : k + 1 ≤ 10 ^ k := by
        calc k + 1 ≤ 2 ^ k := succ_le_pow2 k
          _ ≤ 10 ^ k := Nat.pow_le_pow_left (by norm_num : (2:ℕ) ≤ 10) k
      have h1 : 10 ^ (k + 2 - 1) = 10 * 10 ^ k := by
        rw [show k + 2 - 1 = k + 1 from by omega, pow_succ, mul_comm]
      rw [h1]
      have h10k : 1 ≤ 10 ^ k := pow_pos (by norm_num : (0:ℕ) < 10) k
      omega
    calc 2 * (Nat.digits 10 e).sum
        ≤ 2 * (9 * (Nat.digits 10 e).length) := Nat.mul_le_mul_left _ hlen9
      _ = 9 * (2 * (Nat.digits 10 e).length) := by ring
      _ ≤ 9 * 10 ^ ((Nat.digits 10 e).length - 1) :=
        Nat.mul_le_mul_left _ h2len
      _ ≤ 9 * e := Nat.mul_le_mul_left _ h10le






theorem finGoal_assemble_sandwich {n z a b a' b' v m e K g Lw L B R Sf : ℕ}
    {de C : List ℕ} {e' : ℕ → ℕ}
    (hnd : n = 2 ^ a * 5 ^ b * 3 ^ v * m)
    (hm30 : m.Coprime 30)
    (htz : z = tz n)
    (hzlen : z ≤ n)
    (he : e = 2 ^ a' * 5 ^ b')
    (hza : a = z + a') (hzb : b = z + b')
    (hLw_eq : Lw = 4 * K + g)
    (hL_eq : L = 2 * B + Lw)
    (hL : L = n - z)
    (hSf : Sf = 2 * (Nat.digits 10 e).sum + 18 * K)
    (hSfn : Sf ≤ n)
    (h2R : 2 * R = n - Sf)
    (hde_len : de.length = B)
    (hde_val : Nat.ofDigits 10 de = e)
    (hde_lt10 : ∀ x ∈ de, x < 10)
    (hde_ne : de ≠ [])
    (hde_head : ∀ h : de ≠ [], de.head h ≠ 0)
    (hde_sum : de.sum = (Nat.digits 10 e).sum)
    (hmaxB : max a' b' ≤ B)
    (hCg : C.length = g)
    (hCpal : C.Palindrome)
    (hC10 : ∀ x ∈ C, x < 10)
    (hCsum : C.sum = 2 * R)
    (he' : ∀ k, e' k ≤ 9)
    (hdvdP : m * 3 ^ v ∣ Nat.ofDigits 10
        (de ++ (((List.range (2 * K)).map (pairDigit e') ++ C)
          ++ ((List.range (2 * K)).map (pairDigit e')).reverse)
          ++ de.reverse)) :
    SpecPropA084017N n := by
  set G := (List.range (2 * K)).map (pairDigit e') with hG
  set MID := G ++ C ++ G.reverse with hMID
  set P := Nat.ofDigits 10 (de ++ MID ++ de.reverse) with hP
  have hMIDpal : MID.Palindrome := mid_pal e' C hCpal
  have hMIDlt : ∀ x ∈ MID, x < 10 := mid_lt10 e' he' C hC10
  have hMIDsum : MID.sum = 18 * K + C.sum := mid_sum e' he' C
  have hMIDlen : MID.length = 4 * K + g := by
    rw [hMID, List.length_append, List.length_append, hCg,
      List.length_reverse, hG, List.length_map, List.length_range]
    ring
  have hdvdP' : m * 3 ^ v ∣ Nat.ofDigits 10 (de ++ MID ++ de.reverse) := by
    have hl : de ++ MID ++ de.reverse
        = de ++ (((List.range (2 * K)).map (pairDigit e') ++ C)
            ++ ((List.range (2 * K)).map (pairDigit e')).reverse)
            ++ de.reverse := by
      simp only [hMID, hG, List.append_assoc]
    rw [hl]
    exact hdvdP
  obtain ⟨hP0, hPpal, hPlen, hPσ⟩ :=
    sandwich_spec_gen de MID hde_ne hde_lt10 (hde_head hde_ne) hMIDpal
      hMIDlt rfl rfl
  have hBe : 2 ^ a' * 5 ^ b' ∣ P := by
    rw [hP]
    apply B_dvd_P hde_len _ hmaxB
    rw [hde_val, he]
  have hqm : 3 ^ v * m ∣ P := by
    obtain ⟨w, hw⟩ := hdvdP'
    exact ⟨w, by rw [hP, hw]; ring⟩
  have hdvd : n ∣ P * 10 ^ z := by
    have h := n_dvd_P_pow10_le hBe hqm
      (by omega : a ≤ a' + z) (by omega : b ≤ b' + z) hm30
    rw [hnd]
    exact h
  refine ⟨P, z, hP0, htz, hPpal, ?_, hdvd, ?_⟩
  · rw [hPlen, hde_len, hMIDlen]
    have e1 : 2 * B + (4 * K + g) = L := by
      rw [← hLw_eq, ← hL_eq]
    have e2 : L + z = n := by
      rw [hL]
      exact Nat.sub_add_cancel hzlen
    omega
  · rw [hPσ, hde_sum, hMIDsum, hCsum]
    have ee : 2 * (Nat.digits 10 e).sum + (18 * K + 2 * R) = n := by
      have h1 : Sf + 2 * R = n := by
        rw [h2R]
        exact Nat.add_sub_cancel' hSfn
      rw [hSf] at h1
      omega
    rw [ee]





theorem pinned_A084017_ten (n : ℕ) (hn : n ≠ 0) (h10 : 10 ∣ n) :
    SpecPropA084017N n := by
  classical
  
  obtain ⟨a, b, v, m, hnd, hm30, h2m, h5m, h3m⟩ := decomp235 n hn
  have ha1 : 1 ≤ a := by
    by_contra hlt
    push_neg at hlt
    have ha0 : a = 0 := by omega
    have e : n = 5 ^ b * 3 ^ v * m := by
      rw [hnd, ha0, pow_zero, one_mul]
    exact not10_5b3vm hm30 (e ▸ h10)
  have hb1 : 1 ≤ b := by
    by_contra hlt
    push_neg at hlt
    have hb0 : b = 0 := by omega
    have e : n = 2 ^ a * 3 ^ v * m := by
      rw [hnd, hb0, pow_zero, mul_one]
    exact not10_2a3vm hm30 (e ▸ h10)
  set z := min a b with hz_def
  have hz1 : 1 ≤ z := by rw [hz_def]; omega
  set a' := a - z with ha'
  set b' := b - z with hb'
  have hza : a = z + a' := by omega
  have hzb : b = z + b' := by omega
  have hmin0 : a' = 0 ∨ b' = 0 := by
    rcases Nat.lt_or_ge a b with hba | hab
    · left
      have hz' : z = a := min_eq_left (le_of_lt hba)
      omega
    · right
      have hz' : z = b := min_eq_right hab
      omega
  set n' := 2 ^ a' * 5 ^ b' * 3 ^ v * m with hn'_def
  have hnn' : n = n' * 10 ^ z := by
    rw [hn'_def, hnd, hza, hzb]
    rw [pow_add, pow_add]
    have e10 : (10:ℕ) ^ z = 2 ^ z * 5 ^ z := by
      rw [show (10:ℕ) = 2 * 5 from by norm_num, mul_pow]
    rw [e10]; ring
  have hn'10 : ¬ 10 ∣ n' := by
    rcases hmin0 with ha0 | hb0
    · have e : n' = 5 ^ b' * 3 ^ v * m := by
        rw [hn'_def, ha0, pow_zero, one_mul]
      rw [e]; exact not10_5b3vm hm30
    · have e : n' = 2 ^ a' * 3 ^ v * m := by
        rw [hn'_def, hb0, pow_zero, mul_one]
      rw [e]; exact not10_2a3vm hm30
  have hn'pos : 1 ≤ n' := Nat.pos_iff_ne_zero.mpr (by
    intro e0
    rw [e0, zero_mul] at hnn'
    exact hn hnn')
  
  have h10z : 10 ^ z ∣ n := ⟨n', by rw [hnn']; ring⟩
  have htz : z = tz n := by
    apply le_antisymm (pow10_le_tz hn h10z)
    by_contra hgt
    push_neg at hgt
    have h10z' : 10 ^ (z + 1) ∣ n :=
      (pow_dvd_pow 10 (by omega : z + 1 ≤ tz n)).trans pow10_dvd_of_tz
    rw [hnn'] at h10z'
    have h10n' : 10 ∣ n' := by
      have e : (10:ℕ) ^ (z + 1) = 10 ^ z * 10 := by ring
      rw [e, mul_comm n' (10 ^ z)] at h10z'
      exact (Nat.mul_dvd_mul_iff_left (pow_pos (by norm_num) z)).mp h10z'
    exact hn'10 h10n'
  
  set e := 2 ^ a' * 5 ^ b' with he_def
  set q := 3 ^ v * m with hq_def
  have hn'eq : n' = e * q := by rw [hn'_def, hq_def]; ring
  have hm1 : 1 ≤ m := Nat.pos_iff_ne_zero.mpr (by
    intro hm0
    subst hm0
    exact absurd hm30 (by decide))
  have he0 : 1 ≤ e := Nat.pos_iff_ne_zero.mpr (by
    rw [he_def]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (pow_ne_zero _ (by norm_num)))
  have hq0 : 1 ≤ q := Nat.pos_iff_ne_zero.mpr (by
    rw [hq_def]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by omega))
  have hm2 : m.Coprime 2 := hm30.coprime_dvd_right (by norm_num)
  have hm5 : m.Coprime 5 := hm30.coprime_dvd_right (by norm_num)
  have hm3 : m.Coprime 3 := hm30.coprime_dvd_right (by norm_num)
  have hm10 : m.Coprime 10 := hm30.coprime_dvd_right (by norm_num)
  haveI : NeZero m := ⟨by omega⟩
  have he10 : e % 10 ≠ 0 := by
    intro hmod
    have h10e : (10:ℕ) ∣ e := Nat.dvd_of_mod_eq_zero hmod
    rcases hmin0 with ha0 | hb0
    · have h2 : (2:ℕ) ∣ e := (by norm_num : (2:ℕ) ∣ 10).trans h10e
      have e5 : e = 5 ^ b' := by
        rw [he_def, ha0, pow_zero, one_mul]
      rw [e5] at h2
      exact absurd (Nat.Prime.dvd_of_dvd_pow
        (by norm_num : Nat.Prime 2) h2) (by decide)
    · have h5 : (5:ℕ) ∣ e := (by norm_num : (5:ℕ) ∣ 10).trans h10e
      have e2 : e = 2 ^ a' := by
        rw [he_def, hb0, pow_zero, mul_one]
      rw [e2] at h5
      exact (five_not_dvd_pow2 _) h5
  
  set L := n - z with hL_def
  have h10ge : 10 ≤ 10 ^ z := by
    calc (10:ℕ) = 10 ^ 1 := (pow_one 10).symm
      _ ≤ 10 ^ z := Nat.pow_le_pow_right (by norm_num) hz1
  have hzlen : z ≤ n := by
    calc z ≤ 10 ^ z :=
        le_trans (z_le_pow10_pred hz1)
          (Nat.pow_le_pow_right (by norm_num) (by omega))
      _ ≤ 10 ^ z * n' := Nat.le_mul_of_pos_right _ hn'pos
      _ = n' * 10 ^ z := by ring
      _ = n := hnn'.symm
  set B0 := max 1 (max a' b') with hB0
  set B := if Even L then (if (L - 2 * B0) % 4 = 0 then B0 else B0 + 1)
      else B0 with hB
  have hBB0 : B0 ≤ B := by
    rw [hB]; split_ifs <;> omega
  have hBB1 : B ≤ B0 + 1 := by
    rw [hB]; split_ifs <;> omega
  have hB1 : 1 ≤ B := le_trans (by rw [hB0]; exact le_max_left _ _) hBB0
  have hlen_e : (Nat.digits 10 e).length ≤ B := by
    rcases hmin0 with ha0 | hb0
    · rcases Nat.eq_zero_or_pos b' with hb0' | hb1'
      · have e1 : e = 1 := by
          rw [he_def, ha0, pow_zero, one_mul, hb0', pow_zero]
        have hl : (Nat.digits 10 e).length ≤ B0 := by
          rw [e1]
          have h1 : (Nat.digits 10 (1 : ℕ)).length = 1 := by decide
          rw [h1, hB0]
          exact le_max_left _ _
        exact le_trans hl hBB0
      · have hlt : e < 10 ^ b' := by
          have h10b : 10 ^ b' = 2 ^ b' * 5 ^ b' := by
            rw [show (10:ℕ) = 2 * 5 from by norm_num, mul_pow]
          rw [he_def, ha0, pow_zero, one_mul, h10b, mul_comm (2 ^ b') _]
          exact lt_mul_of_one_lt_right (pow_pos (by norm_num) b')
            (one_lt_pow₀ (by norm_num : (1:ℕ) < 2) (by omega : b' ≠ 0))
        have h1 : (Nat.digits 10 e).length ≤ b' :=
          (Nat.digits_length_le_iff (b := 10) (k := b') (by norm_num) e).mpr hlt
        calc _ ≤ b' := h1
          _ ≤ max a' b' := le_max_right _ _
          _ ≤ B0 := le_max_right _ _
          _ ≤ B := hBB0
    · rcases Nat.eq_zero_or_pos a' with ha0' | ha1'
      · have e1 : e = 1 := by
          rw [he_def, hb0, pow_zero, mul_one, ha0', pow_zero]
        have hl : (Nat.digits 10 e).length ≤ B0 := by
          rw [e1]
          have h1 : (Nat.digits 10 (1 : ℕ)).length = 1 := by decide
          rw [h1, hB0]
          exact le_max_left _ _
        exact le_trans hl hBB0
      · have hlt : e < 10 ^ a' := by
          have h10a : 10 ^ a' = 2 ^ a' * 5 ^ a' := by
            rw [show (10:ℕ) = 2 * 5 from by norm_num, mul_pow]
          rw [he_def, hb0, pow_zero, mul_one, h10a]
          exact lt_mul_of_one_lt_right (pow_pos (by norm_num) a')
            (one_lt_pow₀ (by norm_num : (1:ℕ) < 5) (by omega : a' ≠ 0))
        have h1 : (Nat.digits 10 e).length ≤ a' :=
          (Nat.digits_length_le_iff (b := 10) (k := a') (by norm_num) e).mpr hlt
        calc _ ≤ a' := h1
          _ ≤ max a' b' := le_max_left _ _
          _ ≤ B0 := le_max_right _ _
          _ ≤ B := hBB0
  
  set Mst := m * 3 ^ (v - 4) with hMst
  set r := (Mst + 7) / 9 with hr
  have hMle : Mst ≤ 1 + 9 * r := by
    have hdm := Nat.div_add_mod (Mst + 7) 9
    have hlt9 : (Mst + 7) % 9 ≤ 8 := by
      have hmlt := Nat.mod_lt (Mst + 7) (by norm_num : (0:ℕ) < 9)
      omega
    rw [hr]
    omega
  have h9r : 9 * r ≤ Mst + 7 := by
    have hdm := Nat.div_add_mod (Mst + 7) 9
    rw [hr]
    omega
  set K := 2 * r with hK_def
  have hKcov : m * 3 ^ (v - 4) ≤ 1 + 9 * (K / 2) := by
    rw [hK_def]
    have hrr : (2 * r) / 2 = r := by omega
    rw [hrr]
    exact hMle
  
  set Lw := L - 2 * B with hLw
  set g := Lw - 4 * K with hg_def
  set t := g / 2 with ht_def
  set Sf := 2 * (Nat.digits 10 e).sum + 18 * K with hSf_def
  have h2σe : 2 * (Nat.digits 10 e).sum ≤ 9 * e := two_sigma_le_nine e
  have hMstq : Mst ≤ q := by
    rw [hMst, hq_def]
    calc m * 3 ^ (v - 4) ≤ m * 3 ^ v :=
        Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le v 4))
      _ = 3 ^ v * m := by ring
  have hq7 : 1 ≤ r → 7 ≤ q := by
    intro hr1
    have hM2 : 2 ≤ Mst := by
      have h9 : 9 ≤ Mst + 7 := by
        calc 9 = 9 * 1 := by ring
          _ ≤ 9 * r := Nat.mul_le_mul_left _ hr1
          _ ≤ Mst + 7 := h9r
      omega
    rcases Nat.lt_or_ge m 2 with hm2' | hm2'
    · have hm1v : m = 1 := by omega
      rw [hMst, hm1v, one_mul] at hM2
      have hv5 : 5 ≤ v := by
        by_contra hv5
        push_neg at hv5
        have h04 : v - 4 = 0 := by omega
        rw [h04, pow_zero] at hM2
        omega
      have h75 : (7:ℕ) ≤ 3 ^ v := by
        calc (7:ℕ) ≤ 3 ^ 5 := by norm_num
          _ ≤ 3 ^ v := Nat.pow_le_pow_right (by norm_num) hv5
      exact h75.trans (Nat.le_mul_of_pos_right _ (by omega : 0 < m))
    · have hm7 : 7 ≤ m := by
        by_contra hm7
        push_neg at hm7
        interval_cases m <;> norm_num [Nat.Coprime] at hm30
      exact hm7.trans (Nat.le_mul_of_pos_left _ (pow_pos (by norm_num) v))
  have h36r : 36 * r ≤ 8 * q := by
    rcases Nat.eq_zero_or_pos r with hr0 | hr1
    · rw [hr0]; omega
    · have hq7' := hq7 hr1
      calc 36 * r ≤ 4 * (Mst + 7) := by omega
        _ ≤ 4 * q + 28 := by omega
        _ ≤ 8 * q := by omega
  
  have ha'le : a' + 1 ≤ n' := by
    calc a' + 1 ≤ 2 ^ a' := succ_le_pow2 a'
      _ ≤ e := by
        rw [he_def]
        exact Nat.le_mul_of_pos_right _ (pow_pos (by norm_num) b')
      _ ≤ n' := Nat.le_of_dvd hn'pos ⟨q, hn'eq⟩
  have hb'le : b' + 1 ≤ n' := by
    calc b' + 1 ≤ 2 ^ b' := succ_le_pow2 b'
      _ ≤ 5 ^ b' := Nat.pow_le_pow_left (by norm_num) _
      _ ≤ e := by
        rw [he_def]
        exact Nat.le_mul_of_pos_left _ (pow_pos (by norm_num) a')
      _ ≤ n' := Nat.le_of_dvd hn'pos ⟨q, hn'eq⟩
  have hB0le : B0 ≤ n' := by
    rw [hB0]; omega
  have hBle : B ≤ n' + 1 := by omega
  have h9zn : 9 * z ≤ n := by
    have h1 : 9 * z ≤ 9 * 10 ^ (z - 1) :=
      Nat.mul_le_mul_left _ (z_le_pow10_pred hz1)
    have h2 : 10 ^ z = 10 * 10 ^ (z - 1) := by
      nth_rewrite 1 [← Nat.sub_add_cancel hz1]
      rw [_root_.pow_succ]
      ring
    have h3 : 9 * 10 ^ (z - 1) ≤ 10 ^ z * n' := by
      rw [h2]
      have h9 : 9 ≤ 10 * n' := by omega
      calc 9 * 10 ^ (z - 1) ≤ (10 * n') * 10 ^ (z - 1) :=
          Nat.mul_le_mul_right _ h9
        _ = 10 * 10 ^ (z - 1) * n' := by ring
    calc 9 * z ≤ 9 * 10 ^ (z - 1) := h1
      _ ≤ 10 ^ z * n' := h3
      _ = n' * 10 ^ z := by ring
      _ = n := hnn'.symm
  
  have hI2 : 9 * z + 18 * B + 72 * r + 9 ≤ 8 * n := by
    have h72 : 72 * r ≤ 16 * q := by omega
    have h18B : 18 * B ≤ 18 * (n' + 1) := Nat.mul_le_mul_left _ hBle
    have hqle : q ≤ n' := Nat.le_of_dvd hn'pos ⟨e, by rw [hn'eq]; ring⟩
    have h70 : 70 * n' ≤ 7 * n := by
      have h70e : 7 * (10 ^ z * n') = 7 * n := by
        rw [hnn']; ring
      calc 70 * n' = 7 * (10 * n') := by ring
        _ ≤ 7 * (10 ^ z * n') := Nat.mul_le_mul_left _
            (Nat.mul_le_mul_right n' h10ge)
        _ = 7 * n := h70e
    have hmid : 18 * n' + 16 * q + 27 ≤ 70 * n' := by omega
    omega
  
  have hg8 : 8 * g = 8 * n - 8 * z - 16 * B - 64 * r := by
    have e1 : 8 * g = 8 * Lw - 32 * K := by
      have : 8 * g = 8 * Lw - 8 * (4 * K) := by rw [hg_def, Nat.mul_sub]
      omega
    have e2 : 8 * Lw = 8 * L - 16 * B := by
      rw [hLw, Nat.mul_sub]; ring
    have e3 : 8 * L = 8 * n - 8 * z := by
      rw [hL_def, Nat.mul_sub]
    omega
  have hg2 : 2 ≤ g := by omega
  have hLw_eq : Lw = 4 * K + g := by omega
  have hL_eq : L = 2 * B + Lw := by omega
  
  have hSfn : Sf ≤ n := by
    rcases Nat.eq_zero_or_pos r with hr0 | hr1
    · rw [hSf_def, hK_def, hr0]
      have h9e : 9 * e ≤ n := by
        have heq : 10 ^ z * (e * q) = n := by rw [hnn', hn'eq]; ring
        calc 9 * e = e * 9 := by ring
          _ ≤ e * (10 * q) := Nat.mul_le_mul_left e (by omega)
          _ = 10 * (e * q) := by ring
          _ ≤ 10 ^ z * (e * q) := Nat.mul_le_mul_right (e * q) h10ge
          _ = n := heq
      omega
    · have hq7' := hq7 hr1
      have hbound : 9 * e + 8 * q ≤ 10 ^ z * (e * q) := by
        rcases Nat.lt_or_ge z 2 with hz2 | hz2
        · have hz1' : z = 1 := by omega
          rw [hz1', pow_one]
          have key : 10 * (e * q) = e * (10 * q - 9) + 9 * e := by
            have hq9 : 9 ≤ 10 * q := by omega
            have ee : e * (10 * q - 9) + 9 * e = e * ((10 * q - 9) + 9) := by
              ring
            rw [ee, Nat.sub_add_cancel hq9]; ring
          rw [key]
          have h1 : 10 * q - 9 ≤ e * (10 * q - 9) :=
            Nat.le_mul_of_pos_left _ (by omega : 0 < e)
          have h2 : 8 * q ≤ 10 * q - 9 := by omega
          omega
        · have h10z2 : 100 ≤ 10 ^ z := by
            calc (100:ℕ) = 10 ^ 2 := by norm_num
              _ ≤ 10 ^ z := Nat.pow_le_pow_right (by norm_num) hz2
          have h9e : 9 * e ≤ 9 * (e * q) := by
            have : e ≤ e * q := Nat.le_mul_of_pos_right e hq0
            omega
          have h8q : 8 * q ≤ 8 * (e * q) := by
            have : q ≤ e * q := Nat.le_mul_of_pos_left q he0
            omega
          have h100 : 100 * (e * q) ≤ 10 ^ z * (e * q) :=
            Nat.mul_le_mul_right _ h10z2
          omega
      have hSf9 : Sf ≤ 9 * e + 8 * q := by
        rw [hSf_def, hK_def]; omega
      have heq : 10 ^ z * (e * q) = n := by rw [hnn', hn'eq]; ring
      calc Sf ≤ 9 * e + 8 * q := hSf9
        _ ≤ 10 ^ z * (e * q) := hbound
        _ = n := heq
  set R := (n - Sf) / 2 with hR_def
  have hSfp : 2 ∣ n - Sf := by
    have hn2 : 2 ∣ n := (by norm_num : (2:ℕ) ∣ 10).trans h10
    have hSf2 : 2 ∣ Sf := by
      rw [hSf_def]
      exact Nat.dvd_add (dvd_mul_right _ _)
        (dvd_mul_of_dvd_left (by norm_num : (2:ℕ) ∣ 18) K)
    exact Nat.dvd_sub hn2 hSf2
  have h2R : 2 * R = n - Sf := Nat.mul_div_cancel' hSfp
  
  have hRt : R ≤ 9 * t := by
    have htg : g - 1 ≤ 2 * t := by
      rw [ht_def]
      have hdm := Nat.div_add_mod g 2
      omega
    have hg9 : 9 * g = 9 * n - 9 * z - 18 * B - 36 * K := by
      have e1 : 9 * g = 9 * Lw - 36 * K := by
        have : 9 * g = 9 * Lw - 9 * (4 * K) := by rw [hg_def, Nat.mul_sub]
        omega
      have e2 : 9 * Lw = 9 * L - 18 * B := by
        rw [hLw, Nat.mul_sub]; ring
      have e3 : 9 * L = 9 * n - 9 * z := by
        rw [hL_def, Nat.mul_sub]
      omega
    have hnSf : n - Sf ≤ 18 * t := by
      have h1 : n - Sf ≤ 9 * g - 9 := by
        rw [hg9, hSf_def]
        have hKK : K = 2 * r := hK_def
        omega
      have h2 : 9 * g - 9 ≤ 18 * t := by
        have ee : 9 * g - 9 = 9 * (g - 1) := by omega
        rw [ee]
        calc 9 * (g - 1) ≤ 9 * (2 * t) := Nat.mul_le_mul_left _ htg
          _ = 18 * t := by ring
      omega
    have : 2 * R ≤ 18 * t := by rw [h2R]; exact hnSf
    omega
  
  set de := Nat.digits 10 e
      ++ List.replicate (B - (Nat.digits 10 e).length) 0 with hde_def
  have hde_len : de.length = B := by
    rw [hde_def, List.length_append, List.length_replicate]
    omega
  have hde_val : Nat.ofDigits 10 de = e := by
    rw [hde_def, ofDigits_append', Nat.ofDigits_digits,
      A084017.ofDigits_replicate_zero, mul_zero, add_zero]
  have hde_lt10 : ∀ x ∈ de, x < 10 := by
    intro x hx
    rw [hde_def] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact Nat.digits_lt_base (by norm_num) hx
    · obtain ⟨_, rfl⟩ := List.mem_replicate.mp hx
      norm_num
  have hde_ne : de ≠ [] := by
    intro h
    have hd0 : de.length = 0 := by rw [h]; rfl
    omega
  have hde_head : ∀ h : de ≠ [], de.head h ≠ 0 := by
    intro h
    have hdig : Nat.digits 10 e = e % 10 :: Nat.digits 10 (e / 10) :=
      Nat.digits_eq_cons_digits_div (b := 10) (by norm_num)
        (by omega : e ≠ 0)
    have hhead : de.head h = e % 10 := by
      simp only [hde_def, hdig, List.cons_append, List.head_cons]
    rw [hhead]; exact he10
  have hde_sum : de.sum = (Nat.digits 10 e).sum := by
    rw [hde_def, List.sum_append, List.sum_replicate]
    simp
  have hmaxB : max a' b' ≤ B := by
    calc max a' b' ≤ B0 := le_max_right _ _
      _ ≤ B := hBB0
  
  obtain ⟨F, hFlen, hF9, hFsum⟩ := exists_free_block t R hRt
  
  have h3vn : 3 ^ v ∣ n := by
    have h1 : 3 ^ v ∣ n' :=
      ⟨2 ^ a' * 5 ^ b' * m, by rw [hn'_def, he_def]; ring⟩
    exact h1.trans ⟨10 ^ z, hnn'⟩
  
  rcases Nat.even_or_odd L with hLEv | hLOdd
  · 
    have hLw4 : Lw % 4 = 0 := by
      rw [hLw]
      by_cases h4 : (L - 2 * B0) % 4 = 0
      · have hBB : B = B0 := by
          rw [hB]
          simp [hLEv, h4]
        rw [hBB]; exact h4
      · have hBB : B = B0 + 1 := by
          rw [hB]
          simp [hLEv, h4]
        rw [hBB]
        have hpar : (L - 2 * B0) % 2 = 0 := by
          have hLL : 2 * B0 ≤ L := by omega
          have e2 : L % 2 = 0 := Nat.even_iff.mp hLEv
          have e3 : (2 * B0) % 2 = 0 :=
            Nat.mod_eq_zero_of_dvd (dvd_mul_right 2 B0)
          omega
        have hm4 : (L - 2 * B0) % 4 = 2 := by omega
        have h2le : 2 ≤ L - 2 * B0 := by omega
        have hd4 : 4 ∣ L - 2 * B0 - 2 := by
          have hdm := Nat.div_add_mod (L - 2 * B0) 4
          rw [hm4] at hdm
          refine ⟨(L - 2 * B0) / 4, ?_⟩
          omega
        have ee : L - 2 * (B0 + 1) = L - 2 * B0 - 2 := by
          rw [show 2 * (B0 + 1) = 2 * B0 + 2 from by ring, ← Nat.sub_sub]
        rw [ee]
        exact Nat.mod_eq_zero_of_dvd hd4
    have hg4 : g % 4 = 0 := by
      have ee : Lw % 4 = g % 4 := by
        rw [hLw_eq]; omega
      rw [← ee]; exact hLw4
    have hg4le : 4 ≤ g := by omega
    set C := F ++ F.reverse with hC_def
    have hg2t : 2 * t = g := by
      have hd2 : 2 ∣ g := Nat.dvd_of_mod_eq_zero (by omega)
      exact Nat.mul_div_cancel' hd2
    have hCg : C.length = g := by
      rw [hC_def, List.length_append, List.length_reverse, hFlen]
      omega
    have hCpal : C.Palindrome := by
      rw [hC_def]
      apply List.Palindrome.of_reverse_eq
      simp [List.reverse_append, List.reverse_reverse, List.append_assoc]
    have hC10 : ∀ x ∈ C, x < 10 := by
      intro x hx
      rw [hC_def] at hx
      rcases List.mem_append.mp hx with hx | hx
      · have := hF9 x hx; omega
      · have := hF9 x (List.mem_reverse.mp hx); omega
    have hCsum : C.sum = 2 * R := by
      rw [hC_def, List.sum_append, List.sum_reverse, hFsum]
      ring
    set G₀ := (List.range (2 * K)).map (pairDigit (fun _ => 0)) with hG₀
    have hG₀sum : G₀.sum = 9 * K := by
      rw [hG₀]
      exact pairDigit_sum _ (fun _ => Nat.zero_le 9) K
    have h2A : 2 * (de ++ G₀ ++ F).sum = n := by
      rw [List.sum_append, List.sum_append, hde_sum, hG₀sum, hFsum]
      have ee : 2 * ((Nat.digits 10 e).sum + 9 * K + R) = Sf + 2 * R := by
        rw [hSf_def]; ring
      rw [ee, h2R]
      exact Nat.add_sub_cancel' hSfn
    obtain ⟨s₀, hs0⟩ : ∃ s₀ : ℕ,
        (Nat.ofDigits (10 : ZMod (3 ^ v)) de
          + Nat.ofDigits (10 : ZMod (3 ^ v)) de.reverse
              * (10 : ZMod (3 ^ v)) ^ (B + (4 * K + g)))
        + (10 : ZMod (3 ^ v)) ^ B
          * (Nat.ofDigits (10 : ZMod (3 ^ v)) C
              * (10 : ZMod (3 ^ v)) ^ (2 * K)
            + (9 * ∑ k ∈ Finset.range K, palW (3 ^ v) (4 * K + g) (2 * k + 1)
              + 81 * (s₀ : ZMod (3 ^ v)))) = 0 := by
      rcases Nat.lt_or_ge v 5 with hv | hv
      · have hP0dvd : 3 ^ v ∣ Nat.ofDigits 10
            (de ++ ((G₀ ++ C) ++ G₀.reverse) ++ de.reverse) := by
          rw [hC_def]
          exact dvd3_pow_sandwich_even (by omega : v ≤ 4) de G₀ F
            (by rw [h2A]; exact h3vn)
        exact ⟨0, hs0_of_dvd3 de C hde_len hCg (by
          rw [hC_def] at hP0dvd ⊢; exact hP0dvd)⟩
      · have h81n : 81 ∣ n := by
          have h34 : 3 ^ 4 ∣ 3 ^ v := pow_dvd_pow 3 (by omega : 4 ≤ v)
          exact h34.trans h3vn
        have hP0dvd : 81 ∣ Nat.ofDigits 10
            (de ++ ((G₀ ++ C) ++ G₀.reverse) ++ de.reverse) := by
          rw [hC_def]
          exact dvd3_pow_sandwich_even (by norm_num : 4 ≤ 4) de G₀ F
            (by rw [h2A]; exact h81n)
        exact hs0_of_dvd81 hv de C hde_len hCg (by
          rw [hC_def] at hP0dvd ⊢; exact hP0dvd)
    have hP0_11 : ∀ h : 11 ∣ m, (ZMod.castHom h (ZMod 11))
        ((Nat.ofDigits (10 : ZMod m) de
            + Nat.ofDigits (10 : ZMod m) de.reverse
                * (10 : ZMod m) ^ (B + (4 * K + g)))
          + (10 : ZMod m) ^ B
            * (Nat.ofDigits (10 : ZMod m) C * (10 : ZMod m) ^ (2 * K)
              + 9 * ∑ k ∈ Finset.range K, palW m (4 * K + g) (2 * k + 1)))
        = 0 := by
      intro h
      have hgv : (Nat.ofDigits (10 : ZMod m) de
          + Nat.ofDigits (10 : ZMod m) de.reverse
              * (10 : ZMod m) ^ (B + (4 * K + g)))
        + (10 : ZMod m) ^ B
          * (Nat.ofDigits (10 : ZMod m) C * (10 : ZMod m) ^ (2 * K)
            + 9 * ∑ k ∈ Finset.range K, palW m (4 * K + g) (2 * k + 1))
        = Nat.ofDigits (10 : ZMod m)
            (de ++ ((G₀ ++ C) ++ G₀.reverse) ++ de.reverse) := by
        rw [gadget_val_m (m := m) de hde_len (fun _ => 0)
          (fun _ => Nat.zero_le 9) C hCg]
        simp only [Nat.cast_zero, zero_mul, add_zero]
        rw [← Finset.mul_sum]
      rw [hgv, castHom_ofDigits]
      have hsplit : de ++ ((G₀ ++ C) ++ G₀.reverse) ++ de.reverse
          = (de ++ G₀ ++ F) ++ (de ++ G₀ ++ F).reverse := by
        rw [hC_def]
        simp [List.append_assoc, List.reverse_append]
      rw [hsplit]
      exact ofDigits_palPair11 _
    obtain ⟨e', he', hdvdP⟩ := P_dvd_3m81_pinned hm3 hm10 de hde_len
      C hCg hP0_11 hg4le hg4 hKcov s₀ hs0
    exact finGoal_assemble_sandwich hnd hm30 htz hzlen he_def hza hzb
      hLw_eq hL_eq hL_def hSf_def hSfn h2R hde_len hde_val hde_lt10
      hde_ne hde_head hde_sum hmaxB hCg hCpal hC10 hCsum he' hdvdP
  · 
    have hBB : B = B0 := by
      rw [hB]
      simp [Nat.not_even_iff_odd.mpr hLOdd]
    have hLw2 : Lw % 2 = 1 := by
      have hLL : 2 * B ≤ L := by omega
      have e2 : L % 2 = 1 := Nat.odd_iff.mp hLOdd
      have e3 : (2 * B) % 2 = 0 :=
        Nat.mod_eq_zero_of_dvd (dvd_mul_right 2 B)
      omega
    have hgodd : Odd g := by
      rw [Nat.odd_iff]
      have ee : Lw % 2 = g % 2 := by
        rw [hLw_eq]; omega
      rw [← ee]; exact hLw2
    have hg3 : 3 ≤ g := by omega
    set C := F ++ [0] ++ F.reverse with hC_def
    have hCg : C.length = g := by
      rw [hC_def, List.length_append, List.length_append, hFlen,
        List.length_singleton, List.length_reverse, hFlen]
      have hdm := Nat.div_add_mod g 2
      have hg2' : g % 2 = 1 := Nat.odd_iff.mp hgodd
      omega
    have hCpal : C.Palindrome := by
      rw [hC_def]
      apply List.Palindrome.of_reverse_eq
      simp [List.reverse_append, List.reverse_reverse, List.append_assoc]
    have hC10 : ∀ x ∈ C, x < 10 := by
      intro x hx
      rw [hC_def] at hx
      rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_append.mp hx with hx | hx
        · have := hF9 x hx; omega
        · simp at hx; omega
      · have := hF9 x (List.mem_reverse.mp hx); omega
    have hCsum : C.sum = 2 * R := by
      rw [hC_def, List.sum_append, List.sum_append, List.sum_singleton,
        List.sum_reverse, hFsum]
      ring
    set G₀ := (List.range (2 * K)).map (pairDigit (fun _ => 0)) with hG₀
    have hG₀sum : G₀.sum = 9 * K := by
      rw [hG₀]
      exact pairDigit_sum _ (fun _ => Nat.zero_le 9) K
    have h2A : 2 * (de ++ G₀ ++ F).sum = n := by
      rw [List.sum_append, List.sum_append, hde_sum, hG₀sum, hFsum]
      have ee : 2 * ((Nat.digits 10 e).sum + 9 * K + R) = Sf + 2 * R := by
        rw [hSf_def]; ring
      rw [ee, h2R]
      exact Nat.add_sub_cancel' hSfn
    obtain ⟨s₀, hs0⟩ : ∃ s₀ : ℕ,
        (Nat.ofDigits (10 : ZMod (3 ^ v)) de
          + Nat.ofDigits (10 : ZMod (3 ^ v)) de.reverse
              * (10 : ZMod (3 ^ v)) ^ (B + (4 * K + g)))
        + (10 : ZMod (3 ^ v)) ^ B
          * (Nat.ofDigits (10 : ZMod (3 ^ v)) C
              * (10 : ZMod (3 ^ v)) ^ (2 * K)
            + (9 * ∑ k ∈ Finset.range K, palW (3 ^ v) (4 * K + g) (2 * k + 1)
              + 81 * (s₀ : ZMod (3 ^ v)))) = 0 := by
      rcases Nat.lt_or_ge v 5 with hv | hv
      · have hP0dvd : 3 ^ v ∣ Nat.ofDigits 10
            (de ++ ((G₀ ++ C) ++ G₀.reverse) ++ de.reverse) := by
          rw [hC_def]
          exact dvd3_pow_sandwich_odd (by omega : v ≤ 4) de G₀ F
            (by rw [h2A]; exact h3vn)
        exact ⟨0, hs0_of_dvd3 de C hde_len hCg (by
          rw [hC_def] at hP0dvd ⊢; exact hP0dvd)⟩
      · have h81n : 81 ∣ n := by
          have h34 : 3 ^ 4 ∣ 3 ^ v := pow_dvd_pow 3 (by omega : 4 ≤ v)
          exact h34.trans h3vn
        have hP0dvd : 81 ∣ Nat.ofDigits 10
            (de ++ ((G₀ ++ C) ++ G₀.reverse) ++ de.reverse) := by
          rw [hC_def]
          exact dvd3_pow_sandwich_odd (by norm_num : 4 ≤ 4) de G₀ F
            (by rw [h2A]; exact h81n)
        exact hs0_of_dvd81 hv de C hde_len hCg (by
          rw [hC_def] at hP0dvd ⊢; exact hP0dvd)
    obtain ⟨e', he', hdvdP⟩ := P_dvd_3m81 hm3 hm10 de hde_len C hCg
      hg3 hgodd hKcov s₀ hs0
    exact finGoal_assemble_sandwich hnd hm30 htz hzlen he_def hza hzb
      hLw_eq hL_eq hL_def hSf_def hSfn h2R hde_len hde_val hde_lt10
      hde_ne hde_head hde_sum hmaxB hCg hCpal hC10 hCsum he' hdvdP






end PinnedTen

end PinnedTensrc


end OMA.A084017Port

theorem OMA.solution : OMA.R_oeis_a084017_R1.H2 := by
  intro n hn h10
  exact OMA.A084017Port.PinnedTen.pinned_A084017_ten n hn h10
