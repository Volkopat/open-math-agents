import OMAReductions.R_Erdos11_erdos_11_variants_not_four_dvd_R1
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Positivity
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic.Positivity
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Nat.Totient

/-! An exponent sieve for squarefree numbers translated by powers of two.
The finite zone through ten million (strict upper bound) reuses the bit-sieve proof by
@LordMike for the original finite_bound1. The two remaining inequalities separately count
distinct large obstructing primes and repeat hits. A factorization certificate for the
first 154 Mersenne numbers eliminates all repeat hits through length 155. -/
/- Finite odd case of Erdős problem 11 through ten million. The bit sieve and its
soundness proof are adapted from @LordMike’s accepted OMA proof (#943) of
`Erdos11.erdos_11.variants.finite_bound1`. The sieve marks multiples of prime
squares and tests the remaining bit positions after shifts by powers of two.
We determine the fifteen odd integers requiring exponent six in this interval. -/
namespace OMA.E11

set_option maxRecDepth 100000 in
theorem finite_odd_certificate :
  let N : ℕ := 10^7
  let M (d m : ℕ) := (2^(d*m)-1)/(2^d-1)
  let good (q : ℕ) : Bool :=
    decide (q≤ 23) || (q%2 != 0 && q%3 != 0 && q%5 != 0 && q%7 != 0 && q%11 != 0 &&
      q%13 != 0 && q%17 != 0 && q%19 != 0 && q%23 != 0)
  let ns : ℕ → ℕ := Nat.rec 0 (fun m prior =>
    (if good (m+2) then M ((m+2)*(m+2)) ((N-1)/((m+2)*(m+2))+1) else 0) ||| prior)
  let ns2 : ℕ → ℕ := Nat.rec 0 (fun m prior =>
    (if good (m+2237) then 2^((m+2237)*(m+2237)) else 0) ||| prior)
  let term (S l : ℕ) := (S <<< (2^l)) ||| (2^(2^l)-1)
  let bad (S : ℕ) : ℕ → ℕ := Nat.rec (term S 0) (fun l prior => term S (l+1) &&& prior)
  let points : List ℕ := 1 :: [434977, 618433, 2019077, 3231313, 4357229, 5826545, 5914757, 6261277, 7689677, 8016857, 8020177, 9121133, 9657377, 9835729, 9976579]
  let check (S : ℕ) := (bad S 5 &&& (M 2 (N/2) <<< 1)) == points.foldr (fun a z => 2 ^ a ||| z) 0
  check (ns 2235 ||| ns2 926) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem finite_odd_five_outside (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1< n)
    (outside : n ∉ ([434977, 618433, 2019077, 3231313, 4357229, 5826545, 5914757, 6261277, 7689677, 8016857, 8020177, 9121133, 9657377, 9835729, 9976579] : List ℕ)) :
    ∃ k l : ℕ, Squarefree k ∧ n=k+2^l ∧ l≤ 5 := by
  have hb := finite_odd_certificate
  extract_lets N M good ns ns2 term bad points check at hb
  let T (d m : ℕ) := ∑ j ∈ Finset.range m, 2^(d*j)
  have T_identity(d m : Nat) : T d m * (2^d - 1) + 1 = 2^(d*m) := by
    have hx : 2^d - 1 + 1 = 2^d := Nat.sub_add_cancel Nat.one_le_two_pow
    have h := geom_sum_mul_add (2^d - 1) m
    rw [hx] at h
    have hT : T d m = ∑ i ∈ Finset.range m, (2^d)^i := by
      unfold T
      exact Finset.sum_congr rfl (fun j _ => by rw [← pow_mul])
    rw [hT, pow_mul]
    exact h

  have two_pow_sub_pos (d : Nat) (hd : 0 < d) : 0 < 2^d - 1 := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hd
    simp only [pow_one] at this
    omega

  have T_lt (d m : Nat) (hd : 0 < d) : T d m < 2^(d*m) := by
    have h := T_identity d m
    have h1 := two_pow_sub_pos d hd
    have h2 : T d m ≤ T d m * (2^d - 1) := Nat.le_mul_of_pos_right _ h1
    omega

  have M_eq_T (d m : Nat) (hd : 0 < d) : M d m = T d m := by
    unfold M
    apply Nat.div_eq_of_eq_mul_left (two_pow_sub_pos d hd)
    have := T_identity d m
    rw [← this, Nat.add_sub_cancel]

  have T_testBit (d : Nat) (hd : 0 < d) (m : Nat) : ∀ k, d ∣ k → k < d*m → (T d m).testBit k = true := by
    induction m with
    | zero => intro k _ hk; simp at hk
    | succ m ih =>
      intro k hdk hk
      have hsucc : T d (m+1) = 2^(d*m) + T d m := by
        unfold T
        rw [Finset.sum_range_succ, add_comm]
      rw [hsucc]
      by_cases hlt : k < d*m
      · rw [Nat.testBit_two_pow_add_gt hlt]
        exact ih k hdk hlt
      · obtain ⟨c, rfl⟩ := hdk
        have hc1 : m ≤ c := Nat.le_of_mul_le_mul_left (Nat.not_lt.mp hlt) hd
        have hc2 : c < m + 1 := Nat.lt_of_mul_lt_mul_left hk
        have hcm : c = m := by omega
        subst hcm
        rw [Nat.testBit_two_pow_add_eq, Nat.testBit_eq_false_of_lt (T_lt d c hd)]
        rfl

  have M_testBit (d m k : Nat) (hd : 0 < d) (hdk : d ∣ k) (hk : k < d*m) : (M d m).testBit k = true := by
    rw [M_eq_T d m hd]
    exact T_testBit d hd m k hdk hk

  have good_of_prime (p : Nat) (hp : p.Prime) : good p = true := by
    by_cases h : p ≤ 23
    · simp [good, h]
    · have h2 : p % 2 ≠ 0 := fun h0 => by have := hp.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero h0); omega
      have h3 : p % 3 ≠ 0 := fun h0 => by have := hp.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h0); omega
      have h5 : p % 5 ≠ 0 := fun h0 => by have := hp.eq_one_or_self_of_dvd 5 (Nat.dvd_of_mod_eq_zero h0); omega
      have h7 : p % 7 ≠ 0 := fun h0 => by have := hp.eq_one_or_self_of_dvd 7 (Nat.dvd_of_mod_eq_zero h0); omega
      have h11 : p % 11 ≠ 0 := fun h0 => by have := hp.eq_one_or_self_of_dvd 11 (Nat.dvd_of_mod_eq_zero h0); omega
      have h13 : p % 13 ≠ 0 := fun h0 => by have := hp.eq_one_or_self_of_dvd 13 (Nat.dvd_of_mod_eq_zero h0); omega
      have h17 : p % 17 ≠ 0 := fun h0 => by have := hp.eq_one_or_self_of_dvd 17 (Nat.dvd_of_mod_eq_zero h0); omega
      have h19 : p % 19 ≠ 0 := fun h0 => by have := hp.eq_one_or_self_of_dvd 19 (Nat.dvd_of_mod_eq_zero h0); omega
      have h23 : p % 23 ≠ 0 := fun h0 => by have := hp.eq_one_or_self_of_dvd 23 (Nat.dvd_of_mod_eq_zero h0); omega
      unfold good
      have odd_mod : p % 2 = 1 := by omega
      simp [h, odd_mod, h3, h5, h7, h11, h13, h17, h19, h23]

  have ns_testBit (m : Nat) : ∀ k q, 2 ≤ q → q ≤ m+1 → good q = true → q*q ∣ k → k < N →
      (ns m).testBit k = true := by
    induction m with
    | zero => intro k q h2 hq _ _ _; omega
    | succ m ih =>
      intro k q h2 hq hg hdk hk
      simp only [ns, Nat.testBit_or, Bool.or_eq_true]
      by_cases hq' : q = m+2
      · subst hq'
        left
        rw [if_pos hg]
        have hdpos : 0 < (m+2)*(m+2) := by positivity
        apply M_testBit _ _ _ hdpos hdk
        have h1 := Nat.lt_mul_div_succ (N-1) hdpos
        exact lt_of_le_of_lt (by omega) h1
      · right
        exact ih k q h2 (by omega) hg hdk hk

  have ns2_testBit (m : Nat) : ∀ q, 2237 ≤ q → q ≤ 2236 + m → good q = true →
      (ns2 m).testBit (q*q) = true := by
    induction m with
    | zero => intro q h1 h2; omega
    | succ m ih =>
      intro q h1 h2 hg
      simp only [ns2, Nat.testBit_or, Bool.or_eq_true]
      by_cases hq' : q = m+2237
      · subst hq'
        left
        rw [if_pos hg]
        exact Nat.testBit_two_pow_self
      · right
        exact ih q h1 (by omega) hg

  have S_testBit (k : Nat) (hk : k < N) (hs : ¬ Squarefree k) :
      (ns 2235 ||| ns2 926).testBit k = true := by
    have hk' : k < 10^7 := hk
    rw [Nat.testBit_or, Bool.or_eq_true]
    by_cases h0 : k = 0
    · subst h0
      left
      exact ns_testBit 2235 0 2 (by norm_num) (by norm_num) (by decide) (dvd_zero _) hk
    · rw [Nat.squarefree_iff_prime_squarefree] at hs
      push Not at hs
      obtain ⟨p, hp, hpd⟩ := hs
      have hle : p*p ≤ k := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hpd
      have hp3 : p ≤ 3162 := by nlinarith
      have hg : good p = true := good_of_prime p hp
      have hp2 : 2 ≤ p := hp.two_le
      by_cases hq4 : p ≤ 2236
      · left
        exact ns_testBit 2235 k p hp2 (by omega) hg hpd hk
      · have hq5 : 2237 ≤ p := by omega
        right
        obtain ⟨c, rfl⟩ := hpd
        have hc1 : c = 1 := by
          rcases c with _ | _ | c
          · simp at h0
          · rfl
          · nlinarith [Nat.mul_le_mul hq5 hq5]
        subst hc1
        rw [mul_one]
        exact ns2_testBit 926 p hq5 (by omega) hg

  have term_false (S l n : Nat) (h : (term S l).testBit n = false) :
      2^l ≤ n ∧ S.testBit (n - 2^l) = false := by
    unfold term at h
    rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one] at h
    by_cases hl : 2^l ≤ n
    · refine ⟨hl, ?_⟩
      have hl' : ¬ n < 2^l := Nat.not_lt.mpr hl
      simpa [hl, hl'] using h
    · have hl' : n < 2^l := Nat.lt_of_not_le hl
      simp [hl, hl'] at h

  have bad_false (S : Nat) : ∀ L n, (bad S L).testBit n = false →
      ∃ l, l ≤ L ∧ 2^l ≤ n ∧ S.testBit (n - 2^l) = false := by
    intro L
    induction L with
    | zero =>
      intro n h
      change (term S 0).testBit n = false at h
      obtain ⟨hl, hS⟩ := term_false S 0 n h
      exact ⟨0, le_refl 0, hl, hS⟩
    | succ L ih =>
      intro n h
      change (term S (L+1) &&& bad S L).testBit n = false at h
      rw [Nat.testBit_and] at h
      rcases Bool.and_eq_false_iff.mp h with h1 | h2
      · obtain ⟨hl, hS⟩ := term_false S (L+1) n h1
        exact ⟨L+1, le_refl _, hl, hS⟩
      · obtain ⟨l, hl, h3, h4⟩ := ih n h2
        exact ⟨l, by omega, h3, h4⟩
  have hN : n < N := h
  have hN2 : 2 * (N/2) = N := by norm_num [N]
  unfold check at hb
  rw [beq_iff_eq] at hb
  have hbit := congrArg (fun x => Nat.testBit x n) hb
  obtain ⟨t, ht⟩ := hn
  have hM : (M 2 (N/2)).testBit (n-1) = true :=
    M_testBit 2 (N/2) (n-1) (by norm_num) ⟨t, by omega⟩ (by omega)
  have maskfalse (xs : List ℕ) (hx : n ∉ xs) :
      (xs.foldr (fun a z => 2 ^ a ||| z) 0 : ℕ).testBit n = false := by
    induction xs with
    | nil => simp
    | cons a xs ih =>
      simp only [List.mem_cons, not_or] at hx
      simp [List.foldr, Nat.testBit_or, Ne.symm hx.1, ih hx.2]
  have miss : n ∉ points := by
    change n ∉ 1 :: _
    rw [List.mem_cons, not_or]
    exact ⟨by omega, outside⟩
  rw [Nat.testBit_and, Nat.testBit_shiftLeft, hM, maskfalse points miss] at hbit
  have hbad : (bad (ns 2235 ||| ns2 926) 5).testBit n = false := by
    have hn1 : decide (n ≥ 1) = true := by simp; omega
    rw [hn1] at hbit
    simpa using hbit
  obtain ⟨l, hl6, hl, hS⟩ := bad_false _ 5 n hbad
  have hsq : Squarefree (n - 2^l) := by
    by_contra hsf
    have := S_testBit (n - 2^l) (lt_of_le_of_lt (Nat.sub_le n _) hN) hsf
    rw [hS] at this
    exact Bool.false_ne_true this
  exact ⟨n - 2^l, l, hsq, (Nat.sub_add_cancel hl).symm, hl6⟩

/-- These are exactly the odd integers in the interval that require exponent six. -/
theorem requires_six_iff (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n) :
    (¬ ∃ k l : ℕ, Squarefree k ∧ n = k + 2^l ∧ l ≤ 5) ↔
      n ∈ ([434977, 618433, 2019077, 3231313, 4357229, 5826545, 5914757, 6261277, 7689677, 8016857, 8020177, 9121133, 9657377, 9835729, 9976579] : List ℕ) := by
  constructor
  · intro absent
    by_contra outside
    exact absent (finite_odd_five_outside n hn h hn' outside)
  · intro inside ⟨k, l, hk, he, hl⟩
    have exactList : ([434977, 618433, 2019077, 3231313, 4357229, 5826545, 5914757, 6261277, 7689677, 8016857, 8020177, 9121133, 9657377, 9835729, 9976579] : List ℕ).all (fun m =>
        (List.range 6).all (fun j => decide (¬ Squarefree (m - 2^j)))) = true := by decide +kernel
    have bad := (List.all_eq_true.mp (List.all_eq_true.mp exactList n inside)) l
      (List.mem_range.mpr (by omega))
    exact (of_decide_eq_true bad) (by simpa [he] using hk)

theorem finite_odd_six (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n) :
    ∃ k l : ℕ, Squarefree k ∧ n = k + 2^l ∧ l ≤ 6 := by
  by_cases inside : n ∈ ([434977, 618433, 2019077, 3231313, 4357229, 5826545, 5914757, 6261277, 7689677, 8016857, 8020177, 9121133, 9657377, 9835729, 9976579] : List ℕ)
  · have verified : ([434977, 618433, 2019077, 3231313, 4357229, 5826545, 5914757, 6261277, 7689677, 8016857, 8020177, 9121133, 9657377, 9835729, 9976579] : List ℕ).all (fun m =>
        decide (64 ≤ m ∧ Squarefree (m - 64))) = true := by decide +kernel
    obtain ⟨large, free⟩ := of_decide_eq_true (List.all_eq_true.mp verified n inside)
    exact ⟨n-64, 6, free, (Nat.sub_add_cancel large).symm, le_rfl⟩
  · obtain ⟨k, l, free, eq, bound⟩ := finite_odd_five_outside n hn h hn' inside
    exact ⟨k, l, free, eq, by omega⟩

theorem finite_odd (n : ℕ) (hn : Odd n) (h : n < 10^7) (hn' : 1 < n) :
    ∃ k l : ℕ, Squarefree k ∧ n = k + 2^l := by
  obtain ⟨k,l,hk,he,_⟩ := finite_odd_six n hn h hn'
  exact ⟨k,l,hk,he⟩

/-- The exponent bound is attained at the odd integer 9,976,579. -/
theorem six_necessary (k l : ℕ) (h : 9976579 = k + 2^l) (hs : Squarefree k) : 6 ≤ l := by
  by_contra! small
  have hk : k = 9976579 - 2^l := by omega
  subst k
  have free := Nat.squarefree_iff_prime_squarefree.mp hs
  interval_cases l
  · exact free 101 (by decide) (by decide)
  · exact free 13 (by decide) (by decide)
  · exact free 5 (by decide) (by decide)
  · exact free 11 (by decide) (by decide)
  · exact free 3 (by decide) (by decide)
  · exact free 7 (by decide) (by decide)

end OMA.E11

open Finset
namespace Erdos11Sieve

/-- The power sequence has precisely one exponent class for each residue it reaches. -/
theorem powers_same_class (m : ℕ) (cop : Nat.Coprime 2 m) (i j shift : ℕ) :
    2^(i+shift) ≡ 2^(j+shift) [MOD m] ↔
      i ≡ j [MOD orderOf (ZMod.unitOfCoprime 2 cop)] := by
  let u := ZMod.unitOfCoprime 2 cop
  have hu : (u : ZMod m) = 2 := by simp [u,ZMod.coe_unitOfCoprime]
  calc
    _ ↔ (u^(i+shift) : (ZMod m)ˣ) = u^(j+shift) := by
      rw [← ZMod.natCast_eq_natCast_iff, ← Units.val_inj]
      simp only [Nat.cast_pow,Nat.cast_ofNat,Units.val_pow_eq_pow_val,hu]
    _ ↔ u^i = u^j := by simp only [pow_add,mul_left_inj]
    _ ↔ _ := pow_eq_pow_iff_modEq

theorem one_class (m n shift : ℕ) (cop : Nat.Coprime 2 m) :
    (∀ j : ℕ, ¬ 2^(j+shift) ≡ n [MOD m]) ∨
      ∃ a : ℕ, ∀ j : ℕ, 2^(j+shift) ≡ n [MOD m] ↔ j ≡ a [MOD orderOf (ZMod.unitOfCoprime 2 cop)] := by
  classical
  by_cases h : ∃ a : ℕ, 2^(a+shift) ≡ n [MOD m]
  · obtain ⟨a,ha⟩ := h
    exact Or.inr ⟨a,fun j => ⟨fun hj => (powers_same_class m cop j a shift).mp (hj.trans ha.symm),
      fun hj => ((powers_same_class m cop j a shift).mpr hj).trans ha⟩⟩
  · exact Or.inl fun j hj => h ⟨j,hj⟩

/-- Sharp uniform upper bound: at most a ceiling number of congruence hits. -/
theorem one_class_bound (m n shift L : ℕ) [NeZero m] (cop : Nat.Coprime 2 m) :
    let r := orderOf (ZMod.unitOfCoprime 2 cop)
    ((range L).filter (fun j => 2^(j+shift) ≡ n [MOD m])).card ≤ L / r + if L % r = 0 then 0 else 1 := by
  intro r
  rcases one_class m n shift cop with absent | ⟨a,cls⟩
  · simp [Finset.filter_eq_empty_iff.mpr (fun j _ => absent j)]
  · have eq : ((range L).filter (fun j => 2^(j+shift) ≡ n [MOD m])) =
        (range L).filter (fun j => j ≡ a [MOD r]) := by
      ext j
      simp only [Finset.mem_filter,cls,r]
    rw [eq,← Nat.count_eq_card_filter_range, Nat.count_modEq_card _ (orderOf_pos _) a]
    dsimp only [r]
    split <;> split <;> omega

end Erdos11Sieve

open Finset
namespace Erdos11Sieve

theorem certify_order (m r : ℕ) (cop : Nat.Coprime 2 m) (hr : 0 < r)
    (one : 2^r ≡ 1 [MOD m]) (tests : ∀ p ∈ r.primeFactors, ¬ 2^(r/p) ≡ 1 [MOD m]) :
    orderOf (ZMod.unitOfCoprime 2 cop) = r := by
  let u := ZMod.unitOfCoprime 2 cop
  have criterion (j : ℕ) : u^j = 1 ↔ 2^j ≡ 1 [MOD m] := by
    rw [← Units.val_inj, ← ZMod.natCast_eq_natCast_iff]
    simp [u,ZMod.coe_unitOfCoprime]
  apply orderOf_eq_of_pow_and_pow_div_prime hr ((criterion _).mpr one)
  intro p prime divides pow_eq
  exact tests p (Nat.mem_primeFactors.mpr ⟨prime,divides,hr.ne'⟩) ((criterion _).mp pow_eq)

theorem period_bound (m r n shift L : ℕ) [NeZero m] (cop : Nat.Coprime 2 m)
    (hr : 0 < r) (one : 2^r ≡ 1 [MOD m]) (tests : ∀ p ∈ r.primeFactors, ¬ 2^(r/p) ≡ 1 [MOD m]) :
    ((range L).filter (fun j => 2^(j+shift) ≡ n [MOD m])).card ≤ L / r + 1 := by
  have h := one_class_bound m n shift L cop
  dsimp only at h
  rw [certify_order m r cop hr one tests] at h
  split at h <;> omega

theorem period_bound_finite (m r n shift L : ℕ) [NeZero m] (cop : Nat.Coprime 2 m)
    (hr : 0 < r) (one : 2^r ≡ 1 [MOD m])
    (tests : ∀ j : Fin r, 0 < j.val → ¬ 2^j.val ≡ 1 [MOD m]) :
    ((range L).filter (fun j => 2^(j+shift) ≡ n [MOD m])).card ≤ L / r + 1 := by
  apply period_bound m r _ _ _ cop hr one
  intro p hp
  obtain ⟨prime,dvd,_⟩ := Nat.mem_primeFactors.mp hp
  exact tests ⟨r/p,Nat.div_lt_self hr prime.one_lt⟩
    (Nat.div_pos (Nat.le_of_dvd hr dvd) prime.pos)

end Erdos11Sieve

open Finset
namespace Erdos11Sieve
theorem bound3 (n shift L : ℕ) : ((range L).filter fun j => 2^(j+shift) ≡ n [MOD 3^2]).card ≤ L / 6 + 1 :=
  period_bound_finite _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)

theorem bound5 (n shift L : ℕ) : ((range L).filter fun j => 2^(j+shift) ≡ n [MOD 5^2]).card ≤ L / 20 + 1 :=
  period_bound_finite _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)

theorem bound7 (n shift L : ℕ) : ((range L).filter fun j => 2^(j+shift) ≡ n [MOD 7^2]).card ≤ L / 21 + 1 :=
  period_bound_finite _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)

theorem bound11 (n shift L : ℕ) : ((range L).filter fun j => 2^(j+shift) ≡ n [MOD 11^2]).card ≤ L / 110 + 1 :=
  period_bound_finite _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)

theorem bound13 (n shift L : ℕ) : ((range L).filter fun j => 2^(j+shift) ≡ n [MOD 13^2]).card ≤ L / 156 + 1 :=
  period_bound_finite _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)

theorem bound17 (n shift L : ℕ) : ((range L).filter fun j => 2^(j+shift) ≡ n [MOD 17^2]).card ≤ L / 136 + 1 :=
  period_bound_finite _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 8192 in
theorem bound19 (n shift L : ℕ) : ((range L).filter fun j => 2^(j+shift) ≡ n [MOD 19^2]).card ≤ L / 342 + 1 := by
  apply period_bound _ _ _ _ _ (by decide) (by decide) _ ?_
  swap
  · intro p hmem
    obtain ⟨hp,divides,_⟩ := Nat.mem_primeFactors.mp hmem
    have bound := Nat.le_of_dvd (by decide : 0< 342) divides
    have checks : ∀q : Fin 343, 2≤ q.val → q.val∣ 342 → ¬ 2^(342/q.val) ≡ 1 [MOD 19^2] := by decide
    exact checks ⟨p,by omega⟩ hp.two_le divides
  have half : (2:ℕ)^171 ≡ 360 [MOD 19^2] := by decide
  rw [show (342:ℕ)=171+171 by decide,pow_add]
  exact (half.mul half).trans (by decide : 360*360 ≡ 1 [MOD 19^2])

set_option maxRecDepth 8192 in
theorem bound23 (n shift L : ℕ) : ((range L).filter fun j => 2^(j+shift) ≡ n [MOD 23^2]).card ≤ L / 253 + 1 :=
  period_bound_finite _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)

end Erdos11Sieve

open Finset
namespace Erdos11Sieve
theorem small_hit_bound (n shift L : ℕ) :
    let ps : Fin 8 → ℕ := ![3,5,7,11,13,17,19,23]
    let hits := (univ : Finset (Fin 8)).biUnion fun i =>
      (range L).filter fun j => 2^(j+shift) ≡ n [MOD (ps i)^2]
    10 * hits.card ≤ 3 * L + 80 := by
  intro ps hits
  let r : Fin 8 → ℕ := ![6,20,21,110,156,136,342,253]
  have each (i : Fin 8) : ((range L).filter (fun j => 2^(j+shift) ≡ n [MOD (ps i)^2])).card ≤ L / r i + 1 := by
    fin_cases i
    · exact bound3 n shift L
    · exact bound5 n shift L
    · exact bound7 n shift L
    · exact bound11 n shift L
    · exact bound13 n shift L
    · exact bound17 n shift L
    · exact bound19 n shift L
    · exact bound23 n shift L
  have ub : hits.card ≤ ∑ i : Fin 8, (L / r i + 1) :=
    (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun i _ => each i))
  simp [r,Fin.sum_univ_succ] at ub
  have d6 : 6 * (L / 6) ≤ L := Nat.mul_div_le L 6
  have d20 : 20 * (L / 20) ≤ L := Nat.mul_div_le L 20
  have d21 : 21 * (L / 21) ≤ L := Nat.mul_div_le L 21
  have d110 : 110 * (L / 110) ≤ L := Nat.mul_div_le L 110
  have d156 : 156 * (L / 156) ≤ L := Nat.mul_div_le L 156
  have d136 : 136 * (L / 136) ≤ L := Nat.mul_div_le L 136
  have d342 : 342 * (L / 342) ≤ L := Nat.mul_div_le L 342
  have d253 : 253 * (L / 253) ≤ L := Nat.mul_div_le L 253
  zify at ub ⊢
  linarith only [ub, d6, d20, d21, d110, d156, d136, d342, d253]


end Erdos11Sieve

open Finset
namespace Erdos11Sieve

/-- Enough positive powers surviving the large-square sieve give an exact representation. -/
theorem represent_of_large_hits (n L : ℕ) (odd : Odd n) (bound : 2^L < n) :
    let big := (range L).filter (fun j => ∃ p ∈ (range (n+1)).filter Nat.Prime,
      23 < p ∧ p^2 ∣ n - 2^(j+1))
    10 * big.card + 80 < 7*L → ∃ k l : ℕ, Squarefree k ∧ n = k + 2^l := by
  intro big enough
  let ps : Fin 8 → ℕ := ![3,5,7,11,13,17,19,23]
  let small := (univ : Finset (Fin 8)).biUnion fun i =>
    (range L).filter fun j => 2^(j+1) ≡ n [MOD (ps i)^2]
  have sb : 10 * small.card ≤ 3*L+80 := small_hit_bound n 1 L
  have uc := Finset.card_union_le small big
  have lt : (small ∪ big).card < (range L).card := by rw [card_range]; omega
  obtain ⟨j,hj,miss⟩ := Finset.exists_mem_notMem_of_card_lt_card lt
  have jlt := Finset.mem_range.mp hj
  have pl : 2^(j+1) < n := lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) (by omega : j+1≤ L)) bound
  refine ⟨n-2^(j+1),j+1,?_,by omega⟩
  apply Nat.squarefree_iff_prime_squarefree.mpr
  intro p prime divides
  have hp2 : p^2 ∣ n - 2^(j+1) := by simpa only [pow_two] using divides
  by_cases large : 23 < p
  · have p_le : p ≤ n := by
      have h := Nat.le_of_dvd (by omega : 0< n-2^(j+1))
        (dvd_trans (dvd_mul_right p p) divides)
      exact h.trans (Nat.sub_le _ _)
    apply miss
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hj,p,
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),prime⟩,large,hp2⟩)
  · have small_primes : ∀ a : Fin 24, a.val.Prime → a.val = 2 ∨ ∃ i, ps i = a.val := by decide
    rcases small_primes ⟨p,by omega⟩ prime with eq | ⟨i,ei⟩
    · obtain ⟨t,ht⟩ := odd
      change p=2 at eq
      subst p
      rw [pow_succ] at divides pl
      omega
    · apply miss
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      refine ⟨i,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hj,?_⟩⟩
      change ps i = p at ei
      rw [ei,Nat.modEq_iff_dvd' pl.le]
      exact hp2

end Erdos11Sieve

open Finset
namespace Erdos11Sieve

/-- A repeated hit is witnessed by a Mersenne multiple depending only on the exponent gap. -/
theorem collision_divides (m n i j shift : ℕ) (cop : Nat.Coprime 2 m) (ij : i ≤ j)
    (hi : 2^(i+shift) ≡ n [MOD m]) (hj : 2^(j+shift) ≡ n [MOD m]) :
    m ∣ 2^(j-i)-1 := by
  have h : 2^((j-i)+(i+shift)) ≡ 2^(0+(i+shift)) [MOD m] := by
    simpa only [show j-i+(i+shift) = j+shift by omega,zero_add] using hj.trans hi.symm
  have ord := (powers_same_class m cop (j-i) 0 (i+shift)).mp h
  have bin : 2^(j-i) ≡ 1 [MOD m] := by
    simpa only [add_zero,pow_zero] using (powers_same_class m cop (j-i) 0 0).mpr ord
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by decide))).mp bin.symm

theorem card_hits_le_one (m n shift L : ℕ) (cop : Nat.Coprime 2 m)
    (no_collision : ∀ gap : ℕ, 0 < gap → gap < L → ¬ m ∣ 2^gap-1) :
    ((range L).filter fun j => 2^(j+shift) ≡ n [MOD m]).card ≤ 1 := by
  refine Finset.card_le_one.mpr ?_
  intro i hi j hj
  obtain ⟨hiL,hi⟩ := Finset.mem_filter.mp hi
  obtain ⟨hjL,hj⟩ := Finset.mem_filter.mp hj
  simp only [Finset.mem_range] at hiL hjL
  rcases lt_trichotomy i j with lt | eq | gt
  · exact False.elim (no_collision (j-i) (by omega) (by omega)
      (collision_divides m n i j shift cop lt.le hi hj))
  · exact eq
  · exact False.elim (no_collision (i-j) (by omega) (by omega)
      (collision_divides m n j i shift cop gt.le hj hi))

end Erdos11Sieve

namespace Erdos11Sieve

theorem prime_in_factors (p : ℕ) (hp : p.Prime) (l : List ℕ) (prime : ∀ a ∈ l, a.Prime)
    (dvd : p ∣ l.prod) : p ∈ l := by
  induction l with
  | nil => exact (hp.not_dvd_one dvd).elim
  | cons a as ih =>
    rcases hp.dvd_mul.mp dvd with left | right
    · exact List.mem_cons.mpr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (prime a List.mem_cons_self)).mp left))
    · exact List.mem_cons.mpr (Or.inr (ih (fun b hb => prime b (List.mem_cons_of_mem _ hb)) right))

theorem fast_pow {M : Type} [Monoid M] (x : M) (e : ℕ) : x^e = npowBinRec e x := by
  change x ^ e = npowBinRecAuto e x
  rw [←npowRec_eq_npowBinRec]
  induction e with
  | zero => simp [npowRecAuto,npowRec]
  | succ e ih => rw [pow_succ,ih]; rfl

theorem certificate_prime (p : ℕ) (g : ZMod p) (l : List ℕ) (prod : l.prod=p-1)
    (primes : ∀ q ∈ l, q.Prime) (unit : npowBinRec (p-1) g=1)
    (order : ∀ q ∈ l, npowBinRec ((p-1)/q) g≠ 1) : p.Prime := by
  apply lucas_primality p g ((fast_pow _ _).trans unit)
  intro q hq hdiv
  rw [fast_pow]
  exact order q (prime_in_factors q hq l primes (prod ▸ hdiv))
end Erdos11Sieve

namespace Erdos11Sieve
theorem pc2 : Nat.Prime 2 := by norm_num1
theorem pc3 : Nat.Prime 3 := by norm_num1
theorem pc5 : Nat.Prime 5 := by norm_num1
theorem pc7 : Nat.Prime 7 := by norm_num1
theorem pc11 : Nat.Prime 11 := by norm_num1
theorem pc13 : Nat.Prime 13 := by norm_num1
theorem pc17 : Nat.Prime 17 := by norm_num1
theorem pc19 : Nat.Prime 19 := by norm_num1
theorem pc23 : Nat.Prime 23 := by norm_num1
theorem pc29 : Nat.Prime 29 := by norm_num1
theorem pc31 : Nat.Prime 31 := by norm_num1
theorem pc37 : Nat.Prime 37 := by norm_num1
theorem pc41 : Nat.Prime 41 := by norm_num1
theorem pc43 : Nat.Prime 43 := by norm_num1
theorem pc47 : Nat.Prime 47 := by norm_num1
theorem pc53 : Nat.Prime 53 := by norm_num1
theorem pc59 : Nat.Prime 59 := by norm_num1
theorem pc61 : Nat.Prime 61 := by norm_num1
theorem pc67 : Nat.Prime 67 := by norm_num1
theorem pc71 : Nat.Prime 71 := by norm_num1
theorem pc73 : Nat.Prime 73 := by norm_num1
theorem pc79 : Nat.Prime 79 := by norm_num1
theorem pc83 : Nat.Prime 83 := by norm_num1
theorem pc89 : Nat.Prime 89 := by norm_num1
theorem pc97 : Nat.Prime 97 := by norm_num1
theorem pc101 : Nat.Prime 101 := by norm_num1
theorem pc103 : Nat.Prime 103 := by norm_num1
theorem pc107 : Nat.Prime 107 := by norm_num1
theorem pc109 : Nat.Prime 109 := by norm_num1
theorem pc113 : Nat.Prime 113 := by norm_num1
theorem pc127 : Nat.Prime 127 := by norm_num1
theorem pc131 : Nat.Prime 131 := by norm_num1
theorem pc137 : Nat.Prime 137 := by norm_num1
theorem pc139 : Nat.Prime 139 := by norm_num1
theorem pc149 : Nat.Prime 149 := by norm_num1
theorem pc151 : Nat.Prime 151 := by norm_num1
theorem pc157 : Nat.Prime 157 := by norm_num1
theorem pc163 : Nat.Prime 163 := by norm_num1
theorem pc167 : Nat.Prime 167 := by norm_num1
theorem pc173 : Nat.Prime 173 := by norm_num1
theorem pc179 : Nat.Prime 179 := by norm_num1
theorem pc181 : Nat.Prime 181 := by norm_num1
theorem pc191 : Nat.Prime 191 := by norm_num1
theorem pc193 : Nat.Prime 193 := by norm_num1
theorem pc197 : Nat.Prime 197 := by norm_num1
theorem pc199 : Nat.Prime 199 := by norm_num1
theorem pc211 : Nat.Prime 211 := by norm_num1
theorem pc223 : Nat.Prime 223 := by norm_num1
theorem pc227 : Nat.Prime 227 := by norm_num1
theorem pc229 : Nat.Prime 229 := by norm_num1
theorem pc233 : Nat.Prime 233 := by norm_num1
theorem pc239 : Nat.Prime 239 := by norm_num1
theorem pc241 : Nat.Prime 241 := by norm_num1
theorem pc251 : Nat.Prime 251 := by norm_num1
theorem pc257 : Nat.Prime 257 := by norm_num1
theorem pc263 : Nat.Prime 263 := by norm_num1
theorem pc269 : Nat.Prime 269 := by norm_num1
theorem pc271 : Nat.Prime 271 := by norm_num1
theorem pc277 : Nat.Prime 277 := by norm_num1
theorem pc281 : Nat.Prime 281 := by norm_num1
theorem pc283 : Nat.Prime 283 := by norm_num1
theorem pc293 : Nat.Prime 293 := by norm_num1
theorem pc307 : Nat.Prime 307 := by norm_num1
theorem pc311 : Nat.Prime 311 := by norm_num1
theorem pc317 : Nat.Prime 317 := by norm_num1
theorem pc331 : Nat.Prime 331 := by norm_num1
theorem pc337 : Nat.Prime 337 := by norm_num1
theorem pc347 : Nat.Prime 347 := by norm_num1
theorem pc353 : Nat.Prime 353 := by norm_num1
theorem pc373 : Nat.Prime 373 := by norm_num1
theorem pc379 : Nat.Prime 379 := by norm_num1
theorem pc383 : Nat.Prime 383 := by norm_num1
theorem pc389 : Nat.Prime 389 := by norm_num1
theorem pc397 : Nat.Prime 397 := by norm_num1
theorem pc421 : Nat.Prime 421 := by norm_num1
theorem pc431 : Nat.Prime 431 := by norm_num1
theorem pc433 : Nat.Prime 433 := by norm_num1
theorem pc439 : Nat.Prime 439 := by norm_num1
theorem pc443 : Nat.Prime 443 := by norm_num1
theorem pc457 : Nat.Prime 457 := by norm_num1
theorem pc509 : Nat.Prime 509 := by norm_num1
theorem pc547 : Nat.Prime 547 := by norm_num1
theorem pc569 : Nat.Prime 569 := by norm_num1
theorem pc571 : Nat.Prime 571 := by norm_num1
theorem pc577 : Nat.Prime 577 := by norm_num1
theorem pc593 : Nat.Prime 593 := by norm_num1
theorem pc599 : Nat.Prime 599 := by norm_num1
theorem pc601 : Nat.Prime 601 := by norm_num1
theorem pc613 : Nat.Prime 613 := by norm_num1
theorem pc617 : Nat.Prime 617 := by norm_num1
theorem pc631 : Nat.Prime 631 := by norm_num1
theorem pc641 : Nat.Prime 641 := by norm_num1
theorem pc643 : Nat.Prime 643 := by norm_num1
theorem pc653 : Nat.Prime 653 := by norm_num1
theorem pc659 : Nat.Prime 659 := by norm_num1
theorem pc673 : Nat.Prime 673 := by norm_num1
theorem pc683 : Nat.Prime 683 := by norm_num1
theorem pc709 : Nat.Prime 709 := by norm_num1
theorem pc727 : Nat.Prime 727 := by norm_num1
theorem pc757 : Nat.Prime 757 := by norm_num1
theorem pc761 : Nat.Prime 761 := by norm_num1
theorem pc787 : Nat.Prime 787 := by norm_num1
theorem pc797 : Nat.Prime 797 := by norm_num1
theorem pc809 : Nat.Prime 809 := by norm_num1
theorem pc811 : Nat.Prime 811 := by norm_num1
theorem pc821 : Nat.Prime 821 := by norm_num1
theorem pc823 : Nat.Prime 823 := by norm_num1
theorem pc853 : Nat.Prime 853 := by norm_num1
theorem pc859 : Nat.Prime 859 := by norm_num1
theorem pc877 : Nat.Prime 877 := by norm_num1
theorem pc881 : Nat.Prime 881 := by norm_num1
theorem pc911 : Nat.Prime 911 := by norm_num1
theorem pc919 : Nat.Prime 919 := by norm_num1
theorem pc937 : Nat.Prime 937 := by norm_num1
theorem pc953 : Nat.Prime 953 := by norm_num1
theorem pc991 : Nat.Prime 991 := by norm_num1
theorem pc1013 : Nat.Prime 1013 := by norm_num1
theorem pc1033 : Nat.Prime 1033 := by norm_num1
theorem pc1039 : Nat.Prime 1039 := by norm_num1
theorem pc1051 : Nat.Prime 1051 := by norm_num1
theorem pc1091 : Nat.Prime 1091 := by norm_num1
theorem pc1097 : Nat.Prime 1097 := by norm_num1
theorem pc1103 : Nat.Prime 1103 := by norm_num1
theorem pc1123 : Nat.Prime 1123 := by norm_num1
theorem pc1193 : Nat.Prime 1193 := by norm_num1
theorem pc1217 : Nat.Prime 1217 := by norm_num1
theorem pc1223 : Nat.Prime 1223 := by norm_num1
theorem pc1231 : Nat.Prime 1231 := by norm_num1
theorem pc1237 : Nat.Prime 1237 := by norm_num1
theorem pc1277 : Nat.Prime 1277 := by norm_num1
theorem pc1289 : Nat.Prime 1289 := by norm_num1
theorem pc1297 : Nat.Prime 1297 := by norm_num1
theorem pc1321 : Nat.Prime 1321 := by norm_num1
theorem pc1361 : Nat.Prime 1361 := by norm_num1
theorem pc1429 : Nat.Prime 1429 := by norm_num1
theorem pc1451 : Nat.Prime 1451 := by norm_num1
theorem pc1543 : Nat.Prime 1543 := by norm_num1
theorem pc1549 : Nat.Prime 1549 := by norm_num1
theorem pc1571 : Nat.Prime 1571 := by norm_num1
theorem pc1579 : Nat.Prime 1579 := by norm_num1
theorem pc1609 : Nat.Prime 1609 := by norm_num1
theorem pc1613 : Nat.Prime 1613 := by norm_num1
theorem pc1627 : Nat.Prime 1627 := by norm_num1
theorem pc1657 : Nat.Prime 1657 := by norm_num1
theorem pc1709 : Nat.Prime 1709 := by norm_num1
theorem pc1747 : Nat.Prime 1747 := by norm_num1
theorem pc1753 : Nat.Prime 1753 := by norm_num1
theorem pc1777 : Nat.Prime 1777 := by norm_num1
theorem pc1801 : Nat.Prime 1801 := by norm_num1
theorem pc1861 : Nat.Prime 1861 := by norm_num1
theorem pc1913 : Nat.Prime 1913 := by norm_num1
theorem pc1973 : Nat.Prime 1973 := by norm_num1
theorem pc2087 : Nat.Prime 2087 := by norm_num1
theorem pc2089 : Nat.Prime 2089 := by norm_num1
theorem pc2113 : Nat.Prime 2113 := by norm_num1
theorem pc2143 : Nat.Prime 2143 := by norm_num1
theorem pc2179 : Nat.Prime 2179 := by norm_num1
theorem pc2297 : Nat.Prime 2297 := by norm_num1
theorem pc2309 : Nat.Prime 2309 := by norm_num1
theorem pc2351 : Nat.Prime 2351 := by norm_num1
theorem pc2437 : Nat.Prime 2437 := by norm_num1
theorem pc2503 : Nat.Prime 2503 := by norm_num1
theorem pc2531 : Nat.Prime 2531 := by norm_num1
theorem pc2551 : Nat.Prime 2551 := by norm_num1
theorem pc2593 : Nat.Prime 2593 := by norm_num1
theorem pc2647 : Nat.Prime 2647 := by norm_num1
theorem pc2677 : Nat.Prime 2677 := by norm_num1
theorem pc2687 : Nat.Prime 2687 := by norm_num1
theorem pc2713 : Nat.Prime 2713 := by norm_num1
theorem pc2731 : Nat.Prime 2731 := by norm_num1
theorem pc2833 : Nat.Prime 2833 := by norm_num1
theorem pc2857 : Nat.Prime 2857 := by norm_num1
theorem pc2887 : Nat.Prime 2887 := by norm_num1
theorem pc2971 : Nat.Prime 2971 := by norm_num1
theorem pc3191 : Nat.Prime 3191 := by norm_num1
theorem pc3391 : Nat.Prime 3391 := by norm_num1
theorem pc3557 : Nat.Prime 3557 := by norm_num1
theorem pc3581 : Nat.Prime 3581 := by norm_num1
theorem pc4049 : Nat.Prime 4049 := by norm_num1
theorem pc4051 : Nat.Prime 4051 := by norm_num1
theorem pc4177 : Nat.Prime 4177 := by norm_num1
theorem pc4217 : Nat.Prime 4217 := by norm_num1
theorem pc4273 : Nat.Prime 4273 := by norm_num1
theorem pc4513 : Nat.Prime 4513 := by norm_num1
theorem pc4657 : Nat.Prime 4657 := by norm_num1
theorem pc4703 : Nat.Prime 4703 := by norm_num1
theorem pc5077 : Nat.Prime 5077 := by norm_num1
theorem pc5153 : Nat.Prime 5153 := by norm_num1
theorem pc5381 : Nat.Prime 5381 := by norm_num1
theorem pc5399 : Nat.Prime 5399 := by norm_num1
theorem pc5419 : Nat.Prime 5419 := by norm_num1
theorem pc5581 : Nat.Prime 5581 := by norm_num1
theorem pc6113 : Nat.Prime 6113 := by norm_num1
theorem pc6247 : Nat.Prime 6247 := by norm_num1
theorem pc6361 : Nat.Prime 6361 := by norm_num1
theorem pc6451 : Nat.Prime 6451 := by norm_num1
theorem pc6529 : Nat.Prime 6529 := by norm_num1
theorem pc6553 : Nat.Prime 6553 := by norm_num1
theorem pc6709 : Nat.Prime 6709 := by norm_num1
theorem pc7109 : Nat.Prime 7109 := by norm_num1
theorem pc7331 : Nat.Prime 7331 := by norm_num1
theorem pc7349 : Nat.Prime 7349 := by norm_num1
theorem pc7451 : Nat.Prime 7451 := by norm_num1
theorem pc7673 : Nat.Prime 7673 := by norm_num1
theorem pc8101 : Nat.Prime 8101 := by norm_num1
theorem pc8191 : Nat.Prime 8191 := by norm_num1
theorem pc8501 : Nat.Prime 8501 := by norm_num1
theorem pc8539 : Nat.Prime 8539 := by norm_num1
theorem pc8641 : Nat.Prime 8641 := by norm_num1
theorem pc8681 : Nat.Prime 8681 := by norm_num1
theorem pc8707 : Nat.Prime 8707 := by norm_num1
theorem pc8779 : Nat.Prime 8779 := by norm_num1
theorem pc8963 : Nat.Prime 8963 := by norm_num1
theorem pc9719 : Nat.Prime 9719 := by norm_num1
theorem pc10223 : Nat.Prime 10223 := by
  apply certificate_prime 10223 (5 : ZMod 10223) [2,19,269] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc19,pc269]
theorem pc10513 : Nat.Prime 10513 := by
  apply certificate_prime 10513 (7 : ZMod 10513) [2,2,2,2,3,3,73] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc73]
theorem pc10639 : Nat.Prime 10639 := by
  apply certificate_prime 10639 (6 : ZMod 10639) [2,3,3,3,197] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc197]
theorem pc10889 : Nat.Prime 10889 := by
  apply certificate_prime 10889 (3 : ZMod 10889) [2,2,2,1361] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc1361]
theorem pc11119 : Nat.Prime 11119 := by
  apply certificate_prime 11119 (3 : ZMod 11119) [2,3,17,109] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc17,pc109]
theorem pc11177 : Nat.Prime 11177 := by
  apply certificate_prime 11177 (3 : ZMod 11177) [2,2,2,11,127] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc11,pc127]
theorem pc11329 : Nat.Prime 11329 := by
  apply certificate_prime 11329 (7 : ZMod 11329) [2,2,2,2,2,2,3,59] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc59]
theorem pc11447 : Nat.Prime 11447 := by
  apply certificate_prime 11447 (5 : ZMod 11447) [2,59,97] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc59,pc97]
theorem pc12329 : Nat.Prime 12329 := by
  apply certificate_prime 12329 (3 : ZMod 12329) [2,2,2,23,67] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc23,pc67]
theorem pc12377 : Nat.Prime 12377 := by
  apply certificate_prime 12377 (6 : ZMod 12377) [2,2,2,7,13,17] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc7,pc13,pc17]
theorem pc12959 : Nat.Prime 12959 := by
  apply certificate_prime 12959 (7 : ZMod 12959) [2,11,19,31] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc11,pc19,pc31]
theorem pc13049 : Nat.Prime 13049 := by
  apply certificate_prime 13049 (3 : ZMod 13049) [2,2,2,7,233] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc7,pc233]
theorem pc13367 : Nat.Prime 13367 := by
  apply certificate_prime 13367 (5 : ZMod 13367) [2,41,163] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc41,pc163]
theorem pc14449 : Nat.Prime 14449 := by
  apply certificate_prime 14449 (22 : ZMod 14449) [2,2,2,2,3,7,43] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc7,pc43]
theorem pc14713 : Nat.Prime 14713 := by
  apply certificate_prime 14713 (5 : ZMod 14713) [2,2,2,3,613] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc613]
theorem pc14951 : Nat.Prime 14951 := by
  apply certificate_prime 14951 (19 : ZMod 14951) [2,5,5,13,23] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc13,pc23]
theorem pc15107 : Nat.Prime 15107 := by
  apply certificate_prime 15107 (2 : ZMod 15107) [2,7,13,83] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc7,pc13,pc83]
theorem pc15271 : Nat.Prime 15271 := by
  apply certificate_prime 15271 (11 : ZMod 15271) [2,3,5,509] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc509]
theorem pc16657 : Nat.Prime 16657 := by
  apply certificate_prime 16657 (5 : ZMod 16657) [2,2,2,2,3,347] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc347]
theorem pc17093 : Nat.Prime 17093 := by
  apply certificate_prime 17093 (2 : ZMod 17093) [2,2,4273] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc4273]
theorem pc17191 : Nat.Prime 17191 := by
  apply certificate_prime 17191 (3 : ZMod 17191) [2,3,3,5,191] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc191]
theorem pc17449 : Nat.Prime 17449 := by
  apply certificate_prime 17449 (14 : ZMod 17449) [2,2,2,3,727] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc727]
theorem pc18121 : Nat.Prime 18121 := by
  apply certificate_prime 18121 (23 : ZMod 18121) [2,2,2,3,5,151] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc151]
theorem pc18199 : Nat.Prime 18199 := by
  apply certificate_prime 18199 (11 : ZMod 18199) [2,3,3,3,337] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc337]
theorem pc19333 : Nat.Prime 19333 := by
  apply certificate_prime 19333 (2 : ZMod 19333) [2,2,3,3,3,179] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc179]
theorem pc19457 : Nat.Prime 19457 := by
  apply certificate_prime 19457 (3 : ZMod 19457) [2,2,2,2,2,2,2,2,2,2,19] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc19]
theorem pc20231 : Nat.Prime 20231 := by
  apply certificate_prime 20231 (29 : ZMod 20231) [2,5,7,17,17] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc7,pc17]
theorem pc20261 : Nat.Prime 20261 := by
  apply certificate_prime 20261 (2 : ZMod 20261) [2,2,5,1013] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc1013]
theorem pc20857 : Nat.Prime 20857 := by
  apply certificate_prime 20857 (10 : ZMod 20857) [2,2,2,3,11,79] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc11,pc79]
theorem pc20897 : Nat.Prime 20897 := by
  apply certificate_prime 20897 (3 : ZMod 20897) [2,2,2,2,2,653] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc653]
theorem pc21487 : Nat.Prime 21487 := by
  apply certificate_prime 21487 (3 : ZMod 21487) [2,3,3581] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc3581]
theorem pc22247 : Nat.Prime 22247 := by
  apply certificate_prime 22247 (5 : ZMod 22247) [2,7,7,227] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc7,pc227]
theorem pc23279 : Nat.Prime 23279 := by
  apply certificate_prime 23279 (7 : ZMod 23279) [2,103,113] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc103,pc113]
theorem pc23311 : Nat.Prime 23311 := by
  apply certificate_prime 23311 (3 : ZMod 23311) [2,3,3,5,7,37] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc7,pc37]
theorem pc23761 : Nat.Prime 23761 := by
  apply certificate_prime 23761 (7 : ZMod 23761) [2,2,2,2,3,3,3,5,11] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc11]
theorem pc26099 : Nat.Prime 26099 := by
  apply certificate_prime 26099 (2 : ZMod 26099) [2,13049] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc13049]
theorem pc26317 : Nat.Prime 26317 := by
  apply certificate_prime 26317 (6 : ZMod 26317) [2,2,3,3,17,43] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc17,pc43]
theorem pc27409 : Nat.Prime 27409 := by
  apply certificate_prime 27409 (13 : ZMod 27409) [2,2,2,2,3,571] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc571]
theorem pc27953 : Nat.Prime 27953 := by
  apply certificate_prime 27953 (3 : ZMod 27953) [2,2,2,2,1747] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc1747]
theorem pc28571 : Nat.Prime 28571 := by
  apply certificate_prime 28571 (2 : ZMod 28571) [2,5,2857] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc2857]
theorem pc28751 : Nat.Prime 28751 := by
  apply certificate_prime 28751 (14 : ZMod 28751) [2,5,5,5,5,23] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc23]
theorem pc29191 : Nat.Prime 29191 := by
  apply certificate_prime 29191 (7 : ZMod 29191) [2,3,5,7,139] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc7,pc139]
theorem pc30269 : Nat.Prime 30269 := by
  apply certificate_prime 30269 (3 : ZMod 30269) [2,2,7,23,47] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc7,pc23,pc47]
theorem pc31981 : Nat.Prime 31981 := by
  apply certificate_prime 31981 (6 : ZMod 31981) [2,2,3,5,13,41] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc13,pc41]
theorem pc32377 : Nat.Prime 32377 := by
  apply certificate_prime 32377 (5 : ZMod 32377) [2,2,2,3,19,71] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc19,pc71]
theorem pc33791 : Nat.Prime 33791 := by
  apply certificate_prime 33791 (7 : ZMod 33791) [2,5,31,109] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc31,pc109]
theorem pc37171 : Nat.Prime 37171 := by
  apply certificate_prime 37171 (3 : ZMod 37171) [2,3,3,5,7,59] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc7,pc59]
theorem pc37991 : Nat.Prime 37991 := by
  apply certificate_prime 37991 (7 : ZMod 37991) [2,5,29,131] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc29,pc131]
theorem pc38737 : Nat.Prime 38737 := by
  apply certificate_prime 38737 (5 : ZMod 38737) [2,2,2,2,3,3,269] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc269]
theorem pc43691 : Nat.Prime 43691 := by
  apply certificate_prime 43691 (6 : ZMod 43691) [2,5,17,257] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc17,pc257]
theorem pc43987 : Nat.Prime 43987 := by
  apply certificate_prime 43987 (2 : ZMod 43987) [2,3,7331] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc7331]
theorem pc44029 : Nat.Prime 44029 := by
  apply certificate_prime 44029 (6 : ZMod 44029) [2,2,3,3,1223] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc1223]
theorem pc45317 : Nat.Prime 45317 := by
  apply certificate_prime 45317 (2 : ZMod 45317) [2,2,11329] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc11329]
theorem pc49477 : Nat.Prime 49477 := by
  apply certificate_prime 49477 (11 : ZMod 49477) [2,2,3,7,19,31] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc7,pc19,pc31]
theorem pc49481 : Nat.Prime 49481 := by
  apply certificate_prime 49481 (3 : ZMod 49481) [2,2,2,5,1237] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc1237]
theorem pc51871 : Nat.Prime 51871 := by
  apply certificate_prime 51871 (7 : ZMod 51871) [2,3,5,7,13,19] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc7,pc13,pc19]
theorem pc55829 : Nat.Prime 55829 := by
  apply certificate_prime 55829 (2 : ZMod 55829) [2,2,17,821] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc17,pc821]
theorem pc55871 : Nat.Prime 55871 := by
  apply certificate_prime 55871 (7 : ZMod 55871) [2,5,37,151] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc37,pc151]
theorem pc58481 : Nat.Prime 58481 := by
  apply certificate_prime 58481 (6 : ZMod 58481) [2,2,2,2,5,17,43] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc17,pc43]
theorem pc59497 : Nat.Prime 59497 := by
  apply certificate_prime 59497 (15 : ZMod 59497) [2,2,2,3,37,67] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc37,pc67]
theorem pc60889 : Nat.Prime 60889 := by
  apply certificate_prime 60889 (21 : ZMod 60889) [2,2,2,3,43,59] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc43,pc59]
theorem pc61681 : Nat.Prime 61681 := by
  apply certificate_prime 61681 (29 : ZMod 61681) [2,2,2,2,3,5,257] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc257]
theorem pc65537 : Nat.Prime 65537 := by
  apply certificate_prime 65537 (3 : ZMod 65537) [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2] (by decide) ?_ (by decide) (by decide)
  simp [pc2]
theorem pc65993 : Nat.Prime 65993 := by
  apply certificate_prime 65993 (3 : ZMod 65993) [2,2,2,73,113] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc73,pc113]
theorem pc69431 : Nat.Prime 69431 := by
  apply certificate_prime 69431 (13 : ZMod 69431) [2,5,53,131] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc53,pc131]
theorem pc70687 : Nat.Prime 70687 := by
  apply certificate_prime 70687 (5 : ZMod 70687) [2,3,3,3,7,11,17] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc7,pc11,pc17]
theorem pc71119 : Nat.Prime 71119 := by
  apply certificate_prime 71119 (3 : ZMod 71119) [2,3,3,3,3,439] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc439]
theorem pc71429 : Nat.Prime 71429 := by
  apply certificate_prime 71429 (2 : ZMod 71429) [2,2,7,2551] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc7,pc2551]
theorem pc75983 : Nat.Prime 75983 := by
  apply certificate_prime 75983 (5 : ZMod 75983) [2,37991] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc37991]
theorem pc78233 : Nat.Prime 78233 := by
  apply certificate_prime 78233 (3 : ZMod 78233) [2,2,2,7,11,127] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc7,pc11,pc127]
theorem pc79241 : Nat.Prime 79241 := by
  apply certificate_prime 79241 (3 : ZMod 79241) [2,2,2,5,7,283] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc7,pc283]
theorem pc85607 : Nat.Prime 85607 := by
  apply certificate_prime 85607 (5 : ZMod 85607) [2,23,1861] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc23,pc1861]
theorem pc86113 : Nat.Prime 86113 := by
  apply certificate_prime 86113 (5 : ZMod 86113) [2,2,2,2,2,3,3,13,23] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc13,pc23]
theorem pc86171 : Nat.Prime 86171 := by
  apply certificate_prime 86171 (7 : ZMod 86171) [2,5,7,1231] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc7,pc1231]
theorem pc87211 : Nat.Prime 87211 := by
  apply certificate_prime 87211 (13 : ZMod 87211) [2,3,3,3,5,17,19] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc17,pc19]
theorem pc92737 : Nat.Prime 92737 := by
  apply certificate_prime 92737 (5 : ZMod 92737) [2,2,2,2,2,2,3,3,7,23] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc7,pc23]
theorem pc100801 : Nat.Prime 100801 := by
  apply certificate_prime 100801 (11 : ZMod 100801) [2,2,2,2,2,2,3,3,5,5,7] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc7]
theorem pc102103 : Nat.Prime 102103 := by
  apply certificate_prime 102103 (5 : ZMod 102103) [2,3,7,11,13,17] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc7,pc11,pc13,pc17]
theorem pc106681 : Nat.Prime 106681 := by
  apply certificate_prime 106681 (23 : ZMod 106681) [2,2,2,3,5,7,127] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc7,pc127]
theorem pc107621 : Nat.Prime 107621 := by
  apply certificate_prime 107621 (2 : ZMod 107621) [2,2,5,5381] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc5381]
theorem pc108643 : Nat.Prime 108643 := by
  apply certificate_prime 108643 (5 : ZMod 108643) [2,3,19,953] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc19,pc953]
theorem pc108943 : Nat.Prime 108943 := by
  apply certificate_prime 108943 (3 : ZMod 108943) [2,3,67,271] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc67,pc271]
theorem pc115903 : Nat.Prime 115903 := by
  apply certificate_prime 115903 (3 : ZMod 115903) [2,3,3,47,137] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc47,pc137]
theorem pc116131 : Nat.Prime 116131 := by
  apply certificate_prime 116131 (2 : ZMod 116131) [2,3,5,7,7,79] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc7,pc79]
theorem pc121369 : Nat.Prime 121369 := by
  apply certificate_prime 121369 (7 : ZMod 121369) [2,2,2,3,13,389] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc13,pc389]
theorem pc122921 : Nat.Prime 122921 := by
  apply certificate_prime 122921 (3 : ZMod 122921) [2,2,2,5,7,439] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc7,pc439]
theorem pc131071 : Nat.Prime 131071 := by
  apply certificate_prime 131071 (3 : ZMod 131071) [2,3,5,17,257] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc17,pc257]
theorem pc148961 : Nat.Prime 148961 := by
  apply certificate_prime 148961 (3 : ZMod 148961) [2,2,2,2,2,5,7,7,19] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc7,pc19]
theorem pc152041 : Nat.Prime 152041 := by
  apply certificate_prime 152041 (11 : ZMod 152041) [2,2,2,3,5,7,181] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc7,pc181]
theorem pc153649 : Nat.Prime 153649 := by
  apply certificate_prime 153649 (7 : ZMod 153649) [2,2,2,2,3,3,11,97] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc11,pc97]
theorem pc155539 : Nat.Prime 155539 := by
  apply certificate_prime 155539 (2 : ZMod 155539) [2,3,3,8641] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc8641]
theorem pc165799 : Nat.Prime 165799 := by
  apply certificate_prime 165799 (7 : ZMod 165799) [2,3,3,61,151] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc61,pc151]
theorem pc166571 : Nat.Prime 166571 := by
  apply certificate_prime 166571 (2 : ZMod 166571) [2,5,16657] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc16657]
theorem pc174763 : Nat.Prime 174763 := by
  apply certificate_prime 174763 (17 : ZMod 174763) [2,3,3,7,19,73] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc7,pc19,pc73]
theorem pc175949 : Nat.Prime 175949 := by
  apply certificate_prime 175949 (2 : ZMod 175949) [2,2,43987] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc43987]
theorem pc178481 : Nat.Prime 178481 := by
  apply certificate_prime 178481 (3 : ZMod 178481) [2,2,2,2,5,23,97] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc23,pc97]
theorem pc179951 : Nat.Prime 179951 := by
  apply certificate_prime 179951 (7 : ZMod 179951) [2,5,5,59,61] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc59,pc61]
theorem pc184711 : Nat.Prime 184711 := by
  apply certificate_prime 184711 (3 : ZMod 184711) [2,3,5,47,131] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc47,pc131]
theorem pc190699 : Nat.Prime 190699 := by
  apply certificate_prime 190699 (2 : ZMod 190699) [2,3,37,859] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc37,pc859]
theorem pc195241 : Nat.Prime 195241 := by
  apply certificate_prime 195241 (11 : ZMod 195241) [2,2,2,3,5,1627] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc1627]
theorem pc195677 : Nat.Prime 195677 := by
  apply certificate_prime 195677 (2 : ZMod 195677) [2,2,13,53,71] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc13,pc53,pc71]
theorem pc196271 : Nat.Prime 196271 := by
  apply certificate_prime 196271 (11 : ZMod 196271) [2,5,19,1033] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc19,pc1033]
theorem pc201961 : Nat.Prime 201961 := by
  apply certificate_prime 201961 (13 : ZMod 201961) [2,2,2,3,3,3,5,11,17] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc11,pc17]
theorem pc220553 : Nat.Prime 220553 := by
  apply certificate_prime 220553 (3 : ZMod 220553) [2,2,2,19,1451] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc19,pc1451]
theorem pc227489 : Nat.Prime 227489 := by
  apply certificate_prime 227489 (3 : ZMod 227489) [2,2,2,2,2,7109] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc7109]
theorem pc228479 : Nat.Prime 228479 := by
  apply certificate_prime 228479 (11 : ZMod 228479) [2,71,1609] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc71,pc1609]
theorem pc246241 : Nat.Prime 246241 := by
  apply certificate_prime 246241 (11 : ZMod 246241) [2,2,2,2,2,3,3,3,3,5,19] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc19]
theorem pc252313 : Nat.Prime 252313 := by
  apply certificate_prime 252313 (5 : ZMod 252313) [2,2,2,3,10513] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc10513]
theorem pc257219 : Nat.Prime 257219 := by
  apply certificate_prime 257219 (2 : ZMod 257219) [2,13,13,761] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc13,pc761]
theorem pc262657 : Nat.Prime 262657 := by
  apply certificate_prime 262657 (5 : ZMod 262657) [2,2,2,2,2,2,2,2,2,3,3,3,19] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc19]
theorem pc268501 : Nat.Prime 268501 := by
  apply certificate_prime 268501 (6 : ZMod 268501) [2,2,3,5,5,5,179] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc179]
theorem pc274177 : Nat.Prime 274177 := by
  apply certificate_prime 274177 (5 : ZMod 274177) [2,2,2,2,2,2,2,2,3,3,7,17] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc7,pc17]
theorem pc278557 : Nat.Prime 278557 := by
  apply certificate_prime 278557 (2 : ZMod 278557) [2,2,3,139,167] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc139,pc167]
theorem pc279073 : Nat.Prime 279073 := by
  apply certificate_prime 279073 (10 : ZMod 279073) [2,2,2,2,2,3,3,3,17,19] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc17,pc19]
theorem pc312709 : Nat.Prime 312709 := by
  apply certificate_prime 312709 (7 : ZMod 312709) [2,2,3,11,23,103] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc11,pc23,pc103]
theorem pc321679 : Nat.Prime 321679 := by
  apply certificate_prime 321679 (3 : ZMod 321679) [2,3,3,3,7,23,37] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc7,pc23,pc37]
theorem pc344263 : Nat.Prime 344263 := by
  apply certificate_prime 344263 (6 : ZMod 344263) [2,3,181,317] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc181,pc317]
theorem pc348031 : Nat.Prime 348031 := by
  apply certificate_prime 348031 (3 : ZMod 348031) [2,3,3,3,5,1289] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc1289]
theorem pc350887 : Nat.Prime 350887 := by
  apply certificate_prime 350887 (5 : ZMod 350887) [2,3,58481] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc58481]
theorem pc354689 : Nat.Prime 354689 := by
  apply certificate_prime 354689 (3 : ZMod 354689) [2,2,2,2,2,2,2,17,163] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc17,pc163]
theorem pc384773 : Nat.Prime 384773 := by
  apply certificate_prime 384773 (3 : ZMod 384773) [2,2,29,31,107] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc29,pc31,pc107]
theorem pc397073 : Nat.Prime 397073 := by
  apply certificate_prime 397073 (3 : ZMod 397073) [2,2,2,2,13,23,83] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc13,pc23,pc83]
theorem pc409891 : Nat.Prime 409891 := by
  apply certificate_prime 409891 (14 : ZMod 409891) [2,3,5,13,1051] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc13,pc1051]
theorem pc483869 : Nat.Prime 483869 := by
  apply certificate_prime 483869 (2 : ZMod 483869) [2,2,7,11,1571] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc7,pc11,pc1571]
theorem pc521981 : Nat.Prime 521981 := by
  apply certificate_prime 521981 (2 : ZMod 521981) [2,2,5,26099] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc26099]
theorem pc524287 : Nat.Prime 524287 := by
  apply certificate_prime 524287 (3 : ZMod 524287) [2,3,3,3,7,19,73] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc7,pc19,pc73]
theorem pc525313 : Nat.Prime 525313 := by
  apply certificate_prime 525313 (5 : ZMod 525313) [2,2,2,2,2,2,2,2,2,2,3,3,3,19] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc19]
theorem pc587897 : Nat.Prime 587897 := by
  apply certificate_prime 587897 (3 : ZMod 587897) [2,2,2,43,1709] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc43,pc1709]
theorem pc599479 : Nat.Prime 599479 := by
  apply certificate_prime 599479 (6 : ZMod 599479) [2,3,11,31,293] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc11,pc31,pc293]
theorem pc602999 : Nat.Prime 602999 := by
  apply certificate_prime 602999 (11 : ZMod 602999) [2,11,27409] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc11,pc27409]
theorem pc649657 : Nat.Prime 649657 := by
  apply certificate_prime 649657 (5 : ZMod 649657) [2,2,2,3,3,7,1289] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc7,pc1289]
theorem pc660071 : Nat.Prime 660071 := by
  apply certificate_prime 660071 (11 : ZMod 660071) [2,5,149,443] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc149,pc443]
theorem pc684857 : Nat.Prime 684857 := by
  apply certificate_prime 684857 (3 : ZMod 684857) [2,2,2,85607] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc85607]
theorem pc699053 : Nat.Prime 699053 := by
  apply certificate_prime 699053 (2 : ZMod 699053) [2,2,174763] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc174763]
theorem pc724153 : Nat.Prime 724153 := by
  apply certificate_prime 724153 (5 : ZMod 724153) [2,2,2,3,11,13,211] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc11,pc13,pc211]
theorem pc838631 : Nat.Prime 838631 := by
  apply certificate_prime 838631 (31 : ZMod 838631) [2,5,13,6451] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc13,pc6451]
theorem pc842887 : Nat.Prime 842887 := by
  apply certificate_prime 842887 (3 : ZMod 842887) [2,3,3,3,3,11,11,43] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc11,pc43]
theorem pc858001 : Nat.Prime 858001 := by
  apply certificate_prime 858001 (17 : ZMod 858001) [2,2,2,2,3,5,5,5,11,13] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc11,pc13]
theorem pc860969 : Nat.Prime 860969 := by
  apply certificate_prime 860969 (3 : ZMod 860969) [2,2,2,107621] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc107621]
theorem pc1058389 : Nat.Prime 1058389 := by
  apply certificate_prime 1058389 (2 : ZMod 1058389) [2,2,3,89,991] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc89,pc991]
theorem pc1205951 : Nat.Prime 1205951 := by
  apply certificate_prime 1205951 (13 : ZMod 1205951) [2,5,5,89,271] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc89,pc271]
theorem pc1212847 : Nat.Prime 1212847 := by
  apply certificate_prime 1212847 (5 : ZMod 1212847) [2,3,19,10639] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc19,pc10639]
theorem pc1238789 : Nat.Prime 1238789 := by
  apply certificate_prime 1238789 (2 : ZMod 1238789) [2,2,61,5077] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc61,pc5077]
theorem pc1310329 : Nat.Prime 1310329 := by
  apply certificate_prime 1310329 (7 : ZMod 1310329) [2,2,2,3,3,18199] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc18199]
theorem pc1868569 : Nat.Prime 1868569 := by
  apply certificate_prime 1868569 (11 : ZMod 1868569) [2,2,2,3,13,53,113] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc13,pc53,pc113]
theorem pc2099863 : Nat.Prime 2099863 := by
  apply certificate_prime 2099863 (3 : ZMod 2099863) [2,3,3,43,2713] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc43,pc2713]
theorem pc2216897 : Nat.Prime 2216897 := by
  apply certificate_prime 2216897 (3 : ZMod 2216897) [2,2,2,2,2,2,11,47,67] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc11,pc47,pc67]
theorem pc2281057 : Nat.Prime 2281057 := by
  apply certificate_prime 2281057 (5 : ZMod 2281057) [2,2,2,2,2,3,23761] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc23761]
theorem pc2298041 : Nat.Prime 2298041 := by
  apply certificate_prime 2298041 (13 : ZMod 2298041) [2,2,2,5,73,787] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc73,pc787]
theorem pc2332951 : Nat.Prime 2332951 := by
  apply certificate_prime 2332951 (21 : ZMod 2332951) [2,3,5,5,103,151] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc103,pc151]
theorem pc2473813 : Nat.Prime 2473813 := by
  apply certificate_prime 2473813 (2 : ZMod 2473813) [2,2,3,3,11,6247] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc11,pc6247]
theorem pc2796203 : Nat.Prime 2796203 := by
  apply certificate_prime 2796203 (5 : ZMod 2796203) [2,23,89,683] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc23,pc89,pc683]
theorem pc2991673 : Nat.Prime 2991673 := by
  apply certificate_prime 2991673 (7 : ZMod 2991673) [2,2,2,3,3,37,1123] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc37,pc1123]
theorem pc2998279 : Nat.Prime 2998279 := by
  apply certificate_prime 2998279 (3 : ZMod 2998279) [2,3,3,166571] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc166571]
theorem pc3033169 : Nat.Prime 3033169 := by
  apply certificate_prime 3033169 (7 : ZMod 3033169) [2,2,2,2,3,29,2179] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc29,pc2179]
theorem pc3393713 : Nat.Prime 3393713 := by
  apply certificate_prime 3393713 (3 : ZMod 3393713) [2,2,2,2,7,157,193] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc7,pc157,pc193]
theorem pc3415403 : Nat.Prime 3415403 := by
  apply certificate_prime 3415403 (2 : ZMod 3415403) [2,17,17,19,311] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc17,pc19,pc311]
theorem pc3887047 : Nat.Prime 3887047 := by
  apply certificate_prime 3887047 (17 : ZMod 3887047) [2,3,3,23,41,229] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc23,pc41,pc229]
theorem pc4036961 : Nat.Prime 4036961 := by
  apply certificate_prime 4036961 (3 : ZMod 4036961) [2,2,2,2,2,5,23,1097] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc23,pc1097]
theorem pc4285651 : Nat.Prime 4285651 := by
  apply certificate_prime 4285651 (2 : ZMod 4285651) [2,3,5,5,28571] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc28571]
theorem pc4327489 : Nat.Prime 4327489 := by
  apply certificate_prime 4327489 (7 : ZMod 4327489) [2,2,2,2,2,2,3,3,11,683] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc11,pc683]
theorem pc5409427 : Nat.Prime 5409427 := by
  apply certificate_prime 5409427 (3 : ZMod 5409427) [2,3,11,11,7451] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc11,pc7451]
theorem pc6700417 : Nat.Prime 6700417 := by
  apply certificate_prime 6700417 (5 : ZMod 6700417) [2,2,2,2,2,2,2,3,17449] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc17449]
theorem pc6994333 : Nat.Prime 6994333 := by
  apply certificate_prime 6994333 (6 : ZMod 6994333) [2,2,3,3,37,59,89] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc37,pc59,pc89]
theorem pc7327657 : Nat.Prime 7327657 := by
  apply certificate_prime 7327657 (19 : ZMod 7327657) [2,2,2,3,3,7,7,31,67] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc7,pc31,pc67]
theorem pc7416361 : Nat.Prime 7416361 := by
  apply certificate_prime 7416361 (11 : ZMod 7416361) [2,2,2,3,3,3,3,3,5,7,109] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc7,pc109]
theorem pc7623851 : Nat.Prime 7623851 := by
  apply certificate_prime 7623851 (6 : ZMod 7623851) [2,5,5,13,37,317] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc13,pc37,pc317]
theorem pc8060489 : Nat.Prime 8060489 := by
  apply certificate_prime 8060489 (3 : ZMod 8060489) [2,2,2,23,71,617] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc23,pc71,pc617]
theorem pc8583937 : Nat.Prime 8583937 := by
  apply certificate_prime 8583937 (7 : ZMod 8583937) [2,2,2,2,2,2,2,2,3,11177] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc11177]
theorem pc8620289 : Nat.Prime 8620289 := by
  apply certificate_prime 8620289 (3 : ZMod 8620289) [2,2,2,2,2,2,2,2,151,223] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc151,pc223]
theorem pc10567201 : Nat.Prime 10567201 := by
  apply certificate_prime 10567201 (11 : ZMod 10567201) [2,2,2,2,2,3,5,5,7,17,37] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc7,pc17,pc37]
theorem pc13264529 : Nat.Prime 13264529 := by
  apply certificate_prime 13264529 (3 : ZMod 13264529) [2,2,2,2,31,47,569] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc31,pc47,pc569]
theorem pc15285323 : Nat.Prime 15285323 := by
  apply certificate_prime 15285323 (2 : ZMod 15285323) [2,13,587897] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc13,pc587897]
theorem pc15790321 : Nat.Prime 15790321 := by
  apply certificate_prime 15790321 (19 : ZMod 15790321) [2,2,2,2,3,3,5,7,13,241] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc7,pc13,pc241]
theorem pc17735177 : Nat.Prime 17735177 := by
  apply certificate_prime 17735177 (3 : ZMod 17735177) [2,2,2,2216897] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc2216897]
theorem pc18837001 : Nat.Prime 18837001 := by
  apply certificate_prime 18837001 (19 : ZMod 18837001) [2,2,2,3,3,5,5,5,7,13,23] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc7,pc13,pc23]
theorem pc19628971 : Nat.Prime 19628971 := by
  apply certificate_prime 19628971 (2 : ZMod 19628971) [2,3,5,73,8963] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc73,pc8963]
theorem pc20394401 : Nat.Prime 20394401 := by
  apply certificate_prime 20394401 (3 : ZMod 20394401) [2,2,2,2,2,5,5,13,37,53] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc13,pc37,pc53]
theorem pc22253377 : Nat.Prime 22253377 := by
  apply certificate_prime 22253377 (5 : ZMod 22253377) [2,2,2,2,2,2,3,115903] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc115903]
theorem pc22366891 : Nat.Prime 22366891 := by
  apply certificate_prime 22366891 (3 : ZMod 22366891) [2,3,3,5,7,13,2731] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc7,pc13,pc2731]
theorem pc25781083 : Nat.Prime 25781083 := by
  apply certificate_prime 25781083 (5 : ZMod 25781083) [2,3,37,116131] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc37,pc116131]
theorem pc26295457 : Nat.Prime 26295457 := by
  apply certificate_prime 26295457 (5 : ZMod 26295457) [2,2,2,2,2,3,11,37,673] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc11,pc37,pc673]
theorem pc27977333 : Nat.Prime 27977333 := by
  apply certificate_prime 27977333 (2 : ZMod 27977333) [2,2,6994333] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc6994333]
theorem pc32456563 : Nat.Prime 32456563 := by
  apply certificate_prime 32456563 (3 : ZMod 32456563) [2,3,5409427] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5409427]
theorem pc38381927 : Nat.Prime 38381927 := by
  apply certificate_prime 38381927 (5 : ZMod 38381927) [2,11,11,199,797] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc11,pc199,pc797]
theorem pc40115077 : Nat.Prime 40115077 := by
  apply certificate_prime 40115077 (2 : ZMod 40115077) [2,2,3,307,10889] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc307,pc10889]
theorem pc47392381 : Nat.Prime 47392381 := by
  apply certificate_prime 47392381 (6 : ZMod 47392381) [2,2,3,3,5,7,29,1297] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc7,pc29,pc1297]
theorem pc48544121 : Nat.Prime 48544121 := by
  apply certificate_prime 48544121 (3 : ZMod 48544121) [2,2,2,5,71,17093] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc71,pc17093]
theorem pc48912491 : Nat.Prime 48912491 := by
  apply certificate_prime 48912491 (10 : ZMod 48912491) [2,5,11,23,19333] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc11,pc23,pc19333]
theorem pc56409643 : Nat.Prime 56409643 := by
  apply certificate_prime 56409643 (3 : ZMod 56409643) [2,3,3,3,71,14713] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc71,pc14713]
theorem pc64875199 : Nat.Prime 64875199 := by
  apply certificate_prime 64875199 (3 : ZMod 64875199) [2,3,877,12329] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc877,pc12329]
theorem pc67254877 : Nat.Prime 67254877 := by
  apply certificate_prime 67254877 (2 : ZMod 67254877) [2,2,3,3,13,131,1097] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc13,pc131,pc1097]
theorem pc77555939 : Nat.Prime 77555939 := by
  apply certificate_prime 77555939 (2 : ZMod 77555939) [2,17,2281057] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc17,pc2281057]
theorem pc85880051 : Nat.Prime 85880051 := by
  apply certificate_prime 85880051 (2 : ZMod 85880051) [2,5,5,823,2087] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc823,pc2087]
theorem pc88736771 : Nat.Prime 88736771 := by
  apply certificate_prime 88736771 (2 : ZMod 88736771) [2,5,17,521981] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc17,pc521981]
theorem pc97685839 : Nat.Prime 97685839 := by
  apply certificate_prime 97685839 (6 : ZMod 97685839) [2,3,3,3,3,602999] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc602999]
theorem pc104827273 : Nat.Prime 104827273 := by
  apply certificate_prime 104827273 (5 : ZMod 104827273) [2,2,2,3,11,397073] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc11,pc397073]
theorem pc105465631 : Nat.Prime 105465631 := by
  apply certificate_prime 105465631 (3 : ZMod 105465631) [2,3,5,263,13367] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc263,pc13367]
theorem pc107367629 : Nat.Prime 107367629 := by
  apply certificate_prime 107367629 (3 : ZMod 107367629) [2,2,29,113,8191] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc29,pc113,pc8191]
theorem pc112901153 : Nat.Prime 112901153 := by
  apply certificate_prime 112901153 (3 : ZMod 112901153) [2,2,2,2,2,7,13,137,283] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc7,pc13,pc137,pc283]
theorem pc122440127 : Nat.Prime 122440127 := by
  apply certificate_prime 122440127 (5 : ZMod 122440127) [2,73,838631] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc73,pc838631]
theorem pc155542661 : Nat.Prime 155542661 := by
  apply certificate_prime 155542661 (2 : ZMod 155542661) [2,2,5,7,7,13,29,421] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc7,pc13,pc29,pc421]
theorem pc160465489 : Nat.Prime 160465489 := by
  apply certificate_prime 160465489 (17 : ZMod 160465489) [2,2,2,2,3,19,175949] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc19,pc175949]
theorem pc164511353 : Nat.Prime 164511353 := by
  apply certificate_prime 164511353 (3 : ZMod 164511353) [2,2,2,41,59,8501] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc41,pc59,pc8501]
theorem pc168513931 : Nat.Prime 168513931 := by
  apply certificate_prime 168513931 (2 : ZMod 168513931) [2,3,3,5,13,73,1973] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc13,pc73,pc1973]
theorem pc174775259 : Nat.Prime 174775259 := by
  apply certificate_prime 174775259 (2 : ZMod 174775259) [2,7,7,83,21487] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc7,pc83,pc21487]
theorem pc184481113 : Nat.Prime 184481113 := by
  apply certificate_prime 184481113 (15 : ZMod 184481113) [2,2,2,3,37,83,2503] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc37,pc83,pc2503]
theorem pc193707721 : Nat.Prime 193707721 := by
  apply certificate_prime 193707721 (59 : ZMod 193707721) [2,2,2,3,3,3,5,67,2677] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc67,pc2677]
theorem pc202029703 : Nat.Prime 202029703 := by
  apply certificate_prime 202029703 (3 : ZMod 202029703) [2,3,7,79,60889] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc7,pc79,pc60889]
theorem pc212885833 : Nat.Prime 212885833 := by
  apply certificate_prime 212885833 (11 : ZMod 212885833) [2,2,2,3,17,71,7349] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc17,pc71,pc7349]
theorem pc224968241 : Nat.Prime 224968241 := by
  apply certificate_prime 224968241 (6 : ZMod 224968241) [2,2,2,2,5,7,31,12959] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc7,pc31,pc12959]
theorem pc231769777 : Nat.Prime 231769777 := by
  apply certificate_prime 231769777 (5 : ZMod 231769777) [2,2,2,2,3,7,37,103,181] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc7,pc37,pc103,pc181]
theorem pc235147459 : Nat.Prime 235147459 := by
  apply certificate_prime 235147459 (2 : ZMod 235147459) [2,3,7,13,19,19,1193] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc7,pc13,pc19,pc1193]
theorem pc242906129 : Nat.Prime 242906129 := by
  apply certificate_prime 242906129 (3 : ZMod 242906129) [2,2,2,2,23,660071] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc23,pc660071]
theorem pc295985357 : Nat.Prime 295985357 := by
  apply certificate_prime 295985357 (2 : ZMod 295985357) [2,2,379,195241] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc379,pc195241]
theorem pc307055417 : Nat.Prime 307055417 := by
  apply certificate_prime 307055417 (3 : ZMod 307055417) [2,2,2,38381927] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc38381927]
theorem pc308761441 : Nat.Prime 308761441 := by
  apply certificate_prime 308761441 (17 : ZMod 308761441) [2,2,2,2,2,3,5,13,49481] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc13,pc49481]
theorem pc319020217 : Nat.Prime 319020217 := by
  apply certificate_prime 319020217 (5 : ZMod 319020217) [2,2,2,3,37,101,3557] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc37,pc101,pc3557]
theorem pc408485041 : Nat.Prime 408485041 := by
  apply certificate_prime 408485041 (14 : ZMod 408485041) [2,2,2,2,3,5,643,2647] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc643,pc2647]
theorem pc420778751 : Nat.Prime 420778751 := by
  apply certificate_prime 420778751 (7 : ZMod 420778751) [2,5,5,5,5,7,19,2531] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc7,pc19,pc2531]
theorem pc536903681 : Nat.Prime 536903681 := by
  apply certificate_prime 536903681 (7 : ZMod 536903681) [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,5,29,113] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc29,pc113]
theorem pc616318177 : Nat.Prime 616318177 := by
  apply certificate_prime 616318177 (5 : ZMod 616318177) [2,2,2,2,2,3,37,167,1039] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc37,pc167,pc1039]
theorem pc715827883 : Nat.Prime 715827883 := by
  apply certificate_prime 715827883 (5 : ZMod 715827883) [2,3,7,11,31,151,331] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc7,pc11,pc31,pc151,pc331]
theorem pc745988807 : Nat.Prime 745988807 := by
  apply certificate_prime 745988807 (5 : ZMod 745988807) [2,107,109,31981] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc107,pc109,pc31981]
theorem pc1098372973 : Nat.Prime 1098372973 := by
  apply certificate_prime 1098372973 (5 : ZMod 1098372973) [2,2,3,37,2473813] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc37,pc2473813]
theorem pc1824726041 : Nat.Prime 1824726041 := by
  apply certificate_prime 1824726041 (3 : ZMod 1824726041) [2,2,2,5,37,59,20897] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc37,pc59,pc20897]
theorem pc2147483647 : Nat.Prime 2147483647 := by
  apply certificate_prime 2147483647 (7 : ZMod 2147483647) [2,3,3,7,11,31,151,331] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc7,pc11,pc31,pc151,pc331]
theorem pc2385608807 : Nat.Prime 2385608807 := by
  apply certificate_prime 2385608807 (5 : ZMod 2385608807) [2,7,7,23,1058389] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc7,pc23,pc1058389]
theorem pc2534364967 : Nat.Prime 2534364967 := by
  apply certificate_prime 2534364967 (3 : ZMod 2534364967) [2,3,7,7,8620289] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc7,pc8620289]
theorem pc2550183799 : Nat.Prime 2550183799 := by
  apply certificate_prime 2550183799 (11 : ZMod 2550183799) [2,3,83,83,103,599] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc83,pc103,pc599]
theorem pc2598660833 : Nat.Prime 2598660833 := by
  apply certificate_prime 2598660833 (3 : ZMod 2598660833) [2,2,2,2,2,47,709,2437] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc47,pc709,pc2437]
theorem pc2931542417 : Nat.Prime 2931542417 := by
  apply certificate_prime 2931542417 (3 : ZMod 2931542417) [2,2,2,2,11,1913,8707] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc11,pc1913,pc8707]
theorem pc3145954663 : Nat.Prime 3145954663 := by
  apply certificate_prime 3145954663 (3 : ZMod 3145954663) [2,3,3,174775259] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc174775259]
theorem pc4204230617 : Nat.Prime 4204230617 := by
  apply certificate_prime 4204230617 (3 : ZMod 4204230617) [2,2,2,421,809,1543] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc421,pc809,pc1543]
theorem pc4278255361 : Nat.Prime 4278255361 := by
  apply certificate_prime 4278255361 (23 : ZMod 4278255361) [2,2,2,2,2,2,2,2,3,5,17,65537] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc17,pc65537]
theorem pc4375578271 : Nat.Prime 4375578271 := by
  apply certificate_prime 4375578271 (3 : ZMod 4375578271) [2,3,5,7,47,193,2297] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc7,pc47,pc193,pc2297]
theorem pc4562284561 : Nat.Prime 4562284561 := by
  apply certificate_prime 4562284561 (11 : ZMod 4562284561) [2,2,2,2,3,5,17,19,229,257] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc17,pc19,pc229,pc257]
theorem pc6113571371 : Nat.Prime 6113571371 := by
  apply certificate_prime 6113571371 (2 : ZMod 6113571371) [2,5,179,3415403] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc179,pc3415403]
theorem pc7175817973 : Nat.Prime 7175817973 := by
  apply certificate_prime 7175817973 (2 : ZMod 7175817973) [2,2,3,3,3,193,344263] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc193,pc344263]
theorem pc7830118297 : Nat.Prime 7830118297 := by
  apply certificate_prime 7830118297 (5 : ZMod 7830118297) [2,2,2,3,3,7,11,13,108643] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc7,pc11,pc13,pc108643]
theorem pc8831418697 : Nat.Prime 8831418697 := by
  apply certificate_prime 8831418697 (15 : ZMod 8831418697) [2,2,2,3,3,41,2991673] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc41,pc2991673]
theorem pc23140471537 : Nat.Prime 23140471537 := by
  apply certificate_prime 23140471537 (43 : ZMod 23140471537) [2,2,2,2,3,3,7,13,17,109,953] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc7,pc13,pc17,pc109,pc953]
theorem pc24721057583 : Nat.Prime 24721057583 := by
  apply certificate_prime 24721057583 (5 : ZMod 24721057583) [2,13,6113,155539] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc13,pc6113,pc155539]
theorem pc30327152671 : Nat.Prime 30327152671 := by
  apply certificate_prime 30327152671 (3 : ZMod 30327152671) [2,3,3,5,19,17735177] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc19,pc17735177]
theorem pc33057806959 : Nat.Prime 33057806959 := by
  apply certificate_prime 33057806959 (3 : ZMod 33057806959) [2,3,3,11,757,220553] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc11,pc757,pc220553]
theorem pc35532364099 : Nat.Prime 35532364099 := by
  apply certificate_prime 35532364099 (10 : ZMod 35532364099) [2,3,7,11,229,263,1277] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc7,pc11,pc229,pc263,pc1277]
theorem pc37948862843 : Nat.Prime 37948862843 := by
  apply certificate_prime 37948862843 (2 : ZMod 37948862843) [2,11,43,40115077] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc11,pc43,pc40115077]
theorem pc54410972897 : Nat.Prime 54410972897 := by
  apply certificate_prime 54410972897 (3 : ZMod 54410972897) [2,2,2,2,2,7,242906129] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc7,pc242906129]
theorem pc62983048367 : Nat.Prime 62983048367 := by
  apply certificate_prime 62983048367 (5 : ZMod 62983048367) [2,7,7,17,29,67,19457] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc7,pc17,pc29,pc67,pc19457]
theorem pc75676151107 : Nat.Prime 75676151107 := by
  apply certificate_prime 75676151107 (3 : ZMod 75676151107) [2,3,3,4204230617] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc4204230617]
theorem pc77158673929 : Nat.Prime 77158673929 := by
  apply certificate_prime 77158673929 (11 : ZMod 77158673929) [2,2,2,3,3,3,7,73,699053] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc7,pc73,pc699053]
theorem pc77537251093 : Nat.Prime 77537251093 := by
  apply certificate_prime 77537251093 (22 : ZMod 77537251093) [2,2,3,7,196271,4703] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc7,pc196271,pc4703]
theorem pc131105292137 : Nat.Prime 131105292137 := by
  apply certificate_prime 131105292137 (3 : ZMod 131105292137) [2,2,2,7,13,17,1579,6709] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc7,pc13,pc17,pc1579,pc6709]
theorem pc154826229713 : Nat.Prime 154826229713 := by
  apply certificate_prime 154826229713 (5 : ZMod 154826229713) [2,2,2,2,7,11,659,190699] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc7,pc11,pc659,pc190699]
theorem pc158822951431 : Nat.Prime 158822951431 := by
  apply certificate_prime 158822951431 (11 : ZMod 158822951431) [2,3,5,11,13,43,860969] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc11,pc13,pc43,pc860969]
theorem pc165768537521 : Nat.Prime 165768537521 := by
  apply certificate_prime 165768537521 (3 : ZMod 165768537521) [2,2,2,2,5,47,2887,15271] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc47,pc2887,pc15271]
theorem pc168749965921 : Nat.Prime 168749965921 := by
  apply certificate_prime 168749965921 (17 : ZMod 168749965921) [2,2,2,2,2,3,5,23,15285323] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc23,pc15285323]
theorem pc231017337191 : Nat.Prime 231017337191 := by
  apply certificate_prime 231017337191 (7 : ZMod 231017337191) [2,5,269,85880051] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc269,pc85880051]
theorem pc269089806001 : Nat.Prime 269089806001 := by
  apply certificate_prime 269089806001 (37 : ZMod 269089806001) [2,2,2,2,3,5,5,5,41,107,10223] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc41,pc107,pc10223]
theorem pc309652459427 : Nat.Prime 309652459427 := by
  apply certificate_prime 309652459427 (2 : ZMod 309652459427) [2,154826229713] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc154826229713]
theorem pc487824887233 : Nat.Prime 487824887233 := by
  apply certificate_prime 487824887233 (5 : ZMod 487824887233) [2,2,2,2,2,2,3,3,3,3,3,1091,28751] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc1091,pc28751]
theorem pc761838257287 : Nat.Prime 761838257287 := by
  apply certificate_prime 761838257287 (3 : ZMod 761838257287) [2,3,3,29,67,2551,8539] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc29,pc67,pc2551,pc8539]
theorem pc1113491139767 : Nat.Prime 1113491139767 := by
  apply certificate_prime 1113491139767 (5 : ZMod 1113491139767) [2,79,821,8583937] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc79,pc821,pc8583937]
theorem pc1133836730401 : Nat.Prime 1133836730401 := by
  apply certificate_prime 1133836730401 (13 : ZMod 1133836730401) [2,2,2,2,2,3,5,5,11,31,41,33791] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc11,pc31,pc41,pc33791]
theorem pc2812085643403 : Nat.Prime 2812085643403 := by
  apply certificate_prime 2812085643403 (3 : ZMod 2812085643403) [2,3,3,3,7,379,19628971] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc7,pc379,pc19628971]
theorem pc2879347902817 : Nat.Prime 2879347902817 := by
  apply certificate_prime 2879347902817 (15 : ZMod 2879347902817) [2,2,2,2,2,3,7,11,17,19,1205951] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc7,pc11,pc17,pc19,pc1205951]
theorem pc2932031007403 : Nat.Prime 2932031007403 := by
  apply certificate_prime 2932031007403 (3 : ZMod 2932031007403) [2,3,7,7,43,127,337,5419] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc7,pc43,pc127,pc337,pc5419]
theorem pc3203431780337 : Nat.Prime 3203431780337 := by
  apply certificate_prime 3203431780337 (3 : ZMod 3203431780337) [2,2,2,2,59,421,8060489] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc59,pc421,pc8060489]
theorem pc4363953127297 : Nat.Prime 4363953127297 := by
  apply certificate_prime 4363953127297 (5 : ZMod 4363953127297) [2,2,2,2,2,2,2,3,7,7,127,337,5419] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc7,pc127,pc337,pc5419]
theorem pc4432676798593 : Nat.Prime 4432676798593 := by
  apply certificate_prime 4432676798593 (5 : ZMod 4432676798593) [2,2,2,2,2,2,2,3,3,7,7,43,337,5419] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc7,pc43,pc337,pc5419]
theorem pc5625767248687 : Nat.Prime 5625767248687 := by
  apply certificate_prime 5625767248687 (3 : ZMod 5625767248687) [2,3,3,13,37,53,139,193,457] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc13,pc37,pc53,pc139,pc193,pc457]
theorem pc5895671065241 : Nat.Prime 5895671065241 := by
  apply certificate_prime 5895671065241 (6 : ZMod 5895671065241) [2,2,2,5,11,151,88736771] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc11,pc151,pc88736771]
theorem pc6417545220131 : Nat.Prime 6417545220131 := by
  apply certificate_prime 6417545220131 (2 : ZMod 6417545220131) [2,5,11,17191,3393713] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc11,pc17191,pc3393713]
theorem pc6713103182899 : Nat.Prime 6713103182899 := by
  apply certificate_prime 6713103182899 (19 : ZMod 6713103182899) [2,3,7,67,2385608807] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc7,pc67,pc2385608807]
theorem pc7432339208719 : Nat.Prime 7432339208719 := by
  apply certificate_prime 7432339208719 (3 : ZMod 7432339208719) [2,3,101,44029,278557] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc101,pc44029,pc278557]
theorem pc9361973132609 : Nat.Prime 9361973132609 := by
  apply certificate_prime 9361973132609 (3 : ZMod 9361973132609) [2,2,2,2,2,2,19,73,105465631] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc19,pc73,pc105465631]
theorem pc9857737155463 : Nat.Prime 9857737155463 := by
  apply certificate_prime 9857737155463 (5 : ZMod 9857737155463) [2,3,7,29,37,4217,51871] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc7,pc29,pc37,pc4217,pc51871]
theorem pc10052678938039 : Nat.Prime 10052678938039 := by
  apply certificate_prime 10052678938039 (6 : ZMod 10052678938039) [2,3,11,23,89,683,108943] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc11,pc23,pc89,pc683,pc108943]
theorem pc11248342573613 : Nat.Prime 11248342573613 := by
  apply certificate_prime 11248342573613 (2 : ZMod 11248342573613) [2,2,2812085643403] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc2812085643403]
theorem pc11791342130483 : Nat.Prime 11791342130483 := by
  apply certificate_prime 11791342130483 (2 : ZMod 11791342130483) [2,5895671065241] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5895671065241]
theorem pc13528921548413 : Nat.Prime 13528921548413 := by
  apply certificate_prime 13528921548413 (2 : ZMod 13528921548413) [2,2,19,73,1861,1310329] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc19,pc73,pc1861,pc1310329]
theorem pc13952598148481 : Nat.Prime 13952598148481 := by
  apply certificate_prime 13952598148481 (3 : ZMod 13952598148481) [2,2,2,2,2,2,2,5,71,307055417] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc71,pc307055417]
theorem pc15894170606833 : Nat.Prime 15894170606833 := by
  apply certificate_prime 15894170606833 (11 : ZMod 15894170606833) [2,2,2,2,3,7,547,1549,55829] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc7,pc547,pc1549,pc55829]
theorem pc24517014940753 : Nat.Prime 24517014940753 := by
  apply certificate_prime 24517014940753 (15 : ZMod 24517014940753) [2,2,2,2,3,17,19,2309,684857] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc17,pc19,pc2309,pc684857]
theorem pc28059810762433 : Nat.Prime 28059810762433 := by
  apply certificate_prime 28059810762433 (5 : ZMod 28059810762433) [2,2,2,2,2,2,3,41,53,67254877] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc41,pc53,pc67254877]
theorem pc37888318897441 : Nat.Prime 37888318897441 := by
  apply certificate_prime 37888318897441 (14 : ZMod 37888318897441) [2,2,2,2,2,3,5,11,7175817973] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc11,pc7175817973]
theorem pc41024572597643 : Nat.Prime 41024572597643 := by
  apply certificate_prime 41024572597643 (2 : ZMod 41024572597643) [2,195677,104827273] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc195677,pc104827273]
theorem pc49971617830801 : Nat.Prime 49971617830801 := by
  apply certificate_prime 49971617830801 (11 : ZMod 49971617830801) [2,2,2,2,3,3,3,5,5,102103,45317] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc102103,pc45317]
theorem pc67280421310721 : Nat.Prime 67280421310721 := by
  apply certificate_prime 67280421310721 (3 : ZMod 67280421310721) [2,2,2,2,2,2,2,2,5,47,373,2998279] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc47,pc373,pc2998279]
theorem pc114282372716711 : Nat.Prime 114282372716711 := by
  apply certificate_prime 114282372716711 (11 : ZMod 114282372716711) [2,5,11,23,29,41,167,227489] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc11,pc23,pc29,pc41,pc167,pc227489]
theorem pc145295143558111 : Nat.Prime 145295143558111 := by
  apply certificate_prime 145295143558111 (7 : ZMod 145295143558111) [2,3,3,5,7,7,13,2534364967] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc7,pc13,pc2534364967]
theorem pc800502326409847 : Nat.Prime 800502326409847 := by
  apply certificate_prime 800502326409847 (3 : ZMod 800502326409847) [2,3,41,43,75676151107] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc41,pc43,pc75676151107]
theorem pc1066818132868207 : Nat.Prime 1066818132868207 := by
  apply certificate_prime 1066818132868207 (5 : ZMod 1066818132868207) [2,3,71,113,181,122440127] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc71,pc113,pc181,pc122440127]
theorem pc2646507710984041 : Nat.Prime 2646507710984041 := by
  apply certificate_prime 2646507710984041 (13 : ZMod 2646507710984041) [2,2,2,3,3,3,5,23,97,1098372973] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc23,pc97,pc1098372973]
theorem pc13009975360894471 : Nat.Prime 13009975360894471 := by
  apply certificate_prime 13009975360894471 (3 : ZMod 13009975360894471) [2,3,5,7,17,47,77537251093] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc7,pc17,pc47,pc77537251093]
theorem pc19254501516307153 : Nat.Prime 19254501516307153 := by
  apply certificate_prime 19254501516307153 (5 : ZMod 19254501516307153) [2,2,2,2,3,107,22247,168513931] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc107,pc22247,pc168513931]
theorem pc40429991358605171 : Nat.Prime 40429991358605171 := by
  apply certificate_prime 40429991358605171 (2 : ZMod 40429991358605171) [2,5,7,7,235147459,350887] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc7,pc235147459,pc350887]
theorem pc80859982717210343 : Nat.Prime 80859982717210343 := by
  apply certificate_prime 80859982717210343 (5 : ZMod 80859982717210343) [2,40429991358605171] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc40429991358605171]
theorem pc177722253954175633 : Nat.Prime 177722253954175633 := by
  apply certificate_prime 177722253954175633 (5 : ZMod 177722253954175633) [2,2,2,2,3,13,41,281,24721057583] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc13,pc41,pc281,pc24721057583]
theorem pc341117531003194129 : Nat.Prime 341117531003194129 := by
  apply certificate_prime 341117531003194129 (13 : ZMod 341117531003194129) [2,2,2,2,3,3,101,79241,295985357] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc101,pc79241,pc295985357]
theorem pc572381836983566689 : Nat.Prime 572381836983566689 := by
  apply certificate_prime 572381836983566689 (11 : ZMod 572381836983566689) [2,2,2,2,2,3,13,19,7673,3145954663] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc13,pc19,pc7673,pc3145954663]
theorem pc581283643249112959 : Nat.Prime 581283643249112959 := by
  apply certificate_prime 581283643249112959 (6 : ZMod 581283643249112959) [2,3,3,7,11,31,13528921548413] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc7,pc11,pc31,pc13528921548413]
theorem pc646675035253258729 : Nat.Prime 646675035253258729 := by
  apply certificate_prime 646675035253258729 (19 : ZMod 646675035253258729) [2,2,2,3,47,15107,37948862843] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc47,pc15107,pc37948862843]
theorem pc658812288653553079 : Nat.Prime 658812288653553079 := by
  apply certificate_prime 658812288653553079 (21 : ZMod 658812288653553079) [2,3,3,11,31,83,151,331,1277,20261] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc11,pc31,pc83,pc151,pc331,pc1277,pc20261]
theorem pc768614336404564651 : Nat.Prime 768614336404564651 := by
  apply certificate_prime 768614336404564651 (3 : ZMod 768614336404564651) [2,3,5,5,7,11,13,31,41,61,151,331,1321] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc7,pc11,pc13,pc31,pc41,pc61,pc151,pc331,pc1321]
theorem pc1795918038741070627 : Nat.Prime 1795918038741070627 := by
  apply certificate_prime 1795918038741070627 (3 : ZMod 1795918038741070627) [2,3,73,811,12377,408485041] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc73,pc811,pc12377,pc408485041]
theorem pc1940639585213048233 : Nat.Prime 1940639585213048233 := by
  apply certificate_prime 1940639585213048233 (5 : ZMod 1940639585213048233) [2,2,2,3,80859982717210343] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc80859982717210343]
set_option maxRecDepth 8192 in
theorem pc2305843009213693951 : Nat.Prime 2305843009213693951 := by
  apply certificate_prime 2305843009213693951 (37 : ZMod 2305843009213693951) [2,3,3,5,5,7,11,13,31,41,61,151,331,1321] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc7,pc11,pc13,pc31,pc41,pc61,pc151,pc331,pc1321]
theorem pc4710883168879506001 : Nat.Prime 4710883168879506001 := by
  apply certificate_prime 4710883168879506001 (19 : ZMod 4710883168879506001) [2,2,2,2,3,3,5,5,5,41,41,842887,184711] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc41,pc842887,pc184711]
theorem pc5782172113400990737 : Nat.Prime 5782172113400990737 := by
  apply certificate_prime 5782172113400990737 (5 : ZMod 5782172113400990737) [2,2,2,2,3,11,13,53,15894170606833] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc11,pc13,pc53,pc15894170606833]
theorem pc9520972806333758431 : Nat.Prime 9520972806333758431 := by
  apply certificate_prime 9520972806333758431 (15 : ZMod 9520972806333758431) [2,3,5,17,257,27953,2598660833] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc17,pc257,pc27953,pc2598660833]
theorem pc13753593975618284111 : Nat.Prime 13753593975618284111 := by
  apply certificate_prime 13753593975618284111 (11 : ZMod 13753593975618284111) [2,5,224968241,6113571371] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc224968241,pc6113571371]
theorem pc16910977804748891839 : Nat.Prime 16910977804748891839 := by
  apply certificate_prime 16910977804748891839 (3 : ZMod 16910977804748891839) [2,3,3,3,3,3,13,227,11791342130483] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc13,pc227,pc11791342130483]
theorem pc19406395852130482331 : Nat.Prime 19406395852130482331 := by
  apply certificate_prime 19406395852130482331 (2 : ZMod 19406395852130482331) [2,5,1940639585213048233] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc1940639585213048233]
theorem pc32032215596496435569 : Nat.Prime 32032215596496435569 := by
  apply certificate_prime 32032215596496435569 (3 : ZMod 32032215596496435569) [2,2,2,2,137,59497,8779,27977333] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc137,pc59497,pc8779,pc27977333]
theorem pc86656268566282183151 : Nat.Prime 86656268566282183151 := by
  apply certificate_prime 86656268566282183151 (11 : ZMod 86656268566282183151) [2,5,5,149,307,37888318897441] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc149,pc307,pc37888318897441]
theorem pc3976656429941438590393 : Nat.Prime 3976656429941438590393 := by
  apply certificate_prime 3976656429941438590393 (5 : ZMod 3976656429941438590393) [2,2,2,3,103,149,4657,71429,32456563] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc103,pc149,pc4657,pc71429,pc32456563]
theorem pc5439042183600204290159 : Nat.Prime 5439042183600204290159 := by
  apply certificate_prime 5439042183600204290159 (11 : ZMod 5439042183600204290159) [2,137,483869,41024572597643] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc137,pc483869,pc41024572597643]
theorem pc57912614113275649087721 : Nat.Prime 57912614113275649087721 := by
  apply certificate_prime 57912614113275649087721 (6 : ZMod 57912614113275649087721) [2,2,2,5,83,383,4049,11248342573613] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc83,pc383,pc4049,pc11248342573613]
theorem pc870035986098720987332873 : Nat.Prime 870035986098720987332873 := by
  apply certificate_prime 870035986098720987332873 (3 : ZMod 870035986098720987332873) [2,2,2,59,109,16910977804748891839] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc59,pc109,pc16910977804748891839]
theorem pc2741672362528725535068727 : Nat.Prime 2741672362528725535068727 := by
  apply certificate_prime 2741672362528725535068727 (3 : ZMod 2741672362528725535068727) [2,3,7,7,61,337,70687,6417545220131] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc7,pc61,pc337,pc70687,pc6417545220131]
theorem pc4114641232003272535381657 : Nat.Prime 4114641232003272535381657 := by
  apply certificate_prime 4114641232003272535381657 (10 : ZMod 4114641232003272535381657) [2,2,2,3,7,173,1238789,114282372716711] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc7,pc173,pc1238789,pc114282372716711]
theorem pc7289088383388253664437433 : Nat.Prime 7289088383388253664437433 := by
  apply certificate_prime 7289088383388253664437433 (3 : ZMod 7289088383388253664437433) [2,2,2,7,59,151,1123,13009975360894471] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc7,pc59,pc151,pc1123,pc13009975360894471]
theorem pc8235109336690846723986161 : Nat.Prime 8235109336690846723986161 := by
  apply certificate_prime 8235109336690846723986161 (15 : ZMod 8235109336690846723986161) [2,2,2,2,5,17,71,149,572381836983566689] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc5,pc17,pc71,pc149,pc572381836983566689]
theorem pc11053036065049294753459639 : Nat.Prime 11053036065049294753459639 := by
  apply certificate_prime 11053036065049294753459639 (13 : ZMod 11053036065049294753459639) [2,3,3,7,11,43,53,97,127,337,5419,155542661] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc7,pc11,pc43,pc53,pc97,pc127,pc337,pc5419,pc155542661]
set_option maxRecDepth 8192 in
theorem pc13842607235828485645766393 : Nat.Prime 13842607235828485645766393 := by
  apply certificate_prime 13842607235828485645766393 (3 : ZMod 13842607235828485645766393) [2,2,2,97,1297,13753593975618284111] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc97,pc1297,pc13753593975618284111]
theorem pc75582488424179347083438319 : Nat.Prime 75582488424179347083438319 := by
  apply certificate_prime 75582488424179347083438319 (6 : ZMod 75582488424179347083438319) [2,3,3,17,67,853,5399,800502326409847] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc17,pc67,pc853,pc5399,pc800502326409847]
set_option maxRecDepth 8192 in
theorem pc273399736511044418098908817 : Nat.Prime 273399736511044418098908817 := by
  apply certificate_prime 273399736511044418098908817 (10 : ZMod 273399736511044418098908817) [2,2,2,2,3,3,47,79,103,211,75983,309652459427] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc47,pc79,pc103,pc211,pc75983,pc309652459427]
set_option maxRecDepth 8192 in
theorem pc618970019642690137449562111 : Nat.Prime 618970019642690137449562111 := by
  apply certificate_prime 618970019642690137449562111 (3 : ZMod 618970019642690137449562111) [2,3,5,17,23,89,353,397,683,2113,2931542417] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc17,pc23,pc89,pc353,pc397,pc683,pc2113,pc2931542417]
set_option maxRecDepth 8192 in
theorem pc123876132205208335762278423601 : Nat.Prime 123876132205208335762278423601 := by
  apply certificate_prime 123876132205208335762278423601 (7 : ZMod 123876132205208335762278423601) [2,2,2,2,3,3,3,5,5,139,4285651,19254501516307153] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc139,pc4285651,pc19254501516307153]
set_option maxRecDepth 8192 in
theorem pc1786393878363164227858270210279 : Nat.Prime 1786393878363164227858270210279 := by
  apply certificate_prime 1786393878363164227858270210279 (3 : ZMod 1786393878363164227858270210279) [2,3,3,3,11,11,273399736511044418098908817] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc11,pc273399736511044418098908817]
set_option maxRecDepth 8192 in
theorem pc162259276829213363391578010288127 : Nat.Prime 162259276829213363391578010288127 := by
  apply certificate_prime 162259276829213363391578010288127 (3 : ZMod 162259276829213363391578010288127) [2,3,107,6361,69431,20394401,28059810762433] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc107,pc6361,pc69431,pc20394401,pc28059810762433]
set_option maxRecDepth 8192 in
theorem pc163537220852725398851434325720959 : Nat.Prime 163537220852725398851434325720959 := by
  apply certificate_prime 163537220852725398851434325720959 (3 : ZMod 163537220852725398851434325720959) [2,3,3,3,3,7,19,23,73,252313,77555939,231017337191] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc7,pc19,pc23,pc73,pc252313,pc77555939,pc231017337191]
set_option maxRecDepth 8192 in
theorem pc2679895157783862814690027494144991 : Nat.Prime 2679895157783862814690027494144991 := by
  apply certificate_prime 2679895157783862814690027494144991 (11 : ZMod 2679895157783862814690027494144991) [2,3,5,29,43,113,127,257219,19406395852130482331] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc5,pc29,pc43,pc113,pc127,pc257219,pc19406395852130482331]
set_option maxRecDepth 8192 in
theorem pc10350794431055162386718619237468234569 : Nat.Prime 10350794431055162386718619237468234569 := by
  apply certificate_prime 10350794431055162386718619237468234569 (3 : ZMod 10350794431055162386718619237468234569) [2,2,2,37,131,64875199,4114641232003272535381657] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc37,pc131,pc64875199,pc4114641232003272535381657]
set_option maxRecDepth 8192 in
theorem pc170141183460469231731687303715884105727 : Nat.Prime 170141183460469231731687303715884105727 := by
  apply certificate_prime 170141183460469231731687303715884105727 (43 : ZMod 170141183460469231731687303715884105727) [2,3,3,3,7,7,19,43,73,127,337,5419,92737,649657,77158673929] (by decide) ?_ (by decide) (by decide)
  simp [pc2,pc3,pc7,pc19,pc43,pc73,pc127,pc337,pc5419,pc92737,pc649657,pc77158673929]
end Erdos11Sieve

namespace Erdos11Sieve

theorem gap155_factors0 : ∀ p ∈ [3,3,3,3,5,5,5,7,7,7,11,11,13,17,17,19,23,29,31,37], Nat.Prime p := by
  simp [pc3,pc5,pc7,pc11,pc13,pc17,pc19,pc23,pc29,pc31,pc37]

theorem gap155_factors1 : ∀ p ∈ [41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131], Nat.Prime p := by
  simp [pc41,pc43,pc47,pc53,pc59,pc61,pc67,pc71,pc73,pc79,pc83,pc89,pc97,pc101,pc103,pc107,pc109,pc113,pc127,pc131]

theorem gap155_factors2 : ∀ p ∈ [137,139,149,151,157,167,191,193,199,223,229,233,239,241,251,257,263,271,277,281], Nat.Prime p := by
  simp [pc137,pc139,pc149,pc151,pc157,pc167,pc191,pc193,pc199,pc223,pc229,pc233,pc239,pc241,pc251,pc257,pc263,pc271,pc277,pc281]

theorem gap155_factors3 : ∀ p ∈ [283,307,331,337,353,397,431,433,439,457,571,577,593,601,617,631,641,673,683,727], Nat.Prime p := by
  simp [pc283,pc307,pc331,pc337,pc353,pc397,pc431,pc433,pc439,pc457,pc571,pc577,pc593,pc601,pc617,pc631,pc641,pc673,pc683,pc727]

theorem gap155_factors4 : ∀ p ∈ [881,911,919,937,953,1013,1103,1217,1321,1429,1613,1657,1753,1777,1801,2089,2113,2143,2351,2593], Nat.Prime p := by
  simp [pc881,pc911,pc919,pc937,pc953,pc1013,pc1103,pc1217,pc1321,pc1429,pc1613,pc1657,pc1753,pc1777,pc1801,pc2089,pc2113,pc2143,pc2351,pc2593]

theorem gap155_factors5 : ∀ p ∈ [2687,2731,2833,2857,2971,3191,3391,4051,4177,4513,5153,5419,5581,6361,6529,6553,8101,8191,8681,9719], Nat.Prime p := by
  simp [pc2687,pc2731,pc2833,pc2857,pc2971,pc3191,pc3391,pc4051,pc4177,pc4513,pc5153,pc5419,pc5581,pc6361,pc6529,pc6553,pc8101,pc8191,pc8681,pc9719]

theorem gap155_factors6 : ∀ p ∈ [11119,11447,13367,14449,14951,18121,20231,20857,23279,23311,26317,29191,30269,32377,37171,38737,43691,49477,55871,61681], Nat.Prime p := by
  simp [pc11119,pc11447,pc13367,pc14449,pc14951,pc18121,pc20231,pc20857,pc23279,pc23311,pc26317,pc29191,pc30269,pc32377,pc37171,pc38737,pc43691,pc49477,pc55871,pc61681]

theorem gap155_factors7 : ∀ p ∈ [65537,65993,69431,71119,78233,86113,86171,87211,92737,100801,106681,121369,122921,131071,148961,152041,153649,165799,174763,178481], Nat.Prime p := by
  simp [pc65537,pc65993,pc69431,pc71119,pc78233,pc86113,pc86171,pc87211,pc92737,pc100801,pc106681,pc121369,pc122921,pc131071,pc148961,pc152041,pc153649,pc165799,pc174763,pc178481]

theorem gap155_factors8 : ∀ p ∈ [179951,201961,228479,246241,262657,268501,274177,279073,312709,321679,348031,354689,384773,409891,524287,525313,599479,649657,724153,858001], Nat.Prime p := by
  simp [pc179951,pc201961,pc228479,pc246241,pc262657,pc268501,pc274177,pc279073,pc312709,pc321679,pc348031,pc354689,pc384773,pc409891,pc524287,pc525313,pc599479,pc649657,pc724153,pc858001]

theorem gap155_factors9 : ∀ p ∈ [1212847,1868569,2099863,2298041,2332951,2796203,3033169,3887047,4036961,4327489,6700417,7327657,7416361,7623851,10567201,13264529,15790321,18837001,20394401,22253377], Nat.Prime p := by
  simp [pc1212847,pc1868569,pc2099863,pc2298041,pc2332951,pc2796203,pc3033169,pc3887047,pc4036961,pc4327489,pc6700417,pc7327657,pc7416361,pc7623851,pc10567201,pc13264529,pc15790321,pc18837001,pc20394401,pc22253377]

theorem gap155_factors10 : ∀ p ∈ [22366891,25781083,26295457,47392381,48544121,48912491,56409643,97685839,107367629,112901153,160465489,164511353,184481113,193707721,202029703,212885833,231769777,308761441,319020217,420778751], Nat.Prime p := by
  simp [pc22366891,pc25781083,pc26295457,pc47392381,pc48544121,pc48912491,pc56409643,pc97685839,pc107367629,pc112901153,pc160465489,pc164511353,pc184481113,pc193707721,pc202029703,pc212885833,pc231769777,pc308761441,pc319020217,pc420778751]

theorem gap155_factors11 : ∀ p ∈ [536903681,616318177,715827883,745988807,1824726041,2147483647,2550183799,2931542417,4278255361,4375578271,4562284561,7830118297,8831418697,23140471537,30327152671,33057806959,35532364099,54410972897,62983048367,77158673929], Nat.Prime p := by
  simp [pc536903681,pc616318177,pc715827883,pc745988807,pc1824726041,pc2147483647,pc2550183799,pc2931542417,pc4278255361,pc4375578271,pc4562284561,pc7830118297,pc8831418697,pc23140471537,pc30327152671,pc33057806959,pc35532364099,pc54410972897,pc62983048367,pc77158673929]

theorem gap155_factors12 : ∀ p ∈ [131105292137,158822951431,165768537521,168749965921,269089806001,487824887233,761838257287,1113491139767,1133836730401,2879347902817,2932031007403,3203431780337,4363953127297,4432676798593,5625767248687,6713103182899,7432339208719,9361973132609,9857737155463,10052678938039], Nat.Prime p := by
  simp [pc131105292137,pc158822951431,pc165768537521,pc168749965921,pc269089806001,pc487824887233,pc761838257287,pc1113491139767,pc1133836730401,pc2879347902817,pc2932031007403,pc3203431780337,pc4363953127297,pc4432676798593,pc5625767248687,pc6713103182899,pc7432339208719,pc9361973132609,pc9857737155463,pc10052678938039]

theorem gap155_factors13 : ∀ p ∈ [13952598148481,24517014940753,28059810762433,49971617830801,67280421310721,145295143558111,1066818132868207,2646507710984041,177722253954175633,341117531003194129,581283643249112959,646675035253258729,658812288653553079,768614336404564651,1795918038741070627,2305843009213693951,4710883168879506001,5782172113400990737,9520972806333758431,32032215596496435569], Nat.Prime p := by
  simp [pc13952598148481,pc24517014940753,pc28059810762433,pc49971617830801,pc67280421310721,pc145295143558111,pc1066818132868207,pc2646507710984041,pc177722253954175633,pc341117531003194129,pc581283643249112959,pc646675035253258729,pc658812288653553079,pc768614336404564651,pc1795918038741070627,pc2305843009213693951,pc4710883168879506001,pc5782172113400990737,pc9520972806333758431,pc32032215596496435569]

theorem gap155_factors14 : ∀ p ∈ [86656268566282183151,3976656429941438590393,5439042183600204290159,57912614113275649087721,870035986098720987332873,2741672362528725535068727,7289088383388253664437433,8235109336690846723986161,11053036065049294753459639,13842607235828485645766393,75582488424179347083438319,618970019642690137449562111,123876132205208335762278423601,1786393878363164227858270210279,162259276829213363391578010288127,163537220852725398851434325720959,2679895157783862814690027494144991,10350794431055162386718619237468234569,170141183460469231731687303715884105727], Nat.Prime p := by
  simp [pc86656268566282183151,pc3976656429941438590393,pc5439042183600204290159,pc57912614113275649087721,pc870035986098720987332873,pc2741672362528725535068727,pc7289088383388253664437433,pc8235109336690846723986161,pc11053036065049294753459639,pc13842607235828485645766393,pc75582488424179347083438319,pc618970019642690137449562111,pc123876132205208335762278423601,pc1786393878363164227858270210279,pc162259276829213363391578010288127,pc163537220852725398851434325720959,pc2679895157783862814690027494144991,pc10350794431055162386718619237468234569,pc170141183460469231731687303715884105727]

set_option maxRecDepth 8192 in
theorem gap155 (p d : ℕ) (prime : p.Prime) (large : 23 < p) (pos : 0< d) (lt : d< 155) :
    ¬ p^2 ∣ 2^d - 1 := by
  let M : ℕ := 0xb8bf2beb881c4cdbe3d7c01aa0e219f1c18c4d06d0de13b93558e6b5d551b9df38cbff5ddceacdd72f777b8d9a4eaee886b29d0fe2898f5565a3593aa02127da5fb6e0a40cec5ad612f11120b9ccb9586d34ca9183776dba6d67cda001d1a0a268b6e01eb92abc0f7a172b2056e2f429fc3d0a30f136be8473bdb394f72e1039af33834a53f803bd973eac47908d912e9fab9e267fe7bf8acbe2d581eaec8005bb265b08e65bc0da368903853c00fa7f60ee05f9dd1944e5d03f3997ba9f67b1237398b97f9a6350e5352f844fde9c725cb7832cbce28a84c617380c5b02a6d40cc32012236d4107d95a02e658b25ea93867da344113c2e25fe54afa4f536917e8254f6d211d7e2b86fa4d4b4167c9141463f3c792fc4a846d47ef2bc8b7ab0f61e92d7eba139ea7a0ca204fd3b0fed0c3253190ef6c319f85066251f4458a12491f3eb1d74af0fb4c5a75bb2c81c10dc4a23f4eedd760d2ff0b8d322a02d40e45a5f44edec5dd9ccfafe48039f4abafd8817c5a0680b1dbc54450f901caf11f7c7096cb15c11004488afcf90a1e3aa1cde495a67b063c93a7f6abea1d5cbb4fd6af4caf903457743518c6315dd864f15bb9a40c2543feae2d2cb07e88f180a739298b98b220e8fe157dea4fd10d08f2ea4a37278c4ff1816f83f6cd08c50021a3797f8d8d9425d96a0c9383bcac232d05d8fd935d4473687ea1bb562e08e0d9021cb088e06ab7a286d9372d6cfdb7444e9a75e0db445e6e933bde5037c8daedebd97366d6d0fac68094ff74bc2707f7f053a3e09e49b8d3779847da3774f83207aff38932ce807a01774502e8546b4c1d5a66dc97285846cf3f16b76ec1ef699a484e89498f748e7e72ef75983f2c244077d4d18ee62a62a4647bdf2e5e330cc5355ff66ff9a1c86f81bb6dc85f433c3acb8ad764d923295032a081c9986b24406286f903b99b017f4e31a2eb575f92eab3197b2a710a70de611c6e11c60baf60a8b8b05b1131ede8e4f3e66ea48c57c018a342f882ac81915a0f9e49c924c38ff1f5d82fde6ece797798aec6cc82c40feecf69cbf269fd1c0e6711e94e68f12f390f8fa1b88b643a5cf5a2af3cce150b0adebf79e0ebad70f46156948a4a6f6fce536c619ade0d2067d37e6515ea3e00d9384c29f36d4a2e6134ac8f297adb39d27346f123a862eb5afc3830140223a23e1562993b18a0f8cb970f5f295aa067c400ecfbb3b18966c31c44c59f9f764d1ad102c6647428db302bbe0eede47b78c591f3e3b6a77c87
  let l : List ℕ := [3,3,3,3,5,5,5,7,7,7,11,11,13,17,17,19,23,29,31,37] ++ [41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131] ++ [137,139,149,151,157,167,191,193,199,223,229,233,239,241,251,257,263,271,277,281] ++ [283,307,331,337,353,397,431,433,439,457,571,577,593,601,617,631,641,673,683,727] ++ [881,911,919,937,953,1013,1103,1217,1321,1429,1613,1657,1753,1777,1801,2089,2113,2143,2351,2593] ++ [2687,2731,2833,2857,2971,3191,3391,4051,4177,4513,5153,5419,5581,6361,6529,6553,8101,8191,8681,9719] ++ [11119,11447,13367,14449,14951,18121,20231,20857,23279,23311,26317,29191,30269,32377,37171,38737,43691,49477,55871,61681] ++ [65537,65993,69431,71119,78233,86113,86171,87211,92737,100801,106681,121369,122921,131071,148961,152041,153649,165799,174763,178481] ++ [179951,201961,228479,246241,262657,268501,274177,279073,312709,321679,348031,354689,384773,409891,524287,525313,599479,649657,724153,858001] ++ [1212847,1868569,2099863,2298041,2332951,2796203,3033169,3887047,4036961,4327489,6700417,7327657,7416361,7623851,10567201,13264529,15790321,18837001,20394401,22253377] ++ [22366891,25781083,26295457,47392381,48544121,48912491,56409643,97685839,107367629,112901153,160465489,164511353,184481113,193707721,202029703,212885833,231769777,308761441,319020217,420778751] ++ [536903681,616318177,715827883,745988807,1824726041,2147483647,2550183799,2931542417,4278255361,4375578271,4562284561,7830118297,8831418697,23140471537,30327152671,33057806959,35532364099,54410972897,62983048367,77158673929] ++ [131105292137,158822951431,165768537521,168749965921,269089806001,487824887233,761838257287,1113491139767,1133836730401,2879347902817,2932031007403,3203431780337,4363953127297,4432676798593,5625767248687,6713103182899,7432339208719,9361973132609,9857737155463,10052678938039] ++ [13952598148481,24517014940753,28059810762433,49971617830801,67280421310721,145295143558111,1066818132868207,2646507710984041,177722253954175633,341117531003194129,581283643249112959,646675035253258729,658812288653553079,768614336404564651,1795918038741070627,2305843009213693951,4710883168879506001,5782172113400990737,9520972806333758431,32032215596496435569] ++ [86656268566282183151,3976656429941438590393,5439042183600204290159,57912614113275649087721,870035986098720987332873,2741672362528725535068727,7289088383388253664437433,8235109336690846723986161,11053036065049294753459639,13842607235828485645766393,75582488424179347083438319,618970019642690137449562111,123876132205208335762278423601,1786393878363164227858270210279,162259276829213363391578010288127,163537220852725398851434325720959,2679895157783862814690027494144991,10350794431055162386718619237468234569,170141183460469231731687303715884105727]
  have primes : ∀ a ∈ l, Nat.Prime a := by
    change ∀ a ∈ [3,3,3,3,5,5,5,7,7,7,11,11,13,17,17,19,23,29,31,37] ++ [41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131] ++ [137,139,149,151,157,167,191,193,199,223,229,233,239,241,251,257,263,271,277,281] ++ [283,307,331,337,353,397,431,433,439,457,571,577,593,601,617,631,641,673,683,727] ++ [881,911,919,937,953,1013,1103,1217,1321,1429,1613,1657,1753,1777,1801,2089,2113,2143,2351,2593] ++ [2687,2731,2833,2857,2971,3191,3391,4051,4177,4513,5153,5419,5581,6361,6529,6553,8101,8191,8681,9719] ++ [11119,11447,13367,14449,14951,18121,20231,20857,23279,23311,26317,29191,30269,32377,37171,38737,43691,49477,55871,61681] ++ [65537,65993,69431,71119,78233,86113,86171,87211,92737,100801,106681,121369,122921,131071,148961,152041,153649,165799,174763,178481] ++ [179951,201961,228479,246241,262657,268501,274177,279073,312709,321679,348031,354689,384773,409891,524287,525313,599479,649657,724153,858001] ++ [1212847,1868569,2099863,2298041,2332951,2796203,3033169,3887047,4036961,4327489,6700417,7327657,7416361,7623851,10567201,13264529,15790321,18837001,20394401,22253377] ++ [22366891,25781083,26295457,47392381,48544121,48912491,56409643,97685839,107367629,112901153,160465489,164511353,184481113,193707721,202029703,212885833,231769777,308761441,319020217,420778751] ++ [536903681,616318177,715827883,745988807,1824726041,2147483647,2550183799,2931542417,4278255361,4375578271,4562284561,7830118297,8831418697,23140471537,30327152671,33057806959,35532364099,54410972897,62983048367,77158673929] ++ [131105292137,158822951431,165768537521,168749965921,269089806001,487824887233,761838257287,1113491139767,1133836730401,2879347902817,2932031007403,3203431780337,4363953127297,4432676798593,5625767248687,6713103182899,7432339208719,9361973132609,9857737155463,10052678938039] ++ [13952598148481,24517014940753,28059810762433,49971617830801,67280421310721,145295143558111,1066818132868207,2646507710984041,177722253954175633,341117531003194129,581283643249112959,646675035253258729,658812288653553079,768614336404564651,1795918038741070627,2305843009213693951,4710883168879506001,5782172113400990737,9520972806333758431,32032215596496435569] ++ [86656268566282183151,3976656429941438590393,5439042183600204290159,57912614113275649087721,870035986098720987332873,2741672362528725535068727,7289088383388253664437433,8235109336690846723986161,11053036065049294753459639,13842607235828485645766393,75582488424179347083438319,618970019642690137449562111,123876132205208335762278423601,1786393878363164227858270210279,162259276829213363391578010288127,163537220852725398851434325720959,2679895157783862814690027494144991,10350794431055162386718619237468234569,170141183460469231731687303715884105727], Nat.Prime a
    simp only [List.forall_mem_append]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨gap155_factors0,gap155_factors1⟩,gap155_factors2⟩,gap155_factors3⟩,gap155_factors4⟩,gap155_factors5⟩,gap155_factors6⟩,gap155_factors7⟩,gap155_factors8⟩,gap155_factors9⟩,gap155_factors10⟩,gap155_factors11⟩,gap155_factors12⟩,gap155_factors13⟩,gap155_factors14⟩
  have product : l.prod = M := by decide
  have all : ∀ i : Fin 155, 0 < i.val → 2^i.val - 1 ∣ M := by decide
  have tests : ∀ a ∈ l, 23 < a → ¬ a^2 ∣ M := by decide
  intro hit
  have hitM := hit.trans (all ⟨d,lt⟩ pos)
  have divides : p ∣ M := (dvd_pow_self p (by decide : 2≠ 0)).trans hitM
  have mem := prime_in_factors p prime l primes (product.symm ▸ divides)
  exact tests p mem large hitM

end Erdos11Sieve

namespace Erdos11Sieve
open Finset

theorem prime_not_dvd_of_hit {p n j : ℕ} (hp : p.Prime) (odd : p ≠ 2)
    (hit : 2^j ≡ n [MOD p^2]) : ¬ p ∣ n := by
  intro dvd
  have modp : 2^j ≡ n [MOD p] := hit.of_dvd (dvd_pow_self p (by decide : 2≠ 0))
  exact odd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
    (hp.dvd_of_dvd_pow (Nat.modEq_zero_iff_dvd.mp (modp.trans dvd.modEq_zero_nat))))

theorem small_155 (n b : ℕ) :
    let ps : Fin 8 → ℕ := ![3,5,7,11,13,17,19,23]
    let small := (univ : Finset (Fin 8)).biUnion fun i =>
      (range 155).filter fun j => 2^(j+b) ≡ n [MOD (ps i)^2]
    small.card ≤ 49 := by
  intro ps small
  let r : Fin 8 → ℕ := ![26,8,8,2,1,2,1,1]
  have each (i : Fin 8) : ((range 155).filter (fun j => 2^(j+b) ≡ n [MOD (ps i)^2])).card ≤ r i := by
    fin_cases i
    · exact bound3 n b 155
    · exact bound5 n b 155
    · exact bound7 n b 155
    · exact bound11 n b 155
    · exact bound13 n b 155
    · exact bound17 n b 155
    · exact bound19 n b 155
    · exact bound23 n b 155
  exact (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun i _ => each i)).trans
    (by decide : (∑ i : Fin 8, r i) ≤ 49)

/-- A failure on a full block forces distinct large prime squares.
The parameter detects prime squares that divide short Mersenne numbers. -/
theorem many_distinct_exponents (clean : ∀ p d : ℕ, p.Prime → 23 < p → 0< d → d< 155 → ¬ p^2 ∣ 2^d-1)
    (n b : ℕ) (odd : Odd n) (pl : 2^(155+b) < n)
    (failure : ¬ ∃ k l : ℕ, Squarefree k ∧ n=k+2^l) :
    ∃ J : Finset ℕ, (∀ j ∈ J, j < 155) ∧ 106 ≤ J.card ∧ ∃ pick : J → ℕ,
      Function.Injective pick ∧ ∀ j, (pick j).Prime ∧ 23 < pick j ∧ ¬pick j ∣ n ∧
        (pick j)^2 ∣ n-2^(j.val+(b+1)) := by
  classical
  let ps : Fin 8 → ℕ := ![3,5,7,11,13,17,19,23]
  let small := (univ : Finset (Fin 8)).biUnion fun i =>
    (range 155).filter fun j => 2^(j+(b+1)) ≡ n [MOD (ps i)^2]
  let good := (range 155) \ small
  have sb : small.card ≤ 49 := small_155 n (b+1)
  have gc := Finset.card_le_card_sdiff_add_card (s:=range 155) (t:=small)
  have many : 106 ≤ good.card := by change 106 ≤ ((range 155) \ small).card; rw [card_range] at gc; omega
  have ge (j : good) : j.val < 155 := Finset.mem_range.mp (Finset.mem_sdiff.mp j.property).1
  have le (j : good) : 2^(j.val+(b+1)) ≤ n :=
    (Nat.pow_le_pow_right (by decide) (by have := ge j; omega : j.val+(b+1)≤ 155+b)).trans pl.le
  have existsP (j : good) : ∃ p : ℕ, p.Prime ∧ 23< p ∧ 2^(j.val+(b+1)) ≡ n [MOD p^2] := by
    let a := 2^(j.val+(b+1))
    have ale : a ≤ n := le j
    by_contra! no
    apply failure
    refine ⟨n-a,j.val+(b+1),Nat.squarefree_iff_prime_squarefree.mpr ?_,by omega⟩
    intro p hp hd
    have hit : a ≡ n [MOD p^2] := (Nat.modEq_iff_dvd' ale).mpr (by simpa only [pow_two] using hd)
    by_cases big : 23< p
    · exact no p hp big hit
    · have opts : ∀ m : Fin 24, m.val.Prime → m.val=2 ∨ ∃ i, ps i=m.val := by decide
      rcases opts ⟨p,by omega⟩ hp with two | ⟨i,eq⟩
      · change p=2 at two
        subst p
        obtain ⟨k,hk⟩ := odd
        have aa : a=2^(j.val+b)*2 := by simp [a,←Nat.add_assoc,pow_succ]
        rw [aa] at hd ale
        omega
      · apply (Finset.mem_sdiff.mp j.property).2
        refine Finset.mem_biUnion.mpr ⟨i,mem_univ _,mem_filter.mpr ⟨mem_range.mpr (ge j),?_⟩⟩
        change ps i=p at eq
        simpa only [eq] using hit
  choose pick prime large cong using existsP
  have inj : Function.Injective pick := by
    intro i j eq
    have pr := prime i
    have oddp : Odd (pick i) := pr.eq_two_or_odd'.resolve_left (by have := large i; omega)
    have cop : Nat.Coprime 2 (pick i ^ 2) := (Nat.coprime_two_left.mpr oddp).pow_right _
    have cap := card_hits_le_one (pick i^2) n (b+1) 155 cop (fun d => clean _ d pr (large i))
    have mi : i.val ∈ (range 155).filter (fun j => 2^(j+(b+1)) ≡ n [MOD pick i ^ 2]) := mem_filter.mpr ⟨mem_range.mpr (ge i),cong i⟩
    have mj : j.val ∈ (range 155).filter (fun j => 2^(j+(b+1)) ≡ n [MOD pick i ^ 2]) := mem_filter.mpr ⟨mem_range.mpr (ge j),eq ▸ cong j⟩
    exact Subtype.ext (Finset.card_le_one.mp cap i.val mi j.val mj)
  exact ⟨good,fun j hj => ge ⟨j,hj⟩,many,pick,inj,fun j =>
    ⟨prime j,large j,prime_not_dvd_of_hit (prime j) (by have := large j; omega) (cong j),
      (Nat.modEq_iff_dvd' (le j)).mp (cong j)⟩⟩

theorem many_obstructions (clean : ∀ p d : ℕ, p.Prime → 23 < p → 0< d → d< 155 → ¬ p^2 ∣ 2^d-1)
    (n b : ℕ) (odd : Odd n) (pl : 2^(155+b) < n)
    (failure : ¬ ∃ k l : ℕ, Squarefree k ∧ n=k+2^l) :
    ∃ P : Finset ℕ, 106 ≤ P.card ∧ ∀ p ∈ P, p.Prime ∧ 23 < p ∧ ¬p ∣ n ∧
      ∃ j < 155, p^2 ∣ n-2^(j+(b+1)) := by
  classical
  obtain ⟨J,rng,size,pick,inj,spec⟩ := many_distinct_exponents clean n b odd pl failure
  refine ⟨univ.image pick,?_,?_⟩
  · simpa only [Finset.card_image_of_injective _ inj,card_univ,Fintype.card_coe] using size
  · intro p hp
    obtain ⟨j,_,rfl⟩ := mem_image.mp hp
    exact ⟨(spec j).1,(spec j).2.1,(spec j).2.2.1,j.val,rng j.val j.property,(spec j).2.2.2⟩
end Erdos11Sieve

namespace Erdos11Sieve
theorem counterexample_forces_106 (n b : ℕ) (odd : Odd n) (bound : 2^(155+b) < n)
    (failure : ¬ ∃ k l : ℕ, Squarefree k ∧ n = k+2^l) :
    ∃ P : Finset ℕ, 106 ≤ P.card ∧ ∀ p ∈ P, p.Prime ∧ 23 < p ∧ ¬p ∣ n ∧
      ∃ j < 155, p^2 ∣ n-2^(j+(b+1)) :=
  many_obstructions gap155 n b odd bound failure

theorem counterexample_distinct_pairs
    (n b : ℕ) (odd : Odd n) (pl : 2^(155+b) < n)
    (failure : ¬ ∃ k l : ℕ, Squarefree k ∧ n=k+2^l) :
    ∃ J : Finset ℕ, (∀ j ∈ J, j < 155) ∧ 106 ≤ J.card ∧ ∃ pick : J → ℕ,
      Function.Injective pick ∧ ∀ j, (pick j).Prime ∧ 23 < pick j ∧ ¬pick j ∣ n ∧
        (pick j)^2 ∣ n-2^(j.val+(b+1)) :=
  many_distinct_exponents gap155 n b odd pl failure

/-- The boundary is sharp: 31² already repeats at gap 155. -/
theorem gap_155_sharp : 31^2 ∣ (2:ℕ)^155 - 1 := by decide
end Erdos11Sieve

open Finset
namespace Erdos11Sieve

/-- Each distinct large prime accounts for one obstruction and its further hits account for repeats. -/
theorem large_union_bound (n L : ℕ) :
    let hits := fun p : ℕ => (range L).filter fun j => p^2 ∣ n-2^(j+1)
    let active := ((range (n+1)).filter Nat.Prime).filter fun p => 23< p ∧ (hits p).Nonempty
    let big := (range L).filter (fun j => ∃ p ∈ (range (n+1)).filter Nat.Prime,
      23 < p ∧ p^2 ∣ n-2^(j+1))
    big.card ≤ active.card + ∑ p ∈ active, ((hits p).card-1) := by
  intro hits active big
  have included : big ⊆ active.biUnion hits := by
    intro j hj
    obtain ⟨hj,p,hp,large,divides⟩ := mem_filter.mp hj
    have hit : j ∈ hits p := mem_filter.mpr ⟨hj,divides⟩
    exact mem_biUnion.mpr ⟨p,mem_filter.mpr ⟨hp,large,j,hit⟩,hit⟩
  apply ((Finset.card_le_card included).trans Finset.card_biUnion_le).trans
  have peel : (∑ p ∈ active, (hits p).card) = ∑ p ∈ active, (1+((hits p).card-1)) := by
    apply sum_congr rfl
    intro p hp
    have pos := Finset.card_pos.mpr (mem_filter.mp hp).2.2
    omega
  rw [peel,Finset.sum_add_distrib]
  simp

theorem represent_of_distinct_and_repeated (n : ℕ) (odd : Odd n) (large : 10^7≤ n) :
    let L := Nat.log 2 (n-1)
    let hits := fun p : ℕ => (range L).filter fun j => p^2 ∣ n-2^(j+1)
    let active := ((range (n+1)).filter Nat.Prime).filter fun p => 23< p ∧ (hits p).Nonempty
    2*active.card+8 ≤ L →
    10*(∑ p ∈ active, ((hits p).card-1))+41 ≤ 2*L →
    ∃ k l : ℕ, Squarefree k ∧ n=k+2^l := by
  intro L hits active singles multiples
  have limit : 2^L < n := lt_of_le_of_lt (Nat.pow_log_le_self 2 (by omega : n-1 ≠ 0)) (by omega)
  apply represent_of_large_hits n L odd limit
  have total := large_union_bound n L
  dsimp only at total ⊢
  change _ ≤ active.card + ∑ p ∈ active, ((hits p).card-1) at total
  omega

end Erdos11Sieve

namespace Erdos11Sieve
open Finset

/-- No large prime can obstruct two terms before the first possible Mersenne collision. -/
theorem excess_zero_of_short (n L : ℕ) (fits : 2^L< n) (short : L ≤ 155) :
    let hits := fun p : ℕ => (range L).filter fun j => p^2 ∣ n-2^(j+1)
    let active := ((range (n+1)).filter Nat.Prime).filter fun p => 23< p ∧ (hits p).Nonempty
    (∑ p ∈ active, ((hits p).card-1)) = 0 := by
  intro hits active
  apply Finset.sum_eq_zero
  intro p hp
  obtain ⟨mem,large,_⟩ := mem_filter.mp hp
  have prime := (mem_filter.mp mem).2
  have cop : Nat.Coprime 2 (p^2) :=
    ((Nat.coprime_primes Nat.prime_two prime).mpr (by omega)).pow_right 2
  have one := card_hits_le_one (p^2) n 1 L cop (fun d pos lt => gap155 p d prime large pos (by omega))
  have subs : hits p ⊆ (range L).filter (fun j => 2^(j+1) ≡ n [MOD p^2]) := by
    intro j membership
    obtain ⟨idx,dvd⟩ := mem_filter.mp membership
    have jlt := mem_range.mp idx
    have le := (Nat.pow_le_pow_right (by decide : 0< 2) (by omega : j+1 ≤ L)).trans fits.le
    exact mem_filter.mpr ⟨idx,(Nat.modEq_iff_dvd' le).mpr dvd⟩
  exact Nat.sub_eq_zero_of_le ((Finset.card_le_card subs).trans one)

end Erdos11Sieve
open Finset
namespace Erdos11Sieve

/-- Subtracting the first hit injects every remaining hit into a positive Mersenne gap. -/
theorem extra_hits_le_gaps (m n shift L : ℕ) (cop : Nat.Coprime 2 m) :
    ((range L).filter fun j => 2^(j+shift) ≡ n [MOD m]).card - 1 ≤
      ((Ico 1 L).filter fun d => m ∣ 2^d-1).card := by
  let H := (range L).filter fun j => 2^(j+shift) ≡ n [MOD m]
  change H.card-1 ≤ _
  by_cases active : H.Nonempty
  · let a := H.min' active
    have ha : a ∈ H := H.min'_mem active
    rw [←Finset.card_erase_of_mem ha]
    apply Finset.card_le_card_of_injOn (fun j => j-a)
    · intro j hj
      obtain ⟨ne,hj⟩ := Finset.mem_erase.mp hj
      have le := H.min'_le j hj
      change a ≤ j at le
      obtain ⟨jl,hj⟩ := Finset.mem_filter.mp hj
      have jL := Finset.mem_range.mp jl
      have lpos : 1 ≤ j-a := Nat.sub_pos_of_lt (lt_of_le_of_ne le ne.symm)
      have upper : j-a < L := (Nat.sub_le j a).trans_lt jL
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨lpos,upper⟩,
        collision_divides m n a j shift cop le (Finset.mem_filter.mp ha).2 hj⟩
    · intro i hi j hj eq
      have li : a ≤ i := H.min'_le i (Finset.mem_erase.mp hi).2
      have lj : a ≤ j := H.min'_le j (Finset.mem_erase.mp hj).2
      change i-a=j-a at eq
      omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp active]

/-- An upper bound independent of n, involving only square divisors of Mersenne numbers. -/
theorem excess_le_mersenne_count (n shift L : ℕ) (A : Finset ℕ)
    (primes : ∀p∈A, p.Prime ∧ 23< p) :
    (∑ p ∈ A, (((range L).filter (fun j => 2^(j+shift) ≡ n [MOD p^2])).card - 1)) ≤
      ∑ d ∈ Ico 1 L, ((range (2^d)).filter fun p => p.Prime ∧ 23< p ∧ p^2∣ 2^d-1).card := by
  classical
  calc
    _ ≤ ∑ p ∈ A, ((Ico 1 L).filter fun d => p^2 ∣ 2^d-1).card := by
      refine Finset.sum_le_sum fun p hp => extra_hits_le_gaps _ _ _ _ ?_
      obtain ⟨prime,big⟩ := primes p hp
      have odd : Odd p := prime.eq_two_or_odd'.resolve_left (by omega)
      exact (Nat.coprime_two_left.mpr odd).pow_right _
    _ = ∑ p ∈ A, ∑ d ∈ Ico 1 L, (if p^2∣ 2^d-1 then 1 else 0 : ℕ) := by
      simp
    _ = ∑ d ∈ Ico 1 L, ∑ p ∈ A, (if p^2∣ 2^d-1 then 1 else 0 : ℕ) := Finset.sum_comm
    _ = ∑ d ∈ Ico 1 L, (A.filter fun p => p^2∣ 2^d-1).card := by simp
    _ ≤ _ := by
      refine Finset.sum_le_sum (fun d hd => Finset.card_le_card ?_)
      intro p hp
      obtain ⟨active,dvd⟩ := mem_filter.mp hp
      have dp := Finset.mem_Ico.mp hd
      have pow : 2 ≤ (2:ℕ)^d := by
        simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0< 2) dp.1
      have small := Nat.le_of_dvd (by omega : 0 < 2^d-1)
        ((dvd_pow_self p (by decide : 2≠ 0)).trans dvd)
      exact mem_filter.mpr ⟨mem_range.mpr (by omega),(primes p active).1,(primes p active).2,dvd⟩

end Erdos11Sieve

open Finset
namespace Erdos11Sieve

/-- Repeated divisibility obstructions are bounded uniformly in n by the short Mersenne gaps. -/
theorem natural_excess_le_mersenne (n L : ℕ) (fits : 2^L< n) :
    let hits := fun p : ℕ => (range L).filter fun j => p^2 ∣ n-2^(j+1)
    let active := ((range (n+1)).filter Nat.Prime).filter fun p => 23< p ∧ (hits p).Nonempty
    (∑ p ∈ active, ((hits p).card-1)) ≤
      ∑ d ∈ Ico 1 L, ((range (2^d)).filter fun p => p.Prime ∧ 23< p ∧ p^2∣ 2^d-1).card := by
  intro hits active
  have eq (p : ℕ) : hits p = (range L).filter (fun j => 2^(j+1) ≡ n [MOD p^2]) := by
    apply filter_congr
    intro j hj
    have lt := mem_range.mp hj
    have le := (Nat.pow_le_pow_right (by decide : 0< 2) (by omega : j+1≤ L)).trans fits.le
    exact (Nat.modEq_iff_dvd' le).symm
  simp only [eq]
  exact excess_le_mersenne_count n 1 L active (fun p hp =>
    ⟨(mem_filter.mp (mem_filter.mp hp).1).2,(mem_filter.mp hp).2.1⟩)

end Erdos11Sieve
open Finset
namespace Erdos11Sieve

/-- The eight small prime squares really can cover 49 positions in a block of 155. -/
theorem small_155_attained (t : ℕ) :
    let n : ℕ := 22583038305797579 + 24885214322418450*t
    let ps : Fin 8 → ℕ := ![3,5,7,11,13,17,19,23]
    let small := (univ : Finset (Fin 8)).biUnion fun i =>
      (range 155).filter fun j => 2^(j+1) ≡ n [MOD (ps i)^2]
    Odd n ∧ small.card=49 := by
  intro n ps small
  constructor
  · exact ⟨11291519152898789+12442607161209225*t,by dsimp [n]; omega⟩
  · let reference := (univ : Finset (Fin 8)).biUnion fun i =>
      (range 155).filter fun j => 2^(j+1) ≡ 22583038305797579 [MOD (ps i)^2]
    have moduli : ∀ i : Fin 8, (ps i)^2 ∣ 24885214322418450 := by decide
    have period (i : Fin 8) : n ≡ 22583038305797579 [MOD (ps i)^2] := by
      symm
      rw [Nat.modEq_iff_dvd' (show 22583038305797579 ≤ n by dsimp [n]; omega)]
      change (ps i)^2 ∣ (22583038305797579+24885214322418450*t)-22583038305797579
      rw [Nat.add_sub_cancel_left]
      exact dvd_mul_of_dvd_left (moduli i) t
    have eq : small = reference := by
      apply biUnion_congr rfl
      intro i _
      apply filter_congr
      intro j _
      exact ⟨fun h => h.trans (period i),fun h => h.trans (period i).symm⟩
    rw [eq]
    decide +kernel

end Erdos11Sieve
namespace Erdos11Sieve

/-- Every prescribed finite exponent window can be obstructed by arbitrarily large prime squares. -/
theorem fixed_window_obstructed (shift L cutoff lower : ℕ) :
    ∃ n : ℕ, lower < n ∧ 2^(shift+L) < n ∧ Odd n ∧
      ∀ j < L, ∃ p : ℕ, p.Prime ∧ cutoff< p ∧ p^2 ∣ n-2^(shift+j) := by
  have progressions (u : ℕ) : ∃ a M : ℕ, 0< M ∧ ∀ n, n ≡ a [MOD M] →
      Odd n ∧ ∀ j< u, ∃ p : ℕ, p.Prime ∧ cutoff< p ∧ n ≡ 2^(shift+j) [MOD p^2] := by
    induction u with
    | zero =>
      refine ⟨1,2,by decide,fun n hn => ⟨?_,by omega⟩⟩
      exact Nat.odd_iff.mpr hn
    | succ u ih =>
      obtain ⟨a,M,pos,old⟩ := ih
      obtain ⟨p,bound,prime⟩ := Nat.exists_infinite_primes (M+cutoff+1)
      have cop : Nat.Coprime M (p^2) := (prime.coprime_iff_not_dvd.mpr
        (fun h => by have := Nat.le_of_dvd pos h; omega)).symm.pow_right _
      let b := Nat.chineseRemainder cop a (2^(shift+u))
      refine ⟨b,M*p^2,Nat.mul_pos pos (pow_pos prime.pos _),fun n hn => ?_⟩
      have hM := old n ((hn.of_dvd (dvd_mul_right M _)).trans b.property.1)
      refine ⟨hM.1,fun j hj => ?_⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with before | rfl
      · exact hM.2 j before
      · exact ⟨p,prime,by omega,(hn.of_dvd (dvd_mul_left _ M)).trans b.property.2⟩
  obtain ⟨a,M,pos,found⟩ := progressions L
  let u := lower+2^(shift+L)+1
  let n := a + u*M
  have extra : u ≤ u*M := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left u pos
  have hn : n ≡ a [MOD M] := by simp [n,Nat.ModEq]
  obtain ⟨odd,all⟩ := found n hn
  have un : u ≤ n := extra.trans (Nat.le_add_left _ _)
  have bound : 2^(shift+L)< n := lt_of_lt_of_le (by dsimp [u]; omega : 2^(shift+L)< u) un
  refine ⟨n,lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_add_right lower _)) un,bound,odd,fun j hj => ?_⟩
  · obtain ⟨p,prime,big,modp⟩ := all j hj
    have below := (Nat.pow_le_pow_right (by decide : 0< 2) (by omega : shift+j≤ shift+L)).trans bound.le
    exact ⟨p,prime,big,(Nat.modEq_iff_dvd' below).mp modp.symm⟩
end Erdos11Sieve
open Finset
namespace Erdos11Sieve

theorem every_multiple_hits (m r n L u : ℕ) (hr : 0< r) (one : 2^r ≡ 1 [MOD m])
    (target : n ≡ 1 [MOD m]) (top : 2^L ≤ n) (room : u*r≤ L) :
    u ≤ ((range L).filter fun j => m∣ n-2^(j+1)).card := by
  rw [←Finset.card_range u]
  apply Finset.card_le_card_of_injOn (fun i => (i+1)*r-1)
  · intro i hi
    have il := mem_range.mp hi
    have end_le := (Nat.mul_le_mul_right r (Nat.succ_le_of_lt il)).trans room
    have pos : 0< (i+1)*r := Nat.mul_pos (Nat.succ_pos _) hr
    have eq : (i+1)*r-1+1 = (i+1)*r := by omega
    refine mem_filter.mpr ⟨mem_range.mpr ((Nat.sub_lt pos (by decide : 0< 1)).trans_le end_le),?_⟩
    change m ∣ n-2^((i+1)*r-1+1)
    rw [eq,Nat.mul_comm (i+1) r]
    apply (Nat.modEq_iff_dvd' ((Nat.pow_le_pow_right (by decide : 0< 2)
      (by simpa only [Nat.mul_comm r] using end_le)).trans top)).mp
    exact (by simpa only [pow_mul,one_pow] using one.pow (i+1) : 2^(r*(i+1)) ≡ 1 [MOD m]).trans target.symm
  · intro i hi j hj eq
    have ip := Nat.mul_pos (Nat.succ_pos i) hr
    have jp := Nat.mul_pos (Nat.succ_pos j) hr
    change (i+1)*r-1=(j+1)*r-1 at eq
    have same : (i+1)*r=(j+1)*r := by
      have add := congrArg (fun x : ℕ => x+1) eq
      simpa only [Nat.sub_add_cancel (Nat.succ_le_of_lt ip),Nat.sub_add_cancel (Nat.succ_le_of_lt jp)] using add
    exact Nat.succ.inj (Nat.eq_of_mul_eq_mul_right hr same)

theorem finite_wieferich_constraint
    (H2 : ∀ n : ℕ, Odd n → 10^7≤ n →
      let L := Nat.log 2 (n-1)
      let hits := fun p : ℕ => (range L).filter fun j => p^2 ∣ n-2^(j+1)
      let active := ((range (n+1)).filter Nat.Prime).filter fun p => 23< p ∧ (hits p).Nonempty
      156≤ L → 10*(∑p∈active, ((hits p).card-1))+41≤ 2*L)
    (S : Finset ℕ) (D : ℕ) (posD : 0< D)
    (primes : ∀p∈S, p.Prime ∧ 23< p ∧ 2^(p-1) ≡ 1 [MOD p^2] ∧ p-1∣ D) :
    5*(∑p∈S,D/(p-1)) ≤ D := by
  let M := 2*∏ p∈S,p^2
  have posprod : 0 < ∏p∈S,p^2 := Finset.prod_pos (fun p hp => pow_pos (primes p hp).1.pos _)
  have posM : 0< M := Nat.mul_pos (by decide) posprod
  let t := 156+Nat.log 2 M+5*S.card
  let K := t*D
  let n := M*2^K+1
  let L := Nat.log 2 (n-1)
  let hits := fun p : ℕ => (range L).filter fun j => p^2 ∣ n-2^(j+1)
  let active := ((range (n+1)).filter Nat.Prime).filter fun p => 23< p ∧ (hits p).Nonempty
  have logmul (k : ℕ) : Nat.log 2 (M*2^k) = Nat.log 2 M + k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ,←Nat.mul_assoc,Nat.log_mul_base (by decide)
        (Nat.mul_pos posM (pow_pos (by decide) _)).ne',ih]
      omega
  have len : L=Nat.log 2 M + K := by simpa [L,n] using logmul K
  have tK : t ≤ K := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left t posD
  have base : 156≤ t := by dsimp [t]; omega
  have top : 2^L ≤ n := (Nat.pow_log_le_self 2 (show n-1≠ 0 by dsimp [n]; positivity)).trans (Nat.sub_le _ _)
  have small : 10^7≤ n :=
    (by decide : 10^7 ≤ 2^156).trans ((Nat.pow_le_pow_right (by decide) (by omega : 156≤ L)).trans top)
  have odd : Odd n := by
    refine ⟨(∏p∈S,p^2)*2^K,?_⟩
    dsimp only [n,M]
    ring
  have upper : 10*(∑p∈active,((hits p).card-1))+41 ≤ 2*L := H2 n odd small (by omega)
  have facts (p : ℕ) (hp : p∈S) : t*(D/(p-1)) ≤ (hits p).card ∧ p∈active := by
    obtain ⟨prime,big,one,dvd⟩ := primes p hp
    have divM : p^2∣ M := (Finset.dvd_prod_of_mem (fun q : ℕ => q^2) hp).trans (dvd_mul_left _ 2)
    have modp : n ≡ 1 [MOD p^2] := by
      apply Nat.ModEq.symm
      apply (Nat.modEq_iff_dvd' (by dsimp [n]; omega)).mpr
      simpa [n] using divM.trans (dvd_mul_right M (2^K))
    have upto : t*(D/(p-1))*(p-1) ≤ L := by
      rw [Nat.mul_assoc,Nat.div_mul_cancel dvd]
      change K≤ L
      omega
    have count := every_multiple_hits (p^2) (p-1) n L _ (by omega) one modp top upto
    have pM : p ≤ M := Nat.le_of_dvd posM ((dvd_pow_self p (by decide : 2≠ 0)).trans divM)
    have Mn : M ≤ n := by
      have pw : 1≤ 2^K := Nat.one_le_pow _ _ (by decide)
      have := Nat.mul_le_mul_left M pw
      dsimp [n]
      omega
    have hh : 0 < t*(D/(p-1)) :=
      Nat.mul_pos (by omega) (Nat.div_pos (Nat.le_of_dvd posD dvd) (by omega))
    exact ⟨count,mem_filter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (by omega),prime⟩,big,
      Finset.card_pos.mp (hh.trans_le count)⟩⟩
  have subset : S⊆active := fun p hp => (facts p hp).2
  have bound : t*(∑p∈S,D/(p-1)) ≤ (∑p∈active,((hits p).card-1))+S.card := by
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑p∈S, ((hits p).card-1+1) := Finset.sum_le_sum (fun p hp => by have := (facts p hp).1; omega)
      _ = (∑p∈S,((hits p).card-1))+S.card := by simp [Finset.sum_add_distrib]
      _ ≤ _ := Nat.add_le_add_right (Finset.sum_le_sum_of_subset_of_nonneg subset (by intros; omega)) _
  by_contra! bad
  have grow := Nat.mul_le_mul_left t (Nat.succ_le_of_lt bad)
  let A := ∑p∈S,D/(p-1)
  change t*(D+1)≤ t*(5*A) at grow
  change t*A ≤ _ at bound
  rw [Nat.mul_add,Nat.mul_one,show t*(5*A)=5*(t*A) by ring] at grow
  rw [len] at upper
  change 10*(∑p∈active,((hits p).card-1))+41 ≤ 2*(Nat.log 2 M+t*D) at upper
  have big_t : Nat.log 2 M+5*S.card< t := by dsimp [t]; omega
  omega
end Erdos11Sieve

open Finset
namespace Erdos11Sieve

theorem reciprocal_of_integer_constraint (S : Finset ℕ) (pos : ∀p∈S,1< p)
    (constraint : ∀D:ℕ,0< D → (∀p∈S,p-1∣ D) → 5*(∑p∈S,D/(p-1))≤ D) :
    ∑p∈S, ((1:ℝ)/((p-1:ℕ):ℝ)) ≤ 1/5 := by
  let D := ∏p∈S,(p-1)
  have dpos : 0< D := Finset.prod_pos fun p hp => by have := pos p hp; omega
  have dv (p) (hp : p∈S) : p-1∣ D := Finset.dvd_prod_of_mem (fun p : ℕ => p-1) hp
  have scaled : 5*(∑p∈S,((D/(p-1):ℕ):ℝ))≤ (D:ℝ) := by exact_mod_cast constraint D dpos dv
  have id : (D:ℝ)*(∑p∈S,((1:ℝ)/((p-1:ℕ):ℝ))) = ∑p∈S,((D/(p-1):ℕ):ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro p hp
    have pn : 0< p-1 := by have := pos p hp; omega
    rw [Nat.cast_div (dv p hp) (by exact_mod_cast pn.ne' : ((p-1:ℕ):ℝ)≠ 0)]
    ring
  rw [←id] at scaled
  have dposR : 0< (D:ℝ) := by exact_mod_cast dpos
  nlinarith only [scaled,dposR]
end Erdos11Sieve

open Finset
namespace Erdos11Sieve

theorem rounded_prime_tail
    (bound : ∀ S : Finset ℕ, (∀p∈S,p.Prime ∧ 23< p ∧ 2^(p-1) ≡ 1 [MOD p^2]) →
      ∑p∈S, ((1:ℝ)/((p-1:ℕ):ℝ)) ≤ 1/5) (B : ℕ) :
    ∃ T : Finset ℕ, (∀ p∈T, B< p ∧ p.Prime ∧ ¬2^(p-1) ≡ 1 [MOD p^2]) ∧
      (3:ℝ)/10 ≤ ∑p∈T, 1/(p:ℝ) := by
  let k := max 24 (B+1)
  let S := (4^(k.primesBelow.card+1)).succ.primesBelow \ k.primesBelow
  let W := S.filter fun p => 2^(p-1) ≡ 1 [MOD p^2]
  have spec (p : ℕ) (hp : p∈S) : p.Prime ∧ k ≤ p := by
    obtain ⟨hp',hn⟩ := Finset.mem_sdiff.mp hp
    have pp := Nat.prime_of_mem_primesBelow hp'
    exact ⟨pp,le_of_not_gt (fun h => hn (Nat.mem_primesBelow.mpr ⟨h,pp⟩))⟩
  have upper := bound W (fun p hp => by
    obtain ⟨mem,hw⟩ := mem_filter.mp hp
    have ⟨pp,ge⟩ := spec p mem
    have := (le_max_left 24 (B+1)).trans ge
    exact ⟨pp,by omega,hw⟩)
  have cmp : (∑p∈W,(1:ℝ)/p) ≤ ∑p∈W, ((1:ℝ)/((p-1:ℕ):ℝ)) := by
    refine Finset.sum_le_sum fun p hp => ?_
    have h := (spec p (mem_filter.mp hp).1).1.one_lt
    exact one_div_le_one_div_of_le (by exact_mod_cast (show 0< p-1 by omega))
      (by exact_mod_cast Nat.sub_le p 1)
  have lower : (1:ℝ)/2 ≤ ∑p∈S,(1:ℝ)/p := one_half_le_sum_primes_ge_one_div k
  have total : (∑p∈S \ W,(1:ℝ)/p) + (∑p∈W,(1:ℝ)/p) = ∑p∈S,(1:ℝ)/p :=
    Finset.sum_sdiff (Finset.filter_subset _ S)
  refine ⟨S \ W,?_,by linarith only [total,upper,cmp,lower]⟩
  intro p hp
  obtain ⟨ms,mw⟩ := mem_sdiff.mp hp
  have ⟨pp,ge⟩ := spec p ms
  have := (le_max_right 24 (B+1)).trans ge
  exact ⟨by omega,pp,fun h => mw (mem_filter.mpr ⟨ms,h⟩)⟩

theorem repeated_hit_tail_forces_wieferich_reciprocal
    (H2 : ∀ n : ℕ, Odd n → 10^7≤ n →
      let L := Nat.log 2 (n-1)
      let hits := fun p : ℕ => (range L).filter fun j => p^2 ∣ n-2^(j+1)
      let active := ((range (n+1)).filter Nat.Prime).filter fun p => 23< p ∧ (hits p).Nonempty
      156≤ L → 10*(∑p∈active, ((hits p).card-1))+41≤ 2*L)
    (S : Finset ℕ) (primes : ∀p∈S,p.Prime ∧ 23< p ∧ 2^(p-1) ≡ 1 [MOD p^2]) :
    ∑p∈S, ((1:ℝ)/((p-1:ℕ):ℝ)) ≤ 1/5 := by
  apply reciprocal_of_integer_constraint S (fun p hp => (primes p hp).1.one_lt)
  exact fun D pos dvd => finite_wieferich_constraint H2 S D pos (fun p hp =>
    ⟨(primes p hp).1,(primes p hp).2.1,(primes p hp).2.2,dvd p hp⟩)

theorem repeated_hit_tail_forces_nonwieferich_mass
    (H2 : ∀ n : ℕ, Odd n → 10^7≤ n →
      let L := Nat.log 2 (n-1)
      let hits := fun p : ℕ => (range L).filter fun j => p^2 ∣ n-2^(j+1)
      let active := ((range (n+1)).filter Nat.Prime).filter fun p => 23< p ∧ (hits p).Nonempty
      156≤ L → 10*(∑p∈active, ((hits p).card-1))+41≤ 2*L)
    (B : ℕ) : ∃ T : Finset ℕ, (∀p∈T,B< p ∧ p.Prime ∧ ¬2^(p-1) ≡ 1 [MOD p^2]) ∧
      (3:ℝ)/10 ≤ ∑p∈T, 1/(p:ℝ) :=
  rounded_prime_tail (repeated_hit_tail_forces_wieferich_reciprocal H2) B
end Erdos11Sieve

open Finset Set Filter
open scoped Topology
namespace Erdos11Sieve

theorem series_of_nonwieferich_tail
    (mass : ∀ B : ℕ, ∃ T : Finset ℕ, (∀ p∈T,B< p ∧ p.Prime ∧ ¬2^(p-1) ≡ 1 [MOD p^2]) ∧
      (3:ℝ)/10 ≤ ∑p∈T, 1/(p:ℝ)) :
    ¬ Summable (Set.indicator {p : ℕ | p.Prime ∧ ¬2^(p-1) ≡ 1 [MOD p^2]}
      (fun p => (1:ℝ)/p)) := by
  let U := {p : ℕ | p.Prime ∧ ¬2^(p-1) ≡ 1 [MOD p^2]}
  change ¬Summable (U.indicator fun p => (1:ℝ)/p)
  intro hs
  obtain ⟨k,hk⟩ := hs.nat_tsum_vanishing
    (Iio_mem_nhds (by norm_num : (0:ℝ)< 3/10) : Iio ((3:ℝ)/10) ∈ 𝓝 0)
  obtain ⟨T,spec,big⟩ := mass k
  specialize hk (T : Set ℕ) (fun p hp => (spec p hp).1.le)
  rw [Set.mem_Iio,tsum_fintype] at hk
  have normed : (∑ p : T, U.indicator (fun n : ℕ => (1:ℝ)/n) p) = ∑ p∈T, (1:ℝ)/p := by
    rw [Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro p hp
    exact Set.indicator_of_mem (show p∈U from (spec p hp).2) (fun n : ℕ => (1:ℝ)/n)
  exact (not_lt_of_ge big) (normed ▸ hk)
theorem repeated_hit_tail_forces_divergence
    (H2 : ∀ n : ℕ, Odd n → 10^7≤ n →
      let L := Nat.log 2 (n-1)
      let hits := fun p : ℕ => (range L).filter fun j => p^2 ∣ n-2^(j+1)
      let active := ((range (n+1)).filter Nat.Prime).filter fun p => 23< p ∧ (hits p).Nonempty
      156≤ L → 10*(∑p∈active, ((hits p).card-1))+41≤ 2*L)
    : ¬ Summable (Set.indicator {p : ℕ | p.Prime ∧ ¬2^(p-1) ≡ 1 [MOD p^2]}
        (fun p => (1:ℝ)/p)) :=
  series_of_nonwieferich_tail (repeated_hit_tail_forces_nonwieferich_mass H2)

end Erdos11Sieve


namespace OMA.R_Erdos11_erdos_11_variants_not_four_dvd_R1_H1_R1

/-- An upper bound on the number of distinct primes above 23 whose squares meet the exponent interval. -/
def H1 : Prop := ∀ n : ℕ, Odd n → 10^7 ≤ n →
    let L := Nat.log 2 (n-1)
    let hits := fun p : ℕ => (Finset.range L).filter fun j => p^2 ∣ n-2^(j+1)
    let active := ((Finset.range (n+1)).filter Nat.Prime).filter fun p => 23< p ∧ (hits p).Nonempty
    2*active.card+8 ≤ L

/-- A bound on the extra exponents obstructed by a prime that has already occurred. -/
def H2 : Prop := ∀ n : ℕ, Odd n → 10^7 ≤ n →
    let L := Nat.log 2 (n-1)
    let hits := fun p : ℕ => (Finset.range L).filter fun j => p^2 ∣ n-2^(j+1)
    let active := ((Finset.range (n+1)).filter Nat.Prime).filter fun p => 23< p ∧ (hits p).Nonempty
    156 ≤ L → 10*(∑ p ∈ active, ((hits p).card-1))+41 ≤ 2*L

theorem main : H1 → H2 → OMA.R_Erdos11_erdos_11_variants_not_four_dvd_R1.H1 := by
  intro distinct repeated n odd two
  by_cases small : n < 10^7
  · exact OMA.E11.finite_odd n odd small two
  have large : 10^7 ≤ n := by omega
  let L := Nat.log 2 (n-1)
  let hits := fun p : ℕ => (Finset.range L).filter fun j => p^2 ∣ n-2^(j+1)
  let active := ((Finset.range (n+1)).filter Nat.Prime).filter fun p => 23< p ∧ (hits p).Nonempty
  apply Erdos11Sieve.represent_of_distinct_and_repeated n odd large (distinct n odd large)
  by_cases long : 156 ≤ L
  · exact repeated n odd large long
  have fits : 2^L < n := lt_of_le_of_lt (Nat.pow_log_le_self 2 (by omega : n-1 ≠ 0)) (by omega)
  have zero := Erdos11Sieve.excess_zero_of_short n L fits (by omega)
  change 10*(∑ p ∈ active, ((hits p).card-1))+41 ≤ 2*L
  change (∑ p ∈ active, ((hits p).card-1)) = 0 at zero
  have low : 23 ≤ L := by
    have h := Nat.log_mono_right (b:=2) (show 2^23≤ n-1 by omega)
    exact h.trans' (by decide : 23 ≤ Nat.log 2 (2^23))
  omega

/-- A bound for square divisors of Mersenne numbers alone suffices for H2. -/
theorem repeat_bound_of_mersenne (bound : ∀ L : ℕ, 156 ≤ L →
    10*(∑ d ∈ Finset.Ico 1 L, ((Finset.range (2^d)).filter fun p =>
      p.Prime ∧ 23< p ∧ p^2∣ 2^d-1).card)+41 ≤ 2*L) : H2 := by
  intro n _ large L hits active long
  have fits : 2^L < n := lt_of_le_of_lt (Nat.pow_log_le_self 2 (by omega : n-1 ≠ 0)) (by omega)
  have e := Erdos11Sieve.natural_excess_le_mersenne n L fits
  dsimp only at e
  exact le_trans (Nat.add_le_add_right (Nat.mul_le_mul_left 10 e) 41) (bound L long)

end OMA.R_Erdos11_erdos_11_variants_not_four_dvd_R1_H1_R1


namespace Erdos11Sieve

theorem order_dvd_iff_one (m : ℕ) (cop : Nat.Coprime 2 m) (k : ℕ) :
    orderOf (ZMod.unitOfCoprime 2 cop) ∣ k ↔ 2^k ≡ 1 [MOD m] := by
  simpa only [Nat.add_zero,pow_zero,Nat.modEq_zero_iff_dvd] using
    (powers_same_class m cop k 0 0).symm

private theorem binomial_mod_square (p t a : ℕ) :
    (1+p*t)^a ≡ 1+a*p*t [MOD p^2] := by
  induction a with
  | zero => simp [Nat.ModEq]
  | succ a ih =>
    rw [pow_succ]
    calc
      _ ≡ (1+a*p*t)*(1+p*t) [MOD p^2] := ih.mul_right _
      _ = (1+(a+1)*p*t) + p^2*(a*t^2) := by ring
      _ ≡ 1+(a+1)*p*t [MOD p^2] := by simp [Nat.ModEq, Nat.add_mod]

/-- For a non-Wieferich prime, the order of 2 gains exactly a factor p on passage to p². -/
theorem order_lift_nonwieferich (p : ℕ) (prime : p.Prime) (cop : Nat.Coprime 2 p)
    (nonw : ¬2^(p-1) ≡ 1 [MOD p^2]) :
    orderOf (ZMod.unitOfCoprime 2 (cop.pow_right 2)) =
      p * orderOf (ZMod.unitOfCoprime 2 cop) := by
  let : NeZero p := ⟨prime.ne_zero⟩
  let r := orderOf (ZMod.unitOfCoprime 2 cop)
  let R := orderOf (ZMod.unitOfCoprime 2 (cop.pow_right 2))
  have pos : 0< r := orderOf_pos _
  have fr : r ∣ p-1 := by
    have card : r ∣ Fintype.card (ZMod p)ˣ := orderOf_dvd_card
    simpa only [ZMod.card_units_eq_totient, Nat.totient_prime prime] using card
  have one := (order_dvd_iff_one (p^2) (cop.pow_right 2) R).mp (dvd_refl R)
  have down : r ∣ R := (order_dvd_iff_one p cop R).mpr
    (one.of_dvd (dvd_pow_self p (by decide : 2≠ 0)))
  have first := (order_dvd_iff_one p cop r).mp (dvd_refl r)
  have pospow : 1≤ 2^r := Nat.one_le_pow _ _ (by decide)
  obtain ⟨t,ht⟩ := (Nat.modEq_iff_dvd' pospow).mp first.symm
  have expr : 2^r=1+p*t := by omega
  have up : R ∣ r*p := by
    apply (order_dvd_iff_one (p^2) (cop.pow_right 2) (r*p)).mpr
    rw [pow_mul,expr]
    apply (binomial_mod_square p t p).trans
    rw [←sq]
    simp [Nat.ModEq,Nat.add_mod]
  obtain ⟨k,hk⟩ := down
  have kd : k ∣ p := by
    rw [hk] at up
    exact (Nat.mul_dvd_mul_iff_left pos).mp up
  rcases (Nat.dvd_prime prime).mp kd with h | h
  · rw [h,mul_one] at hk
    exact False.elim (nonw ((order_dvd_iff_one (p^2) (cop.pow_right 2) (p-1)).mp (show R ∣ p-1 by rw [hk]; exact fr)))
  · change R = p*r
    rw [hk,h,mul_comm]
end Erdos11Sieve

open Finset
namespace Erdos11Sieve

/-- When p is non-Wieferich, all contacts beyond the first cost at most L/(p·ord_p(2)). -/
theorem ordinary_extra_hits_bound (p n shift L : ℕ) (prime : p.Prime) (cop : Nat.Coprime 2 p)
    (nonw : ¬2^(p-1) ≡ 1 [MOD p^2]) :
    ((range L).filter (fun j => 2^(j+shift) ≡ n [MOD p^2])).card-1 ≤
      L/(p*orderOf (ZMod.unitOfCoprime 2 cop)) := by
  let : NeZero (p^2) := ⟨pow_ne_zero _ prime.ne_zero⟩
  have bound := one_class_bound (p^2) n shift L (cop.pow_right 2)
  dsimp only at bound
  rw [order_lift_nonwieferich p prime cop nonw] at bound
  rw [Nat.sub_le_iff_le_add]
  apply bound.trans
  split <;> omega

/-- The ordinary-prime part of the obstruction count is bounded by the reciprocal-order sum. -/
theorem ordinary_total_bound (n shift L : ℕ) (A : Finset ℕ)
    (good : ∀ p∈A, p.Prime ∧ Nat.Coprime 2 p ∧ ¬2^(p-1) ≡ 1 [MOD p^2]) :
    (↑(∑ p ∈ A, (((range L).filter (fun j => 2^(j+shift) ≡ n [MOD p^2])).card-1)) : ℝ) ≤
      (L:ℝ) * ∑ p ∈ A.attach, 1/((p.val:ℝ)*orderOf (ZMod.unitOfCoprime 2 (good p.val p.property).2.1)) := by
  rw [Finset.mul_sum, ← Finset.sum_attach A (fun p =>
    (((range L).filter (fun j => 2^(j+shift) ≡ n [MOD p^2])).card-1))]
  push_cast
  apply Finset.sum_le_sum
  intro p _
  obtain ⟨prime,cop,nonw⟩ := good p.val p.property
  let : NeZero p.val := ⟨prime.ne_zero⟩
  let r := orderOf (ZMod.unitOfCoprime 2 cop)
  have positive : 0< p.val*r := Nat.mul_pos prime.pos (orderOf_pos _)
  have bound := ordinary_extra_hits_bound p.val n shift L prime cop nonw
  have scale := (Nat.mul_le_mul_right (p.val*r) bound).trans (Nat.div_mul_le_self L (p.val*r))
  have realScale : (↑(((range L).filter (fun j => 2^(j+shift) ≡ n [MOD p.val^2])).card-1) : ℝ) *
      (p.val*r : ℕ) ≤ L := by exact_mod_cast scale
  rw [mul_one_div]
  apply (le_div_iff₀ (by exact_mod_cast positive : (0:ℝ)< (p.val:ℝ)*r)).2
  simpa only [Nat.cast_mul] using realScale

end Erdos11Sieve

namespace Erdos11Sieve
open Finset

/-- A tenth-unit reciprocal-order bound completely removes the non-Wieferich part of H2. -/
theorem repeat_bound_of_wieferich_part
    (orderBudget : ∀ (A : Finset ℕ)
        (good : ∀ p∈A, p.Prime ∧ 23< p ∧ Nat.Coprime 2 p ∧ ¬2^(p-1) ≡ 1 [MOD p^2]),
      (∑ p ∈ A.attach, 1/((p.val:ℝ)*orderOf (ZMod.unitOfCoprime 2 (good p.val p.property).2.2.1))) ≤ (1:ℝ)/10)
    (n L : ℕ) (fits : 2^L< n) :
    let hits := fun p : ℕ => (range L).filter fun j => p^2 ∣ n-2^(j+1)
    let active := ((range (n+1)).filter Nat.Prime).filter fun p => 23< p ∧ (hits p).Nonempty
    let W := active.filter fun p => 2^(p-1) ≡ 1 [MOD p^2]
    10*(∑p∈W,((hits p).card-1))+41 ≤ L →
      10*(∑p∈active,((hits p).card-1))+41 ≤ 2*L := by
  intro hits active W exceptional
  let O := active.filter fun p => ¬2^(p-1) ≡ 1 [MOD p^2]
  have good : ∀ p∈O, p.Prime ∧ 23< p ∧ Nat.Coprime 2 p ∧ ¬2^(p-1) ≡ 1 [MOD p^2] := by
    intro p hp
    obtain ⟨mem,nonw⟩ := mem_filter.mp hp
    obtain ⟨base,large,_⟩ := mem_filter.mp mem
    have prime := (mem_filter.mp base).2
    exact ⟨prime,large,(Nat.coprime_primes Nat.prime_two prime).mpr (by omega),nonw⟩
  have lower := ordinary_total_bound n 1 L O (fun p hp => ⟨(good p hp).1,(good p hp).2.2⟩)
  have mass := orderBudget O good
  have le := lower.trans (mul_le_mul_of_nonneg_left mass (Nat.cast_nonneg L))
  have eq (p : ℕ) : hits p = (range L).filter (fun j => 2^(j+1) ≡ n [MOD p^2]) := by
    apply filter_congr
    intro j hj
    have idx := mem_range.mp hj
    exact (Nat.modEq_iff_dvd' ((Nat.pow_le_pow_right (by decide : 0< 2) (by omega : j+1≤ L)).trans fits.le)).symm
  have ordinary : 10*(∑p∈O,((hits p).card-1)) ≤ L := by
    simp only [eq]
    exact_mod_cast (show (10:ℝ)*↑(∑ p ∈ O, (((range L).filter (fun j => 2^(j+1) ≡ n [MOD p^2])).card-1)) ≤ (L:ℝ) by linarith)
  have splitSum : (∑p∈W,((hits p).card-1))+(∑p∈O,((hits p).card-1)) = ∑p∈active,((hits p).card-1) :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  omega

end Erdos11Sieve

namespace Erdos11Sieve
open Finset
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem order_head_certificate :
    ∃ lowCut weightCut : ℕ → ℕ, (∀q : Fin 1024,
      23< q.val → Nat.Coprime q.val 223092870 →
      65536≤ weightCut q.val*q.val*lowCut q.val ∧ lowCut q.val≤ 64 ∧
        ∀ j : Fin 64, 0< j.val → q.val∣ 2^j.val-1 → lowCut q.val≤ j.val) ∧
      ∑p∈range 1024,weightCut p = 1783 := by
  let lowCut : ℕ → ℕ := fun p : ℕ => (0x200080000000002000000200000000000000000000200000000008000000000000080000000002000000000080000008000000000200000000000002000000000080000000002000000200000000000002000000000000000008000000000000080000008000000000000080000000000000000000080000008001b8000020000000000000000000000008000000800200000020000000000000000000020008000000000000000020008000000800200000000000000000800200000000000000000000200000000000000000800000000000000000000000200000020000000000000200000020000000000800000000000008000000800000000020000000000800000000000008000000000000000020000000000000200000000000000000800000000000002c000000002000000180000000000000000000200080000000002000000000080000008002000000000000000005a000000000000000000080020000002000000000080000000000c80800000000020000000000800000000000000002000000000080020000000000800000000020000000000000000080000000002000000000000000000000000000000080020000000000000000000020000000000800000080000000000000800000080000000000000800000000000000000000800000080020000002000000000000020000000000800000080000000002000560000000000000002000800000000000000002000000000000020000001600000000000020000000000800000080000000002000000000080000000000000800000000020000002000800000000000000000a8000000003c000000000000000000000020000002000800000080000000000000000000000020000000000000000080020000002000000000080020000000000800000000008000000000640000000000000000c0080000000000e80000200080000004a000000000000000000080000000000000000000080020000002000800000000000000002000800000000020000000000800000080000000001a0000000001e02000000000000000008002000000000080000000e00000000000000000000000e00000120080000006602000000180000000000000580000000080000004e000000000480460000080000000001e0074000000001a0000000002e000001c00a00000120000000000a00e000000000000000000000000000000000000000000000000000 >>> (7*p)) % 128
  let weightCut : ℕ → ℕ := fun p : ℕ => (0x400010000000000000400000000400000000000000000000000000400000000000010000000000000000010000000000000400000000000010000000010000000000000400000000000000000400000000000010000000000000400000000400000000000000000400000000000000000000010000000000000000010000000010000000000000000010000000000000000000000000010000000010000400000000400000000000000000000000000000010000000010000400000000400000000000000000000000000400010000000000000000000000400010000000010000400000000000000000000010000400000000000000000000000000400000000000000000000010000000000000000000000000000000400000000400000000000000000400000000400000000000010000000000000000010000000010000000000000400000000000010000000000000000010000000000000000000000400000000000000000400000000000000000000010000000000000000028000000000000400000000600000000000000000000000000400010000000000000400000000000010000000010000400000000000000000000018000000000000000000000000010000400000000400000000000010000000000000a00010000000000000400000000000010000000000000000000000400000000000010000400000000000010000000000000400000000000000000000010000000000000400000000000000000000000000000000000000010000400000000000000000000000000600000000000018000000018000000000000000018000000018000000000000000018000000000000000000000000018000000018000600000000600000000000000000600000000000018000000018000000000000600020000000000000000000000600018000000000000000000000600000000000000000600000000800000000000000000600000000000018000000018000000000000600000000000018000000000000000018000000000000600000000600018000000000000000000001400000000000038000000000000000000000000000000800000000800020000000020000000000000000000000000000000800000000000000000000020000800000000800000000000020000800000000000020000000000002000000000000030000000000000000000001800028000000000001400000000a00028000000040000000000000000000000000028000000000000000000000000030000c00000000c00030000000000000000000000c00030000000000000c000000000000380000000380000000000012000000000000e8000e00000000000000000000040001000000000000040000000250000000000000000000000000000002a00000002200050000000068001600000001e000000000000000086000000000000680000000b000000000000c8000d80000000800000000000024000a00000000000030000000000001e800000036800a000000006400000000000d3800a200000000000000000000000000000000000000000000000000000000000000000 >>> (9*p)) % 512
  let row (q : ℕ) : Prop :=
    23< q → Nat.Coprime q 223092870 → 65536≤ weightCut q*q*lowCut q ∧ lowCut q≤ 64 ∧
    ∀ j : Fin 64, 0< j.val → q∣ 2^j.val-1 → lowCut q≤ j.val
  have checks (i : Fin 32) : ∀j : Fin 32, row (32*i.val+j.val) := by
    fin_cases i <;> dsimp only [row,lowCut,weightCut] <;> decide +kernel
  refine ⟨lowCut,weightCut,?_,by dsimp only [weightCut]; decide +kernel⟩
  intro q
  have bound : q.val/32< 32 := (Nat.div_lt_iff_lt_mul (by decide)).mpr q.isLt
  have t := checks ⟨_,bound⟩ ⟨q.val%32,Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using t

theorem wheel_coprime {p : ℕ} (hp : p.Prime) (big : 23< p) : Nat.Coprime p 223092870 := by
  apply hp.coprime_iff_not_dvd.mpr
  intro dv
  have fixed : ∀ a ∈ [2,3,5,7,11,13,17,19,23], Nat.Prime a := by decide
  have lim : ∀ a ∈ [2,3,5,7,11,13,17,19,23], a≤ 23 := by decide
  have h := prime_in_factors p hp _ fixed (by exact dv)
  exact (Nat.not_le.mpr big) (lim p h)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem small_order_reciprocal (S : Finset ℕ) (r : ℕ → ℕ)
    (valid : ∀p∈S,p.Prime ∧ 23< p ∧ p< 1024 ∧ 0< r p ∧ p∣ 2^(r p)-1) :
    (∑p∈S, (1:ℝ)/((p:ℝ)*(r p:ℝ))) ≤ 1/32 := by
  obtain ⟨lowCut,weightCut,rows1024,total⟩ := order_head_certificate
  have point (p : ℕ) (hp : p∈S) : (1:ℝ)/((p:ℝ)*(r p:ℝ)) ≤ (weightCut p:ℝ)/65536 := by
    obtain ⟨prime,big,small,positive,period⟩ := valid p hp
    obtain ⟨bound,leCap,truncated⟩ := (rows1024 ⟨p,small⟩) big (wheel_coprime prime big)
    change lowCut p ≤ 64 at leCap
    have le : lowCut p ≤ r p := by
      by_cases hr : r p< 64
      · exact truncated ⟨_,hr⟩ positive period
      · omega
    have finalN : 65536 ≤ weightCut p * p * (r p) := bound.trans (Nat.mul_le_mul_left _ le)
    have pp : 0< (p:ℝ) := by exact_mod_cast prime.pos
    have rp : 0< (r p:ℝ) := by exact_mod_cast positive
    apply (div_le_div_iff₀ (mul_pos pp rp) (by norm_num)).mpr
    simpa only [one_mul,mul_assoc] using (show (65536:ℝ) ≤ (weightCut p:ℝ)*p*(r p) by exact_mod_cast finalN)
  have subset : S⊆range 1024 := fun p hp => Finset.mem_range.mpr (valid p hp).2.2.1
  have wt : ∑p∈S,weightCut p ≤ 1783 := total ▸ Finset.sum_le_sum_of_subset_of_nonneg subset (by intros; omega)
  calc
    _ ≤ ∑p∈S,(weightCut p:ℝ)/65536 := Finset.sum_le_sum point
    _ = ((∑p∈S,weightCut p : ℕ):ℝ)/65536 := by push_cast; rw [Finset.sum_div]
    _ ≤ 1/32 := by
      have : ((∑p∈S,weightCut p : ℕ):ℝ) ≤ 1783 := by exact_mod_cast wt
      linarith only [this]

end Erdos11Sieve

open Finset
namespace Erdos11Sieve

theorem order_fiber_card (d : ℕ) (pos : 0< d) (F : Finset ℕ)
    (valid : ∀p∈F,p.Prime ∧ 1024≤ p ∧ p∣ 2^d-1) : 10*F.card ≤ d := by
  have posM : 0< 2^d-1 := Nat.sub_pos_of_lt (Nat.one_lt_pow pos.ne' (by decide))
  have sub : F ⊆ (2^d-1).primeFactors := fun p hp =>
    Nat.mem_primeFactors.mpr ⟨(valid p hp).1,(valid p hp).2.2,posM.ne'⟩
  have prod := Nat.le_of_dvd posM
    ((Finset.prod_dvd_prod_of_subset F _ (fun p : ℕ => p) sub).trans (Nat.prod_primeFactors_dvd _))
  have base : (1024:ℕ)^F.card ≤ ∏p∈F,p := by
    simpa using (Finset.prod_le_prod' (fun p hp => (valid p hp).2.1))
  have small : (2:ℕ)^(10*F.card) ≤ 2^d := by
    rw [pow_mul]; exact (base.trans prod).trans (Nat.sub_le _ _)
  exact (Nat.pow_le_pow_iff_right (by decide : 1< 2)).mp small

theorem order_shell (a : ℕ) (ha : 32≤ a) (S : Finset ℕ) (r : ℕ → ℕ)
    (valid : ∀p∈S,p.Prime ∧ a*a≤ p ∧ p< 4*(a*a) ∧ 0< r p ∧ p∣ 2^(r p)-1) :
    (∑p∈S,(1:ℝ)/((p:ℝ)*(r p:ℝ))) ≤ 11/(10*(a:ℝ)) := by
  classical
  let f (p : ℕ) := (1:ℝ)/((p:ℝ)*(r p:ℝ))
  let low := S.filter (fun p => r p≤ 5*a)
  let high := S.filter (fun p => ¬r p≤ 5*a)
  have ap : 0< (a:ℝ) := by exact_mod_cast (show 0< a by omega)
  have al : 1024≤ a*a := by nlinarith only [ha,Nat.mul_le_mul ha ha]
  have lows (p : ℕ) (hp : p ∈ low) : r p ∈ Finset.Icc 1 (5*a) :=
    Finset.mem_Icc.mpr ⟨(valid p (mem_filter.mp hp).1).2.2.2.1,(mem_filter.mp hp).2⟩
  have per (d : ℕ) (hd : d∈Finset.Icc 1 (5*a)) :
      (∑p∈low.filter (fun p => r p=d),f p) ≤ 1/(10*(a:ℝ)*a) := by
    let F := low.filter (fun p => r p=d)
    have pos : 0< d := (Finset.mem_Icc.mp hd).1
    have dp : 0< (d:ℝ) := by exact_mod_cast pos
    have prs (p : ℕ) (hp : p∈F) : p∈S ∧ r p=d := ⟨(mem_filter.mp (mem_filter.mp hp).1).1,(mem_filter.mp hp).2⟩
    have bound := order_fiber_card d pos F (fun p hp => by
      obtain ⟨hs,eq⟩ := prs p hp
      obtain ⟨prime,G,_,_,modp⟩ := valid p hs
      exact ⟨prime,al.trans G,eq ▸ modp⟩)
    have one (p : ℕ) (hp : p∈F) : f p ≤ 1/((a:ℝ)*a*d) := by
      obtain ⟨hs,eq⟩ := prs p hp
      dsimp only [f]
      rw [eq]
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.mul_le_mul_right d (valid p hs).2.1
    calc
      _ ≤ F.card • (1/((a:ℝ)*a*d)) := Finset.sum_le_card_nsmul F f _ one
      _ ≤ _ := by
        rw [nsmul_eq_mul]
        have b : 10*(F.card:ℝ)≤ d := by exact_mod_cast bound
        field_simp
        linarith only [b]
  have lowBound : (∑p∈low,f p) ≤ 1/(2*(a:ℝ)) := by
    rw [←Finset.sum_fiberwise_of_maps_to lows f]
    refine (Finset.sum_le_card_nsmul (Finset.Icc 1 (5*a)) _ _ per).trans ?_
    simp only [Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat]
    field_simp
    ring_nf
    rfl
  have hc : high.card ≤ 3*(a*a) := by
    have sub : high ⊆ Finset.Ico (a*a) (4*(a*a)) := fun p hp => by
      obtain ⟨_,lo,hi,_,_⟩ := valid p (mem_filter.mp hp).1
      exact Finset.mem_Ico.mpr ⟨lo,hi⟩
    have h := Finset.card_le_card sub
    rw [Nat.card_Ico] at h
    omega
  have highBound : (∑p∈high,f p) ≤ 3/(5*(a:ℝ)) := by
    have each (p : ℕ) (hp : p∈high) : f p ≤ 1/((a:ℝ)*a*(5*a)) := by
      obtain ⟨hs,ng⟩ := mem_filter.mp hp
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.mul_le_mul (valid p hs).2.1 (Nat.le_of_lt (Nat.lt_of_not_ge ng))
    refine (Finset.sum_le_card_nsmul high f _ each).trans ?_
    rw [nsmul_eq_mul]
    have b : (high.card:ℝ) ≤ 3*((a:ℝ)*a) := by exact_mod_cast hc
    field_simp
    nlinarith only [b]
  have partition : (∑p∈low,f p)+(∑p∈high,f p)=∑p∈S,f p :=
    Finset.sum_filter_add_sum_filter_not S _ f
  change (∑p∈S,f p) ≤ _
  rw [←partition]
  refine (add_le_add lowBound highBound).trans ?_
  field_simp
  ring_nf
  rfl

end Erdos11Sieve

namespace Erdos11Sieve
open Finset

/-- The contribution of primes at least 1024 to the reciprocal order estimate. -/
theorem large_order_reciprocal (S : Finset ℕ) (r : ℕ → ℕ)
    (valid : ∀p∈S, p.Prime ∧ 1024≤ p ∧ 0< r p ∧ p∣ 2^(r p)-1) :
    (∑p∈S,(1:ℝ)/((p:ℝ)*(r p:ℝ))) ≤ 11/160 := by
  classical
  let f (p : ℕ) := (1:ℝ)/((p:ℝ)*(r p:ℝ))
  let a (i : ℕ) := 32*(2:ℕ)^i
  let cut (i : ℕ) := S.filter fun p => p< a i*a i
  have apos (i : ℕ) : 32 ≤ a i := by
    dsimp [a]
    have := Nat.mul_le_mul_left 32 (Nat.one_le_pow i 2 (by decide))
    omega
  have double (i : ℕ) : a (i+1)=2*a i := by dsimp [a]; rw [pow_succ]; ring
  have bounded (i : ℕ) : (∑p∈cut i, f p) ≤ 11/160 - 11/(5*(a i:ℝ)) := by
    induction i with
    | zero =>
      have empty : cut 0 = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro p hp
        obtain ⟨hs,lt⟩ := mem_filter.mp hp
        have ge := (valid p hs).2.1
        change p< 1024 at lt
        omega
      simp [empty,a]
      norm_num
    | succ i ih =>
      let T := cut (i+1) \ cut i
      have sq : a (i+1)*a (i+1)=4*(a i*a i) := by rw [double]; ring
      have inc : cut i ⊆ cut (i+1) := by
        intro p hp
        obtain ⟨hs,lt⟩ := mem_filter.mp hp
        exact mem_filter.mpr ⟨hs,sq ▸ (show p< 4*(a i*a i) by omega)⟩
      have shell := order_shell (a i) (apos i) T r (by
        intro p hp
        obtain ⟨current,old⟩ := mem_sdiff.mp hp
        obtain ⟨hs,top⟩ := mem_filter.mp current
        obtain ⟨pp,_,rpos,dvd⟩ := valid p hs
        have before : ¬p< a i*a i := fun lt => old (mem_filter.mpr ⟨hs,lt⟩)
        exact ⟨pp,by omega,sq ▸ top,rpos,dvd⟩)
      have sum : (∑p∈T,f p)+(∑p∈cut i,f p)=∑p∈cut (i+1),f p := Finset.sum_sdiff inc
      have positive : 0< (a i:ℝ) := by exact_mod_cast (show 0< a i from lt_of_lt_of_le (by decide) (apos i))
      rw [←sum,double]
      refine (add_le_add shell ih).trans ?_
      push_cast
      field_simp
      ring_nf
      rfl
  let k := S.sup id
  have final : cut k = S := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    have pm : p≤ k := Finset.le_sup (f:=id) hp
    have e : k < 2^k := Nat.lt_two_pow_self
    have small : 2^k ≤ a k := by dsimp [a]; omega
    have grow : a k ≤ a k*a k := by
      have gr : 1≤ a k := (by have := apos k; omega)
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (a k) gr
    omega
  rw [←final]
  exact (bounded k).trans (sub_le_self _ (by positivity))
end Erdos11Sieve

namespace Erdos11Sieve
open Finset

theorem order_weighted_tenth (S : Finset ℕ) (r : ℕ → ℕ)
    (valid : ∀p∈S,p.Prime ∧ 23< p ∧ 0< r p ∧ p∣ 2^(r p)-1) :
    (∑p∈S,(1:ℝ)/((p:ℝ)*(r p:ℝ))) ≤ 1/10 := by
  let small := S.filter (fun p => p< 1024)
  let large := S.filter (fun p => ¬p< 1024)
  have sh := small_order_reciprocal small r (fun p hp => by
    obtain ⟨mem,head⟩ := mem_filter.mp hp
    exact ⟨(valid p mem).1,(valid p mem).2.1,head,(valid p mem).2.2⟩)
  have bg := large_order_reciprocal large r (fun p hp => by
    obtain ⟨mem,tail⟩ := mem_filter.mp hp
    exact ⟨(valid p mem).1,le_of_not_gt tail,(valid p mem).2.2⟩)
  rw [←Finset.sum_filter_add_sum_filter_not S (fun p => p< 1024)]
  exact (add_le_add sh bg).trans (by norm_num)

theorem ordinary_order_budget (A : Finset ℕ)
    (good : ∀p∈A,p.Prime ∧ 23< p ∧ Nat.Coprime 2 p ∧ ¬2^(p-1)≡1 [MOD p^2]) :
    (∑p∈A.attach,(1:ℝ)/((p.val:ℝ)*orderOf (ZMod.unitOfCoprime 2 (good p.val p.property).2.2.1))) ≤ 1/10 := by
  classical
  let r (p : ℕ) : ℕ := if hp:p∈A then orderOf (ZMod.unitOfCoprime 2 (good p hp).2.2.1) else 1
  have ok (p : ℕ) (hp : p∈A) : p.Prime ∧ 23< p ∧ 0< r p ∧ p∣ 2^(r p)-1 := by
    obtain ⟨prime,big,cop,_⟩ := good p hp
    let : NeZero p := ⟨prime.ne_zero⟩
    have k : r p = orderOf (ZMod.unitOfCoprime 2 cop) := dif_pos hp
    rw [k]
    refine ⟨prime,big,orderOf_pos _,?_⟩
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by decide))).mp
      ((order_dvd_iff_one p cop _).mp (dvd_refl _)).symm
  have bound := order_weighted_tenth A r ok
  calc
    _ = ∑p∈A.attach,(1:ℝ)/((p.val:ℝ)*r p.val) := by
      apply Finset.sum_congr rfl
      intro p _
      simp [r,p.property]
    _ = ∑p∈A,(1:ℝ)/((p:ℝ)*r p) := Finset.sum_attach A (fun p : ℕ => (1:ℝ)/((p:ℝ)*r p))
    _ ≤ _ := bound

theorem repeated_hit_bound_from_wieferich (n L : ℕ) (fits : 2^L< n) :
    let hits := fun p : ℕ => (range L).filter fun j => p^2 ∣ n-2^(j+1)
    let active := ((range (n+1)).filter Nat.Prime).filter fun p => 23< p ∧ (hits p).Nonempty
    let W := active.filter fun p => 2^(p-1) ≡ 1 [MOD p^2]
    10*(∑p∈W,((hits p).card-1))+41≤ L → 10*(∑p∈active,((hits p).card-1))+41≤ 2*L :=
  repeat_bound_of_wieferich_part ordinary_order_budget n L fits

end Erdos11Sieve


open Finset
namespace Erdos11Sieve

/-- For any prime p, the reciprocal order of 2 modulo p² controls the number of repeat hits. -/
theorem square_order_total (n L : ℕ) (fits : 2^L< n) (A : Finset ℕ)
    (good : ∀ p∈A, p.Prime ∧ 23< p ∧ Nat.Coprime 2 p) :
    (↑(∑p∈A, (((range L).filter (fun j => p^2 ∣ n-2^(j+1))).card-1)) : ℝ) ≤
      (L:ℝ) * ∑ p ∈ A.attach, 1/(orderOf (ZMod.unitOfCoprime 2 ((good p.val p.property).2.2.pow_right 2)):ℝ) := by
  rw [Finset.mul_sum, ← Finset.sum_attach A (fun p =>
    (((range L).filter (fun j => p^2 ∣ n-2^(j+1))).card-1))]
  push_cast
  apply Finset.sum_le_sum
  intro p _
  obtain ⟨prime,_,cop⟩ := good p.val p.property
  let : NeZero (p.val^2) := ⟨pow_ne_zero _ prime.ne_zero⟩
  let r := orderOf (ZMod.unitOfCoprime 2 (cop.pow_right 2))
  have pos : 0< r := orderOf_pos _
  have eq : (range L).filter (fun j => p.val^2 ∣ n-2^(j+1)) =
      (range L).filter (fun j => 2^(j+1) ≡ n [MOD p.val^2]) := by
    apply filter_congr
    intro j hj
    have idx := mem_range.mp hj
    exact (Nat.modEq_iff_dvd' ((Nat.pow_le_pow_right (by decide : 0< 2) (by omega : j+1≤ L)).trans fits.le)).symm
  rw [eq, mul_one_div]
  apply (le_div_iff₀ (by exact_mod_cast pos : (0:ℝ)< r)).2
  have hit := one_class_bound (p.val^2) n 1 L (cop.pow_right 2)
  have ub : (((range L).filter (fun j => 2^(j+1) ≡ n [MOD p.val^2])).card-1) ≤ L/r := by
    rw [Nat.sub_le_iff_le_add]
    apply hit.trans
    dsimp only [r]
    split <;> omega
  exact_mod_cast (Nat.mul_le_mul_right r ub).trans (Nat.div_mul_le_self L r)

end Erdos11Sieve

open Finset
namespace Erdos11Sieve

/-- With the ordinary-prime budget, a uniform bound on reciprocal orders of Wieferich
primes alone suffices for every length in the repeated-hit hypothesis. -/
theorem repeat_bound_of_exceptional_orders
    (ordinaryBudget : ∀ (A : Finset ℕ)
        (good : ∀p∈A, p.Prime ∧ 23< p ∧ Nat.Coprime 2 p ∧ ¬2^(p-1) ≡ 1 [MOD p^2]),
      (∑ p ∈ A.attach, 1/((p.val:ℝ)*orderOf (ZMod.unitOfCoprime 2 (good p.val p.property).2.2.1))) ≤ (1:ℝ)/10)
    (exceptionalBudget : ∀ (W : Finset ℕ)
        (good : ∀p∈W, p.Prime ∧ 23< p ∧ Nat.Coprime 2 p ∧ 2^(p-1) ≡ 1 [MOD p^2]),
      (∑p∈W.attach, 1/(orderOf (ZMod.unitOfCoprime 2 ((good p.val p.property).2.2.1.pow_right 2)):ℝ)) ≤ (1:ℝ)/15)
    (n L : ℕ) (fits : 2^L< n) (long : 156≤ L) :
    let hits := fun p : ℕ => (range L).filter fun j => p^2 ∣ n-2^(j+1)
    let active := ((range (n+1)).filter Nat.Prime).filter fun p => 23< p ∧ (hits p).Nonempty
    10*(∑p∈active,((hits p).card-1))+41 ≤ 2*L := by
  intro hits active
  apply repeat_bound_of_wieferich_part ordinaryBudget n L fits
  let W := active.filter fun p => 2^(p-1) ≡ 1 [MOD p^2]
  have good : ∀ p ∈ W, p.Prime ∧ 23< p ∧ Nat.Coprime 2 p ∧ 2^(p-1) ≡ 1 [MOD p^2] := by
    intro p hp
    obtain ⟨mem,wieferich⟩ := mem_filter.mp hp
    obtain ⟨base,large,_⟩ := mem_filter.mp mem
    have prime := (mem_filter.mp base).2
    exact ⟨prime,large,(Nat.coprime_primes Nat.prime_two prime).mpr (by omega),wieferich⟩
  have counted := square_order_total n L fits W (fun p hp =>
    ⟨(good p hp).1,(good p hp).2.1,(good p hp).2.2.1⟩)
  have upper := counted.trans (mul_le_mul_of_nonneg_left (exceptionalBudget W good) (Nat.cast_nonneg L))
  let E := ∑p∈W,((hits p).card-1)
  change 10*E+41 ≤ L
  change (E:ℝ) ≤ (L:ℝ)*(1/15:ℝ) at upper
  exact_mod_cast (show 10*(E:ℝ)+41≤ (L:ℝ) by
    linarith [show (156:ℝ)≤ (L:ℝ) by exact_mod_cast long])

end Erdos11Sieve

namespace OMA.R_Erdos11_erdos_11_variants_not_four_dvd_R1_H1_R1
/-- Reciprocal orders on the exceptional base-2 Wieferich primes suffice for H2.
The contribution from all ordinary primes has already been bounded unconditionally. -/
theorem repeat_bound_of_wieferich_orders
    (budget : ∀ (W : Finset ℕ)
       (good : ∀p∈W, p.Prime ∧ 23 < p ∧ Nat.Coprime 2 p ∧ 2^(p-1) ≡ 1 [MOD p^2]),
       (∑p∈W.attach, 1/(orderOf (ZMod.unitOfCoprime 2 ((good p.val p.property).2.2.1.pow_right 2)):ℝ)) ≤ (1:ℝ)/15) : H2 := by
  intro n _ large L hits active long
  have fits : 2^L < n := lt_of_le_of_lt (Nat.pow_log_le_self 2 (by omega : n-1 ≠ 0)) (by omega)
  exact Erdos11Sieve.repeat_bound_of_exceptional_orders Erdos11Sieve.ordinary_order_budget budget n L fits long
end OMA.R_Erdos11_erdos_11_variants_not_four_dvd_R1_H1_R1

