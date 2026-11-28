import OMAReductions.R_Erdos929_erdos_929_variants_rosser_R1_H1_R1
import Mathlib

section
theorem ite_eq_left {α : Sort*} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort*} {c : Prop} [Decidable c] {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
theorem Finset.prod_le_prod₀ {ι R : Type*} [CommMonoidWithZero R] [Preorder R] [ZeroLEOneClass R]
    [PosMulMono R] {f g : ι → R} {s : Finset ι} (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := Finset.prod_le_prod h0 h1
theorem Finset.prod_le_one₀ {ι R : Type*} [CommMonoidWithZero R] [Preorder R] [ZeroLEOneClass R]
    [PosMulMono R] {f : ι → R} {s : Finset ι} (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) :
    ∏ i ∈ s, f i ≤ 1 := Finset.prod_le_one h0 h1
theorem Finset.one_le_prod₀ {ι R : Type*} [CommMonoidWithZero R] [Preorder R] [ZeroLEOneClass R]
    [PosMulMono R] {f : ι → R} {s : Finset ι} (h : ∀ i ∈ s, 1 ≤ f i) :
    1 ≤ ∏ i ∈ s, f i := Finset.one_le_prod h
end
section
open Real Finset
namespace IwaniecLinearSieve
noncomputable def primesLT (z : ℝ) : Finset ℕ := Nat.primesBelow ⌈z⌉₊
noncomputable def gTwoFormula (s : ℝ) : ℝ := 3 * log (3 / (s - 1)) + s - 4
noncomputable def gLower (i : ℕ) : ℝ := if Even i then 2 else 3
noncomputable def shiftKernel (h : ℝ → ℝ) (t : ℝ) : ℝ := h (t - 1) / max (t - 1) 1
noncomputable def g : ℕ → ℝ → ℝ
  | 0, _ => 0
  | 1, _ => 0
  | 2, s => gTwoFormula (max 2 (min s 4))
  | n + 3, s => ∫ t in max s (gLower (n + 3))..((n : ℝ) + 5), shiftKernel (g (n + 2)) t
noncomputable def fSieve (s : ℝ) : ℝ := ∑' n : ℕ, g (2 * n + 2) s
noncomputable def FSieve (s : ℝ) : ℝ := ∑' n : ℕ, g (2 * n + 3) s
namespace Delay
noncomputable def step (k y₀ y : ℝ → ℝ) (s : ℝ) : ℝ :=
  y₀ (min s 3) + ∫ x in (3 : ℝ)..max s 3, k x * y (x - 1)
noncomputable def iter (k y₀ : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => y₀
  | n + 1 => step k y₀ (iter k y₀ n)
noncomputable def sol (k y₀ : ℝ → ℝ) (s : ℝ) : ℝ := iter k y₀ ⌈s⌉₊ s
end Delay
noncomputable def delayKer (x : ℝ) : ℝ := max x 3 / (max x 3 - 1) ^ 2
noncomputable def initW (s : ℝ) : ℝ := 1 / (max s 2 - 1) - log (max s 2 - 1)
noncomputable def bigM : ℝ → ℝ := Delay.sol (fun x => -delayKer x) (fun s => 2 + initW s)
end IwaniecLinearSieve
end
section
open Real
namespace IwaniecLinearSieve
noncomputable def primorialLT (z : ℝ) : ℕ := ∏ p ∈ primesLT z, p
noncomputable def R (z : ℝ) : ℝ := ∏ p ∈ primesLT z, (1 - (p : ℝ)⁻¹)
theorem mem_primesLT {z : ℝ} {p : ℕ} : p ∈ primesLT z ↔ p.Prime ∧ (p : ℝ) < z := by
  simp [primesLT, Nat.mem_primesBelow, Nat.lt_ceil, and_comm]
theorem R_nonneg (z : ℝ) : 0 ≤ R z :=
  Finset.prod_nonneg fun p hp ↦ sub_nonneg.2 <| inv_le_one_of_one_le₀ <| by
    exact_mod_cast (mem_primesLT.1 hp).1.one_lt.le
theorem R_pos (z : ℝ) : 0 < R z :=
  Finset.prod_pos fun p hp ↦ sub_pos.2 <| inv_lt_one_of_one_lt₀ <| by
    exact_mod_cast (mem_primesLT.1 hp).1.one_lt
end IwaniecLinearSieve
end
section
open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius
namespace IwaniecLinearSieve
section primesLT
variable {z : ℝ} {p : ℕ}
theorem lt_ceil_of_mem_primesLT (hp : p ∈ primesLT z) : p < ⌈z⌉₊ :=
  Nat.lt_of_mem_primesBelow hp
theorem prime_of_mem_primesLT (hp : p ∈ primesLT z) : p.Prime :=
  (mem_primesLT.1 hp).1
theorem lt_of_mem_primesLT (hp : p ∈ primesLT z) : (p : ℝ) < z :=
  (mem_primesLT.1 hp).2
theorem primesLT_natCast_subset (hp : p ∈ primesLT z) : primesLT p ⊆ primesLT z := by
  intro q hq
  rw [mem_primesLT] at hq ⊢
  exact ⟨hq.1, hq.2.trans (lt_of_mem_primesLT hp)⟩
theorem notMem_primesLT_self : p ∉ primesLT p := by
  simp [mem_primesLT]
theorem primesLT_natCast_ssubset (hp : p ∈ primesLT z) : primesLT p ⊂ primesLT z :=
  ssubset_of_subset_of_ne (primesLT_natCast_subset hp) fun h ↦
    notMem_primesLT_self (h ▸ hp)
theorem filter_lt_primesLT (hp : p ∈ primesLT z) :
    (primesLT z).filter (· < p) = primesLT p := by
  ext q
  simp only [mem_filter, mem_primesLT, Nat.cast_lt]
  constructor
  · rintro ⟨⟨hq, -⟩, hqp⟩
    exact ⟨hq, hqp⟩
  · rintro ⟨hq, hqp⟩
    exact ⟨⟨hq, (Nat.cast_lt.2 hqp).trans (lt_of_mem_primesLT hp)⟩, hqp⟩
theorem primesLT_induction {P : ℝ → Prop} (h : ∀ z, (∀ p ∈ primesLT z, P p) → P z) (z : ℝ) :
    P z := by
  suffices ∀ n : ℕ, ∀ z : ℝ, ⌈z⌉₊ = n → P z from this _ z rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rintro z rfl
    exact h z fun p hp ↦ ih p (by simpa using lt_ceil_of_mem_primesLT hp) p (by simp)
theorem R_eq (z : ℝ) : R z = 1 - ∑ p ∈ primesLT z, R p / p := by
  rw [R, prod_one_sub_ordered]
  congr 1
  refine sum_congr rfl fun p hp ↦ ?_
  rw [filter_lt_primesLT hp, R, div_eq_inv_mul]
end primesLT
noncomputable def rosserPrimes (lower : Bool) (y z : ℝ) : Finset ℕ :=
  (primesLT z).filter fun p ↦ lower = true ∨ (p : ℝ) ^ 3 < y
noncomputable def rosserSet (lower : Bool) (y z : ℝ) : Finset ℕ :=
  insert 1 ((rosserPrimes lower y z).attach.biUnion fun p ↦
    (rosserSet (!lower) (y / p.1) p.1).image (p.1 * ·))
termination_by ⌈z⌉₊
decreasing_by
  rw [Nat.ceil_natCast]
  exact lt_ceil_of_mem_primesLT (mem_filter.1 p.2).1
variable {lower : Bool} {y z : ℝ} {p d : ℕ}
theorem mem_rosserPrimes :
    p ∈ rosserPrimes lower y z ↔ p ∈ primesLT z ∧ (lower = true ∨ (p : ℝ) ^ 3 < y) :=
  mem_filter
@[simp] theorem rosserPrimes_true : rosserPrimes true y z = primesLT z := by
  simp [rosserPrimes]
theorem rosserPrimes_false :
    rosserPrimes false y z = (primesLT z).filter fun p : ℕ ↦ (p : ℝ) ^ 3 < y := by
  simp [rosserPrimes]
theorem rosserPrimes_subset : rosserPrimes lower y z ⊆ primesLT z :=
  filter_subset _ _
theorem rosserSet_eq (lower : Bool) (y z : ℝ) :
    rosserSet lower y z = insert 1 ((rosserPrimes lower y z).biUnion fun p ↦
      (rosserSet (!lower) (y / p) p).image (p * ·)) := by
  rw [rosserSet]
  ext d
  simp
theorem one_mem_rosserSet : 1 ∈ rosserSet lower y z := by
  rw [rosserSet_eq]
  exact mem_insert_self _ _
theorem mem_rosserSet : d ∈ rosserSet lower y z ↔
    d = 1 ∨ ∃ p ∈ rosserPrimes lower y z, ∃ e ∈ rosserSet (!lower) (y / p) p, d = p * e := by
  rw [rosserSet_eq]
  simp [eq_comm (a := d)]
theorem squarefree_and_primeFactors_subset (hd : d ∈ rosserSet lower y z) :
    Squarefree d ∧ d.primeFactors ⊆ primesLT z := by
  induction z using primesLT_induction generalizing lower y d with
  | h z ih =>
    rcases mem_rosserSet.1 hd with rfl | ⟨p, hp, e, he, rfl⟩
    · simp
    have hpz := rosserPrimes_subset hp
    have hpp := prime_of_mem_primesLT hpz
    obtain ⟨hse, hpe⟩ := ih p hpz he
    have hne : ¬ p ∣ e := fun h ↦
      notMem_primesLT_self (hpe (Nat.mem_primeFactors.2 ⟨hpp, h, hse.ne_zero⟩))
    refine ⟨Nat.squarefree_mul_iff.2 ⟨(Nat.Prime.coprime_iff_not_dvd hpp).2 hne,
      hpp.squarefree, hse⟩, ?_⟩
    rw [Nat.primeFactors_mul hpp.ne_zero hse.ne_zero, hpp.primeFactors]
    exact union_subset (singleton_subset_iff.2 hpz) (hpe.trans (primesLT_natCast_subset hpz))
theorem squarefree_of_mem_rosserSet (hd : d ∈ rosserSet lower y z) : Squarefree d :=
  (squarefree_and_primeFactors_subset hd).1
theorem primeFactors_subset_of_mem_rosserSet (hd : d ∈ rosserSet lower y z) :
    d.primeFactors ⊆ primesLT z :=
  (squarefree_and_primeFactors_subset hd).2
theorem pos_of_mem_rosserSet (hd : d ∈ rosserSet lower y z) : 0 < d :=
  Nat.pos_of_ne_zero (squarefree_of_mem_rosserSet hd).ne_zero
theorem lt_of_prime_dvd_of_mem_rosserSet {q : ℕ} (hq : q.Prime) (hd : d ∈ rosserSet lower y z)
    (hqd : q ∣ d) : (q : ℝ) < z :=
  lt_of_mem_primesLT <| primeFactors_subset_of_mem_rosserSet hd <|
    Nat.mem_primeFactors.2 ⟨hq, hqd, (pos_of_mem_rosserSet hd).ne'⟩
theorem not_dvd_of_mem_rosserSet (hp : p.Prime) (hd : d ∈ rosserSet lower y p) : ¬ p ∣ d :=
  fun h ↦ (lt_irrefl _) (lt_of_prime_dvd_of_mem_rosserSet hp hd h)
theorem coprime_of_mem_rosserSet (hp : p.Prime) (hd : d ∈ rosserSet lower y p) :
    p.Coprime d :=
  (Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_of_mem_rosserSet hp hd)
theorem pairwiseDisjoint_rosserSet_image (lower : Bool) (y z : ℝ) :
    (rosserPrimes lower y z : Set ℕ).PairwiseDisjoint fun p ↦
      (rosserSet (!lower) (y / p) p).image (p * ·) := by
  intro p hp q hq hpq
  simp only [Function.onFun]
  rw [disjoint_left]
  simp only [mem_image, not_exists, not_and]
  rintro _ ⟨d, hd, rfl⟩ e he hde
  have hp' := prime_of_mem_primesLT (rosserPrimes_subset hp)
  have hq' := prime_of_mem_primesLT (rosserPrimes_subset hq)
  have key : ∀ {p q d e : ℕ}, p.Prime → q.Prime → p ≠ q → e ∈ rosserSet (!lower) (y / q) q →
      q * e = p * d → (p : ℝ) < q := by
    intro p q d e hp hq hpq he h
    have : p ∣ q * e := h ▸ dvd_mul_right p d
    rcases (Nat.Prime.dvd_mul hp).1 this with h' | h'
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp hq).1 h') hpq
    · exact lt_of_prime_dvd_of_mem_rosserSet hp he h'
  exact lt_asymm (key hp' hq' hpq he hde) (key hq' hp' (Ne.symm hpq) hd hde.symm)
theorem one_notMem_biUnion_rosserSet (lower : Bool) (y z : ℝ) :
    1 ∉ (rosserPrimes lower y z).biUnion fun p ↦
      (rosserSet (!lower) (y / p) p).image (p * ·) := by
  simp only [mem_biUnion, mem_image, not_exists, not_and]
  intro p hp d _ h
  exact (prime_of_mem_primesLT (rosserPrimes_subset hp)).one_lt.ne'
    (Nat.eq_one_of_mul_eq_one_right h)
theorem sum_rosserSet {M : Type*} [AddCommMonoid M] (f : ℕ → M) (lower : Bool) (y z : ℝ) :
    ∑ d ∈ rosserSet lower y z, f d =
      f 1 + ∑ p ∈ rosserPrimes lower y z, ∑ d ∈ rosserSet (!lower) (y / p) p, f (p * d) := by
  rw [rosserSet_eq, sum_insert (one_notMem_biUnion_rosserSet lower y z),
    sum_biUnion (pairwiseDisjoint_rosserSet_image lower y z)]
  congr 1
  refine sum_congr rfl fun p hp ↦ ?_
  rw [sum_image]
  intro a _ b _ h
  exact Nat.eq_of_mul_eq_mul_left (prime_of_mem_primesLT (rosserPrimes_subset hp)).pos h
theorem card_primeFactors_mul_of_mem_rosserSet (hp : p.Prime)
    (hd : d ∈ rosserSet lower y p) : #(p * d).primeFactors = #d.primeFactors + 1 := by
  rw [Nat.primeFactors_mul hp.ne_zero (pos_of_mem_rosserSet hd).ne', hp.primeFactors,
    singleton_union, card_insert_of_notMem]
  exact fun h ↦ not_dvd_of_mem_rosserSet hp hd (Nat.dvd_of_mem_primeFactors h)
theorem card_filter_rosserSet_zero (lower : Bool) (y z : ℝ) :
    #((rosserSet lower y z).filter fun d ↦ #d.primeFactors ≤ 0) = 1 := by
  rw [card_eq_one]
  refine ⟨1, ?_⟩
  ext d
  simp only [mem_filter, nonpos_iff_eq_zero, card_eq_zero, Nat.primeFactors_eq_empty,
    mem_singleton]
  constructor
  · rintro ⟨hd, h0 | h1⟩
    · exact absurd h0 (pos_of_mem_rosserSet hd).ne'
    · exact h1
  · rintro rfl
    exact ⟨one_mem_rosserSet, Or.inr rfl⟩
theorem card_filter_rosserSet_succ (n : ℕ) (lower : Bool) (y z : ℝ) :
    #((rosserSet lower y z).filter fun d ↦ #d.primeFactors ≤ n + 1) =
      1 + ∑ p ∈ rosserPrimes lower y z,
        #((rosserSet (!lower) (y / p) p).filter fun d ↦ #d.primeFactors ≤ n) := by
  simp only [card_filter]
  rw [sum_rosserSet]
  simp only [Nat.primeFactors_one, card_empty, zero_le, ite_true]
  congr 1
  refine sum_congr rfl fun p hp ↦ sum_congr rfl fun d hd ↦ ?_
  rw [card_primeFactors_mul_of_mem_rosserSet (prime_of_mem_primesLT (rosserPrimes_subset hp)) hd]
  simp
noncomputable def rosserMain (lower : Bool) (y z : ℝ) : ℝ :=
  ∑ d ∈ rosserSet lower y z, (μ d : ℝ) / d
theorem moebius_mul_of_mem_rosserSet (hp : p.Prime) (hd : d ∈ rosserSet lower y p) :
    μ (p * d) = -μ d := by
  rw [isMultiplicative_moebius.map_mul_of_coprime (coprime_of_mem_rosserSet hp hd),
    moebius_apply_prime hp, neg_one_mul]
theorem rosserMain_eq (lower : Bool) (y z : ℝ) :
    rosserMain lower y z = 1 - ∑ p ∈ rosserPrimes lower y z, rosserMain (!lower) (y / p) p / p := by
  rw [rosserMain, sum_rosserSet, sub_eq_add_neg, ← sum_neg_distrib]
  simp only [moebius_apply_one, Int.cast_one, Nat.cast_one, div_one]
  congr 1
  refine sum_congr rfl fun p hp ↦ ?_
  have hp' := prime_of_mem_primesLT (rosserPrimes_subset hp)
  rw [rosserMain, sum_div, ← sum_neg_distrib]
  refine sum_congr rfl fun d hd ↦ ?_
  rw [moebius_mul_of_mem_rosserSet hp' hd]
  push_cast
  field_simp
noncomputable def siftIndicator (z : ℝ) (m : ℕ) : ℤ :=
  if ∀ p ∈ primesLT z, ¬ p ∣ m then 1 else 0
theorem siftIndicator_nonneg (z : ℝ) (m : ℕ) : 0 ≤ siftIndicator z m := by
  unfold siftIndicator
  split_ifs <;> norm_num
theorem siftIndicator_eq (z : ℝ) (m : ℕ) :
    siftIndicator z m = 1 - ∑ p ∈ (primesLT z).filter (· ∣ m), siftIndicator p m := by
  set F := (primesLT z).filter (· ∣ m)
  rcases F.eq_empty_or_nonempty with hF | hF
  · rw [hF, sum_empty, sub_zero, siftIndicator, ite_eq_left]
    intro p hp hpm
    have : p ∈ F := mem_filter.2 ⟨hp, hpm⟩
    simp [hF] at this
  set p₀ := F.min' hF
  have hp₀ : p₀ ∈ F := F.min'_mem hF
  have hsum : ∑ p ∈ F, siftIndicator p m = ∑ p ∈ F, if p = p₀ then 1 else 0 := by
    refine sum_congr rfl fun p hp ↦ ?_
    rw [siftIndicator]
    have hpz := (mem_filter.1 hp).1
    congr 1
    apply propext
    constructor
    · intro h
      refine le_antisymm ?_ (F.min'_le p hp)
      by_contra hlt
      exact h p₀ (mem_primesLT.2 ⟨prime_of_mem_primesLT (mem_filter.1 hp₀).1,
        by exact_mod_cast not_le.1 hlt⟩) (mem_filter.1 hp₀).2
    · rintro rfl q hq hqm
      have hqF : q ∈ F := mem_filter.2 ⟨primesLT_natCast_subset hpz hq, hqm⟩
      exact absurd (F.min'_le q hqF) (not_le.2 (by exact_mod_cast lt_of_mem_primesLT hq))
  rw [hsum, sum_ite_eq' F p₀, ite_eq_left hp₀, siftIndicator, ite_eq_right]
  · norm_num
  · push Not
    exact ⟨p₀, (mem_filter.1 hp₀).1, (mem_filter.1 hp₀).2⟩
theorem siftIndicator_of_dvd_primorialLT {m : ℕ} (hm : m ∣ primorialLT z) :
    siftIndicator z m = if m = 1 then 1 else 0 := by
  rw [siftIndicator]
  congr 1
  apply propext
  constructor
  · intro h
    by_contra hm1
    obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd hm1
    have hqP : q ∣ primorialLT z := hqm.trans hm
    obtain ⟨p, hp, hqp⟩ := (Prime.dvd_finsetProd_iff hq.prime _).1 hqP
    rw [(Nat.prime_dvd_prime_iff_eq hq (prime_of_mem_primesLT hp)).1 hqp] at hqm
    exact h p hp hqm
  · rintro rfl p hp h
    exact (prime_of_mem_primesLT hp).one_lt.ne' (Nat.dvd_one.1 h)
noncomputable def rosserSieve (lower : Bool) (y z : ℝ) (m : ℕ) : ℤ :=
  ∑ d ∈ (rosserSet lower y z).filter (· ∣ m), μ d
theorem rosserSieve_eq (lower : Bool) (y z : ℝ) (m : ℕ) :
    rosserSieve lower y z m =
      1 - ∑ p ∈ (rosserPrimes lower y z).filter (· ∣ m), rosserSieve (!lower) (y / p) p m := by
  rw [rosserSieve, sum_filter, sum_rosserSet, sum_filter, sub_eq_add_neg, ← sum_neg_distrib]
  simp only [one_dvd, ite_true, moebius_apply_one]
  congr 1
  refine sum_congr rfl fun p hp ↦ ?_
  have hp' := prime_of_mem_primesLT (rosserPrimes_subset hp)
  split_ifs with hpm
  · rw [rosserSieve, sum_filter, ← sum_neg_distrib]
    refine sum_congr rfl fun d hd ↦ ?_
    have key : p * d ∣ m ↔ d ∣ m :=
      ⟨fun h ↦ (dvd_mul_left d p).trans h,
        fun h ↦ Nat.Coprime.mul_dvd_of_dvd_of_dvd (coprime_of_mem_rosserSet hp' hd) hpm h⟩
    simp only [key, moebius_mul_of_mem_rosserSet hp' hd]
    split_ifs <;> simp
  · refine sum_eq_zero fun d _ ↦ ?_
    rw [ite_eq_right]
    exact fun h ↦ hpm ((dvd_mul_right p d).trans h)
theorem rosserSieve_le_siftIndicator_le (y z : ℝ) (m : ℕ) :
    rosserSieve true y z m ≤ siftIndicator z m ∧ siftIndicator z m ≤ rosserSieve false y z m := by
  induction z using primesLT_induction generalizing y with
  | h z ih =>
    constructor
    · rw [rosserSieve_eq, siftIndicator_eq, rosserPrimes_true]
      refine sub_le_sub_left (sum_le_sum fun p hp ↦ ?_) _
      exact (ih p (mem_filter.1 hp).1 (y / p)).2
    · rw [rosserSieve_eq, siftIndicator_eq]
      refine sub_le_sub_left ?_ _
      calc ∑ p ∈ (rosserPrimes false y z).filter (· ∣ m), rosserSieve (!false) (y / p) p m
          ≤ ∑ p ∈ (rosserPrimes false y z).filter (· ∣ m), siftIndicator p m :=
            sum_le_sum fun p hp ↦
              (ih p (rosserPrimes_subset (mem_filter.1 hp).1) (y / p)).1
        _ ≤ ∑ p ∈ (primesLT z).filter (· ∣ m), siftIndicator p m :=
            sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ rosserPrimes_subset)
              fun p _ _ ↦ siftIndicator_nonneg p m
theorem rosserSieve_of_dvd_primorialLT (y : ℝ) {m : ℕ} (hm : m ∣ primorialLT z) :
    ∑ d ∈ (rosserSet true y z).filter (· ∣ m), μ d ≤ (if m = 1 then 1 else 0) ∧
      (if m = 1 then 1 else 0) ≤ ∑ d ∈ (rosserSet false y z).filter (· ∣ m), μ d := by
  rw [← siftIndicator_of_dvd_primorialLT hm]
  exact rosserSieve_le_siftIndicator_le y z m
noncomputable def fail : Bool → ℕ → ℝ → ℝ → ℝ
  | _, 0, _, _ => 0
  | true, r + 1, y, z => ∑ p ∈ primesLT z, fail false r (y / p) p / p
  | false, r + 1, y, z => ∑ p ∈ rosserPrimes false y z, fail true r (y / p) p / p +
      ∑ p ∈ (primesLT z).filter (fun p : ℕ ↦ ¬ (p : ℝ) ^ 3 < y), R p / p
@[simp] theorem fail_zero (lower : Bool) (y z : ℝ) : fail lower 0 y z = 0 := by
  cases lower <;> rfl
theorem fail_true_succ (r : ℕ) (y z : ℝ) :
    fail true (r + 1) y z = ∑ p ∈ primesLT z, fail false r (y / p) p / p := rfl
theorem fail_false_succ (r : ℕ) (y z : ℝ) :
    fail false (r + 1) y z = ∑ p ∈ rosserPrimes false y z, fail true r (y / p) p / p +
      ∑ p ∈ (primesLT z).filter (fun p : ℕ ↦ ¬ (p : ℝ) ^ 3 < y), R p / p := rfl
theorem fail_nonneg (lower : Bool) (r : ℕ) (y z : ℝ) : 0 ≤ fail lower r y z := by
  induction r generalizing lower y z with
  | zero => simp
  | succ r ih =>
    cases lower
    · rw [fail_false_succ]
      exact add_nonneg (sum_nonneg fun p _ ↦ div_nonneg (ih _ _ _) p.cast_nonneg)
        (sum_nonneg fun p _ ↦ div_nonneg (R_nonneg _) p.cast_nonneg)
    · rw [fail_true_succ]
      exact sum_nonneg fun p _ ↦ div_nonneg (ih _ _ _) p.cast_nonneg
theorem fail_eq_of_card_lt {r : ℕ} (hr : #(primesLT z) < r) (y : ℝ) :
    fail true r y z = R z - rosserMain true y z ∧
      fail false r y z = rosserMain false y z - R z := by
  induction r generalizing y z with
  | zero => simp at hr
  | succ r ih =>
    have ih' : ∀ p ∈ primesLT z, ∀ y, fail true r y p = R p - rosserMain true y p ∧
        fail false r y p = rosserMain false y p - R p := fun p hp y ↦
      ih ((card_lt_card (primesLT_natCast_ssubset hp)).trans_le (Nat.lt_succ_iff.1 hr)) y
    constructor
    · rw [fail_true_succ, rosserMain_eq, R_eq z, rosserPrimes_true]
      simp only [Bool.not_true]
      rw [sub_sub_sub_cancel_left, ← sum_sub_distrib]
      refine sum_congr rfl fun p hp ↦ ?_
      rw [(ih' p hp _).2, sub_div]
    · rw [fail_false_succ, rosserMain_eq, R_eq z, rosserPrimes_false,
        ← sum_filter_add_sum_filter_not (primesLT z) (fun p : ℕ ↦ (p : ℝ) ^ 3 < y)
          (fun p ↦ R p / p)]
      simp only [Bool.not_false, ← rosserPrimes_false]
      have : ∑ p ∈ rosserPrimes false y z, fail true r (y / p) p / p =
          ∑ p ∈ rosserPrimes false y z, R p / p -
            ∑ p ∈ rosserPrimes false y z, rosserMain true (y / p) p / p := by
        rw [← sum_sub_distrib]
        refine sum_congr rfl fun p hp ↦ ?_
        rw [(ih' p (rosserPrimes_subset hp) _).1, sub_div]
      rw [this]
      ring
end IwaniecLinearSieve
end
section
open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius
namespace IwaniecLinearSieve
theorem orderEmbOfFin_le_orderEmbOfFin {T S : Finset ℕ} {r : ℕ} (hT : #T = r) (hS : #S = r)
    (hdown : ∀ q ∈ S, ∀ t ∈ T, q < t → q ∈ T) (i : Fin r) :
    T.orderEmbOfFin hT i ≤ S.orderEmbOfFin hS i := by
  by_contra h
  push Not at h
  set t := T.orderEmbOfFin hT i
  have h1 : (Iic i).map (S.orderEmbOfFin hS).toEmbedding ⊆ T.filter (· < t) := by
    intro u hu
    obtain ⟨j, hj, rfl⟩ := mem_map.1 hu
    have hlt : S.orderEmbOfFin hS j < t :=
      lt_of_le_of_lt ((S.orderEmbOfFin hS).monotone (mem_Iic.1 hj)) h
    exact mem_filter.2 ⟨hdown _ (S.orderEmbOfFin_mem hS j) t (T.orderEmbOfFin_mem hT i) hlt, hlt⟩
  have h2 : T.filter (· < t) ⊆ (Iio i).map (T.orderEmbOfFin hT).toEmbedding := by
    intro u hu
    obtain ⟨huT, hut⟩ := mem_filter.1 hu
    have : u ∈ Set.range (T.orderEmbOfFin hT) := by
      rw [range_orderEmbOfFin]
      exact huT
    obtain ⟨j, rfl⟩ := this
    exact mem_map.2 ⟨j, mem_Iio.2 ((T.orderEmbOfFin hT).lt_iff_lt.1 hut), rfl⟩
  have := card_le_card (h1.trans h2)
  simp [Fin.card_Iic, Fin.card_Iio] at this
theorem exists_bijOn_le {T S : Finset ℕ} (hcard : #S = #T)
    (hdown : ∀ q ∈ S, ∀ t ∈ T, q < t → q ∈ T) :
    ∃ e : ℕ → ℕ, Set.BijOn e T S ∧ ∀ p ∈ T, p ≤ e p := by
  classical
  let iT := T.orderIsoOfFin rfl
  let iS := S.orderIsoOfFin hcard
  refine ⟨fun p ↦ if hp : p ∈ T then (iS (iT.symm ⟨p, hp⟩) : ℕ) else p, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro p hp
    simp only [mem_coe] at hp
    simp only [hp, dite_true, mem_coe]
    exact (iS _).2
  · intro p hp q hq hpq
    simp only [mem_coe] at hp hq
    simp only [hp, hq, dite_true] at hpq
    have := iT.symm.injective (iS.injective (Subtype.ext hpq))
    exact congrArg Subtype.val this
  · intro q hq
    simp only [mem_coe] at hq
    refine ⟨iT (iS.symm ⟨q, hq⟩), (iT _).2, ?_⟩
    simp
  · intro p hp
    simp only [hp, dite_true]
    have h1 : p = T.orderEmbOfFin rfl (iT.symm ⟨p, hp⟩) := by
      rw [← coe_orderIsoOfFin_apply]
      simp [iT]
    have h2 : (iS (iT.symm ⟨p, hp⟩) : ℕ) = S.orderEmbOfFin hcard (iT.symm ⟨p, hp⟩) :=
      coe_orderIsoOfFin_apply _ _ _
    conv_lhs => rw [h1]
    rw [h2]
    exact orderEmbOfFin_le_orderEmbOfFin rfl hcard hdown _
theorem sum_powerset_filter_superset_prod {T A : Finset ℕ} (hA : A ⊆ T) (h : ℕ → ℝ) :
    ∑ B ∈ T.powerset with A ⊆ B, ∏ p ∈ B, h p = (∏ p ∈ A, h p) * ∏ p ∈ T \ A, (1 + h p) := by
  rw [prod_one_add, mul_sum]
  refine sum_nbij' (fun B ↦ B \ A) (fun C ↦ A ∪ C) ?_ ?_ ?_ ?_ ?_
  · intro B hB
    simp only [mem_filter, mem_powerset] at hB ⊢
    exact sdiff_subset_sdiff hB.1 le_rfl
  · intro C hC
    simp only [mem_filter, mem_powerset] at hC ⊢
    exact ⟨union_subset hA (hC.trans sdiff_subset), subset_union_left⟩
  · intro B hB
    simp only [mem_filter, mem_powerset] at hB
    exact union_sdiff_of_subset hB.2
  · intro C hC
    simp only [mem_powerset] at hC
    exact union_sdiff_cancel_left (disjoint_of_subset_right hC disjoint_sdiff)
  · intro B hB
    simp only [mem_filter, mem_powerset] at hB
    rw [← prod_union disjoint_sdiff, union_sdiff_of_subset hB.2]
theorem sum_powerset_div_prod (T : Finset ℕ) (g : ℕ → ℝ) (hg : ∀ p ∈ T, g p ≠ 0 ∧ g p ≠ 1)
    (w : Finset ℕ → ℝ) :
    ∑ A ∈ T.powerset, w A / ∏ p ∈ A, g p =
      (∏ p ∈ T, (1 - (g p)⁻¹)) *
        ∑ B ∈ T.powerset, (∑ A ∈ B.powerset, w A) / ∏ p ∈ B, (g p - 1) := by
  simp_rw [mul_sum, sum_div, mul_sum, div_eq_mul_inv, ← prod_inv_distrib]
  rw [sum_comm' (t' := T.powerset) (s' := fun A ↦ T.powerset.filter (A ⊆ ·))]
  swap
  · intro B A
    simp only [mem_powerset, mem_filter]
    constructor
    · rintro ⟨hB, hA⟩
      exact ⟨⟨hB, hA⟩, hA.trans hB⟩
    · rintro ⟨⟨hB, hA⟩, -⟩
      exact ⟨hB, hA⟩
  refine sum_congr rfl fun A hA ↦ ?_
  rw [mem_powerset] at hA
  rw [← mul_sum, ← mul_sum, sum_powerset_filter_superset_prod hA, mul_left_comm]
  congr 1
  rw [← prod_sdiff hA, show ∀ a b c d : ℝ, a * b * (c * d) = c * b * (a * d) by intros; ring,
    ← prod_mul_distrib, ← prod_mul_distrib]
  rw [prod_congr rfl (s₁ := T \ A) (g := fun _ ↦ (1 : ℝ)), prod_const_one, mul_one]
  · refine prod_congr rfl fun p hp ↦ ?_
    obtain ⟨h0, h1⟩ := hg p (hA hp)
    have : g p - 1 ≠ 0 := sub_ne_zero.2 h1
    field_simp
  · intro p hp
    obtain ⟨h0, h1⟩ := hg p (sdiff_subset hp)
    have : g p - 1 ≠ 0 := sub_ne_zero.2 h1
    field_simp
    ring
theorem prod_mul_sum_div_le_sum (T : Finset ℕ) (f g : ℕ → ℝ) (hg : ∀ p ∈ T, 1 < g p)
    (hgf : ∀ p ∈ T, g p ≤ f p) (w : Finset ℕ → ℝ)
    (hw : ∀ B ⊆ T, B.Nonempty → ∑ A ∈ B.powerset, w A ≤ 0) :
    (∏ p ∈ T, (1 - (f p)⁻¹)) *
        ((∑ A ∈ T.powerset, w A / ∏ p ∈ A, g p) / ∏ p ∈ T, (1 - (g p)⁻¹)) ≤
      ∑ A ∈ T.powerset, w A / ∏ p ∈ A, f p := by
  have hf : ∀ p ∈ T, 1 < f p := fun p hp ↦ (hg p hp).trans_le (hgf p hp)
  have hne : ∀ {h : ℕ → ℝ}, (∀ p ∈ T, 1 < h p) → ∀ p ∈ T, h p ≠ 0 ∧ h p ≠ 1 :=
    fun hh p hp ↦ ⟨(zero_lt_one.trans (hh p hp)).ne', (hh p hp).ne'⟩
  have hpos : ∀ {h : ℕ → ℝ}, (∀ p ∈ T, 1 < h p) → 0 < ∏ p ∈ T, (1 - (h p)⁻¹) :=
    fun hh ↦ prod_pos fun p hp ↦ sub_pos.2 (inv_lt_one_of_one_lt₀ (hh p hp))
  rw [sum_powerset_div_prod T g (hne hg), sum_powerset_div_prod T f (hne hf),
    mul_div_cancel_left₀ _ (hpos hg).ne']
  refine mul_le_mul_of_nonneg_left (sum_le_sum fun B hB ↦ ?_) (hpos hf).le
  rw [mem_powerset] at hB
  rcases B.eq_empty_or_nonempty with rfl | hBne
  · simp
  have h0 : 0 < ∏ p ∈ B, (g p - 1) := prod_pos fun p hp ↦ sub_pos.2 (hg p (hB hp))
  have h1 : ∏ p ∈ B, (g p - 1) ≤ ∏ p ∈ B, (f p - 1) :=
    prod_le_prod₀ (fun p hp ↦ (sub_pos.2 (hg p (hB hp))).le)
      fun p hp ↦ sub_le_sub_right (hgf p (hB hp)) 1
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonpos_left (inv_anti₀ h0 h1) (hw B hB hBne)
theorem sum_rosserSet_eq_sum_powerset {M : Type*} [AddCommMonoid M] (lower : Bool) (y z : ℝ)
    (F : Finset ℕ → M) :
    ∑ d ∈ rosserSet lower y z, F d.primeFactors =
      ∑ A ∈ (primesLT z).powerset, if ∏ p ∈ A, p ∈ rosserSet lower y z then F A else 0 := by
  rw [← sum_filter]
  have hprime : ∀ A ∈ (primesLT z).powerset, ∀ p ∈ A, p.Prime := fun A hA p hp ↦
    prime_of_mem_primesLT (mem_powerset.1 hA hp)
  refine sum_nbij' Nat.primeFactors (fun A ↦ ∏ p ∈ A, p) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    refine mem_filter.2 ⟨mem_powerset.2 (primeFactors_subset_of_mem_rosserSet hd), ?_⟩
    rwa [Nat.prod_primeFactors_of_squarefree (squarefree_of_mem_rosserSet hd)]
  · intro A hA
    exact (mem_filter.1 hA).2
  · intro d hd
    exact Nat.prod_primeFactors_of_squarefree (squarefree_of_mem_rosserSet hd)
  · intro A hA
    exact Nat.primeFactors_prod (hprime A (mem_filter.1 hA).1)
  · intro d _
    rfl
theorem sum_rosserSet_eq_sum_powerset' {M : Type*} [AddCommMonoid M] (lower : Bool) (y z : ℝ)
    (G : ℕ → M) :
    ∑ d ∈ rosserSet lower y z, G d =
      ∑ A ∈ (primesLT z).powerset,
        if ∏ p ∈ A, p ∈ rosserSet lower y z then G (∏ p ∈ A, p) else 0 := by
  rw [← sum_rosserSet_eq_sum_powerset lower y z (fun A ↦ G (∏ p ∈ A, p))]
  refine sum_congr rfl fun d hd ↦ ?_
  rw [Nat.prod_primeFactors_of_squarefree (squarefree_of_mem_rosserSet hd)]
noncomputable def rosserWeight (y z : ℝ) (A : Finset ℕ) : ℝ :=
  if ∏ p ∈ A, p ∈ rosserSet true y z then (μ (∏ p ∈ A, p) : ℝ) else 0
theorem sum_moebius_rosserSet_eq (y z : ℝ) (F : ℕ → ℝ) :
    ∑ d ∈ rosserSet true y z, (μ d : ℝ) * F d =
      ∑ A ∈ (primesLT z).powerset, rosserWeight y z A * F (∏ p ∈ A, p) := by
  rw [sum_rosserSet_eq_sum_powerset']
  refine sum_congr rfl fun A _ ↦ ?_
  rw [rosserWeight]
  split_ifs <;> simp
theorem rosserMain_eq_sum_rosserWeight (y z : ℝ) :
    rosserMain true y z =
      ∑ A ∈ (primesLT z).powerset, rosserWeight y z A / ∏ p ∈ A, (p : ℝ) := by
  have := sum_moebius_rosserSet_eq y z (fun d ↦ (d : ℝ)⁻¹)
  simp only [Nat.cast_prod] at this
  simp_rw [rosserMain, div_eq_mul_inv]
  exact this
theorem sum_abs_rosserWeight_le (y z : ℝ) :
    ∑ A ∈ (primesLT z).powerset, |rosserWeight y z A| ≤ #(rosserSet true y z) := by
  have : ∑ A ∈ (primesLT z).powerset, |rosserWeight y z A| =
      ∑ d ∈ rosserSet true y z, |(μ d : ℝ)| := by
    rw [sum_rosserSet_eq_sum_powerset']
    refine sum_congr rfl fun A _ ↦ ?_
    rw [rosserWeight]
    split_ifs <;> simp
  rw [this, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  refine sum_le_sum fun d _ ↦ ?_
  exact_mod_cast abs_moebius_le_one
theorem prod_dvd_prod_iff_subset {A B : Finset ℕ} (hA : ∀ p ∈ A, p.Prime)
    (hB : ∀ p ∈ B, p.Prime) : ∏ p ∈ A, p ∣ ∏ p ∈ B, p ↔ A ⊆ B := by
  refine ⟨fun h ↦ ?_, fun h ↦ prod_dvd_prod_of_subset _ _ _ h⟩
  have := Nat.primeFactors_mono h (prod_ne_zero_iff.2 fun p hp ↦ (hB p hp).ne_zero)
  rwa [Nat.primeFactors_prod hA, Nat.primeFactors_prod hB] at this
theorem sum_powerset_rosserWeight_le (y : ℝ) {z : ℝ} {B : Finset ℕ} (hB : B ⊆ primesLT z) :
    ∑ A ∈ B.powerset, rosserWeight y z A ≤ if B = ∅ then 1 else 0 := by
  have hBp : ∀ p ∈ B, p.Prime := fun p hp ↦ prime_of_mem_primesLT (hB hp)
  have h1 : ∑ A ∈ B.powerset, rosserWeight y z A =
      ∑ A ∈ (primesLT z).powerset,
        rosserWeight y z A * (if ∏ p ∈ A, p ∣ ∏ p ∈ B, p then 1 else 0) := by
    have : B.powerset = (primesLT z).powerset.filter (· ⊆ B) := by
      ext A
      simp only [mem_powerset, mem_filter]
      exact ⟨fun h ↦ ⟨h.trans hB, h⟩, fun h ↦ h.2⟩
    rw [this, sum_filter]
    refine sum_congr rfl fun A hA ↦ ?_
    simp only [prod_dvd_prod_iff_subset (fun p hp ↦ prime_of_mem_primesLT (mem_powerset.1 hA hp))
      hBp]
    split_ifs <;> simp
  have h2 : ∑ A ∈ (primesLT z).powerset,
        rosserWeight y z A * (if ∏ p ∈ A, p ∣ ∏ p ∈ B, p then 1 else 0) =
      ((∑ d ∈ (rosserSet true y z).filter (· ∣ ∏ p ∈ B, p), μ d : ℤ) : ℝ) := by
    rw [← sum_moebius_rosserSet_eq y z (fun d ↦ if d ∣ ∏ p ∈ B, p then 1 else 0), sum_filter,
      Int.cast_sum]
    refine sum_congr rfl fun d _ ↦ ?_
    split_ifs <;> simp
  have h3 := (rosserSieve_of_dvd_primorialLT (z := z) y
    (prod_dvd_prod_of_subset _ _ _ hB : ∏ p ∈ B, p ∣ primorialLT z)).1
  have h4 : (∏ p ∈ B, p = 1) ↔ B = ∅ := by
    constructor
    · intro h
      have := Nat.primeFactors_prod hBp
      rw [h, Nat.primeFactors_one] at this
      exact this.symm
    · rintro rfl
      simp
  rw [h1, h2]
  simp only [h4] at h3
  exact_mod_cast h3
theorem abs_card_filter_dvd_sub_le (x : ℤ) (X : ℕ) {d : ℕ} (hd : 0 < d) :
    |(#((range X).filter fun k : ℕ ↦ (d : ℤ) ∣ x + k) : ℝ) - X / d| ≤ 1 := by
  have hcard : #((range X).filter fun k : ℕ ↦ (d : ℤ) ∣ x + k) =
      #((Ico x (x + X)).filter ((d : ℤ) ∣ ·)) := by
    refine card_nbij' (fun k ↦ x + k) (fun t ↦ (t - x).toNat) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq, mem_Ico] at hk ⊢
      exact ⟨⟨by omega, by omega⟩, hk.2⟩
    · intro t ht
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq, mem_Ico] at ht ⊢
      refine ⟨by omega, ?_⟩
      rw [Int.toNat_of_nonneg (by omega)]
      simpa using ht.2
    · intro k _
      simp
    · intro t ht
      simp only [coe_filter, Set.mem_ofPred_eq, mem_Ico] at ht
      simp only
      omega
  have h := Int.Ico_filter_dvd_card x (x + X) (r := d) (by exact_mod_cast hd)
  set u : ℚ := x / (d : ℤ)
  set v : ℚ := (x + X : ℤ) / (d : ℤ)
  have hdq : (0 : ℚ) < (d : ℤ) := by exact_mod_cast hd
  have hvu : v = u + X / d := by
    simp only [v, u]
    push_cast
    ring
  have hX : (0 : ℚ) ≤ X / d := by positivity
  have hle : ⌈u⌉ ≤ ⌈v⌉ := Int.ceil_mono (by rw [hvu]; linarith)
  rw [max_eq_left (sub_nonneg.2 hle)] at h
  have hq : |((⌈v⌉ - ⌈u⌉ : ℤ) : ℚ) - X / d| ≤ 1 := by
    have h1 := Int.le_ceil v
    have h2 := Int.ceil_lt_add_one v
    have h3 := Int.le_ceil u
    have h4 := Int.ceil_lt_add_one u
    rw [abs_le]
    push_cast
    constructor <;> linarith
  rw [hcard]
  have : (#((Ico x (x + X)).filter ((d : ℤ) ∣ ·)) : ℝ) = ((⌈v⌉ - ⌈u⌉ : ℤ) : ℝ) := by
    exact_mod_cast h
  rw [this]
  have hq' := (Rat.cast_le (K := ℝ)).2 hq
  push_cast at hq' ⊢
  exact hq'
variable {z : ℝ}
theorem shiftedSieve_of_bijOn (y : ℝ) {S : Finset ℕ} {e : ℕ → ℕ}
    (he : Set.BijOn e (primesLT z) S) (hle : ∀ p ∈ primesLT z, p ≤ e p)
    (hS : ∀ q ∈ S, q.Prime) (x : ℤ) (X : ℕ) :
    (X : ℝ) * (∏ q ∈ S, (1 - (q : ℝ)⁻¹)) * (rosserMain true y z / R z) -
        #(rosserSet true y z) ≤
      #((range X).filter fun k : ℕ ↦ ∀ q ∈ S, ¬ (q : ℤ) ∣ x + k) := by
  set T := primesLT z
  set w := rosserWeight y z
  set n : Finset ℕ → ℕ := fun A ↦ ∏ p ∈ A, e p
  have heS : ∀ p ∈ T, e p ∈ S := fun p hp ↦ he.mapsTo hp
  have hePrime : ∀ p ∈ T, (e p).Prime := fun p hp ↦ hS _ (heS p hp)
  have hn : ∀ A ∈ T.powerset, 0 < n A := fun A hA ↦
    prod_pos fun p hp ↦ (hePrime p (mem_powerset.1 hA hp)).pos
  have ha : ∀ k : ℕ, ∑ A ∈ T.powerset, w A * (if (n A : ℤ) ∣ x + k then 1 else 0) ≤
      if ∀ q ∈ S, ¬ (q : ℤ) ∣ x + k then 1 else 0 := by
    intro k
    set B := T.filter fun p ↦ (e p : ℤ) ∣ x + k
    have hB : B ⊆ T := filter_subset _ _
    have h1 : ∀ A ∈ T.powerset, ((n A : ℤ) ∣ x + k ↔ A ⊆ B) := by
      intro A hA
      rw [mem_powerset] at hA
      constructor
      · intro h p hp
        refine mem_filter.2 ⟨hA hp, (Int.natCast_dvd_natCast.2 ?_).trans h⟩
        exact dvd_prod_of_mem _ hp
      · intro h
        simp only [n, Nat.cast_prod]
        refine prod_dvd_of_coprime ?_ fun p hp ↦ (mem_filter.1 (h hp)).2
        intro p hp q hq hpq
        refine Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes (hePrime p (hA hp))
          (hePrime q (hA hq))).2 fun h' ↦ hpq (he.injOn (hA hp) (hA hq) h'))
    have h2 : B = ∅ ↔ ∀ q ∈ S, ¬ (q : ℤ) ∣ x + k := by
      rw [filter_eq_empty_iff]
      constructor
      · intro h q hq hqk
        obtain ⟨p, hp, rfl⟩ := he.surjOn hq
        exact h hp hqk
      · intro h p hp
        exact h _ (heS p hp)
    have h3 : B.powerset = T.powerset.filter (· ⊆ B) := by
      ext A
      simp only [mem_powerset, mem_filter]
      exact ⟨fun h ↦ ⟨h.trans hB, h⟩, fun h ↦ h.2⟩
    calc ∑ A ∈ T.powerset, w A * (if (n A : ℤ) ∣ x + k then 1 else 0)
        = ∑ A ∈ B.powerset, w A := by
          rw [h3, sum_filter]
          refine sum_congr rfl fun A hA ↦ ?_
          simp only [h1 A hA]
          split_ifs <;> simp
      _ ≤ if B = ∅ then 1 else 0 := sum_powerset_rosserWeight_le y hB
      _ = _ := by simp only [h2]
  have hb : ∑ A ∈ T.powerset, w A * #((range X).filter fun k : ℕ ↦ (n A : ℤ) ∣ x + k) ≤
      #((range X).filter fun k : ℕ ↦ ∀ q ∈ S, ¬ (q : ℤ) ∣ x + k) := by
    simp_rw [natCast_card_filter, mul_sum]
    rw [sum_comm]
    exact sum_le_sum fun k _ ↦ ha k
  have hc : ∀ A ∈ T.powerset, w A * X / n A - |w A| ≤
      w A * #((range X).filter fun k : ℕ ↦ (n A : ℤ) ∣ x + k) := by
    intro A hA
    have h := abs_card_filter_dvd_sub_le x X (hn A hA)
    have h' : |w A * (#((range X).filter fun k : ℕ ↦ (n A : ℤ) ∣ x + k) - X / n A)| ≤ |w A| := by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) h
    have := neg_abs_le (w A * (#((range X).filter fun k : ℕ ↦ (n A : ℤ) ∣ x + k) - X / n A))
    rw [mul_div_assoc]
    linarith [mul_sub (w A) (#((range X).filter fun k : ℕ ↦ (n A : ℤ) ∣ x + k) : ℝ) (X / n A)]
  have hd : (X : ℝ) * (∏ q ∈ S, (1 - (q : ℝ)⁻¹)) * (rosserMain true y z / R z) ≤
      ∑ A ∈ T.powerset, w A * X / n A := by
    have hprodS : ∏ q ∈ S, (1 - (q : ℝ)⁻¹) = ∏ p ∈ T, (1 - (e p : ℝ)⁻¹) :=
      (prod_nbij e heS he.injOn he.surjOn fun p _ ↦ rfl).symm
    have hmain := prod_mul_sum_div_le_sum T (fun p ↦ (e p : ℝ)) (fun p ↦ (p : ℝ))
      (fun p hp ↦ by exact_mod_cast (prime_of_mem_primesLT hp).one_lt)
      (fun p hp ↦ by exact_mod_cast hle p hp) w
      (fun B hB hBne ↦ by
        simpa [hBne.ne_empty] using sum_powerset_rosserWeight_le y hB)
    rw [← rosserMain_eq_sum_rosserWeight] at hmain
    simp_rw [mul_div_right_comm _ (X : ℝ), ← sum_mul, mul_comm _ (X : ℝ)]
    rw [mul_assoc, hprodS]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg X)
    simpa [n, R, T] using hmain
  have he' := sum_abs_rosserWeight_le y z
  have hsum : ∑ A ∈ T.powerset, w A * X / n A - ∑ A ∈ T.powerset, |w A| ≤
      ∑ A ∈ T.powerset, w A * #((range X).filter fun k : ℕ ↦ (n A : ℤ) ∣ x + k) := by
    rw [← sum_sub_distrib]
    exact sum_le_sum hc
  linarith
theorem exists_bijOn_primesLT_le {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime)
    (hcard : #S = #(primesLT z)) :
    ∃ e : ℕ → ℕ, Set.BijOn e (primesLT z) S ∧ ∀ p ∈ primesLT z, p ≤ e p :=
  exists_bijOn_le hcard fun q hq _ ht hqt ↦
    mem_primesLT.2 ⟨hS q hq, (Nat.cast_lt.2 hqt).trans (lt_of_mem_primesLT ht)⟩
theorem shiftedSieve (y : ℝ) {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime)
    (hcard : #S = #(primesLT z)) (x : ℤ) (X : ℕ) :
    (X : ℝ) * (∏ q ∈ S, (1 - (q : ℝ)⁻¹)) * (rosserMain true y z / R z) -
        #(rosserSet true y z) ≤
      #((range X).filter fun k : ℕ ↦ ∀ q ∈ S, ¬ (q : ℤ) ∣ x + k) := by
  obtain ⟨e, he, hle⟩ := exists_bijOn_primesLT_le hS hcard
  exact shiftedSieve_of_bijOn y he hle hS x X
theorem R_le_prod_of_card_eq {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime)
    (hcard : #S = #(primesLT z)) : R z ≤ ∏ q ∈ S, (1 - (q : ℝ)⁻¹) := by
  obtain ⟨e, he, hle⟩ := exists_bijOn_primesLT_le hS hcard
  rw [← prod_nbij e (fun p hp ↦ he.mapsTo hp) he.injOn he.surjOn fun p _ ↦ rfl, R]
  refine prod_le_prod₀ (fun p hp ↦ sub_nonneg.2 (inv_le_one_of_one_le₀ ?_)) fun p hp ↦ ?_
  · exact_mod_cast (prime_of_mem_primesLT hp).one_lt.le
  · have h1 : (0 : ℝ) < p := by exact_mod_cast (prime_of_mem_primesLT hp).pos
    have h2 : (p : ℝ) ≤ e p := by exact_mod_cast hle p hp
    exact sub_le_sub_left (inv_anti₀ h1 h2) 1
end IwaniecLinearSieve
end
section
open Real Set MeasureTheory intervalIntegral
namespace IwaniecLinearSieve
theorem g_two_def (s : ℝ) : g 2 s = gTwoFormula (max 2 (min s 4)) := rfl
theorem g_add_three (n : ℕ) (s : ℝ) :
    g (n + 3) s = ∫ t in max s (gLower (n + 3))..((n : ℝ) + 5), shiftKernel (g (n + 2)) t := rfl
theorem gLower_le_three (i : ℕ) : gLower i ≤ 3 := by
  unfold gLower; split_ifs <;> norm_num
theorem two_le_gLower (i : ℕ) : 2 ≤ gLower i := by
  unfold gLower; split_ifs <;> norm_num
theorem gLower_even {i : ℕ} (hi : Even i) : gLower i = 2 := by simp [gLower, hi]
theorem gLower_odd {i : ℕ} (hi : ¬ Even i) : gLower i = 3 := by simp [gLower, hi]
theorem shiftKernel_of_two_le (h : ℝ → ℝ) {t : ℝ} (ht : 2 ≤ t) :
    shiftKernel h t = h (t - 1) / (t - 1) := by
  rw [shiftKernel, max_eq_left (by linarith)]
theorem continuous_shiftKernel {h : ℝ → ℝ} (hh : Continuous h) : Continuous (shiftKernel h) :=
  (hh.comp (continuous_sub_right 1)).div ((continuous_sub_right 1).max continuous_const)
    fun _ => (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
theorem shiftKernel_nonneg {h : ℝ → ℝ} (hh : ∀ s, 0 ≤ h s) (t : ℝ) : 0 ≤ shiftKernel h t :=
  div_nonneg (hh _) (le_trans zero_le_one (le_max_right _ _))
theorem continuous_integral_left {k : ℝ → ℝ} (hk : Continuous k) (b : ℝ) :
    Continuous fun u => ∫ t in u..b, k t := by
  have : (fun u => ∫ t in u..b, k t) = fun u => -∫ t in b..u, k t := by
    funext u; exact integral_symm _ _
  rw [this]
  exact (continuous_primitive (fun _ _ => hk.intervalIntegrable _ _) b).neg
theorem gTwoFormula_four : gTwoFormula 4 = 0 := by norm_num [gTwoFormula]
theorem gTwoFormula_continuousOn : ContinuousOn gTwoFormula (Icc 2 4) := by
  unfold gTwoFormula
  refine ContinuousOn.sub (ContinuousOn.add (continuousOn_const.mul ?_) continuousOn_id)
    continuousOn_const
  refine ContinuousOn.log (continuousOn_const.div (continuousOn_id.sub continuousOn_const) ?_) ?_
  · intro x hx; have := hx.1; linarith
  · intro x hx; have := hx.1; exact div_ne_zero (by norm_num) (by linarith)
theorem gTwoFormula_sub_ge {u v : ℝ} (hu : 2 ≤ u) (huv : u ≤ v) (hv : v ≤ 4) :
    (v - u) * (4 - v) / (v - 1) ≤ gTwoFormula u - gTwoFormula v ∧
      (u < v → 0 < gTwoFormula u - gTwoFormula v) := by
  have hu1 : 0 < u - 1 := by linarith
  have hv1 : 0 < v - 1 := by linarith
  have hlog : gTwoFormula u - gTwoFormula v = 3 * (-log ((u - 1) / (v - 1))) - (v - u) := by
    simp only [gTwoFormula]
    rw [log_div (by norm_num) hu1.ne', log_div (by norm_num) hv1.ne',
      log_div hu1.ne' hv1.ne']
    ring
  have key : 1 - (u - 1) / (v - 1) ≤ -log ((u - 1) / (v - 1)) := by
    linarith [log_le_sub_one_of_pos (div_pos hu1 hv1), log_inv ((u - 1) / (v - 1)),
      show ((u - 1) / (v - 1))⁻¹ = (v - 1) / (u - 1) from inv_div _ _]
  have h1 : 1 - (u - 1) / (v - 1) = (v - u) / (v - 1) := by field_simp; ring
  refine ⟨?_, fun huv' => ?_⟩
  · rw [hlog]
    have : (v - u) * (4 - v) / (v - 1) = 3 * ((v - u) / (v - 1)) - (v - u) := by
      field_simp; ring
    rw [this]; linarith
  · rw [hlog]
    have hne : (u - 1) / (v - 1) ≠ 1 := by
      rw [Ne, div_eq_one_iff_eq hv1.ne']; linarith
    have key' : 1 - (u - 1) / (v - 1) < -log ((u - 1) / (v - 1)) := by
      have := log_lt_sub_one_of_pos (div_pos hu1 hv1) hne
      linarith
    have : (v - u) ≤ 3 * ((v - u) / (v - 1)) := by
      rw [mul_div_assoc', le_div_iff₀ hv1]; nlinarith
    linarith
theorem gTwoFormula_nonneg {u : ℝ} (hu : 2 ≤ u) (hu4 : u ≤ 4) : 0 ≤ gTwoFormula u := by
  have := (gTwoFormula_sub_ge hu hu4 le_rfl).1
  rw [gTwoFormula_four] at this
  simpa using this
theorem gTwoFormula_pos {u : ℝ} (hu : 2 ≤ u) (hu4 : u < 4) : 0 < gTwoFormula u := by
  have := (gTwoFormula_sub_ge hu hu4.le le_rfl).2 hu4
  rwa [gTwoFormula_four, sub_zero] at this
theorem g_two_eq {s : ℝ} (hs : s ∈ Icc (2 : ℝ) 4) : g 2 s = 3 * log (3 / (s - 1)) + s - 4 := by
  rw [g_two_def, min_eq_left hs.2, max_eq_right hs.1]; rfl
theorem g_two_of_four_le {s : ℝ} (hs : 4 ≤ s) : g 2 s = 0 := by
  rw [g_two_def, min_eq_right hs, max_eq_right (by norm_num), gTwoFormula_four]
theorem g_eq_of_le_gLower (i : ℕ) {s : ℝ} (hs : s ≤ gLower i) : g i s = g i (gLower i) := by
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 =>
    have h2 : gLower 2 = 2 := gLower_even even_two
    rw [h2] at hs ⊢
    rw [g_two_def, g_two_def, min_eq_left (hs.trans (by norm_num)), max_eq_left hs]
    norm_num
  | n + 3 => rw [g_add_three, g_add_three, max_eq_right hs, max_self]
theorem g_add_three_eq (n : ℕ) {s : ℝ} (hs : gLower (n + 3) ≤ s) :
    g (n + 3) s = ∫ t in s..((n : ℝ) + 5), g (n + 2) (t - 1) / (t - 1) := by
  rw [g_add_three, max_eq_left hs]
  refine integral_congr fun t ht => shiftKernel_of_two_le _ ?_
  have := two_le_gLower (n + 3)
  rcases le_total s ((n : ℝ) + 5) with h | h
  · rw [uIcc_of_le h] at ht; linarith [ht.1]
  · rw [uIcc_of_ge h] at ht; linarith [ht.1, n.cast_nonneg (α := ℝ)]
theorem continuous_g : ∀ i, Continuous (g i)
  | 0 => continuous_const
  | 1 => continuous_const
  | 2 => by
    have : g 2 = gTwoFormula ∘ fun s => max 2 (min s 4) := rfl
    rw [this]
    exact gTwoFormula_continuousOn.comp_continuous
      (continuous_const.max (continuous_id.min continuous_const))
      fun s => ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩
  | n + 3 => by
    have : g (n + 3) = (fun u => ∫ t in u..((n : ℝ) + 5), shiftKernel (g (n + 2)) t) ∘
        fun s => max s (gLower (n + 3)) := rfl
    rw [this]
    exact (continuous_integral_left (continuous_shiftKernel (continuous_g (n + 2))) _).comp
      (continuous_id.max continuous_const)
theorem g_eq_zero_of_le : ∀ (i : ℕ) {s : ℝ}, (i : ℝ) + 2 ≤ s → g i s = 0
  | 0, _, _ => rfl
  | 1, _, _ => rfl
  | 2, _, hs => g_two_of_four_le (by norm_num at hs ⊢; linarith)
  | n + 3, s, hs => by
    push_cast at hs
    have hc : gLower (n + 3) ≤ s := (gLower_le_three _).trans (by linarith [n.cast_nonneg (α := ℝ)])
    rw [g_add_three, max_eq_left hc, integral_congr (g := fun _ => (0 : ℝ)),
      intervalIntegral.integral_zero]
    intro t ht
    rw [uIcc_of_ge (by linarith)] at ht
    simp only [shiftKernel]
    rw [g_eq_zero_of_le (n + 2) (by push_cast; linarith [ht.1]), zero_div]
theorem g_nonneg : ∀ (i : ℕ) (s : ℝ), 0 ≤ g i s
  | 0, _ => le_rfl
  | 1, _ => le_rfl
  | 2, _ => gTwoFormula_nonneg (le_max_left _ _) (max_le (by norm_num) (min_le_right _ _))
  | n + 3, s => by
    rcases le_or_gt ((n : ℝ) + 5) s with hs | hs
    · rw [g_eq_zero_of_le (n + 3) (by push_cast; linarith)]
    · rw [g_add_three]
      exact integral_nonneg
        (max_le hs.le (by linarith [gLower_le_three (n + 3), n.cast_nonneg (α := ℝ)]))
        fun t _ => shiftKernel_nonneg (g_nonneg (n + 2)) t
theorem g_pos : ∀ (i : ℕ), 2 ≤ i → ∀ {s : ℝ}, s < i + 2 → 0 < g i s
  | 0, h, _, _ => by omega
  | 1, h, _, _ => by omega
  | 2, _, s, hs => by
    norm_num at hs
    exact gTwoFormula_pos (le_max_left _ _) (max_lt (by norm_num) ((min_le_left _ _).trans_lt hs))
  | n + 3, _, s, hs => by
    push_cast at hs
    rw [g_add_three]
    have hc := gLower_le_three (n + 3)
    have hn := n.cast_nonneg (α := ℝ)
    refine intervalIntegral_pos_of_pos_on
      ((continuous_shiftKernel (continuous_g _)).intervalIntegrable _ _) (fun t ht => ?_)
      (max_lt (by linarith) (by linarith))
    have ht1 : max s (gLower (n + 3)) < t := ht.1
    have ht2 : t < (n : ℝ) + 5 := ht.2
    have h3 : 2 ≤ t := by linarith [le_max_right s (gLower (n + 3)), two_le_gLower (n + 3)]
    rw [shiftKernel_of_two_le _ h3]
    exact div_pos (g_pos (n + 2) (by omega) (by push_cast; linarith)) (by linarith)
theorem g_antitone : ∀ i, Antitone (g i)
  | 0 => antitone_const
  | 1 => antitone_const
  | 2 => fun u v huv => by
    rw [g_two_def, g_two_def]
    have h := (gTwoFormula_sub_ge (le_max_left 2 (min u 4))
      (max_le_max le_rfl (min_le_min huv le_rfl)) (max_le (by norm_num) (min_le_right v 4))).1
    have h1 : 0 ≤ max 2 (min v 4) - max 2 (min u 4) :=
      sub_nonneg.2 (max_le_max le_rfl (min_le_min huv le_rfl))
    have h2 : 0 ≤ 4 - max 2 (min v 4) := sub_nonneg.2 (max_le (by norm_num) (min_le_right v 4))
    have h3 : 0 ≤ max 2 (min v 4) - 1 := by linarith [le_max_left 2 (min v 4)]
    linarith [div_nonneg (mul_nonneg h1 h2) h3]
  | n + 3 => fun u v huv => by
    rw [g_add_three, g_add_three]
    have hk := continuous_shiftKernel (continuous_g (n + 2))
    rw [← integral_add_adjacent_intervals (hk.intervalIntegrable (max u (gLower (n + 3)))
      (max v (gLower (n + 3)))) (hk.intervalIntegrable _ _)]
    have : 0 ≤ ∫ t in max u (gLower (n + 3))..max v (gLower (n + 3)), shiftKernel (g (n + 2)) t :=
      integral_nonneg (max_le_max huv le_rfl) fun t _ => shiftKernel_nonneg (g_nonneg (n + 2)) t
    linarith
theorem g_add_three_sub (n : ℕ) {u v : ℝ} (hu : gLower (n + 3) ≤ u) (hv : gLower (n + 3) ≤ v) :
    g (n + 3) u - g (n + 3) v = ∫ t in u..v, shiftKernel (g (n + 2)) t := by
  have hk := continuous_shiftKernel (continuous_g (n + 2))
  rw [g_add_three, g_add_three, max_eq_left hu, max_eq_left hv,
    ← integral_add_adjacent_intervals (hk.intervalIntegrable u v) (hk.intervalIntegrable v _)]
  ring
theorem integral_Ioi_eq_of_eq_zero {h : ℝ → ℝ} {s b : ℝ} (hsb : s ≤ b)
    (hint : IntegrableOn h (Ioc s b)) (hz : ∀ t, b ≤ t → h t = 0) :
    IntegrableOn h (Ioi s) ∧ ∫ t in Ioi s, h t = ∫ t in s..b, h t := by
  have hI : IntegrableOn h (Ioi b) :=
    integrableOn_zero.congr_fun (fun t ht => (hz t (le_of_lt ht)).symm) measurableSet_Ioi
  have hI' : IntegrableOn h (Ioi s) := by
    rw [← Ioc_union_Ioi_eq_Ioi hsb]; exact hint.union hI
  refine ⟨hI', ?_⟩
  have := integral_Ioi_sub_Ioi hI' hsb
  rwa [setIntegral_eq_zero_of_forall_eq_zero (t := Ioi b) (fun t ht => hz t (le_of_lt ht)),
    sub_zero] at this
theorem g_add_three_eq_Ioi (n : ℕ) {s : ℝ} (hs : gLower (n + 3) ≤ s) :
    IntegrableOn (fun t => g (n + 2) (t - 1) / (t - 1)) (Ioi s) ∧
      g (n + 3) s = ∫ t in Ioi s, g (n + 2) (t - 1) / (t - 1) := by
  have h2 := two_le_gLower (n + 3)
  have hz : ∀ t, (n : ℝ) + 5 ≤ t → g (n + 2) (t - 1) / (t - 1) = 0 := fun t ht => by
    rw [g_eq_zero_of_le (n + 2) (by push_cast; linarith), zero_div]
  rcases le_or_gt s ((n : ℝ) + 5) with hsb | hsb
  · have hcont : ContinuousOn (fun t => g (n + 2) (t - 1) / (t - 1)) (Icc s ((n : ℝ) + 5)) :=
      (continuous_shiftKernel (continuous_g (n + 2))).continuousOn.congr
        fun t ht => (shiftKernel_of_two_le _ (by linarith [ht.1])).symm
    obtain ⟨hI, hEq⟩ := integral_Ioi_eq_of_eq_zero hsb
      ((hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self) hz
    exact ⟨hI, by rw [hEq, g_add_three_eq n hs]⟩
  · obtain ⟨hI, hEq⟩ := integral_Ioi_eq_of_eq_zero le_rfl (by simp) fun t ht => hz t (by linarith)
    refine ⟨hI, ?_⟩
    rw [hEq, integral_same, g_eq_zero_of_le (n + 3) (by push_cast; linarith)]
theorem not_even_two_mul_add_three (m : ℕ) : ¬ Even (2 * m + 3) := by
  rw [Nat.not_even_iff_odd]; exact ⟨m + 1, by ring⟩
theorem even_two_mul_add_four (m : ℕ) : Even (2 * m + 4) := ⟨m + 2, by ring⟩
theorem g_even_of_le_two (n : ℕ) {s : ℝ} (hs : s ≤ 2) : g (2 * n + 2) s = g (2 * n + 2) 2 := by
  have h : gLower (2 * n + 2) = 2 := gLower_even ⟨n + 1, by ring⟩
  rw [g_eq_of_le_gLower _ (h ▸ hs), h]
end IwaniecLinearSieve
end
section
open Real Set MeasureTheory intervalIntegral
namespace IwaniecLinearSieve
theorem log_three_sub_log_two_lt : log 3 - log 2 < 5 / 12 := by
  have h1 := log_three_lt_d9
  have h2 := log_two_gt_d9
  norm_num at h1 h2 ⊢
  linarith
theorem one_lt_log_three : 1 < log 3 := by
  have := log_three_gt_d9; norm_num at this ⊢; linarith
theorem exp_one_sq_lt : exp 1 ^ 2 < 2 + 6 * log 3 := by
  have h1 := exp_one_lt_d9
  have h0 := exp_pos 1
  have h3 := one_lt_log_three
  norm_num at h1
  nlinarith
theorem mul_exp_neg_le_of_one_le {u v : ℝ} (hu : 1 ≤ u) (huv : u ≤ v) :
    v * exp (-v) ≤ u * exp (-u) := by
  have h1 : v ≤ u * exp (v - u) := by
    have := add_one_le_exp (v - u)
    nlinarith
  have h2 : exp (-u) = exp (v - u) * exp (-v) := by rw [← exp_add]; ring_nf
  rw [h2]
  have := exp_pos (-v)
  nlinarith
noncomputable def psi (s : ℝ) : ℝ := s⁻¹ * exp (s - 3) * (1 + 3 * log (3 / (s - 1)))
theorem psi_two : psi 2 = (1 + 3 * log 3) / (2 * exp 1) := by
  have : exp ((2 : ℝ) - 3) = (exp 1)⁻¹ := by rw [← exp_neg]; norm_num
  rw [psi, this]; norm_num; field_simp
theorem psi_deriv_aux {x : ℝ} (hx : 2 < x) :
    (x - 1) * (1 + 3 * log (3 / (x - 1))) ≤ 3 * x / (x - 1) := by
  set y := x - 1 with hy
  have hy0 : 0 < y := by linarith
  have hx' : x = y + 1 := by ring
  rw [hx']
  have hlog : log (2 / y) ≤ 2 / y - 1 := log_le_sub_one_of_pos (by positivity)
  rw [log_div (by norm_num) hy0.ne'] at hlog
  have hL : 1 + 3 * log (3 / y) ≤ -3 / 4 + 6 / y := by
    rw [log_div (by norm_num) hy0.ne']
    have : 6 / y = 3 * (2 / y) := by ring
    linarith [log_three_sub_log_two_lt]
  have h6 : y * (6 / y) = 6 := by field_simp
  have : y * (1 + 3 * log (3 / y)) ≤ -3 / 4 * y + 6 := by
    have := mul_le_mul_of_nonneg_left hL hy0.le
    rw [mul_add y (-3 / 4), h6] at this; linarith
  rw [le_div_iff₀ hy0]
  nlinarith [sq_nonneg (y - 2)]
theorem hasDerivAt_psi {x : ℝ} (hx : 1 < x) :
    HasDerivAt psi
      (exp (x - 3) * ((x - 1) * (1 + 3 * log (3 / (x - 1))) - 3 * x / (x - 1)) /
        x ^ 2) x := by
  have hx0 : x ≠ 0 := by positivity
  have hx1 : x - 1 ≠ 0 := by linarith
  have h3 : (3 : ℝ) / (x - 1) ≠ 0 := div_ne_zero (by norm_num) hx1
  have h := (((hasDerivAt_id' x).inv hx0).mul ((hasDerivAt_id' x).sub_const 3).exp).mul
    ((((hasDerivAt_const x (3 : ℝ)).div ((hasDerivAt_id' x).sub_const 1) hx1).log h3).const_mul
      3 |>.const_add 1)
  convert h using 1 <;> (try with_reducible_and_instances rfl)
  · funext s; simp [psi]
  · simp only [Pi.div_apply, Pi.inv_apply, Pi.mul_apply]
    field_simp
    ring
theorem psi_le_psi_two {s : ℝ} (hs : s ∈ Icc (2 : ℝ) 4) : psi s ≤ psi 2 := by
  have hanti : AntitoneOn psi (Icc 2 4) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 2 4)
      (f' := fun x => exp (x - 3) * ((x - 1) * (1 + 3 * log (3 / (x - 1))) - 3 * x / (x - 1)) /
        x ^ 2) ?_ ?_ ?_
    · intro x hx
      exact (hasDerivAt_psi (by linarith [hx.1])).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hasDerivAt_psi (by linarith [hx.1])).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx1 : 0 < x - 1 := by linarith [hx.1]
      refine div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (exp_pos _).le (sub_nonpos.2 (psi_deriv_aux hx.1)))
        (by positivity)
  exact hanti ⟨le_rfl, by norm_num⟩ hs hs.1
noncomputable def gLead : ℝ := sSup ((fun s => g 2 s * s⁻¹ * exp s) '' Icc 2 4)
noncomputable def gRatio : ℝ := (1 + 3 * log 3) / 6
theorem gRatio_eq : gRatio = exp 1 / 3 * psi 2 := by
  rw [psi_two, gRatio]; field_simp; ring
theorem gRatio_lt : gRatio < 0.72 := by
  have := log_three_lt_d9
  rw [gRatio]; norm_num at this ⊢; linarith
theorem gRatio_pos : 0 < gRatio := by
  rw [gRatio]; have := one_lt_log_three; positivity
theorem gRatio_lt_one : gRatio < 1 := gRatio_lt.trans (by norm_num)
theorem bddAbove_gLead : BddAbove ((fun s => g 2 s * s⁻¹ * exp s) '' Icc 2 4) :=
  isCompact_Icc.bddAbove_image <|
    (((continuous_g 2).continuousOn.mul (continuousOn_inv₀.mono fun x hx => by
      simp only [mem_compl_iff, mem_singleton_iff]; linarith [hx.1])).mul
      continuous_exp.continuousOn)
theorem le_gLead {s : ℝ} (hs : s ∈ Icc (2 : ℝ) 4) : g 2 s * s⁻¹ * exp s ≤ gLead :=
  le_csSup bddAbove_gLead (mem_image_of_mem _ hs)
theorem gLead_nonneg : 0 ≤ gLead := by
  refine le_trans ?_ (le_gLead (s := 2) ⟨le_rfl, by norm_num⟩)
  have := g_nonneg 2 2
  positivity
theorem integral_shift_le {h : ℝ → ℝ} (hh : Continuous h) {C s b : ℝ} (hC : 0 ≤ C)
    (hs : 2 ≤ s) (hsb : s ≤ b) (hb : ∀ u, s - 1 ≤ u → h u ≤ C * u * exp (-u)) :
    ∫ t in s..b, h (t - 1) / (t - 1) ≤ C * exp (1 - s) := by
  have hint1 : IntervalIntegrable (fun t => h (t - 1) / (t - 1)) volume s b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hsb]
    exact (hh.comp (continuous_sub_right 1)).continuousOn.div
      (continuous_sub_right 1).continuousOn fun t ht => by linarith [ht.1]
  have hcont : Continuous fun t : ℝ => C * exp (1 - t) :=
    continuous_const.mul (continuous_exp.comp (continuous_const.sub continuous_id))
  calc ∫ t in s..b, h (t - 1) / (t - 1) ≤ ∫ t in s..b, C * exp (1 - t) := by
        refine integral_mono_on hsb hint1 (hcont.intervalIntegrable _ _) fun t ht => ?_
        have ht1 : 0 < t - 1 := by linarith [ht.1]
        rw [div_le_iff₀ ht1]
        have := hb (t - 1) (by linarith [ht.1])
        have e : exp (-(t - 1)) = exp (1 - t) := by ring_nf
        rw [e] at this; linarith
    _ = C * exp (1 - s) - C * exp (1 - b) := by
        rw [integral_eq_sub_of_hasDerivAt (f := fun t => -(C * exp (1 - t))) (fun t _ => ?_)
          (hcont.intervalIntegrable _ _)]
        · ring
        · have := (((hasDerivAt_id' t).const_sub 1).exp.const_mul C).neg
          convert this using 1 <;> (try with_reducible_and_instances rfl) <;> (try (funext tt; simp only [Pi.neg_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.inv_apply, Pi.smul_apply, Pi.pow_apply, Function.comp_apply, id_eq]; done)); ring
    _ ≤ C * exp (1 - s) := by
        have := mul_nonneg hC (exp_pos (1 - b)).le
        linarith
theorem g_add_three_le {n : ℕ} {C s : ℝ} (hC : 0 ≤ C) (hs : gLower (n + 3) ≤ s)
    (hb : ∀ u, s - 1 ≤ u → g (n + 2) u ≤ C * u * exp (-u)) : g (n + 3) s ≤ C * exp (1 - s) := by
  rcases le_or_gt s ((n : ℝ) + 5) with hsb | hsb
  · rw [g_add_three_eq n hs]
    exact integral_shift_le (continuous_g _) hC ((two_le_gLower _).trans hs) hsb hb
  · rw [g_eq_zero_of_le (n + 3) (by push_cast; linarith)]
    positivity
theorem gLower_two_mul_add_three (n : ℕ) : gLower (2 * n + 3) = 3 :=
  gLower_odd (not_even_two_mul_add_three n)
theorem gLower_two_mul_add_four (n : ℕ) : gLower (2 * n + 1 + 3) = 2 :=
  gLower_even (by rw [show 2 * n + 1 + 3 = 2 * n + 4 by ring]; exact even_two_mul_add_four n)
theorem g_even_eq_on_Icc (n : ℕ) {s : ℝ} (hs : s ∈ Icc (2 : ℝ) 4) :
    g (2 * n + 4) s = g (2 * n + 4) 4 + g (2 * n + 3) 3 * log (3 / (s - 1)) := by
  rw [show 2 * n + 4 = 2 * n + 1 + 3 by ring]
  have h := g_add_three_sub (2 * n + 1) (u := s) (v := 4)
    (by rw [gLower_two_mul_add_four]; exact hs.1) (by rw [gLower_two_mul_add_four]; norm_num)
  have hc : ∫ t in s..4, shiftKernel (g (2 * n + 1 + 2)) t =
      ∫ t in s..4, g (2 * n + 3) 3 * (1 / (t - 1)) := by
    refine integral_congr fun t ht => ?_
    rw [uIcc_of_le hs.2] at ht
    rw [shiftKernel_of_two_le _ (by linarith [ht.1, hs.1]), show 2 * n + 1 + 2 = 2 * n + 3 by ring,
      g_eq_of_le_gLower _ (s := t - 1) (by rw [gLower_two_mul_add_three]; linarith [ht.2]),
      gLower_two_mul_add_three, mul_one_div]
  have hs1 : 0 < s - 1 := by linarith [hs.1]
  rw [hc, intervalIntegral.integral_const_mul,
    integral_comp_sub_right (fun x => 1 / x), integral_one_div_of_pos hs1 (by norm_num)] at h
  norm_num at h
  linarith
private theorem g_odd_le_of_even (n : ℕ)
    (H : ∀ s, 2 ≤ s → g (2 * n + 2) s ≤ gLead * gRatio ^ n * s * exp (-s)) {s : ℝ} (hs : 1 ≤ s) :
    g (2 * n + 3) s ≤ gLead * (exp 1 / 3) * gRatio ^ n * s * exp (-s) := by
  have hC : 0 ≤ gLead * gRatio ^ n := mul_nonneg gLead_nonneg (pow_nonneg gRatio_pos.le _)
  have h3 : ∀ s, 3 ≤ s → g (2 * n + 3) s ≤ gLead * gRatio ^ n * exp (1 - s) := fun s hs =>
    g_add_three_le hC (by rw [gLower_two_mul_add_three]; exact hs)
      fun u hu => H u (by linarith)
  have key : ∀ s, 3 ≤ s → gLead * gRatio ^ n * exp (1 - s) ≤
      gLead * (exp 1 / 3) * gRatio ^ n * s * exp (-s) := fun s hs => by
    have e : exp (1 - s) = exp 1 * exp (-s) := by rw [← exp_add]; ring_nf
    rw [e]
    have := mul_nonneg (mul_nonneg (mul_nonneg hC (exp_pos (-s)).le) (exp_pos 1).le)
      (sub_nonneg.2 hs)
    nlinarith
  rcases le_total 3 s with hs3 | hs3
  · exact (h3 s hs3).trans (key s hs3)
  · have e : g (2 * n + 3) s = g (2 * n + 3) 3 := by
      have := g_eq_of_le_gLower (2 * n + 3) (s := s) (by rw [gLower_two_mul_add_three]; exact hs3)
      rwa [gLower_two_mul_add_three] at this
    rw [e]
    refine (h3 3 le_rfl).trans ((key 3 le_rfl).trans ?_)
    have := mul_exp_neg_le_of_one_le hs hs3
    have h0 : 0 ≤ gLead * (exp 1 / 3) * gRatio ^ n := by
      have := exp_pos 1; have := gLead_nonneg; have := gRatio_pos; positivity
    have := mul_le_mul_of_nonneg_left this h0
    linarith
private theorem g_even_le_of_odd (n : ℕ)
    (H : ∀ s, 1 ≤ s → g (2 * n + 3) s ≤ gLead * (exp 1 / 3) * gRatio ^ n * s * exp (-s))
    {s : ℝ} (hs : 2 ≤ s) : g (2 * n + 4) s ≤ gLead * gRatio ^ (n + 1) * s * exp (-s) := by
  have hC : 0 ≤ gLead * (exp 1 / 3) * gRatio ^ n := by
    have := exp_pos 1; have := gLead_nonneg; have := gRatio_pos; positivity
  have h4 : ∀ s, 2 ≤ s → g (2 * n + 4) s ≤ gLead * (exp 1 / 3) * gRatio ^ n * exp (1 - s) :=
    fun s hs => by
      rw [show 2 * n + 4 = 2 * n + 1 + 3 by ring]
      exact g_add_three_le hC (by rw [gLower_two_mul_add_four]; exact hs)
        fun u hu => by rw [show 2 * n + 1 + 2 = 2 * n + 3 by ring]; exact H u (by linarith)
  have hA := gRatio_pos
  have he := exp_one_sq_lt
  rcases le_total 4 s with hs4 | hs4
  · refine (h4 s hs).trans ?_
    have e : exp (1 - s) = exp 1 * exp (-s) := by rw [← exp_add]; ring_nf
    rw [e, pow_succ]
    have h1 : exp 1 ^ 2 / 3 ≤ gRatio * s := by
      rw [gRatio]; nlinarith
    have h0 : 0 ≤ gLead * gRatio ^ n * exp (-s) :=
      mul_nonneg (mul_nonneg gLead_nonneg (pow_nonneg hA.le _)) (exp_pos _).le
    have := mul_le_mul_of_nonneg_left h1 h0
    nlinarith
  · rw [g_even_eq_on_Icc n ⟨hs, hs4⟩]
    have hg4 := h4 4 (by norm_num)
    have hg3 := H 3 (by norm_num)
    have hlog : 0 ≤ log (3 / (s - 1)) :=
      log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
    have hpsi := psi_le_psi_two ⟨hs, hs4⟩
    have hpsi' : psi s * s * exp (-s) = exp (-3) * (1 + 3 * log (3 / (s - 1))) := by
      rw [psi]
      have : exp (s - 3) * exp (-s) = exp (-3) := by rw [← exp_add]; ring_nf
      rw [← this]
      field_simp
    have e4 : exp (1 - 4) = exp (-3) := by ring_nf
    have hsum : g (2 * n + 4) 4 + g (2 * n + 3) 3 * log (3 / (s - 1)) ≤
        gLead * (exp 1 / 3) * gRatio ^ n * (psi s * s * exp (-s)) := by
      rw [hpsi']
      rw [e4] at hg4
      have := mul_le_mul_of_nonneg_right hg3 hlog
      nlinarith
    have hs0 : 0 ≤ s * exp (-s) := by positivity
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpsi hs0) hC
    calc _ ≤ gLead * (exp 1 / 3) * gRatio ^ n * (psi 2 * (s * exp (-s))) := by
          refine hsum.trans (le_of_eq_of_le ?_ this); ring
      _ = gLead * gRatio ^ (n + 1) * s * exp (-s) := by rw [pow_succ, gRatio_eq]; ring
theorem g_even_le (n : ℕ) {s : ℝ} (hs : 2 ≤ s) :
    g (2 * n + 2) s ≤ gLead * gRatio ^ n * s * exp (-s) := by
  induction n generalizing s with
  | zero =>
    simp only [mul_zero, zero_add, pow_zero, mul_one]
    rcases le_total s 4 with hs4 | hs4
    · have := le_gLead ⟨hs, hs4⟩
      have hs0 : 0 < s := by linarith
      have e : g 2 s = g 2 s * s⁻¹ * exp s * (s * exp (-s)) := by
        rw [exp_neg]; field_simp
      rw [e]
      exact (mul_le_mul_of_nonneg_right this (by positivity : (0 : ℝ) ≤ s * exp (-s))).trans_eq
        (by ring)
    · rw [g_two_of_four_le hs4]
      have := gLead_nonneg
      have : 0 ≤ s := by linarith
      positivity
  | succ n ih =>
    rw [show 2 * (n + 1) + 2 = 2 * n + 4 by ring]
    exact g_even_le_of_odd n (fun s hs => g_odd_le_of_even n (fun s hs => ih hs) hs) hs
theorem g_odd_le (n : ℕ) {s : ℝ} (hs : 1 ≤ s) :
    g (2 * n + 3) s ≤ gLead * (exp 1 / 3) * gRatio ^ n * s * exp (-s) :=
  g_odd_le_of_even n (fun _ hs => g_even_le n hs) hs
end IwaniecLinearSieve
end
section
open Real Set MeasureTheory intervalIntegral Filter Topology
namespace IwaniecLinearSieve
theorem g_odd_of_le_three' (n : ℕ) {s : ℝ} (hs : s ≤ 3) : g (2 * n + 3) s = g (2 * n + 3) 3 := by
  have := g_eq_of_le_gLower (2 * n + 3) (s := s) (by rw [gLower_two_mul_add_three]; exact hs)
  rwa [gLower_two_mul_add_three] at this
theorem g_even_le_at_two (n : ℕ) (s : ℝ) : g (2 * n + 2) s ≤ g (2 * n + 2) 2 := by
  rcases le_total 2 s with h | h
  · exact g_antitone _ h
  · rw [g_even_of_le_two n h]
theorem g_odd_le_at_three (n : ℕ) (s : ℝ) : g (2 * n + 3) s ≤ g (2 * n + 3) 3 := by
  rcases le_total 3 s with h | h
  · exact g_antitone _ h
  · rw [g_odd_of_le_three' n h]
theorem g_even_le_uniform (n : ℕ) (s : ℝ) :
    g (2 * n + 2) s ≤ gLead * 2 * exp (-2) * gRatio ^ n :=
  (g_even_le_at_two n s).trans ((g_even_le n le_rfl).trans_eq (by ring))
theorem g_odd_le_uniform (n : ℕ) (s : ℝ) :
    g (2 * n + 3) s ≤ gLead * (exp 1 / 3) * 3 * exp (-3) * gRatio ^ n :=
  (g_odd_le_at_three n s).trans ((g_odd_le n (by norm_num)).trans_eq (by ring))
theorem summable_geom_gRatio (c : ℝ) : Summable fun n : ℕ => c * gRatio ^ n :=
  (summable_geometric_of_lt_one gRatio_pos.le gRatio_lt_one).mul_left c
theorem summable_g_even (s : ℝ) : Summable fun n : ℕ => g (2 * n + 2) s :=
  Summable.of_nonneg_of_le (fun _ => g_nonneg _ _) (fun n => g_even_le_uniform n s)
    (summable_geom_gRatio _)
theorem summable_g_odd (s : ℝ) : Summable fun n : ℕ => g (2 * n + 3) s :=
  Summable.of_nonneg_of_le (fun _ => g_nonneg _ _) (fun n => g_odd_le_uniform n s)
    (summable_geom_gRatio _)
theorem continuous_fSieve : Continuous fSieve :=
  continuous_tsum (fun _ => continuous_g _) (summable_geom_gRatio _) fun n s => by
    rw [norm_of_nonneg (g_nonneg _ _)]; exact g_even_le_uniform n s
theorem continuous_FSieve : Continuous FSieve :=
  continuous_tsum (fun _ => continuous_g _) (summable_geom_gRatio _) fun n s => by
    rw [norm_of_nonneg (g_nonneg _ _)]; exact g_odd_le_uniform n s
theorem fSieve_nonneg (s : ℝ) : 0 ≤ fSieve s := tsum_nonneg fun _ => g_nonneg _ _
theorem FSieve_nonneg (s : ℝ) : 0 ≤ FSieve s := tsum_nonneg fun _ => g_nonneg _ _
theorem fSieve_pos (s : ℝ) : 0 < fSieve s := by
  set n := ⌈s⌉₊
  have h : 0 < g (2 * n + 2) s :=
    g_pos _ (by omega) (by push_cast; linarith [Nat.le_ceil s, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  exact h.trans_le ((summable_g_even s).le_tsum n fun _ _ => g_nonneg _ _)
theorem fSieve_antitone : Antitone fSieve := fun _ _ h =>
  Summable.tsum_le_tsum (fun _ => g_antitone _ h) (summable_g_even _) (summable_g_even _)
theorem FSieve_antitone : Antitone FSieve := fun _ _ h =>
  Summable.tsum_le_tsum (fun _ => g_antitone _ h) (summable_g_odd _) (summable_g_odd _)
theorem fSieve_of_le_two {s : ℝ} (hs : s ≤ 2) : fSieve s = fSieve 2 :=
  tsum_congr fun n => g_even_of_le_two n hs
theorem FSieve_of_le_three {s : ℝ} (hs : s ≤ 3) : FSieve s = FSieve 3 :=
  tsum_congr fun n => g_odd_of_le_three' n hs
theorem fSieve_le {s : ℝ} (hs : 2 ≤ s) : fSieve s ≤ gLead * (1 - gRatio)⁻¹ * s * exp (-s) :=
  calc fSieve s ≤ ∑' n : ℕ, gLead * s * exp (-s) * gRatio ^ n :=
        Summable.tsum_le_tsum (fun n => (g_even_le n hs).trans_eq (by ring)) (summable_g_even s)
          (summable_geom_gRatio _)
    _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one gRatio_pos.le gRatio_lt_one]; ring
theorem FSieve_le {s : ℝ} (hs : 1 ≤ s) :
    FSieve s ≤ gLead * (exp 1 / 3) * (1 - gRatio)⁻¹ * s * exp (-s) :=
  calc FSieve s ≤ ∑' n : ℕ, gLead * (exp 1 / 3) * s * exp (-s) * gRatio ^ n :=
        Summable.tsum_le_tsum (fun n => (g_odd_le n hs).trans_eq (by ring)) (summable_g_odd s)
          (summable_geom_gRatio _)
    _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one gRatio_pos.le gRatio_lt_one]; ring
theorem shift_div_le {h : ℝ → ℝ} {C t : ℝ} (ht : 1 < t)
    (hb : h (t - 1) ≤ C * (t - 1) * exp (-(t - 1))) :
    h (t - 1) / (t - 1) ≤ C * exp 1 * exp (-t) := by
  have ht1 : 0 < t - 1 := by linarith
  rw [div_le_iff₀ ht1]
  have e : exp (-(t - 1)) = exp 1 * exp (-t) := by rw [← exp_add]; ring_nf
  rw [e] at hb; linarith
theorem integrableOn_shift {h : ℝ → ℝ} (hh : Continuous h) {C s : ℝ} (hs : 2 ≤ s)
    (hnn : ∀ u, 0 ≤ h u) (hb : ∀ u, s - 1 ≤ u → h u ≤ C * u * exp (-u)) :
    IntegrableOn (fun t => h (t - 1) / (t - 1)) (Ioi s) := by
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi s one_pos).const_mul (C * exp 1)) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact (hh.comp (continuous_sub_right 1)).continuousOn.div
      (continuous_sub_right 1).continuousOn fun t ht => by
        have : s < t := ht; linarith
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : s < t := ht
    rw [norm_of_nonneg (div_nonneg (hnn _) (by linarith))]
    have := shift_div_le (C := C) (by linarith) (hb (t - 1) (by linarith))
    simpa using this
theorem tsum_integral_Ioi_shift {φ : ℕ → ℝ → ℝ} {s : ℝ} (hs : 2 ≤ s)
    (hnn : ∀ n x, 0 ≤ φ n x) (hint : ∀ n, IntegrableOn (fun t => φ n (t - 1) / (t - 1)) (Ioi s))
    (hsum : Summable fun n => ∫ t in Ioi s, φ n (t - 1) / (t - 1)) :
    ∑' n, ∫ t in Ioi s, φ n (t - 1) / (t - 1) = ∫ t in Ioi s, (∑' n, φ n (t - 1)) / (t - 1) := by
  rw [integral_tsum_of_summable_integral_norm hint]
  · congr 1; funext t; exact tsum_div_const
  · refine hsum.congr fun n => setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have : s < t := ht
    exact (norm_of_nonneg (div_nonneg (hnn _ _) (by linarith))).symm
theorem integrableOn_FSieve_shift {s : ℝ} (hs : 2 ≤ s) :
    IntegrableOn (fun t => FSieve (t - 1) / (t - 1)) (Ioi s) :=
  integrableOn_shift (C := gLead * (exp 1 / 3) * (1 - gRatio)⁻¹) continuous_FSieve hs
    FSieve_nonneg fun u hu =>
    (FSieve_le (by linarith)).trans_eq (by ring)
theorem integrableOn_fSieve_shift {s : ℝ} (hs : 3 ≤ s) :
    IntegrableOn (fun t => fSieve (t - 1) / (t - 1)) (Ioi s) :=
  integrableOn_shift (C := gLead * (1 - gRatio)⁻¹) continuous_fSieve (by linarith)
    fSieve_nonneg fun u hu =>
    (fSieve_le (by linarith)).trans_eq (by ring)
theorem g_even_add_four_eq_Ioi (n : ℕ) {s : ℝ} (hs : 2 ≤ s) :
    IntegrableOn (fun t => g (2 * n + 3) (t - 1) / (t - 1)) (Ioi s) ∧
      g (2 * n + 4) s = ∫ t in Ioi s, g (2 * n + 3) (t - 1) / (t - 1) := by
  have := g_add_three_eq_Ioi (2 * n + 1) (s := s) (by rw [gLower_two_mul_add_four]; exact hs)
  rwa [show 2 * n + 1 + 3 = 2 * n + 4 by ring, show 2 * n + 1 + 2 = 2 * n + 3 by ring] at this
theorem g_odd_add_three_eq_Ioi (n : ℕ) {s : ℝ} (hs : 3 ≤ s) :
    IntegrableOn (fun t => g (2 * n + 2) (t - 1) / (t - 1)) (Ioi s) ∧
      g (2 * n + 3) s = ∫ t in Ioi s, g (2 * n + 2) (t - 1) / (t - 1) :=
  g_add_three_eq_Ioi (2 * n) (by rw [gLower_two_mul_add_three]; exact hs)
theorem fSieve_eq_integral {s : ℝ} (hs : 2 ≤ s) :
    fSieve s = (∫ t in Ioi s, FSieve (t - 1) / (t - 1)) + g 2 s := by
  have e : ∀ n : ℕ, g (2 * (n + 1) + 2) s = ∫ t in Ioi s, g (2 * n + 3) (t - 1) / (t - 1) :=
    fun n => by rw [show 2 * (n + 1) + 2 = 2 * n + 4 by ring]; exact (g_even_add_four_eq_Ioi n hs).2
  have hsum : Summable fun n : ℕ => g (2 * (n + 1) + 2) s :=
    (summable_nat_add_iff (f := fun n : ℕ => g (2 * n + 2) s) 1).mpr (summable_g_even s)
  have hsum' : Summable fun n : ℕ => ∫ t in Ioi s, g (2 * n + 3) (t - 1) / (t - 1) :=
    hsum.congr e
  have hT := tsum_integral_Ioi_shift (φ := fun n => g (2 * n + 3)) hs (fun _ _ => g_nonneg _ _)
    (fun n => (g_even_add_four_eq_Ioi n hs).1) hsum'
  have h0 := (summable_g_even s).tsum_eq_zero_add
  rw [tsum_congr e, hT] at h0
  rw [fSieve, h0, add_comm]
  rfl
theorem FSieve_eq_integral {s : ℝ} (hs : 3 ≤ s) :
    FSieve s = ∫ t in Ioi s, fSieve (t - 1) / (t - 1) := by
  have e : ∀ n : ℕ, g (2 * n + 3) s = ∫ t in Ioi s, g (2 * n + 2) (t - 1) / (t - 1) :=
    fun n => (g_odd_add_three_eq_Ioi n hs).2
  rw [FSieve, tsum_congr e, tsum_integral_Ioi_shift (φ := fun n => g (2 * n + 2)) (by linarith)
    (fun _ _ => g_nonneg _ _)
    (fun n => (g_odd_add_three_eq_Ioi n hs).1) ((summable_g_odd s).congr e)]
  rfl
end IwaniecLinearSieve
end
section
open Real Set MeasureTheory intervalIntegral Filter Topology
namespace IwaniecLinearSieve
theorem fSieve_eq_on_Icc' {s : ℝ} (hs : s ∈ Icc (2 : ℝ) 4) :
    fSieve s = fSieve 4 + (FSieve 3 + 3) * log (3 / (s - 1)) + s - 4 := by
  have hs' := (summable_g_even s).tsum_eq_zero_add
  have h4 := (summable_g_even 4).tsum_eq_zero_add
  have e : ∀ n : ℕ, g (2 * (n + 1) + 2) s =
      g (2 * (n + 1) + 2) 4 + g (2 * n + 3) 3 * log (3 / (s - 1)) := fun n => by
    rw [show 2 * (n + 1) + 2 = 2 * n + 4 by ring]; exact g_even_eq_on_Icc n hs
  have hsum4 : Summable fun n : ℕ => g (2 * (n + 1) + 2) 4 :=
    (summable_nat_add_iff (f := fun n : ℕ => g (2 * n + 2) 4) 1).mpr (summable_g_even 4)
  rw [tsum_congr e, Summable.tsum_add hsum4 ((summable_g_odd 3).mul_right _), tsum_mul_right]
    at hs'
  rw [fSieve, fSieve, hs', h4, FSieve]
  simp only [mul_zero, zero_add]
  rw [g_two_eq hs, g_two_of_four_le le_rfl]
  ring
theorem hasDerivAt_integral_Ioi {k : ℝ → ℝ} {a s : ℝ} (hint : IntegrableOn k (Ioi a))
    (hc : ContinuousOn k (Ioi a)) (has : a < s) :
    HasDerivAt (fun u => ∫ t in Ioi u, k t) (-k s) s := by
  have hd : HasDerivAt (fun u => (∫ t in Ioi a, k t) - ∫ t in a..u, k t) (-k s) s := by
    refine (integral_hasDerivAt_right ?_ (hc.stronglyMeasurableAtFilter isOpen_Ioi s has)
      (hc.continuousAt (Ioi_mem_nhds has))).const_sub _
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le has.le).2
      (hint.mono_set Ioc_subset_Ioi_self)
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds has] with u hu
  have := integral_Ioi_sub_Ioi hint (le_of_lt hu)
  linarith
theorem continuousOn_shift {h : ℝ → ℝ} (hh : Continuous h) :
    ContinuousOn (fun t => h (t - 1) / (t - 1)) (Ioi 1) :=
  (hh.comp (continuous_sub_right 1)).continuousOn.div (continuous_sub_right 1).continuousOn
    fun t ht => by have : (1 : ℝ) < t := ht; linarith
theorem hasDerivAt_FSieve {s : ℝ} (hs : 3 < s) :
    HasDerivAt FSieve (-(fSieve (s - 1) / (s - 1))) s := by
  have hd := hasDerivAt_integral_Ioi (integrableOn_fSieve_shift le_rfl)
    ((continuousOn_shift continuous_fSieve).mono (Ioi_subset_Ioi (by norm_num))) hs
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hs] with u hu
  exact FSieve_eq_integral (le_of_lt hu)
theorem hasDerivAt_fSieve_of_four_lt {s : ℝ} (hs : 4 < s) :
    HasDerivAt fSieve (-(FSieve (s - 1) / (s - 1))) s := by
  have hd := hasDerivAt_integral_Ioi (integrableOn_FSieve_shift le_rfl)
    ((continuousOn_shift continuous_FSieve).mono (Ioi_subset_Ioi (by norm_num))) (by linarith)
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hs] with u hu
  have hu' : (4 : ℝ) < u := hu
  rw [fSieve_eq_integral (by linarith), g_two_of_four_le hu'.le, add_zero]
theorem hasDerivAt_fSieve_of_lt_four {s : ℝ} (hs2 : 2 < s) (hs4 : s < 4) :
    HasDerivAt fSieve (1 - (FSieve 3 + 3) / (s - 1)) s := by
  have hne : s - 1 ≠ 0 := by linarith
  have hd : HasDerivAt
      (fun u => fSieve 4 + (FSieve 3 + 3) * (log 3 - log (u - 1)) + u - 4)
      (1 - (FSieve 3 + 3) / (s - 1)) s := by
    have := ((((((hasDerivAt_id' s).sub_const 1).log hne).const_sub (log 3)).const_mul
      (FSieve 3 + 3)).const_add (fSieve 4)).add (hasDerivAt_id' s) |>.sub_const 4
    convert this using 1 <;> (try with_reducible_and_instances rfl) <;> (try (funext tt; simp only [Pi.neg_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.inv_apply, Pi.smul_apply, Pi.pow_apply, Function.comp_apply, id_eq]; done))
    field_simp
    ring
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hs2 hs4] with u hu
  rw [fSieve_eq_on_Icc' ⟨hu.1.le, hu.2.le⟩, log_div (by norm_num) (by linarith [hu.1])]
noncomputable def MSieve (s : ℝ) : ℝ := fSieve s + FSieve s + max (3 - s) 0
theorem MSieve_of_three_le {s : ℝ} (hs : 3 ≤ s) : MSieve s = fSieve s + FSieve s := by
  rw [MSieve, max_eq_right (by linarith), add_zero]
theorem MSieve_of_le_three {s : ℝ} (hs : s ≤ 3) : MSieve s = 3 + FSieve 3 - s + fSieve s := by
  rw [MSieve, max_eq_left (by linarith), FSieve_of_le_three hs]; ring
theorem continuous_MSieve : Continuous MSieve :=
  (continuous_fSieve.add continuous_FSieve).add ((continuous_const.sub continuous_id).max
    continuous_const)
theorem MSieve_nonneg (s : ℝ) : 0 ≤ MSieve s := by
  have := fSieve_nonneg s; have := FSieve_nonneg s; have := le_max_right (3 - s) 0
  rw [MSieve]; linarith
theorem MSieve_antitone : Antitone MSieve := fun u v h => by
  have := fSieve_antitone h; have := FSieve_antitone h
  have : max (3 - v) 0 ≤ max (3 - u) 0 := max_le_max (by linarith) le_rfl
  rw [MSieve, MSieve]; linarith
theorem MSieve_le {s : ℝ} (hs : 3 ≤ s) :
    MSieve s ≤ (gLead * (1 - gRatio)⁻¹ + gLead * (exp 1 / 3) * (1 - gRatio)⁻¹) * s * exp (-s) := by
  rw [MSieve_of_three_le hs]
  have := fSieve_le (by linarith : (2 : ℝ) ≤ s)
  have := FSieve_le (by linarith : (1 : ℝ) ≤ s)
  linarith
theorem hasDerivAt_MSieve {s : ℝ} (hs3 : 3 < s) (hs4 : s ≠ 4) :
    HasDerivAt MSieve (-(MSieve (s - 1) / (s - 1))) s := by
  have hne : s - 1 ≠ 0 := by linarith
  have hev : MSieve =ᶠ[𝓝 s] fun u => fSieve u + FSieve u := by
    filter_upwards [Ioi_mem_nhds hs3] with u hu
    exact MSieve_of_three_le (le_of_lt hu)
  rcases lt_or_gt_of_ne hs4 with h4 | h4
  · have hd := (hasDerivAt_fSieve_of_lt_four (by linarith) h4).add (hasDerivAt_FSieve hs3)
    refine (hd.congr_of_eventuallyEq hev).congr_deriv ?_
    rw [MSieve_of_le_three (by linarith)]
    field_simp
    ring
  · have hd := (hasDerivAt_fSieve_of_four_lt h4).add (hasDerivAt_FSieve hs3)
    refine (hd.congr_of_eventuallyEq hev).congr_deriv ?_
    rw [MSieve_of_three_le (by linarith)]
    field_simp
    ring
noncomputable def lemma5Q (s : ℝ) : ℝ := (s - 1) * MSieve s - ∫ x in (s - 1)..s, MSieve x
theorem lemma5Q_eq (s : ℝ) : lemma5Q s =
    (s - 1) * MSieve s - ((∫ x in (0 : ℝ)..s, MSieve x) - ∫ x in (0 : ℝ)..(s - 1), MSieve x) := by
  rw [lemma5Q, integral_interval_sub_left (continuous_MSieve.intervalIntegrable _ _)
    (continuous_MSieve.intervalIntegrable _ _)]
theorem continuous_lemma5Q : Continuous lemma5Q := by
  have hP : Continuous fun u => ∫ x in (0 : ℝ)..u, MSieve x :=
    continuous_primitive (fun _ _ => continuous_MSieve.intervalIntegrable _ _) 0
  rw [funext lemma5Q_eq]
  exact ((continuous_id.sub continuous_const).mul continuous_MSieve).sub
    (hP.sub (hP.comp (continuous_id.sub continuous_const)))
theorem hasDerivAt_lemma5Q {s : ℝ} (hs3 : 3 < s) (hs4 : s ≠ 4) : HasDerivAt lemma5Q 0 s := by
  have hM := hasDerivAt_MSieve hs3 hs4
  have hP : ∀ u, HasDerivAt (fun u => ∫ x in (0 : ℝ)..u, MSieve x) (MSieve u) u := fun u =>
    (continuous_MSieve.integral_hasStrictDerivAt 0 u).hasDerivAt
  have hP1 : HasDerivAt (fun u => ∫ x in (0 : ℝ)..(u - 1), MSieve x) (MSieve (s - 1)) s :=
    HasDerivAt.comp_sub_const s 1 (hP (s - 1))
  have hd := (((hasDerivAt_id' s).sub_const 1).mul hM).sub ((hP s).sub hP1)
  rw [funext lemma5Q_eq]
  refine hd.congr_deriv ?_
  have hne : s - 1 ≠ 0 := by linarith
  field_simp
  ring
theorem lemma5Q_eq_of_deriv {a b : ℝ} (hab : a ≤ b) (hd : ∀ x ∈ Ioo a b, HasDerivAt lemma5Q 0 x) :
    lemma5Q b = lemma5Q a := by
  rcases eq_or_lt_of_le hab with h | h
  · rw [h]
  · obtain ⟨c, _, hc⟩ := exists_hasDerivAt_eq_slope lemma5Q (fun _ => (0 : ℝ)) h
      continuous_lemma5Q.continuousOn hd
    have hba : b - a ≠ 0 := by linarith
    rw [eq_div_iff hba, zero_mul] at hc
    linarith
theorem lemma5Q_const {b : ℝ} (hb : 3 ≤ b) : lemma5Q b = lemma5Q 3 := by
  rcases le_total b 4 with h4 | h4
  · exact lemma5Q_eq_of_deriv hb fun x hx => hasDerivAt_lemma5Q hx.1 (by linarith [hx.2])
  · rw [lemma5Q_eq_of_deriv h4 fun x hx => hasDerivAt_lemma5Q (by linarith [hx.1])
      (by linarith [hx.1]),
      lemma5Q_eq_of_deriv (by norm_num) fun x hx => hasDerivAt_lemma5Q hx.1 (by linarith [hx.2])]
theorem abs_lemma5Q_le {b : ℝ} (hb : 4 ≤ b) :
    |lemma5Q b| ≤ ((gLead * (1 - gRatio)⁻¹ + gLead * (exp 1 / 3) * (1 - gRatio)⁻¹) * exp 1) *
      (b ^ 2 * exp (-b)) := by
  set C := gLead * (1 - gRatio)⁻¹ + gLead * (exp 1 / 3) * (1 - gRatio)⁻¹
  have hM1 : MSieve (b - 1) ≤ C * (b - 1) * exp (-(b - 1)) := MSieve_le (s := b - 1) (by linarith)
  have hMb : MSieve b ≤ MSieve (b - 1) := MSieve_antitone (by linarith)
  have hI0 : 0 ≤ ∫ x in (b - 1)..b, MSieve x :=
    integral_nonneg (by linarith) fun x _ => MSieve_nonneg x
  have hI1 : ∫ x in (b - 1)..b, MSieve x ≤ MSieve (b - 1) := by
    have := integral_mono_on (μ := volume) (by linarith : b - 1 ≤ b)
      (continuous_MSieve.intervalIntegrable _ _)
      (intervalIntegrable_const (c := MSieve (b - 1))) fun x hx => MSieve_antitone hx.1
    simpa using this
  have hQ : |lemma5Q b| ≤ b * MSieve (b - 1) := by
    rw [lemma5Q, abs_le]
    have := MSieve_nonneg b
    constructor <;> nlinarith
  have he : exp (-(b - 1)) = exp 1 * exp (-b) := by rw [← exp_add]; ring_nf
  rw [he] at hM1
  refine hQ.trans ?_
  have := mul_le_mul_of_nonneg_left hM1 (by linarith : (0 : ℝ) ≤ b)
  have hb' : 0 ≤ C * exp 1 * exp (-b) * b := by
    have : 0 ≤ C := by
      have := gLead_nonneg; have := gRatio_lt_one; have := exp_pos 1
      have : 0 ≤ (1 - gRatio)⁻¹ := inv_nonneg.2 (by linarith)
      positivity
    have := exp_pos 1; have := exp_pos (-b); positivity
  nlinarith
theorem lemma5Q_three : lemma5Q 3 = 0 := by
  set C := (gLead * (1 - gRatio)⁻¹ + gLead * (exp 1 / 3) * (1 - gRatio)⁻¹) * exp 1
  have hlim : Tendsto lemma5Q atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by
      simpa using (tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).const_mul C)
    filter_upwards [eventually_ge_atTop 4] with b hb
    rw [norm_eq_abs]; exact abs_lemma5Q_le hb
  have hconst : Tendsto lemma5Q atTop (𝓝 (lemma5Q 3)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 3] with b hb
    exact (lemma5Q_const hb).symm
  exact tendsto_nhds_unique hconst hlim
theorem integral_MSieve_two_three :
    ∫ x in (2 : ℝ)..3, MSieve x = FSieve 3 - 1 + fSieve 4 +
      (FSieve 3 + 3) * (2 * (log 3 - log 2) - log 3 + 1) := by
  set K := FSieve 3 + 3
  set c := FSieve 3 - 1 + fSieve 4
  have hcongr :
      ∫ x in (2 : ℝ)..3, MSieve x = ∫ x in (2 : ℝ)..3, (c + K * (log 3 - log (x - 1))) := by
    refine integral_congr fun x hx => ?_
    rw [uIcc_of_le (by norm_num)] at hx
    rw [MSieve_of_le_three hx.2, fSieve_eq_on_Icc' ⟨hx.1, by linarith [hx.2]⟩,
      log_div (by norm_num) (by linarith [hx.1])]
    ring
  rw [hcongr, integral_eq_sub_of_hasDerivAt
    (f := fun x => c * x + K * ((x - 1) * (log 3 - log (x - 1)) + x))]
  · norm_num
    ring
  · intro x hx
    rw [uIcc_of_le (by norm_num)] at hx
    have hne : x - 1 ≠ 0 := by linarith [hx.1]
    have := ((hasDerivAt_id' x).const_mul c).add
      (((((hasDerivAt_id' x).sub_const 1).mul
        ((((hasDerivAt_id' x).sub_const 1).log hne).const_sub (log 3))).add
        (hasDerivAt_id' x)).const_mul K)
    convert this using 1 <;> (try with_reducible_and_instances rfl) <;> (try (funext tt; simp only [Pi.neg_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.inv_apply, Pi.smul_apply, Pi.pow_apply, Function.comp_apply, id_eq]; done))
    field_simp
    ring
  · refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.add (continuousOn_const.mul (continuousOn_const.sub ?_))
    refine ((continuous_sub_right 1).continuousOn).log fun x hx => ?_
    rw [uIcc_of_le (by norm_num)] at hx
    linarith [hx.1]
theorem fSieve_four_add : fSieve 4 + (FSieve 3 + 3) * log 3 = 4 := by
  have h := lemma5Q_three
  rw [lemma5Q, show (3 : ℝ) - 1 = 2 by norm_num, integral_MSieve_two_three,
    MSieve_of_three_le le_rfl, fSieve_eq_on_Icc' ⟨by norm_num, by norm_num⟩,
    show (3 : ℝ) / (3 - 1) = 3 / 2 by norm_num, log_div (by norm_num) (by norm_num)] at h
  linarith
theorem fSieve_eq_on_Icc {s : ℝ} (hs : s ∈ Icc (2 : ℝ) 4) :
    fSieve s = s - (FSieve 3 + 3) * log (s - 1) := by
  rw [fSieve_eq_on_Icc' hs, log_div (by norm_num) (by linarith [hs.1])]
  linarith [fSieve_four_add]
theorem fSieve_two : fSieve 2 = 2 := by
  rw [fSieve_eq_on_Icc ⟨le_rfl, by norm_num⟩]; norm_num
theorem le_one_sub_fSieve_div {s : ℝ} (hs : s ∈ Icc (2 : ℝ) 4) :
    3 * log (s - 1) / s ≤ 1 - fSieve s / s := by
  have hs0 : 0 < s := by linarith [hs.1]
  have hlog : 0 ≤ log (s - 1) := log_nonneg (by linarith [hs.1])
  have hF := FSieve_nonneg 3
  rw [fSieve_eq_on_Icc hs, div_le_iff₀ hs0, sub_mul, div_mul_cancel₀ _ hs0.ne']
  nlinarith
theorem one_sub_fSieve_div_ge : ∀ s ∈ Icc (2 : ℝ) 4, 1 - fSieve s / s ≥ 3 * Real.log (s - 1) / s :=
  fun _ hs => le_one_sub_fSieve_div hs
end IwaniecLinearSieve
end
section
end
section
open Set Filter Topology MeasureTheory
namespace IwaniecLinearSieve
namespace Delay
variable {k y₀ : ℝ → ℝ}
theorem step_of_le {y : ℝ → ℝ} {s : ℝ} (hs : s ≤ 3) : step k y₀ y s = y₀ s := by
  simp [step, min_eq_left hs, max_eq_right hs]
theorem step_of_ge {y : ℝ → ℝ} {s : ℝ} (hs : 3 ≤ s) :
    step k y₀ y s = y₀ 3 + ∫ x in (3 : ℝ)..s, k x * y (x - 1) := by
  simp [step, min_eq_right hs, max_eq_left hs]
theorem step_congr {y y' : ℝ → ℝ} {m : ℝ} (h : ∀ x ≤ m, y x = y' x) {s : ℝ} (hs : s ≤ m + 1) :
    step k y₀ y s = step k y₀ y' s := by
  rcases le_total s 3 with h3 | h3
  · rw [step_of_le h3, step_of_le h3]
  · rw [step_of_ge h3, step_of_ge h3]
    congr 1
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le h3] at hx
    rw [h (x - 1) (by linarith [hx.2])]
theorem iter_succ_eq (n : ℕ) {s : ℝ} (hs : s ≤ n + 3) :
    iter k y₀ (n + 1) s = iter k y₀ n s := by
  induction n generalizing s with
  | zero =>
    simp only [Nat.cast_zero, zero_add] at hs
    exact step_of_le hs
  | succ n ih =>
    change step k y₀ (iter k y₀ (n + 1)) s = step k y₀ (iter k y₀ n) s
    refine step_congr (m := n + 3) (fun x hx => ih hx) ?_
    push_cast at hs
    linarith
theorem iter_add_eq (n j : ℕ) {s : ℝ} (hs : s ≤ n + 3) :
    iter k y₀ (n + j) s = iter k y₀ n s := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← add_assoc, iter_succ_eq _ (by push_cast; linarith), ih]
theorem iter_eq_of_le {m n : ℕ} (hmn : m ≤ n) {s : ℝ} (hs : s ≤ m + 3) :
    iter k y₀ n s = iter k y₀ m s := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact iter_add_eq m j hs
theorem sol_eq_iter {n : ℕ} {s : ℝ} (hs : s ≤ n + 3) : sol k y₀ s = iter k y₀ n s := by
  unfold sol
  rcases le_total n ⌈s⌉₊ with h | h
  · exact iter_eq_of_le h hs
  · exact (iter_eq_of_le h (by linarith [Nat.le_ceil s])).symm
theorem sol_eq_step (s : ℝ) : sol k y₀ s = step k y₀ (sol k y₀) s := by
  set n := ⌈s⌉₊
  have hn : s ≤ n := Nat.le_ceil s
  rw [sol_eq_iter (n := n + 1) (by push_cast; linarith)]
  change step k y₀ (iter k y₀ n) s = _
  exact step_congr (m := n + 3) (fun x hx => (sol_eq_iter hx).symm) (by linarith)
theorem sol_of_le {s : ℝ} (hs : s ≤ 3) : sol k y₀ s = y₀ s := by
  rw [sol_eq_step, step_of_le hs]
theorem sol_of_ge {s : ℝ} (hs : 3 ≤ s) :
    sol k y₀ s = y₀ 3 + ∫ x in (3 : ℝ)..s, k x * sol k y₀ (x - 1) := by
  rw [sol_eq_step, step_of_ge hs]
theorem continuous_step (hk : Continuous k) (hy₀ : Continuous y₀) {y : ℝ → ℝ}
    (hy : Continuous y) : Continuous (step k y₀ y) := by
  have hF : Continuous fun x => k x * y (x - 1) := hk.mul (hy.comp (continuous_sub_right 1))
  have hP : Continuous fun b => ∫ x in (3 : ℝ)..b, k x * y (x - 1) :=
    intervalIntegral.continuous_primitive (fun a b => hF.intervalIntegrable a b) 3
  exact (hy₀.comp (continuous_id.min continuous_const)).add
    (hP.comp (continuous_id.max continuous_const))
theorem continuous_iter (hk : Continuous k) (hy₀ : Continuous y₀) (n : ℕ) :
    Continuous (iter k y₀ n) := by
  induction n with
  | zero => exact hy₀
  | succ n ih => exact continuous_step hk hy₀ ih
theorem continuous_sol (hk : Continuous k) (hy₀ : Continuous y₀) : Continuous (sol k y₀) := by
  rw [continuous_iff_continuousAt]
  intro s
  set n := ⌈s⌉₊
  have hn : s ≤ n := Nat.le_ceil s
  have hev : iter k y₀ n =ᶠ[𝓝 s] sol k y₀ := by
    filter_upwards [Iio_mem_nhds (show s < n + 3 by linarith)] with x hx
    exact (sol_eq_iter hx.le).symm
  exact ((continuous_iter hk hy₀ n).continuousAt).congr hev
theorem hasDerivAt_primitive (hk : Continuous k) (hy₀ : Continuous y₀) (s : ℝ) :
    HasDerivAt (fun t => y₀ 3 + ∫ x in (3 : ℝ)..t, k x * sol k y₀ (x - 1))
      (k s * sol k y₀ (s - 1)) s := by
  have hF : Continuous fun x => k x * sol k y₀ (x - 1) :=
    hk.mul ((continuous_sol hk hy₀).comp (continuous_sub_right 1))
  exact ((hF.integral_hasStrictDerivAt 3 s).hasDerivAt).const_add _
theorem hasDerivAt_sol (hk : Continuous k) (hy₀ : Continuous y₀) {s : ℝ} (hs : 3 < s) :
    HasDerivAt (sol k y₀) (k s * sol k y₀ (s - 1)) s := by
  refine (hasDerivAt_primitive hk hy₀ s).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hs] with x hx
  exact sol_of_ge hx.out.le
theorem hasDerivWithinAt_sol_Ici (hk : Continuous k) (hy₀ : Continuous y₀) {s : ℝ}
    (hs : 3 ≤ s) : HasDerivWithinAt (sol k y₀) (k s * sol k y₀ (s - 1)) (Ici s) s := by
  refine (hasDerivAt_primitive hk hy₀ s).hasDerivWithinAt.congr (fun x hx => ?_) ?_
  · exact sol_of_ge (hs.trans hx)
  · exact sol_of_ge hs
end Delay
theorem pos_of_first_crossing {f : ℝ → ℝ} {a₀ a : ℝ} (hf : ContinuousOn f (Ici a))
    (hinit : ∀ x ∈ Icc a₀ a, 0 ≤ f x) (ha : 0 < f a)
    (hstep : ∀ s > a, (∀ x ∈ Icc a₀ s, 0 ≤ f x) → (∀ x ∈ Ico a s, 0 < f x) → 0 < f s) :
    ∀ s, a ≤ s → 0 < f s := by
  by_contra hcon
  push Not at hcon
  set B := Ici a ∩ f ⁻¹' Iic 0 with hB
  have hBne : B.Nonempty := by
    obtain ⟨s, hs, hfs⟩ := hcon
    exact ⟨s, hs, hfs⟩
  have hBc : IsClosed B := hf.preimage_isClosed_of_isClosed isClosed_Ici isClosed_Iic
  have hBb : BddBelow B := ⟨a, fun x hx => hx.1⟩
  set t := sInf B
  have htB : t ∈ B := hBc.csInf_mem hBne hBb
  have hat : a ≤ t := htB.1
  have hft : f t ≤ 0 := htB.2
  have hat' : a < t := lt_of_le_of_ne hat fun h => by rw [← h] at hft; linarith
  have hpos : ∀ x ∈ Ico a t, 0 < f x := by
    intro x hx
    by_contra hx'
    push Not at hx'
    have : t ≤ x := csInf_le hBb ⟨hx.1, hx'⟩
    exact absurd hx.2 (not_lt.2 this)
  have hnn : ∀ x ∈ Icc a t, 0 ≤ f x := by
    have hcl : closure (Ico a t) = Icc a t := closure_Ico hat'.ne
    have hcont : ContinuousOn f (closure (Ico a t)) := by
      rw [hcl]; exact hf.mono Icc_subset_Ici_self
    have := le_on_closure (f := fun _ => (0 : ℝ)) (g := f) (fun x hx => (hpos x hx).le)
      continuousOn_const hcont
    rwa [hcl] at this
  have hall : ∀ x ∈ Icc a₀ t, 0 ≤ f x := by
    intro x hx
    rcases le_total x a with hxa | hxa
    · exact hinit x ⟨hx.1, hxa⟩
    · exact hnn x ⟨hxa, hx.2⟩
  linarith [hstep t hat' hall hpos]
end IwaniecLinearSieve
end
section
open Real Set Filter Topology MeasureTheory
namespace IwaniecLinearSieve
noncomputable def bigW : ℝ → ℝ := Delay.sol delayKer initW
theorem delayKer_of_ge {x : ℝ} (hx : 3 ≤ x) : delayKer x = x / (x - 1) ^ 2 := by
  simp [delayKer, max_eq_left hx]
theorem continuous_delayKer : Continuous delayKer := by
  unfold delayKer
  refine (continuous_id.max continuous_const).div
    (((continuous_id.max continuous_const).sub continuous_const).pow 2) fun x => ?_
  have : (3 : ℝ) ≤ max x 3 := le_max_right _ _
  have : (0 : ℝ) < max x 3 - 1 := by linarith
  positivity
theorem continuous_initW : Continuous initW := by
  unfold initW
  have h1 : Continuous fun s : ℝ => max s 2 - 1 :=
    (continuous_id.max continuous_const).sub continuous_const
  have hne : ∀ s : ℝ, max s 2 - 1 ≠ 0 := fun s => by
    have : (2 : ℝ) ≤ max s 2 := le_max_right _ _
    linarith
  exact (continuous_const.div h1 hne).sub (h1.log hne)
theorem initW_of_le {s : ℝ} (hs : s ≤ 2) : initW s = 1 := by
  simp [initW, max_eq_right hs]
  norm_num
theorem initW_of_ge {s : ℝ} (hs : 2 ≤ s) : initW s = 1 / (s - 1) - log (s - 1) := by
  simp [initW, max_eq_left hs]
theorem continuous_bigW : Continuous bigW :=
  Delay.continuous_sol continuous_delayKer continuous_initW
theorem continuous_initM : Continuous fun s => 2 + initW s :=
  continuous_const.add continuous_initW
theorem continuous_bigM : Continuous bigM :=
  Delay.continuous_sol continuous_delayKer.neg continuous_initM
theorem bigW_of_le_three {s : ℝ} (hs : s ≤ 3) : bigW s = initW s :=
  Delay.sol_of_le hs
theorem bigM_of_le_three {s : ℝ} (hs : s ≤ 3) : bigM s = 2 + initW s :=
  Delay.sol_of_le hs
theorem bigW_of_le_two {s : ℝ} (hs : s ≤ 2) : bigW s = 1 := by
  rw [bigW_of_le_three (by linarith), initW_of_le hs]
theorem bigM_of_le_two {s : ℝ} (hs : s ≤ 2) : bigM s = 3 := by
  rw [bigM_of_le_three (by linarith), initW_of_le hs]; norm_num
theorem bigW_eq {s : ℝ} (hs : 2 ≤ s) (hs' : s ≤ 3) : bigW s = 1 / (s - 1) - log (s - 1) := by
  rw [bigW_of_le_three hs', initW_of_ge hs]
theorem bigM_eq {s : ℝ} (hs : 2 ≤ s) (hs' : s ≤ 3) :
    bigM s = 2 + 1 / (s - 1) - log (s - 1) := by
  rw [bigM_of_le_three hs', initW_of_ge hs]; ring
theorem bigM_two : bigM 2 = 3 := bigM_of_le_two le_rfl
theorem bigW_three : bigW 3 = 1 / 2 - log 2 := by
  rw [bigW_eq (by norm_num) le_rfl]; norm_num
theorem bigM_three : bigM 3 = 5 / 2 - log 2 := by
  rw [bigM_eq (by norm_num) le_rfl]; norm_num
theorem hasDerivAt_initForm {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun x => 1 / (x - 1) - log (x - 1)) (-(x / (x - 1) ^ 2)) x := by
  have h0 : x - 1 ≠ 0 := by linarith
  have h1 : HasDerivAt (fun x : ℝ => x - 1) 1 x := (hasDerivAt_id x).sub_const 1
  have := (h1.inv h0).sub (h1.log h0)
  convert this using 1 <;> (try with_reducible_and_instances rfl)
  · ext y; simp [one_div]
  · field_simp; ring
theorem bigM_eq_integral {s : ℝ} (hs : 3 ≤ s) :
    bigM s = bigM 3 - ∫ x in (3 : ℝ)..s, x / (x - 1) ^ 2 * bigM (x - 1) := by
  rw [bigM, Delay.sol_of_ge hs, ← bigM, bigM_of_le_three le_rfl, sub_eq_add_neg,
    ← intervalIntegral.integral_neg]
  congr 1
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [uIcc_of_le hs] at hx
  simp only [delayKer_of_ge hx.1, bigM, neg_mul]
theorem hasDerivAt_bigW {s : ℝ} (hs : 3 < s) :
    HasDerivAt bigW (s / (s - 1) ^ 2 * bigW (s - 1)) s := by
  have := Delay.hasDerivAt_sol continuous_delayKer continuous_initW hs
  rwa [delayKer_of_ge hs.le] at this
theorem hasDerivAt_bigM {s : ℝ} (hs : 3 < s) :
    HasDerivAt bigM (-(s / (s - 1) ^ 2 * bigM (s - 1))) s := by
  have := Delay.hasDerivAt_sol continuous_delayKer.neg
    continuous_initM hs
  rwa [Pi.neg_apply, delayKer_of_ge hs.le, neg_mul] at this
theorem hasDerivWithinAt_bigW_Ici {s : ℝ} (hs : 3 ≤ s) :
    HasDerivWithinAt bigW (s / (s - 1) ^ 2 * bigW (s - 1)) (Ici s) s := by
  have := Delay.hasDerivWithinAt_sol_Ici continuous_delayKer continuous_initW hs
  rwa [delayKer_of_ge hs] at this
theorem hasDerivWithinAt_bigM_Ici {s : ℝ} (hs : 3 ≤ s) :
    HasDerivWithinAt bigM (-(s / (s - 1) ^ 2 * bigM (s - 1))) (Ici s) s := by
  have := Delay.hasDerivWithinAt_sol_Ici continuous_delayKer.neg
    continuous_initM hs
  rwa [Pi.neg_apply, delayKer_of_ge hs, neg_mul] at this
theorem hasDerivAt_integral_unit {F : ℝ → ℝ} (hF : Continuous F) (t : ℝ) :
    HasDerivAt (fun t => ∫ x in (t - 1)..t, F x) (F t - F (t - 1)) t := by
  have hI : ∀ a b : ℝ, IntervalIntegrable F volume a b := fun a b => hF.intervalIntegrable a b
  have heq : (fun t => ∫ x in (t - 1)..t, F x) =
      fun t => (∫ x in (0 : ℝ)..t, F x) - ∫ x in (0 : ℝ)..(t - 1), F x := by
    ext t
    rw [intervalIntegral.integral_interval_sub_left (hI 0 t) (hI 0 (t - 1))]
  rw [heq]
  have h1 := (hF.integral_hasStrictDerivAt 0 t).hasDerivAt
  have h2 := ((hF.integral_hasStrictDerivAt 0 (t - 1)).hasDerivAt).comp t
    ((hasDerivAt_id t).sub_const 1)
  convert h1.sub h2 using 1 <;> (try with_reducible_and_instances rfl)
  · funext x; simp [Function.comp_def]
  · ring
theorem eq_of_hasDerivAt_zero {g : ℝ → ℝ} {a : ℝ} (hg : ContinuousOn g (Ici a))
    (hd : ∀ x, a < x → HasDerivAt g 0 x) {s : ℝ} (hs : a ≤ s) : g s = g a := by
  rcases hs.eq_or_lt with rfl | hs
  · rfl
  obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope g (fun _ => (0 : ℝ)) hs
    (hg.mono Icc_subset_Ici_self) fun x hx => hd x hx.1
  have : s - a ≠ 0 := by linarith
  field_simp at hc'
  linarith
noncomputable def wIntegrand (x : ℝ) : ℝ := bigW x / max x 1 ^ 2
theorem continuous_wIntegrand : Continuous wIntegrand := by
  unfold wIntegrand
  refine continuous_bigW.div ((continuous_id.max continuous_const).pow 2) fun x => ?_
  have : (1 : ℝ) ≤ max x 1 := le_max_right _ _
  positivity
theorem wIntegrand_of_ge {x : ℝ} (hx : 1 ≤ x) : wIntegrand x = bigW x / x ^ 2 := by
  simp [wIntegrand, max_eq_left hx]
theorem integral_wIntegrand_two_three :
    ∫ x in (2 : ℝ)..3, wIntegrand x = (1 + log 2) / 3 - 1 / 2 := by
  have hcongr : ∫ x in (2 : ℝ)..3, wIntegrand x =
      ∫ x in (2 : ℝ)..3, (1 / (x - 1) - log (x - 1)) / x ^ 2 := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le (by norm_num)] at hx
    rw [wIntegrand_of_ge (by linarith [hx.1]), bigW_eq hx.1 hx.2]
  rw [hcongr]
  have hderiv : ∀ x ∈ uIcc (2 : ℝ) 3, HasDerivAt (fun x => (1 + log (x - 1)) / x)
      ((1 / (x - 1) - log (x - 1)) / x ^ 2) x := by
    intro x hx
    rw [uIcc_of_le (by norm_num)] at hx
    have hx1 : x - 1 ≠ 0 := by linarith [hx.1]
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have h1 : HasDerivAt (fun x : ℝ => x - 1) 1 x := (hasDerivAt_id x).sub_const 1
    have := ((h1.log hx1).const_add 1).div (hasDerivAt_id x) hx0
    refine this.congr_deriv ?_
    simp only [id]
    field_simp
    ring
  have hcont : ContinuousOn (fun x : ℝ => (1 / (x - 1) - log (x - 1)) / x ^ 2) (uIcc 2 3) := by
    rw [uIcc_of_le (by norm_num)]
    intro x hx
    have hx1 : x - 1 ≠ 0 := by linarith [hx.1]
    have hx0 : x ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith [hx.1])
    exact (((continuousAt_const.div (continuousAt_id.sub continuousAt_const) hx1).sub
      ((continuousAt_id.sub continuousAt_const).log hx1)).div
      (continuousAt_id.pow 2) hx0).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  norm_num
theorem bigW_eq_neg_mul_integral {s : ℝ} (hs : 3 ≤ s) :
    bigW s = -s * ∫ x in (s - 1)..s, bigW x / x ^ 2 := by
  set g : ℝ → ℝ := fun t => bigW t / t + ∫ x in (t - 1)..t, wIntegrand x
  have hgc : ContinuousOn g (Ici 3) := by
    refine ContinuousOn.add ?_ ?_
    · exact continuous_bigW.continuousOn.div continuousOn_id fun x hx => by
        linarith [hx.out]
    · exact fun t _ => (hasDerivAt_integral_unit continuous_wIntegrand t).continuousAt
        |>.continuousWithinAt
  have hgd : ∀ t, 3 < t → HasDerivAt g 0 t := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith
    have ht1 : t - 1 ≠ 0 := by linarith
    have := ((hasDerivAt_bigW ht).div (hasDerivAt_id t) ht0).add
      (hasDerivAt_integral_unit continuous_wIntegrand t)
    refine this.congr_deriv ?_
    rw [wIntegrand_of_ge (by linarith), wIntegrand_of_ge (by linarith)]
    simp only [id]
    field_simp
    ring
  have h3 : g 3 = 0 := by
    simp only [g]
    norm_num
    rw [integral_wIntegrand_two_three, bigW_three]
    ring
  have hgs : g s = 0 := (eq_of_hasDerivAt_zero hgc hgd hs).trans h3
  have hint : ∫ x in (s - 1)..s, wIntegrand x = ∫ x in (s - 1)..s, bigW x / x ^ 2 := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le (by linarith)] at hx
    exact wIntegrand_of_ge (by linarith [hx.1])
  simp only [g, hint] at hgs
  have hs0 : s ≠ 0 := by linarith
  field_simp at hgs
  linarith
noncomputable def mIntegrand (x : ℝ) : ℝ := (1 - 1 / (2 * max x 1 ^ 2)) * bigM x
theorem continuous_mIntegrand : Continuous mIntegrand := by
  unfold mIntegrand
  refine (continuous_const.sub (continuous_const.div
    (continuous_const.mul ((continuous_id.max continuous_const).pow 2)) fun x => ?_)).mul
    continuous_bigM
  exact mul_ne_zero two_ne_zero (pow_ne_zero 2 (lt_of_lt_of_le one_pos (le_max_right _ _)).ne')
theorem mIntegrand_of_ge {x : ℝ} (hx : 1 ≤ x) :
    mIntegrand x = (1 - 1 / (2 * x ^ 2)) * bigM x := by
  simp [mIntegrand, max_eq_left hx]
theorem integral_mIntegrand_two_three :
    ∫ x in (2 : ℝ)..3, mIntegrand x = 7 / 2 * (5 / 2 - log 2) / 3 := by
  have hcongr : ∫ x in (2 : ℝ)..3, mIntegrand x =
      ∫ x in (2 : ℝ)..3, (1 - 1 / (2 * x ^ 2)) * (2 + (1 / (x - 1) - log (x - 1))) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le (by norm_num)] at hx
    rw [mIntegrand_of_ge (by linarith [hx.1]), bigM_eq hx.1 hx.2]
    ring
  rw [hcongr]
  have hderiv : ∀ x ∈ uIcc (2 : ℝ) 3, HasDerivAt
      (fun x => ((x - 1) ^ 2 - 1 / 2) * (2 + (1 / (x - 1) - log (x - 1))) / x + x +
        1 / (2 * (x - 1)))
      ((1 - 1 / (2 * x ^ 2)) * (2 + (1 / (x - 1) - log (x - 1)))) x := by
    intro x hx
    rw [uIcc_of_le (by norm_num)] at hx
    have hx1 : x - 1 ≠ 0 := by linarith [hx.1]
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have h1 : HasDerivAt (fun x : ℝ => x - 1) 1 x := (hasDerivAt_id x).sub_const 1
    have hr : HasDerivAt (fun x : ℝ => (x - 1) ^ 2 - 1 / 2) (2 * (x - 1)) x := by
      convert (h1.pow 2).sub_const (1 / 2) using 1 <;> (try with_reducible_and_instances rfl) <;> (try (funext tt; simp only [Pi.neg_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.inv_apply, Pi.smul_apply, Pi.pow_apply, Function.comp_apply, id_eq]; done)); ring
    have hm := (hasDerivAt_initForm (x := x) (by linarith [hx.1])).const_add 2
    have hq : HasDerivAt (fun x : ℝ => 2 * (x - 1)) 2 x := by
      convert h1.const_mul 2 using 1 <;> (try with_reducible_and_instances rfl) <;> (try (funext tt; simp only [Pi.neg_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.inv_apply, Pi.smul_apply, Pi.pow_apply, Function.comp_apply, id_eq]; done)); ring
    have := (((hr.mul hm).div (hasDerivAt_id x) hx0).add (hasDerivAt_id x)).add
      ((hasDerivAt_const x (1 : ℝ)).div hq (by positivity))
    refine this.congr_deriv ?_
    simp only [id, Pi.mul_apply]
    field_simp
    ring
  have hcont : ContinuousOn
      (fun x : ℝ => (1 - 1 / (2 * x ^ 2)) * (2 + (1 / (x - 1) - log (x - 1)))) (uIcc 2 3) := by
    rw [uIcc_of_le (by norm_num)]
    intro x hx
    have hx1 : x - 1 ≠ 0 := by linarith [hx.1]
    have hx0 : 2 * x ^ 2 ≠ 0 := by have : x ≠ 0 := by linarith [hx.1]
                                   positivity
    exact ((continuousAt_const.sub (continuousAt_const.div
      (continuousAt_const.mul (continuousAt_id.pow 2)) hx0)).mul
      (continuousAt_const.add ((continuousAt_const.div (continuousAt_id.sub continuousAt_const)
        hx1).sub ((continuousAt_id.sub continuousAt_const).log hx1)))).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  norm_num
  ring
theorem bigM_integral_identity {s : ℝ} (hs : 3 ≤ s) :
    ((s - 1) ^ 2 - 1 / 2) * bigM s / s = ∫ x in (s - 1)..s, (1 - 1 / (2 * x ^ 2)) * bigM x := by
  set g : ℝ → ℝ := fun t => ((t - 1) ^ 2 - 1 / 2) * bigM t / t - ∫ x in (t - 1)..t, mIntegrand x
  have hgc : ContinuousOn g (Ici 3) := by
    refine ContinuousOn.sub ?_ ?_
    · refine ContinuousOn.div ?_ continuousOn_id fun x hx => by linarith [hx.out]
      exact (((continuous_id.sub continuous_const).pow 2).sub continuous_const).continuousOn.mul
        continuous_bigM.continuousOn
    · exact fun t _ => (hasDerivAt_integral_unit continuous_mIntegrand t).continuousAt
        |>.continuousWithinAt
  have hgd : ∀ t, 3 < t → HasDerivAt g 0 t := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith
    have ht1 : t - 1 ≠ 0 := by linarith
    have h1 : HasDerivAt (fun x : ℝ => x - 1) 1 t := (hasDerivAt_id t).sub_const 1
    have hr : HasDerivAt (fun x : ℝ => (x - 1) ^ 2 - 1 / 2) (2 * (t - 1)) t := by
      convert (h1.pow 2).sub_const (1 / 2) using 1 <;> (try with_reducible_and_instances rfl) <;> (try (funext tt; simp only [Pi.neg_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.inv_apply, Pi.smul_apply, Pi.pow_apply, Function.comp_apply, id_eq]; done)); ring
    have := ((hr.mul (hasDerivAt_bigM ht)).div (hasDerivAt_id t) ht0).sub
      (hasDerivAt_integral_unit continuous_mIntegrand t)
    refine this.congr_deriv ?_
    rw [mIntegrand_of_ge (by linarith), mIntegrand_of_ge (by linarith)]
    simp only [id, Pi.mul_apply]
    field_simp
    ring
  have h3 : g 3 = 0 := by
    simp only [g]
    norm_num
    rw [integral_mIntegrand_two_three, bigM_three]
    ring
  have hgs : g s = 0 := (eq_of_hasDerivAt_zero hgc hgd hs).trans h3
  have hint : ∫ x in (s - 1)..s, mIntegrand x =
      ∫ x in (s - 1)..s, (1 - 1 / (2 * x ^ 2)) * bigM x := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le (by linarith)] at hx
    exact mIntegrand_of_ge (by linarith [hx.1])
  simp only [g, hint] at hgs
  linarith
end IwaniecLinearSieve
end
section
open Real Set Filter Topology MeasureTheory
namespace IwaniecLinearSieve
theorem initW_mem {s : ℝ} (hs : s ≤ 3) : -(1 / 2) ≤ initW s ∧ initW s ≤ 1 := by
  unfold initW
  set y := max s 2 - 1 with hy
  have hy1 : 1 ≤ y := by have := le_max_right s 2; linarith
  have hy2 : y ≤ 2 := by have : max s 2 ≤ 3 := max_le hs (by norm_num); linarith
  have hlog0 : 0 ≤ log y := log_nonneg hy1
  have hlog1 : log y ≤ y - 1 := log_le_sub_one_of_pos (by linarith)
  have h1 : 1 / y ≤ 1 := by rw [div_le_one (by linarith)]; exact hy1
  have h2 : 1 / 2 ≤ 1 / y := one_div_le_one_div_of_le (by linarith) hy2
  constructor <;> linarith
theorem bigM_pos_of_le_three {s : ℝ} (hs : s ≤ 3) : 0 < bigM s := by
  rw [bigM_of_le_three hs]; linarith [(initW_mem hs).1]
theorem abs_bigW_le_of_le_three {s : ℝ} (hs : s ≤ 3) : |bigW s| ≤ bigM s / 3 := by
  rw [bigW_of_le_three hs, bigM_of_le_three hs, abs_le]
  obtain ⟨h1, h2⟩ := initW_mem hs
  constructor <;> linarith
theorem weight_mem {x : ℝ} (hx : 1 ≤ x) : 0 < 1 - 1 / (2 * x ^ 2) ∧ 1 - 1 / (2 * x ^ 2) ≤ 1 := by
  have : 1 / (2 * x ^ 2) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith
  have : 0 < 1 / (2 * x ^ 2) := by positivity
  constructor <;> linarith
theorem continuousOn_weight_mul {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun x => (1 - 1 / (2 * x ^ 2)) * g x) (Icc a b) := by
  refine ContinuousOn.mul ?_ hg.continuousOn
  refine continuousOn_const.sub (continuousOn_const.div (continuousOn_const.mul
    (continuousOn_id.pow 2)) fun x hx => ?_)
  have : 0 < x := lt_of_lt_of_le ha hx.1
  positivity
theorem bigM_pos (s : ℝ) : 0 < bigM s := by
  rcases le_total s 3 with hs | hs
  · exact bigM_pos_of_le_three hs
  refine pos_of_first_crossing (f := bigM) (a₀ := 3) (a := 3) continuous_bigM.continuousOn
    (fun x hx => (bigM_pos_of_le_three hx.2).le) (bigM_pos_of_le_three le_rfl) ?_ s hs
  intro t ht _ hpos
  have hpos' : ∀ x, x < t → 0 < bigM x := fun x hx => by
    rcases le_total x 3 with h | h
    · exact bigM_pos_of_le_three h
    · exact hpos x ⟨h, hx⟩
  have hI : 0 < ∫ x in (t - 1)..t, (1 - 1 / (2 * x ^ 2)) * bigM x := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ (fun x hx => ?_) (by linarith)
    · exact (continuousOn_weight_mul continuous_bigM (by linarith)).intervalIntegrable_of_Icc
        (by linarith)
    · exact mul_pos (weight_mem (by linarith [hx.1])).1 (hpos' x hx.2)
  rw [← bigM_integral_identity ht.le] at hI
  have hr : 0 < (t - 1) ^ 2 - 1 / 2 := by nlinarith
  have ht0 : 0 < t := by linarith
  by_contra h
  push Not at h
  have : ((t - 1) ^ 2 - 1 / 2) * bigM t / t ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hr.le h) ht0.le
  linarith
theorem antitone_of_antitoneOn_Iic_Ici {f : ℝ → ℝ} {a : ℝ} (h₁ : AntitoneOn f (Iic a))
    (h₂ : AntitoneOn f (Ici a)) : Antitone f := by
  intro s t hst
  rcases le_total t a with hta | hta
  · exact h₁ (hst.trans hta) hta hst
  rcases le_total a s with has | has
  · exact h₂ has hta hst
  exact (h₂ (le_refl a) hta hta).trans (h₁ has (le_refl a) has)
theorem antitoneOn_initW : AntitoneOn initW (Iic 3) := by
  intro s _ t _ hst
  unfold initW
  have h1 : 1 ≤ max s 2 - 1 := by have := le_max_right s 2; linarith
  have h2 : max s 2 ≤ max t 2 := max_le_max hst le_rfl
  have h3 : log (max s 2 - 1) ≤ log (max t 2 - 1) := log_le_log (by linarith) (by linarith)
  have h4 : 1 / (max t 2 - 1) ≤ 1 / (max s 2 - 1) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  linarith
theorem continuousOn_kernel_mul {g : ℝ → ℝ} (hg : Continuous g) :
    ContinuousOn (fun x => x / (x - 1) ^ 2 * g (x - 1)) (Ici 2) := by
  refine ContinuousOn.mul (continuousOn_id.div ((continuousOn_id.sub continuousOn_const).pow 2)
    fun x hx => ?_) (hg.comp (continuous_sub_right 1)).continuousOn
  have : (2 : ℝ) ≤ x := hx
  have : 0 < x - 1 := by linarith
  positivity
theorem intervalIntegrable_kernel_mul {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ} (ha : 2 ≤ a)
    (hb : 2 ≤ b) : IntervalIntegrable (fun x => x / (x - 1) ^ 2 * g (x - 1)) volume a b := by
  refine ((continuousOn_kernel_mul hg).mono fun x hx => ?_).intervalIntegrable
  rcases le_total a b with h | h
  · rw [uIcc_of_le h] at hx; exact ha.trans hx.1
  · rw [uIcc_of_ge h] at hx; exact hb.trans hx.1
theorem kernel_pos {x : ℝ} (hx : 1 < x) : 0 < x / (x - 1) ^ 2 := by
  have : 0 < x - 1 := by linarith
  positivity
theorem bigM_antitone : Antitone bigM := by
  refine antitone_of_antitoneOn_Iic_Ici (a := 3) ?_ ?_
  · intro s hs t ht hst
    rw [bigM_of_le_three hs, bigM_of_le_three ht]
    linarith [antitoneOn_initW hs ht hst]
  · intro s hs t ht hst
    have hs' : (3 : ℝ) ≤ s := hs
    have ht' : (3 : ℝ) ≤ t := ht
    rw [bigM_eq_integral hs', bigM_eq_integral ht',
      ← intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_kernel_mul continuous_bigM (by norm_num) (b := s) (by linarith))
        (intervalIntegrable_kernel_mul continuous_bigM (by linarith) (by linarith))]
    have : 0 ≤ ∫ x in s..t, x / (x - 1) ^ 2 * bigM (x - 1) :=
      intervalIntegral.integral_nonneg hst fun x hx =>
        (mul_pos (kernel_pos (by linarith [hx.1])) (bigM_pos _)).le
    linarith
theorem bigM_le_three (s : ℝ) : bigM s ≤ 3 := by
  rcases le_total s 2 with h | h
  · rw [bigM_of_le_two h]
  · exact (bigM_antitone h).trans_eq bigM_two
theorem bigM_le_ratio {s : ℝ} (hs : 3 ≤ s) :
    bigM s ≤ s / ((s - 1) ^ 2 - 1 / 2) * bigM (s - 1) := by
  have hr : 0 < (s - 1) ^ 2 - 1 / 2 := by nlinarith
  have hs0 : 0 < s := by linarith
  have h := bigM_integral_identity hs
  have hle : ∫ x in (s - 1)..s, (1 - 1 / (2 * x ^ 2)) * bigM x ≤
      ∫ _ in (s - 1)..s, bigM (s - 1) := by
    refine intervalIntegral.integral_mono_on (by linarith)
      ((continuousOn_weight_mul continuous_bigM (by linarith)).intervalIntegrable_of_Icc
        (by linarith)) intervalIntegrable_const fun x hx => ?_
    obtain ⟨h0, h1⟩ := weight_mem (x := x) (by linarith [hx.1])
    calc (1 - 1 / (2 * x ^ 2)) * bigM x ≤ 1 * bigM x :=
          mul_le_mul_of_nonneg_right h1 (bigM_pos x).le
      _ ≤ bigM (s - 1) := by rw [one_mul]; exact bigM_antitone hx.1
  rw [intervalIntegral.integral_const, ← h] at hle
  simp only [sub_sub_cancel, smul_eq_mul, one_mul] at hle
  rw [div_mul_eq_mul_div, le_div_iff₀ hr]
  rw [div_le_iff₀ hs0] at hle
  linarith
theorem bigM_le_exp (s : ℝ) : bigM s ≤ 3 * exp 5 * exp (-s) := by
  have base : ∀ s : ℝ, s ≤ 5 → bigM s ≤ 3 * exp 5 * exp (-s) := by
    intro s hs
    have : 1 ≤ exp 5 * exp (-s) := by
      rw [← exp_add]; exact one_le_exp (by linarith)
    nlinarith [bigM_le_three s]
  have key : ∀ n : ℕ, ∀ s : ℝ, s ≤ n → bigM s ≤ 3 * exp 5 * exp (-s) := by
    intro n
    induction n with
    | zero => intro s hs; exact base s (by simp at hs; linarith)
    | succ n ih =>
      intro s hs
      rcases le_total s 5 with h5 | h5
      · exact base s h5
      have h1 := bigM_le_ratio (s := s) (by linarith)
      have h2 := ih (s - 1) (by push_cast at hs; linarith)
      have hr : 0 < (s - 1) ^ 2 - 1 / 2 := by nlinarith
      have hc : s / ((s - 1) ^ 2 - 1 / 2) ≤ exp (-1) := by
        rw [div_le_iff₀ hr, exp_neg, ← div_eq_inv_mul, le_div_iff₀ (exp_pos 1)]
        nlinarith [exp_one_lt_d9]
      calc bigM s ≤ s / ((s - 1) ^ 2 - 1 / 2) * bigM (s - 1) := h1
        _ ≤ exp (-1) * (3 * exp 5 * exp (-(s - 1))) :=
          mul_le_mul hc h2 (bigM_pos _).le (exp_pos _).le
        _ = 3 * exp 5 * exp (-s) := by
          rw [show -s = -1 + -(s - 1) by ring, exp_add]; ring
  exact key ⌈s⌉₊ s (Nat.le_ceil s)
theorem tendsto_bigM_atTop : Tendsto bigM atTop (𝓝 0) := by
  have h : Tendsto (fun s => 3 * exp 5 * exp (-s)) atTop (𝓝 0) := by
    simpa using tendsto_exp_neg_atTop_nhds_zero.const_mul (3 * exp 5)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
    (fun s => (bigM_pos s).le) bigM_le_exp
theorem lemma6_aux {r x M : ℝ} (hr : r ≠ 0) (hx : x ≠ 0) :
    1 / (3 * r) * ((1 - 1 / (2 * x ^ 2)) * M) - M / 3 / x ^ 2 =
      M * (x ^ 2 - 1 / 2 - r) / (3 * r * x ^ 2) := by
  field_simp
theorem abs_bigW_lt {s : ℝ} (hs : 3 ≤ s) : |bigW s| < bigM s / 3 := by
  refine sub_pos.1 <| pos_of_first_crossing (f := fun s => bigM s / 3 - |bigW s|) (a₀ := 2)
    (a := 3) ((continuous_bigM.div_const 3).sub continuous_bigW.abs).continuousOn
    (fun x hx => sub_nonneg.2 (abs_bigW_le_of_le_three hx.2)) ?_ ?_ s hs
  · rw [bigM_three, bigW_three, abs_of_neg (by linarith [log_two_gt_d9])]
    linarith [log_two_lt_d9]
  intro t ht hall _
  have ht0 : 0 < t := by linarith
  have hr : 0 < (t - 1) ^ 2 - 1 / 2 := by nlinarith
  have hx0 : ∀ x ∈ Icc (t - 1) t, x ^ 2 ≠ 0 := fun x hx =>
    pow_ne_zero 2 (by linarith [hx.1])
  have hcW : ContinuousOn (fun x => |bigW x / x ^ 2|) (Icc (t - 1) t) :=
    (continuous_bigW.continuousOn.div (continuousOn_id.pow 2) hx0).abs
  have hcM : ContinuousOn (fun x => bigM x / 3 / x ^ 2) (Icc (t - 1) t) :=
    (continuous_bigM.div_const 3).continuousOn.div (continuousOn_id.pow 2) hx0
  have hcM' : ContinuousOn (fun x => 1 / (3 * ((t - 1) ^ 2 - 1 / 2)) *
      ((1 - 1 / (2 * x ^ 2)) * bigM x)) (Icc (t - 1) t) :=
    continuousOn_const.mul (continuousOn_weight_mul continuous_bigM (by linarith))
  have h1 : |bigW t| ≤ t * ∫ x in (t - 1)..t, |bigW x / x ^ 2| := by
    rw [bigW_eq_neg_mul_integral ht.le, abs_mul, abs_neg, abs_of_pos ht0]
    exact mul_le_mul_of_nonneg_left (intervalIntegral.abs_integral_le_integral_abs
      (by linarith)) ht0.le
  have h2 : ∫ x in (t - 1)..t, |bigW x / x ^ 2| ≤ ∫ x in (t - 1)..t, bigM x / 3 / x ^ 2 := by
    refine intervalIntegral.integral_mono_on (by linarith) (hcW.intervalIntegrable_of_Icc
      (by linarith)) (hcM.intervalIntegrable_of_Icc (by linarith)) fun x hx => ?_
    have hx2 : 0 < x ^ 2 := pow_pos (by linarith [hx.1]) 2
    rw [abs_div, abs_of_pos hx2]
    have := hall x ⟨by linarith [hx.1], hx.2⟩
    exact div_le_div_of_nonneg_right (by linarith) hx2.le
  have hpt : ∀ x, t - 1 < x → 0 < 1 / (3 * ((t - 1) ^ 2 - 1 / 2)) *
      ((1 - 1 / (2 * x ^ 2)) * bigM x) - bigM x / 3 / x ^ 2 := by
    intro x hx
    have hx' : 0 < x := by linarith
    rw [lemma6_aux hr.ne' hx'.ne']
    have : 0 < x ^ 2 - 1 / 2 - ((t - 1) ^ 2 - 1 / 2) := by nlinarith
    have := bigM_pos x
    positivity
  have h3 : ∫ x in (t - 1)..t, bigM x / 3 / x ^ 2 < ∫ x in (t - 1)..t,
      1 / (3 * ((t - 1) ^ 2 - 1 / 2)) * ((1 - 1 / (2 * x ^ 2)) * bigM x) := by
    refine intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (by linarith) hcM hcM' (fun x hx => (sub_pos.1 (hpt x hx.1)).le)
      ⟨t, ⟨by linarith, le_rfl⟩, sub_pos.1 (hpt t (by linarith))⟩
  rw [intervalIntegral.integral_const_mul, ← bigM_integral_identity ht.le] at h3
  have h4 : t * (1 / (3 * ((t - 1) ^ 2 - 1 / 2)) * (((t - 1) ^ 2 - 1 / 2) * bigM t / t)) =
      bigM t / 3 := by
    generalize (t - 1) ^ 2 - 1 / 2 = r at hr ⊢
    field_simp
  have := mul_lt_mul_of_pos_left h3 ht0
  rw [h4] at this
  have := mul_le_mul_of_nonneg_left h2 ht0.le
  linarith
theorem abs_bigW_le (s : ℝ) : |bigW s| ≤ bigM s / 3 := by
  rcases le_total s 3 with hs | hs
  · exact abs_bigW_le_of_le_three hs
  · exact (abs_bigW_lt hs).le
end IwaniecLinearSieve
end
section
open Real Set Filter Topology MeasureTheory
namespace IwaniecLinearSieve
noncomputable def majf (s : ℝ) : ℝ := (bigM s + bigW s) / 2
noncomputable def majF (s : ℝ) : ℝ := (bigM s - bigW s) / 2
noncomputable def majG (r : ℕ) (s : ℝ) : ℝ := if Even r then majf s else majF s
theorem majG_of_even {r : ℕ} (hr : Even r) : majG r = majf := by
  ext s; simp [majG, hr]
theorem majG_of_odd {r : ℕ} (hr : Odd r) : majG r = majF := by
  ext s; simp [majG, Nat.not_even_iff_odd.2 hr]
theorem continuous_majf : Continuous majf :=
  (continuous_bigM.add continuous_bigW).div_const 2
theorem continuous_majF : Continuous majF :=
  (continuous_bigM.sub continuous_bigW).div_const 2
theorem continuous_majG (r : ℕ) : Continuous (majG r) := by
  rcases Nat.even_or_odd r with hr | hr
  · rw [majG_of_even hr]; exact continuous_majf
  · rw [majG_of_odd hr]; exact continuous_majF
theorem majF_of_le_three {s : ℝ} (hs : s ≤ 3) : majF s = 1 := by
  simp only [majF, bigM_of_le_three hs, bigW_of_le_three hs]; ring
theorem majf_eq {s : ℝ} (hs : 2 ≤ s) (hs' : s ≤ 3) :
    majf s = 1 + 1 / (s - 1) - log (s - 1) := by
  simp only [majf, bigM_eq hs hs', bigW_eq hs hs']; ring
theorem majf_of_le_two {s : ℝ} (hs : s ≤ 2) : majf s = 2 := by
  simp only [majf, bigM_of_le_two hs, bigW_of_le_two hs]; norm_num
theorem majf_mem (s : ℝ) : bigM s / 3 ≤ majf s ∧ majf s ≤ 2 * bigM s / 3 := by
  have := abs_le.1 (abs_bigW_le s)
  unfold majf; constructor <;> linarith [this.1, this.2]
theorem majF_mem (s : ℝ) : bigM s / 3 ≤ majF s ∧ majF s ≤ 2 * bigM s / 3 := by
  have := abs_le.1 (abs_bigW_le s)
  unfold majF; constructor <;> linarith [this.1, this.2]
theorem majG_mem (r : ℕ) (s : ℝ) : bigM s / 3 ≤ majG r s ∧ majG r s ≤ 2 * bigM s / 3 := by
  unfold majG; split_ifs
  · exact majf_mem s
  · exact majF_mem s
theorem majG_pos (r : ℕ) (s : ℝ) : 0 < majG r s :=
  lt_of_lt_of_le (by linarith [bigM_pos s]) (majG_mem r s).1
theorem majf_pos (s : ℝ) : 0 < majf s := by
  simpa [majG_of_even (⟨0, rfl⟩ : Even 0)] using majG_pos 0 s
theorem majF_pos (s : ℝ) : 0 < majF s := by
  simpa [majG_of_odd odd_one] using majG_pos 1 s
theorem hasDerivAt_majF {s : ℝ} (hs : 3 < s) :
    HasDerivAt majF (-(s / (s - 1) ^ 2 * majf (s - 1))) s := by
  refine ((hasDerivAt_bigM hs).sub (hasDerivAt_bigW hs)).div_const 2 |>.congr_deriv ?_
  simp only [majf]; ring
theorem hasDerivWithinAt_majf_Ici {s : ℝ} (hs : 3 ≤ s) :
    HasDerivWithinAt majf (-(s / (s - 1) ^ 2 * majF (s - 1))) (Ici s) s := by
  refine ((hasDerivWithinAt_bigM_Ici hs).add (hasDerivWithinAt_bigW_Ici hs)).div_const 2
    |>.congr_deriv ?_
  simp only [majF]; ring
theorem hasDerivAt_majf {s : ℝ} (hs : 2 < s) :
    HasDerivAt majf (-(s / (s - 1) ^ 2 * majF (s - 1))) s := by
  have hexp : ∀ x, 2 < x → x ≤ 4 → HasDerivAt (fun x => 1 + (1 / (x - 1) - log (x - 1)))
      (-(x / (x - 1) ^ 2 * majF (x - 1))) x := by
    intro x hx hx4
    rw [majF_of_le_three (by linarith), mul_one]
    exact (hasDerivAt_initForm (by linarith)).const_add 1
  have heq : ∀ x, 2 ≤ x → x ≤ 3 → majf x = 1 + (1 / (x - 1) - log (x - 1)) := by
    intro x hx hx3; rw [majf_eq hx hx3]; ring
  rcases lt_trichotomy s 3 with h3 | rfl | h3
  · refine (hexp s hs (by linarith)).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hs h3] with x hx
    exact heq x hx.1.le hx.2.le
  · have hl : HasDerivWithinAt majf (-(3 / (3 - 1) ^ 2 * majF (3 - 1))) (Iic 3) 3 := by
      refine (hexp 3 (by norm_num) (by norm_num)).hasDerivWithinAt.congr_of_eventuallyEq ?_
        (heq 3 (by norm_num) le_rfl)
      filter_upwards [inter_mem_nhdsWithin (Iic 3) (Ioi_mem_nhds (show (2 : ℝ) < 3 by norm_num)),
        self_mem_nhdsWithin] with x hx _
      exact heq x hx.2.out.le hx.1
    have := hl.union (hasDerivWithinAt_majf_Ici le_rfl)
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
  · refine ((hasDerivAt_bigM h3).add (hasDerivAt_bigW h3)).div_const 2 |>.congr_deriv ?_
    simp only [majF]; ring
theorem hasDerivAt_majG_succ (r : ℕ) {t : ℝ} (ht : (5 + (-1) ^ r) / 2 < t) :
    HasDerivAt (majG (r + 1)) (-(majG r (t - 1) * t / (t - 1) ^ 2)) t := by
  rcases Nat.even_or_odd r with hr | hr
  · rw [majG_of_odd hr.add_one, majG_of_even hr]
    rw [hr.neg_one_pow] at ht
    exact (hasDerivAt_majF (by linarith)).congr_deriv (by ring)
  · rw [majG_of_even hr.add_one, majG_of_odd hr]
    rw [hr.neg_one_pow] at ht
    exact (hasDerivAt_majf (by linarith)).congr_deriv (by ring)
theorem majF_antitone : Antitone majF := by
  refine antitone_of_antitoneOn_Iic_Ici (a := 3) ?_ ?_
  · intro s hs t ht _
    rw [majF_of_le_three hs, majF_of_le_three ht]
  · refine antitoneOn_of_deriv_nonpos (convex_Ici 3) continuous_majF.continuousOn
      (fun x hx => ?_) (fun x hx => ?_) <;> rw [interior_Ici] at hx
    · exact (hasDerivAt_majF hx).differentiableAt.differentiableWithinAt
    · rw [(hasDerivAt_majF hx).deriv]
      have := mul_pos (kernel_pos (by linarith [hx.out] : (1 : ℝ) < x)) (majf_pos (x - 1))
      linarith
theorem majf_antitone : Antitone majf := by
  refine antitone_of_antitoneOn_Iic_Ici (a := 2) ?_ ?_
  · intro s hs t ht _
    rw [majf_of_le_two hs, majf_of_le_two ht]
  · refine antitoneOn_of_deriv_nonpos (convex_Ici 2) continuous_majf.continuousOn
      (fun x hx => ?_) (fun x hx => ?_) <;> rw [interior_Ici] at hx
    · exact (hasDerivAt_majf hx).differentiableAt.differentiableWithinAt
    · rw [(hasDerivAt_majf hx).deriv]
      have := mul_pos (kernel_pos (by linarith [hx.out] : (1 : ℝ) < x)) (majF_pos (x - 1))
      linarith
theorem tendsto_majG_atTop (r : ℕ) : Tendsto (majG r) atTop (𝓝 0) := by
  have h : Tendsto (fun s => 2 * bigM s / 3) atTop (𝓝 0) := by
    simpa using (tendsto_bigM_atTop.const_mul 2).div_const 3
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
    (fun s => (majG_pos r s).le) fun s => (majG_mem r s).2
theorem tendsto_majf_atTop : Tendsto majf atTop (𝓝 0) := by
  simpa [majG_of_even (⟨0, rfl⟩ : Even 0)] using tendsto_majG_atTop 0
theorem tendsto_majF_atTop : Tendsto majF atTop (𝓝 0) := by
  simpa [majG_of_odd odd_one] using tendsto_majG_atTop 1
end IwaniecLinearSieve
end
section
open Real Set Filter Topology MeasureTheory
namespace IwaniecLinearSieve
theorem bigM_sub_half_le {s : ℝ} (hs : 3 ≤ s) :
    bigM (s - 1 / 2) ≤ 2 * (s - 1) ^ 2 / s * bigM s := by
  have hs0 : 0 < s := by linarith
  have hy : 0 < (s - 1) ^ 2 := by nlinarith
  have hs1 : s - 1 ≠ 0 := by linarith
  have hwc := continuousOn_weight_mul continuous_bigM (a := s - 1) (b := s) (by linarith)
  have hI : ∀ a b, s - 1 ≤ a → a ≤ b → b ≤ s →
      IntervalIntegrable (fun x => (1 - 1 / (2 * x ^ 2)) * bigM x) volume a b :=
    fun a b ha hab hb => (hwc.mono (Icc_subset_Icc ha hb)).intervalIntegrable_of_Icc hab
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hI (s - 1) (s - 1 / 2) le_rfl (by linarith) (by linarith))
    (hI (s - 1 / 2) s (by linarith) (by linarith) le_rfl)
  have h2 : 0 ≤ ∫ x in (s - 1 / 2)..s, (1 - 1 / (2 * x ^ 2)) * bigM x :=
    intervalIntegral.integral_nonneg (by linarith) fun x hx =>
      (mul_pos (weight_mem (by linarith [hx.1])).1 (bigM_pos x)).le
  have h1 : ∫ _ in (s - 1)..(s - 1 / 2), (1 - 1 / (2 * (s - 1) ^ 2)) * bigM (s - 1 / 2) ≤
      ∫ x in (s - 1)..(s - 1 / 2), (1 - 1 / (2 * x ^ 2)) * bigM x := by
    refine intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
      (hI _ _ le_rfl (by linarith) (by linarith)) fun x hx => ?_
    have hw : 1 - 1 / (2 * (s - 1) ^ 2) ≤ 1 - 1 / (2 * x ^ 2) := by
      have : 1 / (2 * x ^ 2) ≤ 1 / (2 * (s - 1) ^ 2) :=
        one_div_le_one_div_of_le (by positivity) (by nlinarith [hx.1])
      linarith
    exact mul_le_mul hw (bigM_antitone hx.2) (bigM_pos _).le
      (weight_mem (by linarith [hx.1])).1.le
  rw [intervalIntegral.integral_const, smul_eq_mul] at h1
  have key := bigM_integral_identity hs
  rw [← hsplit] at key
  have : (s - 1 / 2 - (s - 1)) * ((1 - 1 / (2 * (s - 1) ^ 2)) * bigM (s - 1 / 2)) ≤
      ((s - 1) ^ 2 - 1 / 2) * bigM s / s := by linarith
  have e1 : (s - 1 / 2 - (s - 1)) * ((1 - 1 / (2 * (s - 1) ^ 2)) * bigM (s - 1 / 2)) =
      ((s - 1) ^ 2 - 1 / 2) * bigM (s - 1 / 2) / (2 * (s - 1) ^ 2) := by
    field_simp; ring
  rw [e1, div_le_div_iff₀ (by positivity) hs0] at this
  have hr : 0 < (s - 1) ^ 2 - 1 / 2 := by nlinarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hs0]
  nlinarith
theorem bigM_sub_one_lt {s : ℝ} (hs : 3 ≤ s) : bigM (s - 1) < 4 * s ^ 2 * bigM s := by
  have hs0 : 0 < s := by linarith
  have hB := bigM_sub_half_le hs
  have hMs := bigM_pos s
  rcases le_total s (7 / 2) with h | h
  · have h1 : bigM (s - 1) ≤ 3 := bigM_le_three _
    have h2 : bigM 3 ≤ bigM (s - 1 / 2) := bigM_antitone (by linarith)
    rw [bigM_three] at h2
    have h3 : 2 * (s - 1) ^ 2 / s ≤ s ^ 2 := by
      rw [div_le_iff₀ hs0]; nlinarith
    have := mul_le_mul_of_nonneg_right h3 hMs.le
    nlinarith [log_two_lt_d9]
  · have hA := bigM_sub_half_le (s := s - 1 / 2) (by linarith)
    rw [show s - 1 / 2 - 1 / 2 = s - 1 by ring] at hA
    have h3 : 2 * (s - 1 / 2 - 1) ^ 2 / (s - 1 / 2) < 2 * s := by
      rw [div_lt_iff₀ (by linarith)]; nlinarith
    have h4 : 2 * (s - 1) ^ 2 / s < 2 * s := by
      rw [div_lt_iff₀ hs0]; nlinarith
    have h5 : 0 < 2 * (s - 1) ^ 2 / s := div_pos (by nlinarith) hs0
    calc bigM (s - 1) ≤ 2 * (s - 1 / 2 - 1) ^ 2 / (s - 1 / 2) * bigM (s - 1 / 2) := hA
      _ ≤ 2 * (s - 1 / 2 - 1) ^ 2 / (s - 1 / 2) * (2 * (s - 1) ^ 2 / s * bigM s) :=
        mul_le_mul_of_nonneg_left hB (div_nonneg (by positivity) (by linarith))
      _ < 2 * s * (2 * s * bigM s) := by
        apply mul_lt_mul' h3.le (mul_lt_mul_of_pos_right h4 hMs) (by positivity) (by linarith)
      _ = 4 * s ^ 2 * bigM s := by ring
theorem integral_exp_neg_mul_unit (a : ℝ) {l : ℝ} (hl : l ≠ 0) :
    ∫ x in a..(a + 1), exp (-(l * (x - a))) = (1 - exp (-l)) / l := by
  have hderiv : ∀ x ∈ uIcc a (a + 1), HasDerivAt (fun x => -exp (-(l * (x - a))) / l)
      (exp (-(l * (x - a)))) x := by
    intro x _
    have h := ((((hasDerivAt_id' x).sub_const a).const_mul l).neg).exp.neg.div_const l
    refine h.congr_deriv ?_
    simp only [Pi.neg_apply]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous fun x => exp (-(l * (x - a)))).intervalIntegrable _ _)]
  simp only [add_sub_cancel_left, mul_one, sub_self, mul_zero, neg_zero, exp_zero]
  ring
theorem log_four_lt : log 4 < 1.3863 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
  have := log_two_lt_d9
  push_cast
  linarith
theorem log_mul_ratio_lt {t q L : ℝ} (ht0 : 0 < t) (hq1 : 1 < q)
    (hq2 : q ^ 2 = t - 1) (hL : 1 < L) (hLt : log t ≤ L + 1 / (t - 1)) :
    log t * (t / ((t - 1) ^ 2 - 1 / 2) * ((1 - q⁻¹) / (L / 2))) <
      2 * (t / (t - 1) ^ 2) := by
  have hq0 : 0 < q := by linarith only [hq1]
  have hq4 : 0 < q ^ 4 - 1 / 2 := by
    linarith only [one_lt_pow₀ hq1 (by decide : 4 ≠ 0)]
  have hL0 : 0 < L := by linarith only [hL]
  have hD : 0 < L * q * (q ^ 4 - 1 / 2) := by positivity
  have hy : (t - 1) ^ 2 = q ^ 4 := by rw [← hq2]; ring
  have e1 : log t * (t / ((t - 1) ^ 2 - 1 / 2) * ((1 - q⁻¹) / (L / 2))) =
      t * (2 * (log t * (q - 1)) / (L * q * (q ^ 4 - 1 / 2))) := by
    rw [hy]
    field_simp
  have e2 : 2 * (t / (t - 1) ^ 2) = t * (2 / q ^ 4) := by
    rw [hy]; ring
  rw [e1, e2]
  refine mul_lt_mul_of_pos_left ?_ ht0
  rw [div_lt_div_iff₀ hD (by positivity)]
  have hLt' : log t ≤ L + 1 / q ^ 2 := by rwa [hq2]
  have h1 := mul_le_mul_of_nonneg_right hLt'
    (show 0 ≤ (q - 1) * q ^ 4 by have : 0 ≤ q - 1 := by linarith
                                 positivity)
  have h2 : (L + 1 / q ^ 2) * ((q - 1) * q ^ 4) = L * (q - 1) * q ^ 4 + (q - 1) * q ^ 2 := by
    field_simp
  have h3 : L * (q - 1) * q ^ 4 + (q - 1) * q ^ 2 < L * q * (q ^ 4 - 1 / 2) := by
    have hA : 0 < q ^ 4 - q / 2 := by
      have hcube := mul_lt_mul_of_pos_right (one_lt_pow₀ hq1 (by decide : 3 ≠ 0)) hq0
      nlinarith only [hcube, hq0]
    have hB' : 0 < q ^ 2 * q * (q - 1) + q * (q - 1 / 2) := by
      have : 0 < q - 1 := by linarith
      have : 0 < q - 1 / 2 := by linarith
      positivity
    nlinarith [mul_lt_mul_of_pos_right hL hA]
  nlinarith
theorem log_mul_bigM_lt {t : ℝ} (ht : 2 ≤ t) :
    log t * bigM t < 2 * (t / (t - 1) ^ 2) * bigM (t - 1) := by
  refine sub_pos.1 <| pos_of_first_crossing
    (f := fun t => 2 * (t / (t - 1) ^ 2) * bigM (t - 1) - log t * bigM t) (a₀ := 2) (a := 2)
    ?_ ?_ ?_ ?_ t ht
  · refine ContinuousOn.sub (ContinuousOn.mul (continuousOn_const.mul
      (continuousOn_id.div ((continuousOn_id.sub continuousOn_const).pow 2) fun x hx => ?_))
      (continuous_bigM.comp (continuous_sub_right 1)).continuousOn)
      ((continuousOn_log.mono fun x hx => ?_).mul continuous_bigM.continuousOn)
    · have : 0 < x - 1 := by linarith [hx.out]
      positivity
    · simp only [mem_compl_iff, mem_singleton_iff]; linarith [hx.out]
  · intro x hx
    obtain rfl : x = 2 := le_antisymm hx.2 hx.1
    rw [show (2 : ℝ) - 1 = 1 by norm_num, bigM_of_le_two (by norm_num), bigM_two]
    linarith [log_two_lt_d9]
  · rw [show (2 : ℝ) - 1 = 1 by norm_num, bigM_of_le_two (by norm_num), bigM_two]
    linarith [log_two_lt_d9]
  intro t ht _ hpos
  show 0 < 2 * (t / (t - 1) ^ 2) * bigM (t - 1) - log t * bigM t
  rw [sub_pos]
  have ht0 : 0 < t := by linarith
  have hB := bigM_pos (t - 1)
  have hlog0 : 0 ≤ log t := log_nonneg (by linarith)
  rcases le_total t 3 with h3 | h3
  ·
    rw [bigM_of_le_two (show t - 1 ≤ 2 by linarith)]
    have hl : log t < 1.3863 := (log_le_log ht0 (by linarith)).trans_lt log_four_lt
    have hk : 3 / 4 ≤ t / (t - 1) ^ 2 := by
      rw [le_div_iff₀ (by have : 0 < t - 1 := by linarith
                          positivity)]
      nlinarith
    have := bigM_le_three t
    nlinarith
  rcases le_total t 4 with h4 | h4
  ·
    have hl : log t < 1.3863 := (log_le_log ht0 h4).trans_lt log_four_lt
    have hR := bigM_le_ratio h3
    have hy : 4 ≤ (t - 1) ^ 2 := by nlinarith
    have hr : 0 < (t - 1) ^ 2 - 1 / 2 := by linarith
    have key : log t * (t / ((t - 1) ^ 2 - 1 / 2)) < 2 * (t / (t - 1) ^ 2) := by
      rw [mul_div_assoc', mul_div_assoc', div_lt_div_iff₀ hr (by linarith)]
      have : 1 < (2 - log t) * (t - 1) ^ 2 := by nlinarith
      nlinarith [mul_lt_mul_of_pos_left this ht0]
    calc log t * bigM t ≤ log t * (t / ((t - 1) ^ 2 - 1 / 2) * bigM (t - 1)) :=
          mul_le_mul_of_nonneg_left hR hlog0
      _ = log t * (t / ((t - 1) ^ 2 - 1 / 2)) * bigM (t - 1) := by ring
      _ < 2 * (t / (t - 1) ^ 2) * bigM (t - 1) := mul_lt_mul_of_pos_right key hB
  set L₁ := log (t - 1) with hL₁
  set l := L₁ / 2 with hl
  have hL₁1 : 1 < L₁ := by
    rw [hL₁, lt_log_iff_exp_lt (by linarith)]
    linarith [exp_one_lt_d9]
  have hl0 : 0 < l := by linarith
  have hanti : AntitoneOn (fun x => bigM x * exp (l * x)) (Icc (t - 1) t) := by
    have hd : ∀ x, 3 < x → HasDerivAt (fun x => bigM x * exp (l * x))
        (-(x / (x - 1) ^ 2 * bigM (x - 1)) * exp (l * x) + bigM x * (exp (l * x) * l)) x :=
      fun x hx => (hasDerivAt_bigM hx).mul (((hasDerivAt_id x).const_mul l).exp.congr_deriv
        (by simp))
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (continuous_bigM.mul (continuous_const.mul continuous_id).rexp).continuousOn
      (fun x hx => ?_) (fun x hx => ?_) <;> rw [interior_Icc] at hx
    · exact (hd x (by linarith [hx.1])).differentiableAt.differentiableWithinAt
    · rw [(hd x (by linarith [hx.1])).deriv]
      have hfx := hpos x ⟨by linarith [hx.1], hx.2⟩
      have hlx : L₁ ≤ log x := log_le_log (by linarith) hx.1.le
      have hMx := bigM_pos x
      have : l * bigM x < x / (x - 1) ^ 2 * bigM (x - 1) := by nlinarith
      have he := exp_pos (l * x)
      nlinarith
  have hbound : ∀ x ∈ Icc (t - 1) t,
      (1 - 1 / (2 * x ^ 2)) * bigM x ≤ bigM (t - 1) * exp (-(l * (x - (t - 1)))) := by
    intro x hx
    have h := hanti ⟨le_rfl, by linarith⟩ hx hx.1
    simp only at h
    have hw := weight_mem (x := x) (by linarith [hx.1])
    have hMx := bigM_pos x
    have e : bigM (t - 1) * exp (-(l * (x - (t - 1)))) =
        bigM (t - 1) * exp (l * (t - 1)) / exp (l * x) := by
      rw [div_eq_mul_inv, ← exp_neg, mul_assoc, ← exp_add]; ring_nf
    rw [e, le_div_iff₀ (exp_pos _)]
    calc (1 - 1 / (2 * x ^ 2)) * bigM x * exp (l * x) ≤ 1 * bigM x * exp (l * x) := by
          gcongr; exact hw.2
      _ ≤ _ := by rw [one_mul]; exact h
  have hint : ((t - 1) ^ 2 - 1 / 2) * bigM t / t ≤ bigM (t - 1) * ((1 - exp (-l)) / l) := by
    rw [bigM_integral_identity h3, ← integral_exp_neg_mul_unit (t - 1) hl0.ne',
      sub_add_cancel, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (by linarith)
      ((continuousOn_weight_mul continuous_bigM (by linarith)).intervalIntegrable_of_Icc
        (by linarith)) ((by fun_prop : Continuous fun x =>
          bigM (t - 1) * exp (-(l * (x - (t - 1))))).intervalIntegrable _ _) hbound
  set q := exp l with hq
  have hq2 : q ^ 2 = t - 1 := by
    rw [hq, sq, ← exp_add, show l + l = L₁ by rw [hl]; ring, hL₁, exp_log (by linarith)]
  have hq1 : 1 < q := one_lt_exp_iff.2 hl0
  have hel : exp (-l) = q⁻¹ := by rw [exp_neg]
  have hLt : log t ≤ L₁ + 1 / (t - 1) := by
    have := log_le_sub_one_of_pos (div_pos ht0 (by linarith : (0 : ℝ) < t - 1))
    rw [log_div (by linarith) (by linarith)] at this
    have : t - 1 ≠ 0 := by linarith
    have e : t / (t - 1) - 1 = 1 / (t - 1) := by field_simp; ring
    linarith
  rw [hel] at hint
  have hr : 0 < (t - 1) ^ 2 - 1 / 2 := by nlinarith
  have hMt : bigM t ≤ t / ((t - 1) ^ 2 - 1 / 2) * (bigM (t - 1) * ((1 - q⁻¹) / l)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hr]
    rw [div_le_iff₀ ht0] at hint
    linarith
  have key := log_mul_ratio_lt ht0 hq1 hq2 hL₁1 hLt
  calc log t * bigM t ≤ log t * (t / ((t - 1) ^ 2 - 1 / 2) * (bigM (t - 1) * ((1 - q⁻¹) / l))) :=
        mul_le_mul_of_nonneg_left hMt hlog0
    _ = log t * (t / ((t - 1) ^ 2 - 1 / 2) * ((1 - q⁻¹) / l)) * bigM (t - 1) := by ring
    _ < 2 * (t / (t - 1) ^ 2) * bigM (t - 1) := mul_lt_mul_of_pos_right key hB
theorem majG_succ_mul_log_div_lt (r : ℕ) {t : ℝ} (ht : 2 ≤ t) :
    majG (r + 1) t * (t - 1) ^ 2 * log t / (majG r (t - 1) * t) < 4 := by
  have h := log_mul_bigM_lt ht
  have ht0 : 0 < t := by linarith
  have hy : 0 < (t - 1) ^ 2 := by nlinarith
  have hlog : 0 ≤ log t := log_nonneg (by linarith)
  have hG := majG_mem (r + 1) t
  have hG' := majG_mem r (t - 1)
  have hGpos := majG_pos r (t - 1)
  rw [div_lt_iff₀ (mul_pos hGpos ht0)]
  have h1 : majG (r + 1) t * (t - 1) ^ 2 * log t ≤ 2 * bigM t / 3 * (t - 1) ^ 2 * log t :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hG.2 hy.le) hlog
  have h2 : log t * bigM t * (t - 1) ^ 2 < 2 * t * bigM (t - 1) := by
    have ht1 : t - 1 ≠ 0 := by linarith
    have := mul_lt_mul_of_pos_right h hy
    rwa [show 2 * (t / (t - 1) ^ 2) * bigM (t - 1) * (t - 1) ^ 2 = 2 * t * bigM (t - 1) by
      field_simp] at this
  nlinarith
noncomputable def lemma9Fun (s : ℝ) : ℝ := exp (-(s * log s + s * log (log s) + 2 * s))
theorem continuousOn_lemma9Fun : ContinuousOn lemma9Fun (Ici 3) := by
  unfold lemma9Fun
  have hlog : ContinuousOn log (Ici 3) := continuousOn_log.mono fun x hx => by
    simp only [mem_compl_iff, mem_singleton_iff]; linarith [hx.out]
  have hloglog : ContinuousOn (fun x => log (log x)) (Ici 3) :=
    ContinuousOn.log hlog fun x hx => (log_pos (by linarith [hx.out])).ne'
  exact ((((continuousOn_id.mul hlog).add (continuousOn_id.mul hloglog)).add
    (continuousOn_const.mul continuousOn_id)).neg).rexp
theorem one_le_log_of_three_le {x : ℝ} (hx : 3 ≤ x) : 1 ≤ log x := by
  rw [le_log_iff_exp_le (by linarith)]
  linarith [exp_one_lt_d9]
theorem lemma9Fun_le_one {x : ℝ} (hx : 3 ≤ x) : lemma9Fun x ≤ 1 := by
  unfold lemma9Fun
  rw [exp_le_one_iff, neg_nonpos]
  have h1 := log_nonneg (one_le_log_of_three_le hx)
  have h2 := log_nonneg (show 1 ≤ x by linarith)
  have : 0 ≤ x := by linarith
  positivity
theorem lemma9_phi_sub {s x : ℝ} (hs : 4 ≤ s) (hx : s - 1 ≤ x) (hxs : x ≤ s) :
    (log (s - 1) + log (log (s - 1)) + 3) * (s - x) ≤
      (s * log s + s * log (log s) + 2 * s) - (x * log x + x * log (log x) + 2 * x) := by
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < s := by linarith
  have h1 : (s - x) * (1 + log x) ≤ s * log s - x * log x := by
    have := log_le_sub_one_of_pos (div_pos hx0 hs0)
    rw [log_div hx0.ne' hs0.ne'] at this
    have e : s * (x / s - 1) = x - s := by field_simp
    nlinarith
  have h2 : log (s - 1) ≤ log x := log_le_log (by linarith) hx
  have hl1 : 1 ≤ log (s - 1) := one_le_log_of_three_le (by linarith)
  have h3 : log (log (s - 1)) ≤ log (log x) := log_le_log (by linarith) h2
  have h4 : log (log x) ≤ log (log s) := log_le_log (by linarith) (log_le_log hx0 hxs)
  have h5 : 0 ≤ log (log (s - 1)) := log_nonneg hl1
  have hsx : 0 ≤ s - x := by linarith
  nlinarith [mul_le_mul_of_nonneg_left h2 hsx, mul_le_mul_of_nonneg_left h3 hsx,
    mul_le_mul_of_nonneg_left h4 hs0.le]
theorem lemma9Fun_weighted_exp_le {s x : ℝ} (hs : 4 ≤ s) (hx : s - 1 ≤ x) (hxs : x ≤ s) :
    let l := log (s - 1) + log (log (s - 1)) + 3
    (1 - 1 / (2 * (s - 1) ^ 2)) * (lemma9Fun s * exp l) *
      exp (-(l * (x - (s - 1)))) ≤ (1 - 1 / (2 * x ^ 2)) * lemma9Fun x := by
  dsimp only
  set l := log (s - 1) + log (log (s - 1)) + 3
  have hweight : 1 - 1 / (2 * (s - 1) ^ 2) ≤ 1 - 1 / (2 * x ^ 2) := by
    have hrecip : 1 / (2 * x ^ 2) ≤ 1 / (2 * (s - 1) ^ 2) :=
      one_div_le_one_div_of_le (by nlinarith only [hs]) (by nlinarith only [hs, hx])
    linarith only [hrecip]
  have hexp : lemma9Fun s * exp l * exp (-(l * (x - (s - 1)))) ≤ lemma9Fun x := by
    unfold lemma9Fun
    rw [← exp_add, ← exp_add, exp_le_exp]
    have hconvex := lemma9_phi_sub hs hx hxs
    dsimp only [l]
    linarith only [hconvex]
  rw [mul_assoc]
  exact mul_le_mul hweight hexp (by unfold lemma9Fun; positivity)
    (weight_mem (by linarith only [hs, hx])).1.le
theorem lemma9_integral_factor_ge_one {s : ℝ} (hs : 4 ≤ s) :
    let l := log (s - 1) + log (log (s - 1)) + 3
    1 ≤ (1 - 1 / (2 * (s - 1) ^ 2)) * (exp l * ((1 - exp (-l)) / l)) *
      (s / ((s - 1) ^ 2 - 1 / 2)) := by
  dsimp only
  set L := log (s - 1) with hL
  set l := L + log L + 3 with hl
  set w₀ := 1 - 1 / (2 * (s - 1) ^ 2) with hw₀
  have hL1 : 1 ≤ L := one_le_log_of_three_le (by linarith)
  have hlogL : log L ≤ L - 1 := log_le_sub_one_of_pos (by linarith)
  have hlogL0 : 0 ≤ log L := log_nonneg hL1
  have hl0 : 0 < l := by linarith only [hL1, hlogL0, hl]
  have hr : 0 < (s - 1) ^ 2 - 1 / 2 := by nlinarith only [hs]
  have hel : exp l = (s - 1) * L * exp 3 := by
    rw [hl, exp_add, exp_add, hL, exp_log (by linarith), exp_log (by linarith)]
  have he3 : 20 ≤ exp 3 := by
    have : exp 3 = exp 1 ^ 3 := by rw [← exp_nat_mul]; norm_num
    rw [this]
    have h := pow_le_pow_left₀ (by norm_num) exp_one_gt_d9.le 3
    norm_num at h
    linarith
  have hexp_gain : l * (s - 1) ^ 2 ≤ s * (exp l - 1) := by
    rw [hel]
    have hy : 3 ≤ s - 1 := by linarith
    have h0 : 0 ≤ (s - 1) * L := by positivity
    have : 20 * ((s - 1) * L) ≤ (s - 1) * L * exp 3 := by
      nlinarith [mul_le_mul_of_nonneg_left he3 h0]
    nlinarith [mul_le_mul_of_nonneg_left hL1 (by nlinarith : (0 : ℝ) ≤ (s - 1) ^ 2)]
  have hexp_cancel : exp l * (1 - exp (-l)) = exp l - 1 := by
    rw [mul_sub, mul_one, ← exp_add]; simp
  have hweight_cancel : w₀ / ((s - 1) ^ 2 - 1 / 2) = 1 / (s - 1) ^ 2 := by
    have : s - 1 ≠ 0 := by linarith
    rw [hw₀, div_eq_div_iff hr.ne' (by positivity)]
    field_simp
  have hfactor : w₀ * (exp l * ((1 - exp (-l)) / l)) * (s / ((s - 1) ^ 2 - 1 / 2)) =
      s * (exp l - 1) / (l * (s - 1) ^ 2) := by
    rw [← hexp_cancel]
    calc w₀ * (exp l * ((1 - exp (-l)) / l)) * (s / ((s - 1) ^ 2 - 1 / 2))
        = w₀ / ((s - 1) ^ 2 - 1 / 2) * (s * (exp l * (1 - exp (-l))) / l) := by ring
      _ = _ := by rw [hweight_cancel]; field_simp
  rw [hfactor, le_div_iff₀ (mul_pos hl0 (by nlinarith)), one_mul]
  exact hexp_gain
theorem lemma9Fun_le_integral {s : ℝ} (hs : 4 ≤ s) :
    lemma9Fun s ≤ s / ((s - 1) ^ 2 - 1 / 2) *
      ∫ x in (s - 1)..s, (1 - 1 / (2 * x ^ 2)) * lemma9Fun x := by
  set l := log (s - 1) + log (log (s - 1)) + 3
  set w₀ := 1 - 1 / (2 * (s - 1) ^ 2)
  have hL1 : 1 ≤ log (s - 1) := one_le_log_of_three_le (by linarith only [hs])
  have hl0 : 0 < l := by
    dsimp only [l]
    linarith only [hL1, log_nonneg hL1]
  have hr : 0 < (s - 1) ^ 2 - 1 / 2 := by nlinarith only [hs]
  have hint : w₀ * (lemma9Fun s * exp l) * ((1 - exp (-l)) / l) ≤
      ∫ x in (s - 1)..s, (1 - 1 / (2 * x ^ 2)) * lemma9Fun x := by
    have hexp := integral_exp_neg_mul_unit (s - 1) hl0.ne'
    rw [sub_add_cancel] at hexp
    rw [← hexp, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (by linarith only)
      ((by fun_prop : Continuous fun x =>
        w₀ * (lemma9Fun s * exp l) * exp (-(l * (x - (s - 1))))).intervalIntegrable _ _)
      ?_ (fun x hx => lemma9Fun_weighted_exp_le hs hx.1 hx.2)
    refine ContinuousOn.intervalIntegrable_of_Icc (by linarith only) ?_
    refine ContinuousOn.mul (continuousOn_const.sub (continuousOn_const.div
      (continuousOn_const.mul (continuousOn_id.pow 2)) fun x hx => ?_))
      (continuousOn_lemma9Fun.mono fun x hx => by
        simp only [mem_Ici]; linarith only [hs, hx.1])
    have : 0 < x := by linarith only [hs, hx.1]
    positivity
  have hF : 0 < lemma9Fun s := exp_pos _
  calc
    lemma9Fun s ≤ lemma9Fun s * (w₀ * (exp l * ((1 - exp (-l)) / l)) *
        (s / ((s - 1) ^ 2 - 1 / 2))) :=
      le_mul_of_one_le_right hF.le (lemma9_integral_factor_ge_one hs)
    _ = s / ((s - 1) ^ 2 - 1 / 2) *
        (w₀ * (lemma9Fun s * exp l) * ((1 - exp (-l)) / l)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hint (div_nonneg (by linarith only [hs]) hr.le)
theorem bigM_gt_lemma9Fun {s : ℝ} (hs : 3 ≤ s) : bigM 4 / 2 * lemma9Fun s < bigM s := by
  set κ := bigM 4 / 2 with hκ
  have hM4 := bigM_pos 4
  have hinit : ∀ x ∈ Icc (3 : ℝ) 4, 0 < bigM x - κ * lemma9Fun x := by
    intro x hx
    have h1 := lemma9Fun_le_one hx.1
    have h2 : bigM 4 ≤ bigM x := bigM_antitone hx.2
    have h3 : κ * lemma9Fun x ≤ κ := by
      have : 0 ≤ κ := by positivity
      nlinarith
    linarith
  rcases le_total s 4 with h4 | h4
  · exact sub_pos.1 (hinit s ⟨hs, h4⟩)
  refine sub_pos.1 <| pos_of_first_crossing (f := fun s => bigM s - κ * lemma9Fun s) (a₀ := 3)
    (a := 4) (continuous_bigM.continuousOn.sub (continuousOn_const.mul
      (continuousOn_lemma9Fun.mono fun x hx => by simp only [mem_Ici] at hx ⊢; linarith)))
    (fun x hx => (hinit x hx).le) (hinit 4 ⟨by norm_num, le_rfl⟩) ?_ s h4
  intro t ht hall hpos
  show 0 < bigM t - κ * lemma9Fun t
  have hpos' : ∀ x ∈ Ioo (t - 1) t, 0 < bigM x - κ * lemma9Fun x := by
    intro x hx
    rcases le_total x 4 with h | h
    · exact hinit x ⟨by linarith [hx.1], h⟩
    · exact hpos x ⟨h, hx.2⟩
  have ht0 : 0 < t := by linarith
  have hr : 0 < (t - 1) ^ 2 - 1 / 2 := by nlinarith
  have hcw : ContinuousOn (fun x => (1 - 1 / (2 * x ^ 2)) * (κ * lemma9Fun x)) (Icc (t - 1) t) := by
    refine ContinuousOn.mul (continuousOn_const.sub (continuousOn_const.div
      (continuousOn_const.mul (continuousOn_id.pow 2)) fun x hx => ?_))
      (continuousOn_const.mul (continuousOn_lemma9Fun.mono fun x hx => by
        simp only [mem_Ici]; linarith [hx.1]))
    have : 0 < x := by linarith [hx.1]
    positivity
  have hlt : ∫ x in (t - 1)..t, (1 - 1 / (2 * x ^ 2)) * (κ * lemma9Fun x) <
      ∫ x in (t - 1)..t, (1 - 1 / (2 * x ^ 2)) * bigM x := by
    refine intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (by linarith) hcw (continuousOn_weight_mul continuous_bigM (by linarith)) ?_ ?_
    · intro x hx
      have hw := (weight_mem (x := x) (by linarith [hx.1])).1
      rcases hx.2.lt_or_eq with h | rfl
      · exact mul_le_mul_of_nonneg_left (sub_pos.1 (hpos' x ⟨hx.1, h⟩)).le hw.le
      · exact mul_le_mul_of_nonneg_left (sub_nonneg.1 (hall x ⟨by linarith, le_rfl⟩)) hw.le
    · refine ⟨t - 1 / 2, ⟨by linarith, by linarith⟩, ?_⟩
      exact mul_lt_mul_of_pos_left (sub_pos.1 (hpos' _ ⟨by linarith, by linarith⟩))
        (weight_mem (by linarith)).1
  rw [← bigM_integral_identity (by linarith), intervalIntegral.integral_congr
    (g := fun x => κ * ((1 - 1 / (2 * x ^ 2)) * lemma9Fun x)) (fun x _ => by simp only; ring),
    intervalIntegral.integral_const_mul] at hlt
  have hsub := lemma9Fun_le_integral ht.le
  have hκ0 : 0 < κ := by positivity
  have h1 : κ * lemma9Fun t ≤
      t / ((t - 1) ^ 2 - 1 / 2) * (κ * ∫ x in (t - 1)..t, (1 - 1 / (2 * x ^ 2)) * lemma9Fun x) := by
    calc κ * lemma9Fun t ≤ κ * (t / ((t - 1) ^ 2 - 1 / 2) *
          ∫ x in (t - 1)..t, (1 - 1 / (2 * x ^ 2)) * lemma9Fun x) :=
          mul_le_mul_of_nonneg_left hsub hκ0.le
      _ = _ := by ring
  have h2 := mul_lt_mul_of_pos_left hlt (div_pos ht0 hr)
  have e : t / ((t - 1) ^ 2 - 1 / 2) * (((t - 1) ^ 2 - 1 / 2) * bigM t / t) = bigM t := by
    generalize (t - 1) ^ 2 - 1 / 2 = r at hr ⊢
    field_simp
  rw [e] at h2
  linarith
theorem bigM_ge_exp : ∃ κ > 0, ∀ s ≥ 3,
    κ * exp (-(s * log s + s * log (log s) + 2 * s)) ≤ bigM s :=
  ⟨bigM 4 / 2, by linarith [bigM_pos 4], fun _ hs => (bigM_gt_lemma9Fun hs).le⟩
theorem majG_ge_exp : ∃ c : ℝ, ∀ (r : ℕ) (s : ℝ), 3 ≤ s →
    exp (-(s * log s) - s * log (log s) - c * s) ≤ majG r s := by
  obtain ⟨κ, hκ, hM⟩ := bigM_ge_exp
  set K := |log (κ / 3)| / 3 with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨2 + K, fun r s hs => ?_⟩
  have hG := (majG_mem r s).1
  have h1 := hM s hs
  have hexp : exp (-(K * s)) ≤ κ / 3 := by
    calc exp (-(K * s)) ≤ exp (log (κ / 3)) := by
          rw [exp_le_exp]
          have : -log (κ / 3) ≤ |log (κ / 3)| := neg_le_abs _
          nlinarith
      _ = κ / 3 := exp_log (by positivity)
  have e : exp (-(s * log s) - s * log (log s) - (2 + K) * s) =
      exp (-(K * s)) * exp (-(s * log s + s * log (log s) + 2 * s)) := by
    rw [← exp_add]; ring_nf
  rw [e]
  calc exp (-(K * s)) * exp (-(s * log s + s * log (log s) + 2 * s))
      ≤ κ / 3 * exp (-(s * log s + s * log (log s) + 2 * s)) :=
        mul_le_mul_of_nonneg_right hexp (exp_pos _).le
    _ ≤ bigM s / 3 := by linarith
    _ ≤ majG r s := hG
end IwaniecLinearSieve
end
section
open Real
namespace IwaniecLinearSieve
noncomputable def xi (y : ℝ) : ℝ := log y / log (log (3 * y)) ^ (11 / 5 : ℝ)
noncomputable def delta (s y : ℝ) : ℝ := (1 + s ^ 2 * log s ^ 5 / log y ^ 2) ^ (5 * s)
noncomputable def mainMaj : Bool → ℝ → ℝ
  | true, s => fSieve s
  | false, s => FSieve s + max (3 - s) 0
noncomputable def errMaj : Bool → ℝ → ℝ
  | true => majf
  | false => majF
def sMin : Bool → ℝ
  | true => 2
  | false => 1
end IwaniecLinearSieve
end
section
open Real Set Filter Topology MeasureTheory
namespace IwaniecLinearSieve
@[simp] theorem mainMaj_true (s : ℝ) : mainMaj true s = fSieve s := rfl
@[simp] theorem mainMaj_false (s : ℝ) : mainMaj false s = FSieve s + max (3 - s) 0 := rfl
theorem mainMaj_nonneg : ∀ (lower : Bool) (s : ℝ), 0 ≤ mainMaj lower s
  | true, s => fSieve_nonneg s
  | false, s => add_nonneg (FSieve_nonneg s) (le_max_right _ _)
theorem mainMaj_antitone : ∀ lower, Antitone (mainMaj lower)
  | true => fSieve_antitone
  | false => fun u v h => by
    simp only [mainMaj_false]
    exact add_le_add (FSieve_antitone h) (max_le_max (by linarith) le_rfl)
theorem mainMaj_le_MSieve : ∀ (lower : Bool) (s : ℝ), mainMaj lower s ≤ MSieve s
  | true, s => by
    have := FSieve_nonneg s; have := le_max_right (3 - s) 0
    simp only [mainMaj_true, MSieve]; linarith
  | false, s => by
    have := fSieve_nonneg s
    simp only [mainMaj_false, MSieve]; linarith
theorem g_two_eq_integral {s : ℝ} (hs : 2 ≤ s) :
    IntegrableOn (fun t => max (3 - (t - 1)) 0 / (t - 1)) (Ioi s) ∧
      g 2 s = ∫ t in Ioi s, max (3 - (t - 1)) 0 / (t - 1) := by
  have hz : ∀ t : ℝ, 4 ≤ t → max (3 - (t - 1)) 0 / (t - 1) = 0 := fun t ht => by
    rw [max_eq_right (by linarith), zero_div]
  rcases le_or_gt s 4 with hs4 | hs4
  · have heq : EqOn (fun t : ℝ => max (3 - (t - 1)) 0 / (t - 1)) (fun t => 3 / (t - 1) - 1)
        (Icc s 4) := fun t ht => by
      have : 0 < t - 1 := by linarith [ht.1]
      simp only
      rw [max_eq_left (by linarith [ht.2])]
      field_simp
    have hcont : ContinuousOn (fun t : ℝ => 3 / (t - 1) - 1) (Icc s 4) :=
      (continuousOn_const.div (continuousOn_id.sub continuousOn_const) fun t ht => by
        simp only [Pi.sub_apply, id]; linarith [ht.1]).sub continuousOn_const
    obtain ⟨hI, hE⟩ := integral_Ioi_eq_of_eq_zero hs4
      (((hcont.congr heq).integrableOn_Icc).mono_set Ioc_subset_Icc_self) hz
    refine ⟨hI, ?_⟩
    rw [hE, intervalIntegral.integral_congr (heq.mono (uIcc_of_le hs4).subset)]
    have hderiv : ∀ t ∈ uIcc s 4, HasDerivAt (fun t => 3 * log (t - 1) - t) (3 / (t - 1) - 1) t :=
      fun t ht => by
        rw [uIcc_of_le hs4] at ht
        have h1 : t - 1 ≠ 0 := by linarith [ht.1]
        have := ((((hasDerivAt_id' t).sub_const 1).log h1).const_mul 3).sub (hasDerivAt_id' t)
        convert this using 1 <;> (try with_reducible_and_instances rfl) <;> (try (funext tt; simp only [Pi.neg_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.inv_apply, Pi.smul_apply, Pi.pow_apply, Function.comp_apply, id_eq]; done)); field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (hcont.mono (uIcc_of_le hs4).subset |>.intervalIntegrable), g_two_eq ⟨hs, hs4⟩,
      log_div (by norm_num) (by linarith)]
    norm_num; ring
  · obtain ⟨hI, hE⟩ := integral_Ioi_eq_of_eq_zero le_rfl (by simp) fun t ht => hz t (by linarith)
    exact ⟨hI, by rw [hE, intervalIntegral.integral_same, g_two_of_four_le hs4.le]⟩
theorem integrableOn_mainMaj_false_shift {s : ℝ} (hs : 2 ≤ s) :
    IntegrableOn (fun t => mainMaj false (t - 1) / (t - 1)) (Ioi s) := by
  simp only [mainMaj_false, add_div]
  exact (integrableOn_FSieve_shift hs).add (g_two_eq_integral hs).1
theorem fSieve_eq_integral_mainMaj {s : ℝ} (hs : 2 ≤ s) :
    fSieve s = ∫ t in Ioi s, mainMaj false (t - 1) / (t - 1) := by
  simp only [mainMaj_false, add_div]
  rw [integral_add (integrableOn_FSieve_shift hs) (g_two_eq_integral hs).1,
    ← (g_two_eq_integral hs).2, fSieve_eq_integral hs]
theorem mainMaj_false_eq_integral (s : ℝ) :
    mainMaj false s = max (3 - s) 0 + ∫ t in Ioi (max s 3), fSieve (t - 1) / (t - 1) := by
  have hF : FSieve s = FSieve (max s 3) := by
    rcases le_total s 3 with h | h
    · rw [max_eq_right h, FSieve_of_le_three h]
    · rw [max_eq_left h]
  rw [mainMaj_false, hF, FSieve_eq_integral (le_max_right _ _), add_comm]
@[simp] theorem errMaj_true : errMaj true = majf := rfl
@[simp] theorem errMaj_false : errMaj false = majF := rfl
def errLower : Bool → ℝ
  | true => 2
  | false => 3
@[simp] theorem errLower_true : errLower true = 2 := rfl
@[simp] theorem errLower_false : errLower false = 3 := rfl
theorem two_le_errLower (lower : Bool) : 2 ≤ errLower lower := by
  cases lower <;> norm_num [errLower]
theorem majG_add_two (r : ℕ) : majG (r + 2) = majG r := by
  rcases Nat.even_or_odd r with hr | hr
  · rw [majG_of_even hr, majG_of_even (hr.add (by decide))]
  · rw [majG_of_odd hr, majG_of_odd (hr.add_even (by decide))]
theorem continuous_errMaj : ∀ lower, Continuous (errMaj lower)
  | true => continuous_majf
  | false => continuous_majF
theorem errMaj_pos : ∀ (lower : Bool) (s : ℝ), 0 < errMaj lower s
  | true, s => majf_pos s
  | false, s => majF_pos s
theorem errMaj_antitone : ∀ lower, Antitone (errMaj lower)
  | true => majf_antitone
  | false => majF_antitone
theorem errMaj_mem : ∀ (lower : Bool) (s : ℝ),
    bigM s / 3 ≤ errMaj lower s ∧ errMaj lower s ≤ 2 * bigM s / 3
  | true, s => majf_mem s
  | false, s => majF_mem s
theorem errMaj_le_two (lower : Bool) (s : ℝ) : errMaj lower s ≤ 2 := by
  linarith [(errMaj_mem lower s).2, bigM_le_three s]
theorem errMaj_false_of_le_three {s : ℝ} (hs : s ≤ 3) : errMaj false s = 1 :=
  majF_of_le_three hs
theorem hasDerivAt_errMaj : ∀ (lower : Bool) {t : ℝ}, errLower lower < t →
    HasDerivAt (errMaj lower) (-(errMaj (!lower) (t - 1) * t / (t - 1) ^ 2)) t
  | true, _, ht => (hasDerivAt_majf ht).congr_deriv (by simp; ring)
  | false, _, ht => (hasDerivAt_majF ht).congr_deriv (by simp; ring)
theorem tendsto_errMaj_atTop : ∀ lower, Tendsto (errMaj lower) atTop (𝓝 0)
  | true => tendsto_majf_atTop
  | false => tendsto_majF_atTop
theorem errMaj_shift_pos (lower : Bool) {t : ℝ} (ht : 1 < t) :
    0 < errMaj lower (t - 1) * t / (t - 1) ^ 2 := by
  have h1 : 0 < t - 1 := by linarith
  have := errMaj_pos lower (t - 1)
  have : 0 < t := by linarith
  positivity
theorem errMaj_eq_integral (lower : Bool) {s : ℝ} (hs : errLower lower ≤ s) :
    IntegrableOn (fun t => errMaj (!lower) (t - 1) * t / (t - 1) ^ 2) (Ioi s) ∧
      errMaj lower s = ∫ t in Ioi s, errMaj (!lower) (t - 1) * t / (t - 1) ^ 2 := by
  have h2 := two_le_errLower lower
  have hcont : ContinuousWithinAt (fun t => -errMaj lower t) (Ici s) s :=
    (continuous_errMaj lower).neg.continuousWithinAt
  have hderiv : ∀ t ∈ Ioi s, HasDerivAt (fun t => -errMaj lower t)
      (errMaj (!lower) (t - 1) * t / (t - 1) ^ 2) t := fun t ht =>
    (hasDerivAt_errMaj lower (hs.trans_lt ht)).neg.congr_deriv (by ring)
  have hpos : ∀ t ∈ Ioi s, 0 ≤ errMaj (!lower) (t - 1) * t / (t - 1) ^ 2 := fun t ht =>
    (errMaj_shift_pos _ (by linarith [ht.out])).le
  have hlim : Tendsto (fun t => -errMaj lower t) atTop (𝓝 0) := by
    simpa using (tendsto_errMaj_atTop lower).neg
  refine ⟨integrableOn_Ioi_deriv_of_nonneg hcont hderiv hpos hlim, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hpos hlim]; ring
theorem integral_errMaj_shift (lower : Bool) {s b : ℝ} (hs : errLower lower ≤ s) (hsb : s ≤ b) :
    ∫ t in s..b, errMaj (!lower) (t - 1) * t / (t - 1) ^ 2 = errMaj lower s - errMaj lower b := by
  obtain ⟨hI, hE⟩ := errMaj_eq_integral lower hs
  rw [hE, (errMaj_eq_integral lower (hs.trans hsb)).2, intervalIntegral.integral_Ioi_sub_Ioi hI hsb]
end IwaniecLinearSieve
end
section
open Real Set Filter Topology MeasureTheory
namespace IwaniecLinearSieve
theorem FSieve_three_add_lt_four : FSieve 3 + 3 < 4 := by
  have h := fSieve_four_add
  have h4 := fSieve_pos 4
  have hl := one_lt_log_three
  have hK : 0 < FSieve 3 + 3 := by linarith [FSieve_nonneg 3]
  nlinarith
theorem MSieve_eq_on_Icc {s : ℝ} (hs : s ∈ Icc (2 : ℝ) 3) :
    MSieve s = (FSieve 3 + 3) * (1 - log (s - 1)) := by
  rw [MSieve_of_le_three hs.2, fSieve_eq_on_Icc ⟨hs.1, by linarith [hs.2]⟩]; ring
theorem MSieve_lt_four_mul_bigM_of_le_three {s : ℝ} (hs : s ∈ Icc (2 : ℝ) 3) :
    MSieve s < 4 * bigM s := by
  rw [MSieve_eq_on_Icc hs, bigM_eq hs.1 hs.2]
  have h1 : 0 < s - 1 := by linarith [hs.1]
  have hl0 : 0 ≤ log (s - 1) := log_nonneg (by linarith [hs.1])
  have hl1 : log (s - 1) < 1 := by
    rw [log_lt_iff_lt_exp h1]; linarith [hs.2, exp_one_gt_d9]
  have hK := FSieve_three_add_lt_four
  have hinv : 0 < 1 / (s - 1) := by positivity
  nlinarith
theorem sub_one_mul_MSieve {s : ℝ} (hs : 3 ≤ s) :
    (s - 1) * MSieve s = ∫ x in (s - 1)..s, MSieve x := by
  have h := lemma5Q_const hs
  rw [lemma5Q_three, lemma5Q] at h
  linarith
theorem integral_bigM_le {s : ℝ} (hs : 3 ≤ s) :
    ∫ x in (s - 1)..s, bigM x ≤ (s - 1) ^ 2 * bigM s / s := by
  have hs0 : 0 < s := by linarith
  have hc : 0 < 1 - 1 / (2 * (s - 1) ^ 2) := by
    have : 1 / (2 * (s - 1) ^ 2) < 1 := by
      rw [div_lt_one (by nlinarith)]; nlinarith
    linarith
  have hle : ∫ x in (s - 1)..s, (1 - 1 / (2 * (s - 1) ^ 2)) * bigM x ≤
      ∫ x in (s - 1)..s, (1 - 1 / (2 * x ^ 2)) * bigM x := by
    refine intervalIntegral.integral_mono_on (by linarith)
      (continuous_bigM.intervalIntegrable _ _ |>.const_mul _)
      ((continuousOn_weight_mul continuous_bigM (by linarith)).intervalIntegrable_of_Icc
        (by linarith)) fun x hx => ?_
    have hx1 : 0 < s - 1 := by linarith
    have : 1 / (2 * x ^ 2) ≤ 1 / (2 * (s - 1) ^ 2) := by
      apply one_div_le_one_div_of_le (by positivity)
      have := hx.1; nlinarith
    exact mul_le_mul_of_nonneg_right (by linarith) (bigM_pos x).le
  rw [intervalIntegral.integral_const_mul, ← bigM_integral_identity hs] at hle
  have hkey : (1 - 1 / (2 * (s - 1) ^ 2)) * ((s - 1) ^ 2 * bigM s / s) =
      ((s - 1) ^ 2 - 1 / 2) * bigM s / s := by
    have h0 : s - 1 ≠ 0 := by linarith
    have : (1 - 1 / (2 * (s - 1) ^ 2)) * (s - 1) ^ 2 = (s - 1) ^ 2 - 1 / 2 := by
      field_simp
    calc _ = ((1 - 1 / (2 * (s - 1) ^ 2)) * (s - 1) ^ 2) * bigM s / s := by ring
      _ = _ := by rw [this]
  rw [← hkey] at hle
  exact le_of_mul_le_mul_left hle hc
theorem MSieve_lt_four_mul_bigM {s : ℝ} (hs : 2 ≤ s) : MSieve s < 4 * bigM s := by
  rcases le_total s 3 with h3 | h3
  · exact MSieve_lt_four_mul_bigM_of_le_three ⟨hs, h3⟩
  refine sub_pos.1 <| pos_of_first_crossing (f := fun s => 4 * bigM s - MSieve s) (a₀ := 2)
    (a := 3) ((continuous_bigM.const_smul (4 : ℝ)).sub continuous_MSieve).continuousOn
    (fun x hx => (sub_pos.2 (MSieve_lt_four_mul_bigM_of_le_three hx)).le)
    (sub_pos.2 (MSieve_lt_four_mul_bigM_of_le_three ⟨by norm_num, le_rfl⟩)) ?_ s h3
  intro s hs3 hnn _
  have hs0 : 0 < s := by linarith
  have hint : ∫ x in (s - 1)..s, MSieve x ≤ ∫ x in (s - 1)..s, 4 * bigM x :=
    intervalIntegral.integral_mono_on (by linarith) (continuous_MSieve.intervalIntegrable _ _)
      ((continuous_bigM.intervalIntegrable _ _).const_mul _) fun x hx => by
        linarith [hnn x ⟨by linarith [hx.1], hx.2⟩]
  rw [intervalIntegral.integral_const_mul, ← sub_one_mul_MSieve hs3.le] at hint
  have hB := integral_bigM_le hs3.le
  have hMs := bigM_pos s
  have h1 : (s - 1) * MSieve s ≤ 4 * ((s - 1) ^ 2 * bigM s / s) := by nlinarith
  have h2 : 4 * ((s - 1) ^ 2 * bigM s / s) < (s - 1) * (4 * bigM s) := by
    rw [div_eq_mul_inv]
    have : (s - 1) * s⁻¹ < 1 := by rw [← div_eq_mul_inv, div_lt_one hs0]; linarith
    have hs1 : 0 < s - 1 := by linarith
    nlinarith [mul_pos hs1 hMs]
  have := lt_of_le_of_lt h1 h2
  have hs1 : 0 < s - 1 := by linarith
  nlinarith
theorem MSieve_sub_one_lt {s : ℝ} (hs : 3 ≤ s) : MSieve (s - 1) < 16 * s ^ 2 * bigM s := by
  have h1 := MSieve_lt_four_mul_bigM (s := s - 1) (by linarith)
  have h2 := bigM_sub_one_lt hs
  linarith
theorem bigM_three_gt : 3 / 2 < bigM 3 := by
  rw [bigM_three]; linarith [log_two_lt_d9]
theorem mainMaj_sub_one_le (lower lower' : Bool) {s : ℝ} (hs : 1 ≤ s) :
    mainMaj lower (s - 1) ≤ 48 * s ^ 2 * errMaj lower' s := by
  have hG := (errMaj_mem lower' s).1
  have hM := mainMaj_le_MSieve lower (s - 1)
  rcases le_total 3 s with h3 | h3
  · have := MSieve_sub_one_lt h3
    nlinarith
  · have h0 : MSieve (s - 1) ≤ MSieve 0 := MSieve_antitone (by linarith)
    rw [MSieve_of_le_three (s := 0) (by norm_num), fSieve_of_le_two (by norm_num),
      fSieve_two] at h0
    have hK := FSieve_three_add_lt_four
    have hB : bigM 3 ≤ bigM s := bigM_antitone h3
    have := bigM_three_gt
    have hs2 : 1 ≤ s ^ 2 := by nlinarith
    have : 24 ≤ 48 * s ^ 2 * errMaj lower' s := by nlinarith
    linarith
end IwaniecLinearSieve
end
section
open Real Set Filter Topology MeasureTheory
namespace IwaniecLinearSieve
theorem hasDerivAt_lsx (L : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => t ^ 2 * log t ^ 5 / L ^ 2)
      ((2 * t * log t ^ 5 + 5 * t * log t ^ 4) / L ^ 2) t := by
  have h := ((hasDerivAt_pow 2 t).mul ((hasDerivAt_log ht.ne').pow 5)).div_const (L ^ 2)
  simp only [Pi.pow_apply, Pi.mul_apply] at h
  convert h using 1 <;> (try with_reducible_and_instances rfl) <;> (try (funext tt; simp only [Pi.neg_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.inv_apply, Pi.smul_apply, Pi.pow_apply, Function.comp_apply, id_eq]; done))
  field_simp
  ring
theorem lsx_nonneg (L : ℝ) {t : ℝ} (ht : 1 ≤ t) : 0 ≤ t ^ 2 * log t ^ 5 / L ^ 2 := by
  have := log_nonneg ht
  positivity
theorem hasDerivAt_growth (L a : ℝ) {t : ℝ} (ht : 1 ≤ t) :
    HasDerivAt (fun t => (1 + t ^ 2 * log t ^ 5 / L ^ 2) ^ (5 * (t - a)))
      ((1 + t ^ 2 * log t ^ 5 / L ^ 2) ^ (5 * (t - a)) *
        (5 * log (1 + t ^ 2 * log t ^ 5 / L ^ 2) + 5 * (t - a) *
          ((2 * t * log t ^ 5 + 5 * t * log t ^ 4) / L ^ 2) /
            (1 + t ^ 2 * log t ^ 5 / L ^ 2))) t := by
  set x := t ^ 2 * log t ^ 5 / L ^ 2
  have hx : 0 < 1 + x := by linarith [lsx_nonneg L ht]
  have h := ((hasDerivAt_lsx L (by linarith)).const_add 1).rpow
    (((hasDerivAt_id' t).sub_const a).const_mul 5) hx
  convert h using 1 <;> (try with_reducible_and_instances rfl) <;> (try (funext tt; simp only [Pi.neg_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.inv_apply, Pi.smul_apply, Pi.pow_apply, Function.comp_apply, id_eq]; done))
  rw [rpow_sub_one hx.ne']
  field_simp
  ring
theorem rate_bound_of_small_weight {u W E : ℝ} (hu : 32 ≤ u) (hW0 : 0 ≤ W)
    (hW : W ≤ 1 / 160) (hE : 4 * E ≤ W * (60 * u + 100)) :
    4 * E ≤ u - 1 ∧ 4 * E * (1 + 5 * (W * u)) ≤ 5 * (W * u) * u := by
  have hu0 : 0 ≤ u := by linarith only [hu]
  have hWu : 0 ≤ W * u := mul_nonneg hW0 hu0
  constructor
  · have h := mul_le_mul_of_nonneg_right hW (by linarith only [hu] : 0 ≤ 60 * u + 100)
    linarith only [hE, h, hu]
  · calc 4 * E * (1 + 5 * (W * u)) ≤ W * (60 * u + 100) * (1 + 5 * (W * u)) :=
          mul_le_mul_of_nonneg_right hE (by linarith only [hWu])
      _ ≤ 5 * (W * u) * u := by
          have h := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hW hu0) hW0
          nlinarith only [h, hWu, hu, hW0]
theorem rate_bound {L a t : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (ht1 : 1 ≤ t) (ht : 32 ≤ log t)
    (hw : t ^ 2 * log t ^ 4 / L ^ 2 ≤ 1 / 160) :
    0 ≤ 5 * log (1 + t ^ 2 * log t ^ 5 / L ^ 2) + 5 * (t - a) *
        ((2 * t * log t ^ 5 + 5 * t * log t ^ 4) / L ^ 2) / (1 + t ^ 2 * log t ^ 5 / L ^ 2) ∧
    4 * (5 * log (1 + t ^ 2 * log t ^ 5 / L ^ 2) + 5 * (t - a) *
        ((2 * t * log t ^ 5 + 5 * t * log t ^ 4) / L ^ 2) / (1 + t ^ 2 * log t ^ 5 / L ^ 2))
      ≤ log t - 1 ∧
    4 * (5 * log (1 + t ^ 2 * log t ^ 5 / L ^ 2) + 5 * (t - a) *
        ((2 * t * log t ^ 5 + 5 * t * log t ^ 4) / L ^ 2) / (1 + t ^ 2 * log t ^ 5 / L ^ 2)) *
        (1 + 5 * (t ^ 2 * log t ^ 5 / L ^ 2)) ≤ 5 * (t ^ 2 * log t ^ 5 / L ^ 2) * log t := by
  set u := log t
  set W := t ^ 2 * u ^ 4 / L ^ 2 with hW
  have hW0 : 0 ≤ W := by positivity
  have hx : t ^ 2 * u ^ 5 / L ^ 2 = W * u := by rw [hW]; ring
  have hx' : t * ((2 * t * u ^ 5 + 5 * t * u ^ 4) / L ^ 2) = W * (2 * u + 5) := by rw [hW]; ring
  have hd0 : 0 ≤ (2 * t * u ^ 5 + 5 * t * u ^ 4) / L ^ 2 := by positivity
  rw [hx]
  set E := 5 * log (1 + W * u) + 5 * (t - a) * ((2 * t * u ^ 5 + 5 * t * u ^ 4) / L ^ 2) /
    (1 + W * u) with hE
  have hWu : 0 ≤ W * u := mul_nonneg hW0 (by linarith only [ht])
  have h1 : 0 ≤ log (1 + W * u) := log_nonneg (by linarith only [hWu])
  have h2 : log (1 + W * u) ≤ W * u := by
    have := log_le_sub_one_of_pos (by linarith only [hWu] : 0 < 1 + W * u)
    linarith only [this]
  have h3 : 0 ≤ (t - a) * ((2 * t * u ^ 5 + 5 * t * u ^ 4) / L ^ 2) / (1 + W * u) :=
    div_nonneg (mul_nonneg (by linarith only [ht1, ha1]) hd0) (by linarith only [hWu])
  have h4 : (t - a) * ((2 * t * u ^ 5 + 5 * t * u ^ 4) / L ^ 2) / (1 + W * u) ≤
      W * (2 * u + 5) := by
    calc (t - a) * ((2 * t * u ^ 5 + 5 * t * u ^ 4) / L ^ 2) / (1 + W * u)
        ≤ (t - a) * ((2 * t * u ^ 5 + 5 * t * u ^ 4) / L ^ 2) :=
          div_le_self (mul_nonneg (by linarith only [ht1, ha1]) hd0)
            (by linarith only [hWu])
      _ ≤ t * ((2 * t * u ^ 5 + 5 * t * u ^ 4) / L ^ 2) :=
          mul_le_mul_of_nonneg_right (by linarith only [ha]) hd0
      _ = W * (2 * u + 5) := hx'
  have hE0 : 0 ≤ E := by rw [hE, mul_assoc 5, mul_div_assoc]; positivity
  have hE1 : 4 * E ≤ W * (60 * u + 100) := by
    rw [hE, mul_assoc 5 (t - a), mul_div_assoc]
    linarith only [h2, h4]
  exact ⟨hE0, rate_bound_of_small_weight ht hW0 hw hE1⟩
theorem majG_succ_mul_log_lt (r : ℕ) {t : ℝ} (ht : 2 ≤ t) :
    majG (r + 1) t * log t < 4 * (majG r (t - 1) * t / (t - 1) ^ 2) := by
  have h := majG_succ_mul_log_div_lt r ht
  have hK : 0 < majG r (t - 1) * t := mul_pos (majG_pos r _) (by linarith)
  have h1 : 0 < (t - 1) ^ 2 := by nlinarith
  rw [div_lt_iff₀ hK] at h
  rw [mul_div_assoc', lt_div_iff₀ h1]
  linarith
theorem five_add_neg_one_pow_div_le (r : ℕ) : (5 + (-1 : ℝ) ^ r) / 2 ≤ 3 := by
  rcases Nat.even_or_odd r with hr | hr
  · rw [hr.neg_one_pow]; norm_num
  · rw [hr.neg_one_pow]; norm_num
theorem range_facts {L t b : ℝ} (ht : exp 32 ≤ t) (htb : t ≤ b)
    (hb : b ^ 2 * log b ^ 4 ≤ L ^ 2 / 160) :
    1 ≤ t ∧ 32 ≤ log t ∧ t ^ 2 * log t ^ 4 / L ^ 2 ≤ 1 / 160 ∧ 0 < L ^ 2 := by
  have ht1 : 1 ≤ t := le_trans (by linarith [add_one_le_exp (32 : ℝ)]) ht
  have hlt : 32 ≤ log t := (le_log_iff_exp_le (by linarith)).2 ht
  have hlb : log t ≤ log b := log_le_log (by linarith) htb
  have h4 : t ^ 2 * log t ^ 4 ≤ b ^ 2 * log b ^ 4 := by
    have : 0 ≤ log t := by linarith
    gcongr
  have hpos : 0 < t ^ 2 * log t ^ 4 := by
    have : 0 < log t := by linarith
    have : 0 < t := by linarith
    positivity
  have hL : 0 < L ^ 2 := by linarith
  refine ⟨ht1, hlt, ?_, hL⟩
  rw [div_le_iff₀ hL]; linarith
theorem rpow_five_mul_sub_one {x : ℝ} (hx : 0 < x) (t : ℝ) :
    x ^ (5 * (t - 1)) = x ^ (5 * t) / x ^ 5 := by
  rw [show 5 * (t - 1) = 5 * t - 5 by ring, rpow_sub hx]
  norm_cast
theorem continuousAt_growth (L a : ℝ) {t : ℝ} (ht : 1 ≤ t) :
    ContinuousAt (fun t => (1 + t ^ 2 * log t ^ 5 / L ^ 2) ^ (5 * (t - a))) t :=
  (hasDerivAt_growth L a ht).continuousAt
theorem continuousOn_lemma11_integrand (L : ℝ) (r : ℕ) {s b : ℝ} (hs : 2 ≤ s) :
    ContinuousOn (fun t => (1 + t ^ 2 * log t ^ 5 / L ^ 2) ^ (5 * (t - 1)) * majG r (t - 1) * t /
      (t - 1) ^ 2) (Icc s b) := by
  refine continuousOn_of_forall_continuousAt fun t ht => ?_
  have ht1 : t - 1 ≠ 0 := by linarith [ht.1]
  exact (((continuousAt_growth L 1 (by linarith [ht.1])).mul
    ((continuous_majG r).continuousAt.comp (continuous_sub_right 1).continuousAt)).mul
    continuousAt_id).div ((continuous_sub_right 1).continuousAt.pow 2) (pow_ne_zero 2 ht1)
theorem delta_eq_growth (s y : ℝ) :
    delta s y = (1 + s ^ 2 * log s ^ 5 / log y ^ 2) ^ (5 * (s - 0)) := by
  rw [delta, sub_zero]
theorem delta_pos {s : ℝ} (hs : 1 ≤ s) (y : ℝ) : 0 < delta s y := by
  have := lsx_nonneg (log y) hs
  exact rpow_pos_of_pos (by linarith) _
theorem lemma11_decay_bound {x E G K ℓ : ℝ} (hx : 0 ≤ x) (hE : 0 ≤ E)
    (hK : 0 ≤ K) (hℓ : 0 < ℓ) (hG : G * ℓ ≤ 4 * K)
    (hrate : 4 * E * (1 + 5 * x) ≤ 5 * x * ℓ) :
    K / (1 + x) ^ 5 ≤ K - E * G := by
  have hx5 : 0 < 1 + 5 * x := by linarith only [hx]
  have hbern : 1 + 5 * x ≤ (1 + x) ^ 5 :=
    one_add_mul_le_pow (by linarith only [hx]) 5
  have hEG : E * G * (1 + 5 * x) ≤ 5 * x * K := by
    have h1 := mul_le_mul_of_nonneg_left hG hE
    have h2 := mul_le_mul_of_nonneg_right h1 hx5.le
    have h3 := mul_le_mul_of_nonneg_right hrate hK
    apply le_of_mul_le_mul_left (a := ℓ) _ hℓ
    nlinarith only [h2, h3]
  calc K / (1 + x) ^ 5 ≤ K / (1 + 5 * x) :=
        div_le_div_of_nonneg_left hK hx5 hbern
    _ ≤ K - E * G := by
        rw [div_le_iff₀ hx5]
        nlinarith only [hEG]
theorem lemma11 (r : ℕ) {y s b : ℝ} (hs : exp 32 ≤ s) (hsb : s ≤ b)
    (hb : b ^ 2 * log b ^ 4 ≤ log y ^ 2 / 160) :
    ∫ t in s..b, (1 + t ^ 2 * log t ^ 5 / log y ^ 2) ^ (5 * (t - 1)) * majG r (t - 1) * t /
      (t - 1) ^ 2 < delta s y * majG (r + 1) s := by
  set L := log y
  have hs3 : 3 < s := by linarith [add_one_le_exp (32 : ℝ)]
  set τ : ℝ → ℝ := fun t => delta t y * majG (r + 1) t
  have hτd : ∀ t, 3 < t → HasDerivAt τ
      ((1 + t ^ 2 * log t ^ 5 / L ^ 2) ^ (5 * (t - 0)) *
        (5 * log (1 + t ^ 2 * log t ^ 5 / L ^ 2) + 5 * (t - 0) *
          ((2 * t * log t ^ 5 + 5 * t * log t ^ 4) / L ^ 2) /
            (1 + t ^ 2 * log t ^ 5 / L ^ 2)) * majG (r + 1) t +
        (1 + t ^ 2 * log t ^ 5 / L ^ 2) ^ (5 * (t - 0)) *
          (-(majG r (t - 1) * t / (t - 1) ^ 2))) t := fun t ht => by
    have h1 := hasDerivAt_growth L 0 (t := t) (by linarith)
    have h2 := hasDerivAt_majG_succ r (t := t) (by linarith [five_add_neg_one_pow_div_le r])
    have := h1.mul h2
    simp only [τ, delta_eq_growth]
    exact this
  have key := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le (g := fun t => -τ t)
    (φ := fun t => (1 + t ^ 2 * log t ^ 5 / L ^ 2) ^ (5 * (t - 1)) * majG r (t - 1) * t /
      (t - 1) ^ 2) hsb
    (continuousOn_of_forall_continuousAt fun t ht => (hτd t (by linarith [ht.1])).continuousAt.neg)
    (fun t ht => (hτd t (by linarith [ht.1])).neg.hasDerivWithinAt)
    ((continuousOn_lemma11_integrand L r (by linarith)).integrableOn_Icc) ?_
  · have hτb : 0 < τ b := mul_pos (delta_pos (by linarith) y) (majG_pos _ _)
    simp only [τ] at key hτb ⊢
    linarith
  intro t ht
  have ht3 : 3 < t := by linarith [ht.1]
  obtain ⟨ht1, hlt, hw, hL⟩ := range_facts (L := L) (hs.trans ht.1.le) ht.2.le hb
  obtain ⟨hE0, -, hE2⟩ := rate_bound (L := L) (a := 0) le_rfl zero_le_one ht1 hlt hw
  set x := t ^ 2 * log t ^ 5 / L ^ 2
  set E := 5 * log (1 + x) + 5 * (t - 0) * ((2 * t * log t ^ 5 + 5 * t * log t ^ 4) / L ^ 2) /
    (1 + x)
  have hK0 : 0 < majG r (t - 1) * t / (t - 1) ^ 2 :=
    div_pos (mul_pos (majG_pos r _) (by linarith only [ht3]))
      (sq_pos_of_pos (by linarith only [ht3]))
  set K := majG r (t - 1) * t / (t - 1) ^ 2 with hK
  set G := majG (r + 1) t
  have hx0 : 0 ≤ x := lsx_nonneg L ht1
  have hG : G * log t < 4 * K := majG_succ_mul_log_lt r (by linarith only [ht3])
  have hP : 0 < (1 + x) ^ (5 * (t - 0)) := rpow_pos_of_pos (by linarith only [hx0]) _
  have hdecay := lemma11_decay_bound hx0 hE0 hK0.le
    (by linarith only [hlt] : 0 < log t) hG.le hE2
  show (1 + x) ^ (5 * (t - 1)) * majG r (t - 1) * t / (t - 1) ^ 2 ≤
    -((1 + x) ^ (5 * (t - 0)) * E * G + (1 + x) ^ (5 * (t - 0)) * -K)
  rw [rpow_five_mul_sub_one (by linarith)]
  simp only [sub_zero] at hP ⊢
  calc (1 + x) ^ (5 * t) / (1 + x) ^ 5 * majG r (t - 1) * t / (t - 1) ^ 2
      = (1 + x) ^ (5 * t) * (K / (1 + x) ^ 5) := by rw [hK]; ring
    _ ≤ (1 + x) ^ (5 * t) * (K - E * G) := mul_le_mul_of_nonneg_left hdecay hP.le
    _ = _ := by ring
theorem four_lt_of_exp_le {t : ℝ} (ht : exp 32 ≤ t) : 4 < t := by
  linarith [add_one_le_exp (32 : ℝ)]
theorem growth_le_decay {E G K ℓ : ℝ} (hG : 0 ≤ G) (hE : 4 * E ≤ ℓ)
    (hdecay : G * ℓ ≤ 4 * K) : E * G ≤ K := by
  have h := (mul_le_mul_of_nonneg_left hE hG).trans hdecay
  nlinarith only [h]
theorem antitoneOn_growth_mul {L s b : ℝ} {g k ℓ : ℝ → ℝ} (hs : exp 32 ≤ s)
    (hb : b ^ 2 * log b ^ 4 ≤ L ^ 2 / 160) (hg : ∀ t ∈ Icc s b, HasDerivAt g (-k t) t)
    (hg0 : ∀ t ∈ Icc s b, 0 ≤ g t) (hgk : ∀ t ∈ Icc s b, g t * ℓ t ≤ 4 * k t)
    (hℓ : ∀ t ∈ Icc s b, log t - 1 ≤ ℓ t) :
    AntitoneOn (fun t => (1 + t ^ 2 * log t ^ 5 / L ^ 2) ^ (5 * (t - 1)) * g t) (Icc s b) := by
  let A : ℝ → ℝ := fun t => (1 + t ^ 2 * log t ^ 5 / L ^ 2) ^ (5 * (t - 1))
  let E : ℝ → ℝ := fun t => 5 * log (1 + t ^ 2 * log t ^ 5 / L ^ 2) + 5 * (t - 1) *
    ((2 * t * log t ^ 5 + 5 * t * log t ^ 4) / L ^ 2) / (1 + t ^ 2 * log t ^ 5 / L ^ 2)
  have hd : ∀ t ∈ Icc s b,
      HasDerivAt (fun t => A t * g t) (A t * (E t * g t - k t)) t := by
    intro t ht
    have hA : HasDerivAt A (A t * E t) t :=
      hasDerivAt_growth L 1 (range_facts (hs.trans ht.1) ht.2 hb).1
    convert hA.mul (hg t ht) using 1 <;> (try with_reducible_and_instances rfl) <;> (try (funext tt; simp only [Pi.neg_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.inv_apply, Pi.smul_apply, Pi.pow_apply, Function.comp_apply, id_eq]; done))
    ring
  have hnonpos : ∀ t ∈ Icc s b, A t * (E t * g t - k t) ≤ 0 := by
    intro t ht
    obtain ⟨ht1, hlt, hw, -⟩ := range_facts (hs.trans ht.1) ht.2 hb
    obtain ⟨-, hE, -⟩ := rate_bound (L := L) (a := 1) zero_le_one le_rfl ht1 hlt hw
    have hdecay : E t * g t ≤ k t :=
      growth_le_decay (hg0 t ht) (hE.trans (hℓ t ht)) (hgk t ht)
    have hA0 : 0 ≤ A t :=
      (rpow_pos_of_pos (by linarith only [lsx_nonneg L ht1]) _).le
    exact mul_nonpos_of_nonneg_of_nonpos hA0 (sub_nonpos.2 hdecay)
  exact antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc s b)
    (continuousOn_of_forall_continuousAt fun t ht => (hd t ht).continuousAt)
    (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
    (fun t ht => hnonpos t (interior_subset ht))
theorem log_sub_one_ge {t : ℝ} (ht : 2 ≤ t) : log t - 1 ≤ log (t - 1) := by
  have h1 : 0 < t - 1 := by linarith
  have h := log_le_sub_one_of_pos (div_pos (by linarith : (0 : ℝ) < t) h1)
  rw [log_div (by linarith) h1.ne'] at h
  have : t / (t - 1) - 1 ≤ 1 := by
    rw [div_sub_one h1.ne', div_le_one h1]; linarith
  linarith
theorem antitoneOn_sq_div_sq_sub_one : AntitoneOn (fun t : ℝ => t ^ 2 / (t - 1) ^ 2) (Ioi 1) := by
  intro u hu v hv huv
  have hu1 : 0 < u - 1 := by linarith [hu.out]
  have hv1 : 0 < v - 1 := by linarith [hv.out]
  have h : v / (v - 1) ≤ u / (u - 1) := by
    rw [div_le_div_iff₀ hv1 hu1]; nlinarith
  have h0 : 0 ≤ v / (v - 1) := div_nonneg (by linarith) hv1.le
  simp only
  rw [← div_pow, ← div_pow]
  exact pow_le_pow_left₀ h0 h 2
theorem antitoneOn_mul_of_nonneg {f g : ℝ → ℝ} {S : Set ℝ} (hf : AntitoneOn f S)
    (hg : AntitoneOn g S) (hf0 : ∀ t ∈ S, 0 ≤ f t) (hg0 : ∀ t ∈ S, 0 ≤ g t) :
    AntitoneOn (fun t => f t * g t) S := fun u hu v hv huv =>
  mul_le_mul (hf hu hv huv) (hg hu hv huv) (hg0 v hv) (hf0 u hu)
theorem antitoneOn_cor3Weight (r : ℕ) {L s b : ℝ} (hs : exp 32 ≤ s)
    (hb : b ^ 2 * log b ^ 4 ≤ L ^ 2 / 160) :
    AntitoneOn (fun t => (1 + t ^ 2 * log t ^ 5 / L ^ 2) ^ (5 * (t - 1)) * majG r (t - 1) *
      (t ^ 2 / (t - 1) ^ 2)) (Icc s b) := by
  have hfacts : ∀ t ∈ Icc s b, 4 < t := fun t ht => four_lt_of_exp_le (hs.trans ht.1)
  have hψ : AntitoneOn (fun t => (1 + t ^ 2 * log t ^ 5 / L ^ 2) ^ (5 * (t - 1)) *
      majG r (t - 1)) (Icc s b) := by
    refine antitoneOn_growth_mul
      (k := fun t => majG (r + 1) (t - 1 - 1) * (t - 1) / (t - 1 - 1) ^ 2)
      (ℓ := fun t => log (t - 1)) hs hb (fun t ht => ?_) (fun t _ => (majG_pos _ _).le)
      (fun t ht => ?_) fun t ht => log_sub_one_ge (by linarith [hfacts t ht])
    · have h := hasDerivAt_majG_succ (r + 1) (t := t - 1)
        (by linarith [five_add_neg_one_pow_div_le (r + 1), hfacts t ht])
      rw [majG_add_two] at h
      exact h.comp_sub_const t 1
    · have h := majG_succ_mul_log_lt (r + 1) (t := t - 1) (by linarith [hfacts t ht])
      rw [majG_add_two] at h
      exact h.le
  refine antitoneOn_mul_of_nonneg hψ
    (antitoneOn_sq_div_sq_sub_one.mono fun t ht => show (1 : ℝ) < t by linarith [hfacts t ht])
    (fun t ht => ?_) fun t _ => by positivity
  have := lsx_nonneg L (by linarith [hfacts t ht] : (1 : ℝ) ≤ t)
  exact mul_nonneg (rpow_pos_of_pos (by linarith) _).le (majG_pos _ _).le
theorem xi_sq_mul_log_pow_four_div_le {y : ℝ} (hy : 1 < y) (hℓ : 1 ≤ log (log (3 * y)))
    (hξ : 1 ≤ xi y) :
    xi y ^ 2 * log (xi y) ^ 4 / log y ^ 2 ≤ log (log (3 * y)) ^ (-(2 / 5 : ℝ)) := by
  set ℓ := log (log (3 * y)) with hℓdef
  set L := log y with hL
  have hL0 : 0 < L := log_pos hy
  have hℓ0 : 0 < ℓ := by linarith
  have hP : 1 ≤ ℓ ^ (11 / 5 : ℝ) := one_le_rpow hℓ (by norm_num)
  have hξL : xi y ≤ L := by
    rw [xi]; exact div_le_self hL0.le hP
  have h3 : L ≤ log (3 * y) := by
    rw [log_mul (by norm_num) (by linarith)]; linarith [log_nonneg (by norm_num : (1 : ℝ) ≤ 3)]
  have hlogξ : log (xi y) ≤ ℓ := log_le_log (by linarith) (by linarith)
  have hlogξ0 : 0 ≤ log (xi y) := log_nonneg hξ
  have hsq : xi y ^ 2 / L ^ 2 = (ℓ ^ (22 / 5 : ℝ))⁻¹ := by
    have hx : xi y = L / ℓ ^ (11 / 5 : ℝ) := rfl
    have h2 : (ℓ ^ (11 / 5 : ℝ)) ^ 2 = ℓ ^ (22 / 5 : ℝ) := by
      rw [← rpow_natCast, ← rpow_mul hℓ0.le]; norm_num
    rw [hx, div_pow, h2]
    field_simp
  have hP' : 0 < ℓ ^ (22 / 5 : ℝ) := rpow_pos_of_pos hℓ0 _
  calc xi y ^ 2 * log (xi y) ^ 4 / L ^ 2 = log (xi y) ^ 4 * (xi y ^ 2 / L ^ 2) := by ring
    _ ≤ ℓ ^ 4 * (ℓ ^ (22 / 5 : ℝ))⁻¹ := by
        rw [hsq]; gcongr
    _ = ℓ ^ (-(2 / 5 : ℝ)) := by
        rw [← rpow_natCast, ← rpow_neg hℓ0.le, ← rpow_add hℓ0]; norm_num
theorem tendsto_log_log_three_mul : Tendsto (fun y : ℝ => log (log (3 * y))) atTop atTop :=
  tendsto_log_atTop.comp (tendsto_log_atTop.comp (tendsto_id.const_mul_atTop (by norm_num)))
theorem tendsto_xi : Tendsto xi atTop atTop := by
  have hv : Tendsto (fun y : ℝ => log (3 * y)) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  have ho := (isLittleO_log_rpow_rpow_atTop (11 / 5 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)).bound
    (by norm_num : (0 : ℝ) < 1)
  have hbound : ∀ᶠ y in atTop, log (3 * y) ^ (1 / 2 : ℝ) / 2 ≤ xi y := by
    filter_upwards [hv.eventually ho, hv.eventually (eventually_ge_atTop (exp 1)),
      hv.eventually (eventually_ge_atTop (2 * log 3)), eventually_gt_atTop 1] with y h1 h2 h3 hy
    simp only [one_mul] at h1 h2 h3
    have hv0 : 0 < log (3 * y) := by linarith [exp_pos 1]
    have hℓ : 1 ≤ log (log (3 * y)) := (le_log_iff_exp_le hv0).2 h2
    rw [norm_of_nonneg (rpow_nonneg (by linarith) _),
      norm_of_nonneg (rpow_nonneg hv0.le _)] at h1
    have hL : log y = log (3 * y) - log 3 := by
      rw [log_mul (by norm_num) (by linarith)]; ring
    have hP : 0 < log (log (3 * y)) ^ (11 / 5 : ℝ) := rpow_pos_of_pos (by linarith) _
    have hsq : 0 < log (3 * y) ^ (1 / 2 : ℝ) := rpow_pos_of_pos hv0 _
    have hsq2 : log (3 * y) ^ (1 / 2 : ℝ) * log (3 * y) ^ (1 / 2 : ℝ) = log (3 * y) := by
      rw [← rpow_add hv0]; norm_num
    rw [xi, hL, le_div_iff₀ hP]
    calc log (3 * y) ^ (1 / 2 : ℝ) / 2 * log (log (3 * y)) ^ (11 / 5 : ℝ)
        ≤ log (3 * y) ^ (1 / 2 : ℝ) / 2 * log (3 * y) ^ (1 / 2 : ℝ) := by gcongr
      _ = log (3 * y) / 2 := by rw [div_mul_eq_mul_div, hsq2]
      _ ≤ log (3 * y) - log 3 := by linarith
  exact tendsto_atTop_mono' atTop hbound
    (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hv).atTop_div_const (by norm_num))
theorem exists_xi_large : ∃ y₀ : ℝ, ∀ y ≥ y₀, 1 < y ∧ exp 32 ≤ xi y ∧
    xi y ^ 2 * log (xi y) ^ 4 ≤ log y ^ 2 / 160 ∧ 2 ≤ y ^ (1 / xi y) := by
  have hsmall : ∀ᶠ y in atTop, log (log (3 * y)) ^ (-(2 / 5 : ℝ)) ≤ 1 / 160 :=
    ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 5)).comp
      tendsto_log_log_three_mul).eventually (eventually_le_nhds (by norm_num))
  obtain ⟨y₀, hy₀⟩ := eventually_atTop.1 (hsmall.and ((tendsto_xi.eventually
    (eventually_ge_atTop (exp 32))).and ((tendsto_log_log_three_mul.eventually
      (eventually_ge_atTop 1)).and (eventually_gt_atTop 1))))
  refine ⟨y₀, fun y hy => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hy₀ y hy
  have hξ1 : 1 ≤ xi y := le_trans (by linarith [add_one_le_exp (32 : ℝ)]) h2
  have hL0 : 0 < log y := log_pos h4
  refine ⟨h4, h2, ?_, ?_⟩
  · have := (xi_sq_mul_log_pow_four_div_le h4 h3 hξ1).trans h1
    rwa [div_le_iff₀ (by positivity), div_mul_eq_mul_div, one_mul] at this
  · have hℓ0 : 0 < log (log (3 * y)) := by linarith
    have hP : 0 < log (log (3 * y)) ^ (11 / 5 : ℝ) := rpow_pos_of_pos hℓ0 _
    rw [rpow_def_of_pos (by linarith), xi, mul_one_div, div_div_cancel₀ hL0.ne']
    have : 1 ≤ log (log (3 * y)) ^ (11 / 5 : ℝ) := one_le_rpow h3 (by norm_num)
    calc (2 : ℝ) ≤ exp 1 := by linarith [exp_one_gt_d9]
      _ ≤ _ := exp_le_exp.2 this
end IwaniecLinearSieve
end
section
open Real Filter Asymptotics Topology
namespace IwaniecLinearSieve
def StrongPNTProp : Prop :=
  ∃ c > 0, Asymptotics.IsBigO Filter.atTop (Chebyshev.psi - id)
    (fun x : ℝ ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 2)))
noncomputable def pntc : ℝ := by
  classical
  exact if h : StrongPNTProp then h.choose else 1
theorem pntc_pos : 0 < pntc := by
  classical
  unfold pntc
  split_ifs with h
  · exact h.choose_spec.1
  · norm_num
theorem pntc_spec (h : StrongPNTProp) : (Chebyshev.psi - id) =O[atTop]
    fun (x : ℝ) ↦ x * Real.exp (-pntc * (Real.log x) ^ ((1 : ℝ) / 2)) := by
  classical
  have e : pntc = h.choose := by unfold pntc; rw [dif_pos h]
  rw [e]
  exact h.choose_spec.2
noncomputable def pntκ : ℝ := min pntc (1 / 2)
theorem pntκ_pos : 0 < pntκ := lt_min pntc_pos (by norm_num)
theorem pntκ_le_half : pntκ ≤ 1 / 2 := min_le_right _ _
theorem pntκ_le_pntc : pntκ ≤ pntc := min_le_left _ _
noncomputable def pntE (x : ℝ) : ℝ := exp (-pntκ * √(log x))
theorem pntE_pos (x : ℝ) : 0 < pntE x := exp_pos _
theorem pntE_nonneg (x : ℝ) : 0 ≤ pntE x := (pntE_pos x).le
theorem pntE_le_one (x : ℝ) : pntE x ≤ 1 := by
  rw [pntE, exp_le_one_iff, neg_mul]
  exact neg_nonpos.2 (mul_nonneg pntκ_pos.le (sqrt_nonneg _))
theorem pntE_le_pntE {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : pntE y ≤ pntE x := by
  unfold pntE
  apply exp_le_exp.2
  rw [neg_mul, neg_mul, neg_le_neg_iff]
  exact mul_le_mul_of_nonneg_left (sqrt_le_sqrt (log_le_log hx hxy)) pntκ_pos.le
theorem tendsto_pntE : Tendsto pntE atTop (𝓝 0) := by
  have h : Tendsto (fun x ↦ -pntκ * √(log x)) atTop atBot :=
    (tendsto_sqrt_atTop.comp tendsto_log_atTop).const_mul_atTop_of_neg (neg_lt_zero.2 pntκ_pos)
  exact tendsto_exp_atBot.comp h
theorem inv_le_pntE {x : ℝ} (hx : 2 ≤ x) : x⁻¹ ≤ pntE x := by
  have hx0 : 0 < x := by linarith
  have hL : 1 / 4 ≤ log x := by
    have := log_two_gt_d9
    have := log_le_log (by norm_num) hx
    linarith
  have hs : 1 / 2 ≤ √(log x) := by
    exact (le_sqrt (by norm_num) (by linarith)).2 (by linarith)
  rw [← exp_log (inv_pos.2 hx0), pntE, log_inv]
  apply exp_le_exp.2
  have h1 : pntκ * √(log x) ≤ √(log x) * √(log x) := by
    have := pntκ_le_half
    have := sqrt_nonneg (log x)
    nlinarith
  rw [mul_self_sqrt (by linarith)] at h1
  linarith
theorem one_div_mul_log_le_pntE {x : ℝ} (hx : 2 ≤ x) : 1 / (x * log x) ≤ 2 * pntE x := by
  have hx0 : 0 < x := by linarith
  have hL : 1 / 2 ≤ log x := by
    have := log_two_gt_d9
    have := log_le_log (by norm_num) hx
    linarith
  calc 1 / (x * log x) = x⁻¹ * (log x)⁻¹ := by rw [one_div, mul_inv]
    _ ≤ pntE x * 2 := by
      refine mul_le_mul (inv_le_pntE hx) ?_ (inv_nonneg.2 (by linarith)) (pntE_nonneg _)
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    _ = 2 * pntE x := mul_comm _ _
theorem sqrt_mul_log_le {x : ℝ} (hx : 1 ≤ x) : √x * log x ≤ 12 * x * pntE x := by
  have hx0 : 0 < x := by linarith
  set L := log x with hLdef
  have hL : 0 ≤ L := log_nonneg hx
  have hsx : √x = exp (L / 2) := by
    rw [sqrt_eq_iff_mul_self_eq hx0.le (exp_pos _).le, ← exp_add, add_halves, hLdef,
      exp_log hx0]
  have hxL : x = exp (L / 2) * exp (L / 2) := by
    rw [← exp_add, add_halves, hLdef, exp_log hx0]
  clear_value L
  have h1 : L ≤ 4 * exp (L / 4) := by linarith [add_one_le_exp (L / 4)]
  have h2 : pntκ * √L ≤ L / 4 + 1 / 4 := by
    have hκ := pntκ_le_half
    have hs := sqrt_nonneg L
    have hsq := mul_self_sqrt hL
    nlinarith [sq_nonneg (√L - 1)]
  have h3 : exp (pntκ * √L) ≤ 3 * exp (L / 4) := by
    calc exp (pntκ * √L) ≤ exp (L / 4 + 1 / 4) := exp_le_exp.2 h2
      _ = exp (L / 4) * exp (1 / 4) := exp_add _ _
      _ ≤ exp (L / 4) * 3 := by
        gcongr
        calc exp (1 / 4 : ℝ) ≤ exp 1 := exp_le_exp.2 (by norm_num)
          _ ≤ 3 := by have := exp_one_lt_d9; linarith
      _ = 3 * exp (L / 4) := mul_comm _ _
  have h4 : L * exp (pntκ * √L) ≤ 12 * exp (L / 2) := by
    calc L * exp (pntκ * √L) ≤ (4 * exp (L / 4)) * (3 * exp (L / 4)) := by
          gcongr
      _ = 12 * (exp (L / 4) * exp (L / 4)) := by ring
      _ = 12 * exp (L / 2) := by rw [← exp_add]; ring_nf
  have hE : pntE x * exp (pntκ * √L) = 1 := by
    rw [pntE, ← exp_add, ← hLdef]; simp
  have h5 : √x * (12 * exp (L / 2)) = 12 * x := by
    rw [hsx, hxL]; ring
  calc √x * L = √x * L * (pntE x * exp (pntκ * √L)) := by rw [hE, mul_one]
    _ = √x * pntE x * (L * exp (pntκ * √L)) := by ring
    _ ≤ √x * pntE x * (12 * exp (L / 2)) := by
        gcongr
        exact mul_nonneg (sqrt_nonneg _) (pntE_nonneg _)
    _ = pntE x * (√x * (12 * exp (L / 2))) := by ring
    _ = 12 * x * pntE x := by rw [h5]; ring
theorem hasDerivAt_pntE {x : ℝ} (hx : 1 < x) :
    HasDerivAt pntE (pntE x * (-pntκ * (x⁻¹ / (2 * √(log x))))) x := by
  have hlog : HasDerivAt log x⁻¹ x := hasDerivAt_log (by linarith)
  have h := ((hlog.sqrt (log_pos hx).ne').const_mul (-pntκ)).exp
  exact h
theorem exists_abs_psi_sub_le (hPNT : StrongPNTProp) :
    ∃ C X : ℝ, 0 ≤ C ∧ ∀ x ≥ X, |Chebyshev.psi x - x| ≤ C * x * pntE x := by
  obtain ⟨C, hC⟩ := isBigO_iff.1 (pntc_spec hPNT)
  obtain ⟨X, hX⟩ := eventually_atTop.1 hC
  refine ⟨max C 0, max X 1, le_max_right _ _, fun x hx ↦ ?_⟩
  have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  have h := hX x ((le_max_left _ _).trans hx)
  simp only [Pi.sub_apply, id, norm_eq_abs, norm_mul, abs_of_pos hx0, abs_exp] at h
  have hexp : exp (-pntc * log x ^ ((1 : ℝ) / 2)) ≤ pntE x := by
    rw [pntE, ← sqrt_eq_rpow]
    apply exp_le_exp.2
    rw [neg_mul, neg_mul, neg_le_neg_iff]
    exact mul_le_mul_of_nonneg_right pntκ_le_pntc (sqrt_nonneg _)
  calc |Chebyshev.psi x - x| ≤ C * (x * exp (-pntc * log x ^ ((1 : ℝ) / 2))) := h
    _ ≤ max C 0 * (x * exp (-pntc * log x ^ ((1 : ℝ) / 2))) := by
      gcongr
      exact le_max_left _ _
    _ ≤ max C 0 * (x * pntE x) := by gcongr
    _ = max C 0 * x * pntE x := by ring
theorem theta_asymp (hPNT : StrongPNTProp) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ≥ 2, |Chebyshev.theta x - x| ≤ C * x * pntE x := by
  obtain ⟨C, X, hC, hX⟩ := (exists_abs_psi_sub_le hPNT)
  set X' := max X 2
  refine ⟨max (C + 24) (pntE X')⁻¹, (hC.trans (by linarith)).trans (le_max_left _ _),
    fun x hx ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  have hE := pntE_pos x
  rcases le_or_gt X' x with hxX | hxX
  ·
    have h1 := hX x ((le_max_left _ _).trans hxX)
    have h2 := Chebyshev.psi_sub_theta_le (x := x) (by linarith)
    have h3 := Chebyshev.theta_le_psi x
    have h4 := sqrt_mul_log_le (x := x) (by linarith)
    calc |Chebyshev.theta x - x|
        ≤ |Chebyshev.psi x - x| + (Chebyshev.psi x - Chebyshev.theta x) := by
          have h5 := le_abs_self (Chebyshev.psi x - x)
          have h6 := neg_abs_le (Chebyshev.psi x - x)
          rw [abs_le]; constructor <;> linarith
      _ ≤ C * x * pntE x + 2 * (12 * x * pntE x) := by linarith
      _ = (C + 24) * x * pntE x := by ring
      _ ≤ max (C + 24) (pntE X')⁻¹ * x * pntE x := by gcongr; exact le_max_left _ _
  ·
    have h1 := Chebyshev.theta_nonneg x
    have h2 := Chebyshev.theta_le_log4_mul_x hx0.le
    have hlog4 : log 4 < 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
      have := log_two_lt_d9
      push_cast
      linarith
    have h3 : |Chebyshev.theta x - x| ≤ x := by
      rw [abs_le]; constructor <;> nlinarith
    have h4 : pntE X' ≤ pntE x := pntE_le_pntE hx0 hxX.le
    calc |Chebyshev.theta x - x| ≤ x := h3
      _ = (pntE X')⁻¹ * x * pntE X' := by have := (pntE_pos X').ne'; field_simp
      _ ≤ (pntE X')⁻¹ * x * pntE x :=
        mul_le_mul_of_nonneg_left h4 (by have := pntE_pos X'; positivity)
      _ ≤ max (C + 24) (pntE X')⁻¹ * x * pntE x := by gcongr; exact le_max_right _ _
end IwaniecLinearSieve
end
section
open Real Filter Topology MeasureTheory Finset intervalIntegral
open scoped Chebyshev
namespace IwaniecLinearSieve
theorem exists_abs_sub_le_of_cauchy {T g : ℝ → ℝ} {a : ℝ}
    (h : ∀ x y, a ≤ x → x ≤ y → |T y - T x| ≤ g x) (hg : Tendsto g atTop (𝓝 0)) :
    ∃ c, ∀ x ≥ a, |T x - c| ≤ g x := by
  set u : ℕ → ℝ := fun n ↦ T (a + n)
  have hu : CauchySeq u := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨X, hX⟩ := eventually_atTop.1 (hg.eventually (eventually_lt_nhds hε))
    obtain ⟨N, hN⟩ := exists_nat_ge (X - a)
    refine ⟨N, fun n hn ↦ ?_⟩
    rw [Real.dist_eq]
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
    calc |u n - u N| ≤ g (a + N) := h _ _ (by simp) (by linarith)
      _ < ε := hX _ (by linarith)
  obtain ⟨c, hc⟩ := cauchySeq_tendsto_of_complete hu
  refine ⟨c, fun x hx ↦ ?_⟩
  have h1 : Tendsto (fun n : ℕ ↦ |u n - T x|) atTop (𝓝 |c - T x|) := (hc.sub_const _).abs
  have h2 : ∀ᶠ n : ℕ in atTop, |u n - T x| ≤ g x := by
    obtain ⟨N, hN⟩ := exists_nat_ge (x - a)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
    exact h x (a + n) hx (by linarith)
  rw [abs_sub_comm]
  exact le_of_tendsto h1 h2
noncomputable def S (x : ℝ) : ℝ := ∑ p ∈ primesLT (⌊x⌋₊ + 1), (p : ℝ)⁻¹
theorem S_eq_sum (x : ℝ) :
    S x = ∑ k ∈ range (⌊x⌋₊ + 1), if k.Prime then (k : ℝ)⁻¹ else 0 := by
  rw [S, primesLT, show ⌈(⌊x⌋₊ : ℝ) + 1⌉₊ = ⌊x⌋₊ + 1 by exact_mod_cast Nat.ceil_natCast _,
    Nat.primesBelow, sum_filter]
noncomputable def logPrime (k : ℕ) : ℝ := if k.Prime then log k else 0
theorem sum_logPrime_eq_theta (t : ℝ) :
    ∑ k ∈ Icc 0 ⌊t⌋₊, logPrime k = Chebyshev.theta t := by
  rw [Chebyshev.theta_eq_sum_Icc, sum_filter]
  rfl
theorem S_sub_S {x y : ℝ} (hxy : x ≤ y) :
    S y - S x = ∑ k ∈ Ioc ⌊x⌋₊ ⌊y⌋₊, ((k : ℝ) * log k)⁻¹ * logPrime k := by
  rw [S_eq_sum, S_eq_sum, ← sum_Ico_eq_sub _ (by gcongr), Finset.Ico_add_one_add_one_eq_Ioc]
  refine sum_congr rfl fun k _ ↦ ?_
  unfold logPrime
  split_ifs with hk
  · have : 0 < log k := log_pos (by exact_mod_cast hk.one_lt)
    field_simp
  · simp
theorem hasDerivAt_inv_mul_log {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun t ↦ (t * log t)⁻¹) (-((log t + 1) / (t * log t) ^ 2)) t := by
  have h0 : t ≠ 0 := by linarith
  have h1 : HasDerivAt (fun t ↦ t * log t) (1 * log t + t * t⁻¹) t :=
    (hasDerivAt_id t).mul (hasDerivAt_log h0)
  convert h1.inv (mul_ne_zero h0 (log_pos ht).ne') using 1 <;> (try with_reducible_and_instances rfl) <;> (try (funext tt; simp only [Pi.neg_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.inv_apply, Pi.smul_apply, Pi.pow_apply, Function.comp_apply, id_eq]; done))
  rw [mul_inv_cancel₀ h0]
  ring
theorem hasDerivAt_log_log_sub_inv_log {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun t ↦ log (log t) - (log t)⁻¹) ((log t + 1) / (t * log t) ^ 2 * t) t := by
  have h0 : t ≠ 0 := by linarith
  have hl : log t ≠ 0 := (log_pos ht).ne'
  convert ((hasDerivAt_log h0).log hl).sub ((hasDerivAt_log h0).inv hl) using 1 <;> (try with_reducible_and_instances rfl) <;> (try (funext tt; simp only [Pi.neg_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.inv_apply, Pi.smul_apply, Pi.pow_apply, Function.comp_apply, id_eq]; done))
  field_simp
  ring
theorem continuousOn_log_add_one_div {x y : ℝ} (hx : 1 < x) :
    ContinuousOn (fun t ↦ (log t + 1) / (t * log t) ^ 2) (Set.Icc x y) := by
  have hlog : ContinuousOn log (Set.Icc x y) :=
    continuousOn_log.mono fun t ht ↦ by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [ht.1]
  refine ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht ↦ ?_
  have : 1 < t := by linarith [ht.1]
  have := log_pos this
  positivity
theorem S_sub_loglog_eq {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) :
    (S y - log (log y)) - (S x - log (log x)) =
      (y * log y)⁻¹ * (θ y - y) - (x * log x)⁻¹ * (θ x - x) +
        ∫ t in x..y, (log t + 1) / (t * log t) ^ 2 * (θ t - t) := by
  have hpos : ∀ t ∈ Set.Icc x y, 1 < t := fun t ht ↦ by linarith [ht.1]
  have hderiv : ∀ t ∈ Set.Icc x y,
      HasDerivAt (fun t ↦ (t * log t)⁻¹) (-((log t + 1) / (t * log t) ^ 2)) t :=
    fun t ht ↦ hasDerivAt_inv_mul_log (hpos t ht)
  have hcont := continuousOn_log_add_one_div (y := y) (show 1 < x by linarith)
  have hint : IntegrableOn (deriv fun t ↦ (t * log t)⁻¹) (Set.Icc x y) :=
    hcont.neg.integrableOn_Icc.congr_fun (fun t ht ↦ ((hderiv t ht).deriv).symm)
      measurableSet_Icc
  have habel := sum_mul_eq_sub_sub_integral_mul logPrime (f := fun t ↦ (t * log t)⁻¹)
    (by linarith) hxy (fun t ht ↦ (hderiv t ht).differentiableAt) hint
  rw [← S_sub_S hxy] at habel
  simp only [sum_logPrime_eq_theta] at habel
  rw [setIntegral_congr_fun measurableSet_Ioc
    (g := fun t ↦ -((log t + 1) / (t * log t) ^ 2) * θ t)
    (fun t ht ↦ by rw [(hderiv t (Set.Ioc_subset_Icc_self ht)).deriv]),
    ← intervalIntegral.integral_of_le hxy] at habel
  have hcont' : ContinuousOn (fun t ↦ (log t + 1) / (t * log t) ^ 2) (Set.uIcc x y) := by
    rwa [Set.uIcc_of_le hxy]
  have hθ : IntervalIntegrable θ volume x y := Chebyshev.theta_mono.intervalIntegrable
  have hi1 := hθ.continuousOn_mul hcont'
  have hi2 : IntervalIntegrable (fun t ↦ (log t + 1) / (t * log t) ^ 2 * t) volume x y :=
    (continuousOn_id.mono (Set.subset_univ _)).intervalIntegrable.continuousOn_mul hcont'
  have hsplit : ∫ t in x..y, (log t + 1) / (t * log t) ^ 2 * (θ t - t) =
      (∫ t in x..y, (log t + 1) / (t * log t) ^ 2 * θ t) -
        ∫ t in x..y, (log t + 1) / (t * log t) ^ 2 * t := by
    rw [← integral_sub hi1 hi2]
    congr 1
    ext t
    ring
  have hneg : ∫ t in x..y, -((log t + 1) / (t * log t) ^ 2) * θ t =
      -∫ t in x..y, (log t + 1) / (t * log t) ^ 2 * θ t := by
    rw [← intervalIntegral.integral_neg]
    congr 1
    ext t
    ring
  have hftc : ∫ t in x..y, (log t + 1) / (t * log t) ^ 2 * t =
      (log (log y) - (log y)⁻¹) - (log (log x) - (log x)⁻¹) :=
    integral_eq_sub_of_hasDerivAt
      (fun t ht ↦ hasDerivAt_log_log_sub_inv_log (hpos t (by rwa [Set.uIcc_of_le hxy] at ht)))
      hi2
  have hy0 : y ≠ 0 := by linarith
  have hx0 : x ≠ 0 := by linarith
  have hfy : (y * log y)⁻¹ * y = (log y)⁻¹ := by field_simp
  have hfx : (x * log x)⁻¹ * x = (log x)⁻¹ := by field_simp
  rw [hneg] at habel
  rw [hsplit, hftc]
  linear_combination habel - hfx + hfy
theorem half_le_log {t : ℝ} (ht : 2 ≤ t) : 1 / 2 ≤ log t := by
  have := log_two_gt_d9
  have := log_le_log (by norm_num) ht
  linarith
theorem continuousOn_deriv_pntE {x y : ℝ} (hx : 1 < x) :
    ContinuousOn (fun t ↦ pntE t * (-pntκ * (t⁻¹ / (2 * √(log t))))) (Set.Icc x y) := by
  have hpos : ∀ t ∈ Set.Icc x y, 1 < t := fun t ht ↦ by linarith [ht.1]
  have hlog : ContinuousOn log (Set.Icc x y) :=
    continuousOn_log.mono fun t ht ↦ by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [hpos t ht]
  unfold pntE
  refine ContinuousOn.mul (by fun_prop) (ContinuousOn.mul (by fun_prop) ?_)
  refine ContinuousOn.div (continuousOn_inv₀.mono fun t ht ↦ ?_) (by fun_prop) fun t ht ↦ ?_
  · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [hpos t ht]
  · have := sqrt_pos.2 (log_pos (hpos t ht))
    positivity
theorem abs_integrand_le {C t : ℝ} (hC : 0 ≤ C) (ht : 2 ≤ t)
    (hθ : |θ t - t| ≤ C * t * pntE t) :
    |(log t + 1) / (t * log t) ^ 2 * (θ t - t)| ≤
      -(12 * C / pntκ) * (pntE t * (-pntκ * (t⁻¹ / (2 * √(log t))))) := by
  have ht0 : 0 < t := by linarith
  have hL := half_le_log ht
  have hL0 : 0 < log t := by linarith
  have hs : 1 / 2 ≤ √(log t) := (le_sqrt (by norm_num) hL0.le).2 (by linarith)
  have hs0 : 0 < √(log t) := by linarith
  have hss := mul_self_sqrt hL0.le
  have hE := pntE_pos t
  have hκ := pntκ_pos
  have key : (log t + 1) * √(log t) ≤ 6 * log t ^ 2 := by nlinarith
  calc |(log t + 1) / (t * log t) ^ 2 * (θ t - t)|
      = (log t + 1) / (t * log t) ^ 2 * |θ t - t| := by
        rw [abs_mul, abs_of_nonneg (by positivity)]
    _ ≤ (log t + 1) / (t * log t) ^ 2 * (C * t * pntE t) := by gcongr
    _ = C * pntE t * ((log t + 1) / (t * log t ^ 2)) := by field_simp
    _ ≤ C * pntE t * (6 / (t * √(log t))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
    _ = -(12 * C / pntκ) * (pntE t * (-pntκ * (t⁻¹ / (2 * √(log t))))) := by
        field_simp
        ring
theorem exists_abs_S_sub_loglog_sub_le (hPNT : StrongPNTProp) :
    ∃ K, 0 ≤ K ∧ ∀ x y, 2 ≤ x → x ≤ y →
      |(S y - log (log y)) - (S x - log (log x))| ≤ K * pntE x := by
  obtain ⟨C, hC0, hC⟩ := (theta_asymp hPNT)
  have hκ := pntκ_pos
  refine ⟨4 * C + 12 * C / pntκ, by positivity, fun x y hx hxy ↦ ?_⟩
  rw [S_sub_loglog_eq hx hxy]
  have hy : 2 ≤ y := hx.trans hxy
  have hbd : ∀ t, x ≤ t → |(t * log t)⁻¹ * (θ t - t)| ≤ 2 * C * pntE x := by
    intro t hxt
    have ht : 2 ≤ t := hx.trans hxt
    have ht0 : 0 < t := by linarith
    have hL := half_le_log ht
    have hE := pntE_pos t
    calc |(t * log t)⁻¹ * (θ t - t)| = (t * log t)⁻¹ * |θ t - t| := by
          rw [abs_mul, abs_of_pos (inv_pos.2 (by positivity))]
      _ ≤ (t * log t)⁻¹ * (C * t * pntE t) := by gcongr; exact hC t ht
      _ = C * pntE t / log t := by field_simp
      _ ≤ 2 * C * pntE t := by
          rw [div_le_iff₀ (by linarith)]
          nlinarith [mul_nonneg hC0 hE.le]
      _ ≤ 2 * C * pntE x := by gcongr; exact pntE_le_pntE (by linarith) hxt
  have hderivE : ∀ t ∈ Set.uIcc x y,
      HasDerivAt pntE (pntE t * (-pntκ * (t⁻¹ / (2 * √(log t))))) t := fun t ht ↦
    hasDerivAt_pntE (by rw [Set.uIcc_of_le hxy] at ht; linarith [ht.1])
  have hcontE := continuousOn_deriv_pntE (y := y) (show 1 < x by linarith)
  rw [← Set.uIcc_of_le hxy] at hcontE
  have hintE := hcontE.intervalIntegrable (μ := volume)
  have hftc : ∫ t in x..y, -(12 * C / pntκ) * (pntE t * (-pntκ * (t⁻¹ / (2 * √(log t))))) =
      12 * C / pntκ * (pntE x - pntE y) := by
    rw [intervalIntegral.integral_const_mul, integral_eq_sub_of_hasDerivAt hderivE hintE]
    ring
  have hint : |∫ t in x..y, (log t + 1) / (t * log t) ^ 2 * (θ t - t)| ≤
      12 * C / pntκ * pntE x := by
    rw [← norm_eq_abs]
    refine (norm_integral_le_of_norm_le hxy (ae_of_all _ fun t ht ↦ ?_)
      (hintE.const_mul (-(12 * C / pntκ)))).trans ?_
    · rw [norm_eq_abs]
      have ht2 : 2 ≤ t := by linarith [ht.1]
      exact abs_integrand_le hC0 ht2 (hC t ht2)
    · rw [hftc]
      have := pntE_pos y
      have : 0 ≤ 12 * C / pntκ := by positivity
      nlinarith
  have h1 := hbd y hxy
  have h2 := hbd x le_rfl
  calc _ ≤ |(y * log y)⁻¹ * (θ y - y)| + |(x * log x)⁻¹ * (θ x - x)| +
        |∫ t in x..y, (log t + 1) / (t * log t) ^ 2 * (θ t - t)| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_sub _ _) _)
    _ ≤ (4 * C + 12 * C / pntκ) * pntE x := by linarith
theorem S_asymp (hPNT : StrongPNTProp) : ∃ c₅ C : ℝ, ∀ x ≥ 2, |S x - log (log x) - c₅| ≤ C * pntE x := by
  obtain ⟨K, -, hK⟩ := (exists_abs_S_sub_loglog_sub_le hPNT)
  obtain ⟨c, hc⟩ := exists_abs_sub_le_of_cauchy (T := fun x ↦ S x - log (log x))
    (g := fun x ↦ K * pntE x) (a := 2) hK (by simpa using tendsto_pntE.const_mul K)
  exact ⟨c, K, hc⟩
end IwaniecLinearSieve
end
section
open Real Filter Topology Finset
namespace IwaniecLinearSieve
theorem one_sub_inv_pos {p : ℕ} (hp : p.Prime) : 0 < 1 - (p : ℝ)⁻¹ := by
  have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  rw [sub_pos]
  exact inv_lt_one_of_one_lt₀ this
theorem one_sub_inv_le_one (p : ℕ) : 1 - (p : ℝ)⁻¹ ≤ 1 := by
  have : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  linarith
theorem primesLT_mono {z w : ℝ} (hzw : z ≤ w) : primesLT z ⊆ primesLT w := fun p hp ↦ by
  rw [mem_primesLT] at hp ⊢
  exact ⟨hp.1, hp.2.trans_le hzw⟩
theorem R_eq_mul_prod_sdiff {z w : ℝ} (hzw : z ≤ w) :
    R w = R z * ∏ p ∈ primesLT w \ primesLT z, (1 - (p : ℝ)⁻¹) := by
  rw [R, R, mul_comm, prod_sdiff (primesLT_mono hzw)]
theorem R_antitone : Antitone R := fun z w hzw ↦ by
  rw [R_eq_mul_prod_sdiff hzw]
  refine mul_le_of_le_one_right (R_pos z).le (prod_le_one₀ (fun p hp ↦ ?_) fun p _ ↦
    one_sub_inv_le_one p)
  exact (one_sub_inv_pos (mem_primesLT.1 (Finset.mem_sdiff.1 hp).1).1).le
noncomputable def SLT (z : ℝ) : ℝ := ∑ p ∈ primesLT z, (p : ℝ)⁻¹
theorem S_sub_SLT {z : ℝ} (hz : 0 < z) : 0 ≤ S z - SLT z ∧ S z - SLT z ≤ z⁻¹ := by
  have hS : S z = ∑ p ∈ Nat.primesBelow (⌊z⌋₊ + 1), (p : ℝ)⁻¹ := by
    rw [S, primesLT, show ⌈(⌊z⌋₊ : ℝ) + 1⌉₊ = ⌊z⌋₊ + 1 by exact_mod_cast Nat.ceil_natCast _]
  have hsub : primesLT z ⊆ Nat.primesBelow (⌊z⌋₊ + 1) := fun p hp ↦ by
    rw [primesLT, Nat.mem_primesBelow] at hp
    rw [Nat.mem_primesBelow]
    exact ⟨hp.1.trans_le (Nat.ceil_le_floor_add_one z), hp.2⟩
  rw [hS, SLT, ← sum_sdiff hsub, add_sub_cancel_right]
  refine ⟨sum_nonneg fun p _ ↦ by positivity, ?_⟩
  have hmem : ∀ p ∈ Nat.primesBelow (⌊z⌋₊ + 1) \ primesLT z, (p : ℝ) = z ∧ p = ⌊z⌋₊ := by
    intro p hp
    rw [Finset.mem_sdiff, Nat.mem_primesBelow, primesLT, Nat.mem_primesBelow] at hp
    have h1 : p ≤ ⌊z⌋₊ := Nat.lt_succ_iff.1 hp.1.1
    have h2 : ⌈z⌉₊ ≤ p := by
      by_contra h
      exact hp.2 ⟨Nat.lt_of_not_le h, hp.1.2⟩
    have h3 : z ≤ p := Nat.ceil_le.1 h2
    have h4 : (p : ℝ) ≤ z := (Nat.le_floor_iff hz.le).1 h1
    exact ⟨le_antisymm h4 h3, le_antisymm h1 (Nat.floor_le_of_le h3)⟩
  have hcard : (Nat.primesBelow (⌊z⌋₊ + 1) \ primesLT z).card ≤ 1 :=
    card_le_one.2 fun a ha b hb ↦ (hmem a ha).2.trans (hmem b hb).2.symm
  calc ∑ p ∈ Nat.primesBelow (⌊z⌋₊ + 1) \ primesLT z, (p : ℝ)⁻¹
      = ∑ p ∈ Nat.primesBelow (⌊z⌋₊ + 1) \ primesLT z, z⁻¹ :=
        sum_congr rfl fun p hp ↦ by rw [(hmem p hp).1]
    _ = (Nat.primesBelow (⌊z⌋₊ + 1) \ primesLT z).card * z⁻¹ := by rw [sum_const, nsmul_eq_mul]
    _ ≤ 1 * z⁻¹ := by gcongr; exact_mod_cast hcard
    _ = z⁻¹ := one_mul _
theorem abs_log_one_sub_inv_add_inv_le {p : ℝ} (hp : 2 ≤ p) :
    |log (1 - p⁻¹) + p⁻¹| ≤ (p - 1)⁻¹ - p⁻¹ := by
  have hp0 : 0 < p := by linarith
  have hq : 0 < 1 - p⁻¹ := by
    rw [sub_pos]; exact inv_lt_one_of_one_lt₀ (by linarith)
  have h1 : log (1 - p⁻¹) ≤ -p⁻¹ := by linarith [log_le_sub_one_of_pos hq]
  have h2 : -((1 - p⁻¹)⁻¹ - 1) ≤ log (1 - p⁻¹) := by
    have := log_le_sub_one_of_pos (inv_pos.2 hq)
    rw [log_inv] at this
    linarith
  have h3 : (1 - p⁻¹)⁻¹ - 1 = (p - 1)⁻¹ := by
    have : p - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [abs_of_nonpos (by linarith)]
  linarith
theorem sum_Ico_inv_sub_inv {m M : ℕ} (hmM : m ≤ M) :
    ∑ n ∈ Ico m M, (((n : ℝ) - 1)⁻¹ - (n : ℝ)⁻¹) = ((m : ℝ) - 1)⁻¹ - ((M : ℝ) - 1)⁻¹ := by
  induction M, hmM using Nat.le_induction with
  | base => simp
  | succ M hmM ih =>
    rw [sum_Ico_succ_top hmM, ih]
    push_cast
    ring
theorem abs_sum_log_one_sub_inv_add_inv_le {z w : ℝ} (hz : 2 ≤ z) (hzw : z ≤ w) :
    |∑ p ∈ primesLT w \ primesLT z, (log (1 - (p : ℝ)⁻¹) + (p : ℝ)⁻¹)| ≤ 2 * z⁻¹ := by
  have hz1 : (2 : ℝ) ≤ ⌈z⌉₊ := hz.trans (Nat.le_ceil z)
  have hw1 : (2 : ℝ) ≤ ⌈w⌉₊ := hz1.trans (by exact_mod_cast Nat.ceil_mono hzw)
  have hsub : primesLT w \ primesLT z ⊆ Ico ⌈z⌉₊ ⌈w⌉₊ := fun p hp ↦ by
    rw [Finset.mem_sdiff, primesLT, primesLT, Nat.mem_primesBelow, Nat.mem_primesBelow] at hp
    rw [Finset.mem_Ico]
    exact ⟨not_lt.1 fun h ↦ hp.2 ⟨h, hp.1.2⟩, hp.1.1⟩
  have hnn : ∀ n ∈ Ico ⌈z⌉₊ ⌈w⌉₊, 0 ≤ ((n : ℝ) - 1)⁻¹ - (n : ℝ)⁻¹ := fun n hn ↦ by
    have : (2 : ℝ) ≤ n := hz1.trans (by exact_mod_cast (Finset.mem_Ico.1 hn).1)
    rw [sub_nonneg]
    exact inv_anti₀ (by linarith) (by linarith)
  calc |∑ p ∈ primesLT w \ primesLT z, (log (1 - (p : ℝ)⁻¹) + (p : ℝ)⁻¹)|
      ≤ ∑ p ∈ primesLT w \ primesLT z, |log (1 - (p : ℝ)⁻¹) + (p : ℝ)⁻¹| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ primesLT w \ primesLT z, (((p : ℝ) - 1)⁻¹ - (p : ℝ)⁻¹) := by
        refine sum_le_sum fun p hp ↦ abs_log_one_sub_inv_add_inv_le ?_
        exact hz1.trans (by exact_mod_cast (Finset.mem_Ico.1 (hsub hp)).1)
    _ ≤ ∑ n ∈ Ico ⌈z⌉₊ ⌈w⌉₊, (((n : ℝ) - 1)⁻¹ - (n : ℝ)⁻¹) :=
        sum_le_sum_of_subset_of_nonneg hsub fun n hn _ ↦ hnn n hn
    _ = ((⌈z⌉₊ : ℝ) - 1)⁻¹ - ((⌈w⌉₊ : ℝ) - 1)⁻¹ := sum_Ico_inv_sub_inv (Nat.ceil_mono hzw)
    _ ≤ (z - 1)⁻¹ := by
        have : 0 ≤ ((⌈w⌉₊ : ℝ) - 1)⁻¹ := inv_nonneg.2 (by linarith)
        have : ((⌈z⌉₊ : ℝ) - 1)⁻¹ ≤ (z - 1)⁻¹ :=
          inv_anti₀ (by linarith) (by linarith [Nat.le_ceil z])
        linarith
    _ ≤ 2 * z⁻¹ := by
        rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by linarith) (by linarith)]
        linarith
theorem abs_exp_sub_one_le_mul_exp (d : ℝ) : |exp d - 1| ≤ |d| * exp |d| := by
  rcases le_total 0 d with hd | hd
  · rw [abs_of_nonneg hd, abs_of_nonneg (by linarith [add_one_le_exp d])]
    have h1 := add_one_le_exp (-d)
    have h2 : exp d * exp (-d) = 1 := by rw [← exp_add]; simp
    nlinarith [exp_pos d]
  · rw [abs_of_nonpos hd, abs_of_nonpos (by linarith [exp_le_one_iff.2 hd])]
    have h1 := add_one_le_exp d
    have h2 : 1 ≤ exp (-d) := one_le_exp_iff.2 (by linarith)
    nlinarith
theorem exists_abs_log_R_add_loglog_sub_le (hPNT : StrongPNTProp) :
    ∃ K, 0 ≤ K ∧ ∀ z w, 2 ≤ z → z ≤ w →
      |(log (R w) + log (log w)) - (log (R z) + log (log z))| ≤ K * pntE z := by
  obtain ⟨c₅, C, hC⟩ := (S_asymp hPNT)
  have hC0 : 0 ≤ C := by
    have h := (abs_nonneg _).trans (hC 2 le_rfl)
    exact nonneg_of_mul_nonneg_left h (pntE_pos 2)
  refine ⟨2 * C + 4, by positivity, fun z w hz hzw ↦ ?_⟩
  have hw : 2 ≤ w := hz.trans hzw
  set D := primesLT w \ primesLT z
  have hR : log (R w) - log (R z) = ∑ p ∈ D, log (1 - (p : ℝ)⁻¹) := by
    rw [R_eq_mul_prod_sdiff hzw, log_mul (R_pos z).ne', log_prod]
    · ring
    · exact fun p hp ↦ (one_sub_inv_pos (mem_primesLT.1 (Finset.mem_sdiff.1 hp).1).1).ne'
    · exact (prod_pos fun p hp ↦
        one_sub_inv_pos (mem_primesLT.1 (Finset.mem_sdiff.1 hp).1).1).ne'
  have hS : SLT w - SLT z = ∑ p ∈ D, (p : ℝ)⁻¹ := by
    rw [SLT, SLT, ← sum_sdiff (primesLT_mono hzw)]
    ring
  have h1 := abs_sum_log_one_sub_inv_add_inv_le hz hzw
  rw [sum_add_distrib, ← hR, ← hS] at h1
  have h2 := S_sub_SLT (z := z) (by linarith)
  have h3 := S_sub_SLT (z := w) (by linarith)
  have h4 := hC z hz
  have h5 := hC w hw
  have hE : pntE w ≤ pntE z := pntE_le_pntE (by linarith) hzw
  have hiz := inv_le_pntE hz
  have hiw : w⁻¹ ≤ z⁻¹ := inv_anti₀ (by linarith) hzw
  rw [abs_le] at h1 h4 h5 ⊢
  constructor <;> nlinarith
theorem R_asymp (hPNT : StrongPNTProp) : ∃ cR > 0, ∃ C, ∀ z ≥ 2, |R z * log z - cR| ≤ C * pntE z := by
  obtain ⟨K, hK0, hK⟩ := (exists_abs_log_R_add_loglog_sub_le hPNT)
  obtain ⟨L, hL⟩ := exists_abs_sub_le_of_cauchy (T := fun z ↦ log (R z) + log (log z))
    (g := fun z ↦ K * pntE z) (a := 2) hK (by simpa using tendsto_pntE.const_mul K)
  refine ⟨exp L, exp_pos L, exp L * (K * exp K), fun z hz ↦ ?_⟩
  have hlog : 0 < log z := log_pos (by linarith)
  have hRz : R z * log z = exp (log (R z) + log (log z)) := by
    rw [exp_add, exp_log (R_pos z), exp_log hlog]
  have hd := hL z hz
  have hdK : |log (R z) + log (log z) - L| ≤ K := by
    have := pntE_le_one z
    nlinarith
  rw [hRz, show exp (log (R z) + log (log z)) - exp L =
      exp L * (exp (log (R z) + log (log z) - L) - 1) by rw [mul_sub, ← exp_add]; ring_nf,
    abs_mul, abs_of_pos (exp_pos L)]
  calc exp L * |exp (log (R z) + log (log z) - L) - 1|
      ≤ exp L * (|log (R z) + log (log z) - L| * exp |log (R z) + log (log z) - L|) := by
        gcongr; exact abs_exp_sub_one_le_mul_exp _
    _ ≤ exp L * ((K * pntE z) * exp K) := by
        have := pntE_pos z
        gcongr
    _ = exp L * (K * exp K) * pntE z := by ring
theorem R_lower (hPNT : StrongPNTProp) : ∃ c > 0, ∀ z ≥ 2, c / log z ≤ R z := by
  obtain ⟨cR, hcR, C, hC⟩ := (R_asymp hPNT)
  obtain ⟨Z, hZ⟩ := eventually_atTop.1
    ((by simpa using tendsto_pntE.const_mul C : Tendsto (fun z ↦ C * pntE z) atTop (𝓝 0)).eventually
      (eventually_lt_nhds (half_pos hcR)))
  set Z' := max Z 2
  have hlog2 : 0 < log 2 := log_pos one_lt_two
  refine ⟨min (cR / 2) (R Z' * log 2), lt_min (half_pos hcR) (mul_pos (R_pos _) hlog2),
    fun z hz ↦ ?_⟩
  have hlog : 0 < log z := log_pos (by linarith)
  rw [div_le_iff₀ hlog]
  rcases le_or_gt Z' z with hzZ | hzZ
  · have h1 := hC z hz
    have h2 := hZ z ((le_max_left _ _).trans hzZ)
    rw [abs_le] at h1
    exact (min_le_left _ _).trans (by linarith)
  · refine (min_le_right _ _).trans ?_
    exact mul_le_mul (R_antitone hzZ.le) (log_le_log (by norm_num) hz) hlog2.le (R_pos z).le
end IwaniecLinearSieve
end
section
open Finset MeasureTheory intervalIntegral
namespace IwaniecLinearSieve
theorem abs_sum_mul_sub_le {n : ℕ} {β e : ℕ → ℝ} {ε : ℝ}
    (hβ : ∀ j < n, β j ≤ β (j + 1)) (hβ0 : 0 ≤ β 0) (he : ∀ j ≤ n, |e j| ≤ ε) :
    |∑ j ∈ range n, β (j + 1) * (e (j + 1) - e j)| ≤ 2 * ε * β n := by
  have key : ∀ m ≤ n, 0 ≤ β m ∧ β 0 ≤ β m ∧
      |∑ j ∈ range m, β (j + 1) * (e (j + 1) - e j) - β m * e m + β 0 * e 0| ≤
        ε * (β m - β 0) := by
    intro m hm
    induction m with
    | zero => simpa using hβ0
    | succ m ih =>
      obtain ⟨h0, h1, h2⟩ := ih (by omega)
      have hm' : β m ≤ β (m + 1) := hβ m (by omega)
      refine ⟨by linarith, by linarith, ?_⟩
      rw [sum_range_succ]
      have h3 : |(β (m + 1) - β m) * e m| ≤ (β (m + 1) - β m) * ε := by
        rw [abs_mul, abs_of_nonneg (by linarith)]
        exact mul_le_mul_of_nonneg_left (he m (by omega)) (by linarith)
      calc |∑ j ∈ range m, β (j + 1) * (e (j + 1) - e j) + β (m + 1) * (e (m + 1) - e m) -
            β (m + 1) * e (m + 1) + β 0 * e 0|
          = |(∑ j ∈ range m, β (j + 1) * (e (j + 1) - e j) - β m * e m + β 0 * e 0) -
              (β (m + 1) - β m) * e m| := by ring_nf
        _ ≤ |∑ j ∈ range m, β (j + 1) * (e (j + 1) - e j) - β m * e m + β 0 * e 0| +
              |(β (m + 1) - β m) * e m| := abs_sub _ _
        _ ≤ ε * (β m - β 0) + (β (m + 1) - β m) * ε := add_le_add h2 h3
        _ = ε * (β (m + 1) - β 0) := by ring
  obtain ⟨h0, h1, h2⟩ := key n le_rfl
  have hn : |β n * e n| ≤ β n * ε := by
    rw [abs_mul, abs_of_nonneg h0]; exact mul_le_mul_of_nonneg_left (he n le_rfl) h0
  have hz : |β 0 * e 0| ≤ β 0 * ε := by
    rw [abs_mul, abs_of_nonneg hβ0]; exact mul_le_mul_of_nonneg_left (he 0 (by omega)) hβ0
  rw [abs_le] at h2 hn hz ⊢
  constructor <;> nlinarith
theorem abs_sum_sub_integral_le {n : ℕ} {a : ℕ → ℝ} (ha : Monotone a) {b f F : ℝ → ℝ}
    {g : ℕ → ℝ} {δ ε : ℝ} (hδ0 : 0 ≤ δ)
    (hb : MonotoneOn b (Set.Icc (a 0) (a n))) (hb0 : 0 ≤ b (a 0))
    (hf : ∀ x ∈ Set.Icc (a 0) (a n), 0 ≤ f x) (hfc : ContinuousOn f (Set.Icc (a 0) (a n)))
    (hFf : ∀ j < n, ∫ x in a j..a (j + 1), f x = F (a (j + 1)) - F (a j))
    (hδ : ∀ j < n, F (a (j + 1)) - F (a j) ≤ δ)
    (hε : ∀ j ≤ n, |g j - F (a j)| ≤ ε) :
    |∑ j ∈ range n, b (a (j + 1)) * (g (j + 1) - g j) - ∫ x in a 0..a n, b x * f x| ≤
      (δ + 2 * ε) * b (a n) := by
  have hmem : ∀ j ≤ n, a j ∈ Set.Icc (a 0) (a n) := fun j hj ↦ ⟨ha (Nat.zero_le j), ha hj⟩
  have hsub : ∀ j < n, Set.Icc (a j) (a (j + 1)) ⊆ Set.Icc (a 0) (a n) := fun j hj x hx ↦
    ⟨(hmem j hj.le).1.trans hx.1, hx.2.trans (hmem (j + 1) hj).2⟩
  have hle : ∀ j, a j ≤ a (j + 1) := fun j ↦ ha (Nat.le_succ j)
  have hβ : ∀ j < n, b (a j) ≤ b (a (j + 1)) := fun j hj ↦
    hb (hmem j hj.le) (hmem (j + 1) hj) (hle j)
  have hint : ∀ j < n, IntervalIntegrable (fun x ↦ b x * f x) volume (a j) (a (j + 1)) := by
    intro j hj
    have h1 := hsub j hj
    rw [← Set.uIcc_of_le (hle j)] at h1
    exact (hb.mono h1).intervalIntegrable.mul_continuousOn (hfc.mono h1)
  have hintf : ∀ j < n, IntervalIntegrable f volume (a j) (a (j + 1)) := by
    intro j hj
    have h1 := hsub j hj
    rw [← Set.uIcc_of_le (hle j)] at h1
    exact (hfc.mono h1).intervalIntegrable
  have hI : ∀ j < n, 0 ≤ F (a (j + 1)) - F (a j) := fun j hj ↦ by
    rw [← hFf j hj]
    exact intervalIntegral.integral_nonneg (hle j) fun x hx ↦ hf x (hsub j hj hx)
  have hpiece : ∀ j < n, b (a j) * (F (a (j + 1)) - F (a j)) ≤ ∫ x in a j..a (j + 1), b x * f x ∧
      ∫ x in a j..a (j + 1), b x * f x ≤ b (a (j + 1)) * (F (a (j + 1)) - F (a j)) := by
    intro j hj
    rw [← hFf j hj, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    constructor
    · refine intervalIntegral.integral_mono_on (hle j) ((hintf j hj).const_mul _) (hint j hj)
        fun x hx ↦ mul_le_mul_of_nonneg_right ?_ (hf x (hsub j hj hx))
      exact hb (hmem j hj.le) (hsub j hj hx) hx.1
    · refine intervalIntegral.integral_mono_on (hle j) (hint j hj) ((hintf j hj).const_mul _)
        fun x hx ↦ mul_le_mul_of_nonneg_right ?_ (hf x (hsub j hj hx))
      exact hb (hsub j hj hx) (hmem (j + 1) hj) hx.2
  rw [← intervalIntegral.sum_integral_adjacent_intervals hint]
  have hsplit : ∑ j ∈ range n, b (a (j + 1)) * (g (j + 1) - g j) -
      ∑ j ∈ range n, ∫ x in a j..a (j + 1), b x * f x =
      ∑ j ∈ range n, (b (a (j + 1)) * (F (a (j + 1)) - F (a j)) -
        ∫ x in a j..a (j + 1), b x * f x) +
      ∑ j ∈ range n, b (a (j + 1)) * ((g (j + 1) - F (a (j + 1))) - (g j - F (a j))) := by
    rw [← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun j _ ↦ ?_
    ring
  rw [hsplit]
  have hmain0 : 0 ≤ ∑ j ∈ range n, (b (a (j + 1)) * (F (a (j + 1)) - F (a j)) -
      ∫ x in a j..a (j + 1), b x * f x) :=
    sum_nonneg fun j hj ↦ sub_nonneg.2 (hpiece j (mem_range.1 hj)).2
  have hmain : ∑ j ∈ range n, (b (a (j + 1)) * (F (a (j + 1)) - F (a j)) -
      ∫ x in a j..a (j + 1), b x * f x) ≤ δ * b (a n) := by
    calc _ ≤ ∑ j ∈ range n, (b (a (j + 1)) - b (a j)) * δ := by
          refine sum_le_sum fun j hj ↦ ?_
          have hj := mem_range.1 hj
          have h1 := (hpiece j hj).1
          have h2 : (b (a (j + 1)) - b (a j)) * (F (a (j + 1)) - F (a j)) ≤
              (b (a (j + 1)) - b (a j)) * δ :=
            mul_le_mul_of_nonneg_left (hδ j hj) (sub_nonneg.2 (hβ j hj))
          linarith
      _ = (b (a n) - b (a 0)) * δ := by rw [← sum_mul, sum_range_sub (fun j ↦ b (a j))]
      _ ≤ δ * b (a n) := by nlinarith
  have herr := abs_sum_mul_sub_le (β := fun j ↦ b (a j)) (e := fun j ↦ g j - F (a j)) hβ hb0 hε
  rw [abs_le] at herr ⊢
  constructor <;> linarith
end IwaniecLinearSieve
end
section
open Real Finset MeasureTheory intervalIntegral
namespace IwaniecLinearSieve
theorem continuousOn_inv_mul_log {u v : ℝ} (hu : 1 < u) :
    ContinuousOn (fun x ↦ (x * log x)⁻¹) (Set.Icc u v) := by
  have hpos : ∀ x ∈ Set.Icc u v, 1 < x := fun x hx ↦ by linarith [hx.1]
  refine ContinuousOn.inv₀ (ContinuousOn.mul continuousOn_id ?_) fun x hx ↦ ?_
  · exact continuousOn_log.mono fun x hx ↦ by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [hpos x hx]
  · have := hpos x hx
    have := log_pos this
    positivity
theorem integral_inv_mul_log {u v : ℝ} (hu : 1 < u) (huv : u ≤ v) :
    ∫ x in u..v, (x * log x)⁻¹ = log (log v) - log (log u) := by
  have hpos : ∀ x ∈ Set.uIcc u v, 1 < x := fun x hx ↦ by
    rw [Set.uIcc_of_le huv] at hx; linarith [hx.1]
  refine integral_eq_sub_of_hasDerivAt (f := fun x ↦ log (log x)) (fun x hx ↦ ?_) ?_
  · have hx := hpos x hx
    have h := (hasDerivAt_log (by linarith : x ≠ 0)).log (log_pos hx).ne'
    convert h using 1 <;> (try with_reducible_and_instances rfl) <;> (try (funext tt; simp only [Pi.neg_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.inv_apply, Pi.smul_apply, Pi.pow_apply, Function.comp_apply, id_eq]; done))
    rw [mul_inv, div_eq_mul_inv]
  · refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le huv]
    exact continuousOn_inv_mul_log hu
theorem log_log_sub_log_log_le {u v : ℝ} (hu : 1 < u) (huv : u ≤ v) :
    log (log v) - log (log u) ≤ (v - u) / (u * log u) := by
  have hu0 : 0 < u := by linarith
  have hlu : 0 < log u := log_pos hu
  have hlv : 0 < log v := log_pos (by linarith)
  have h1 : log (log v) - log (log u) ≤ log v / log u - 1 := by
    rw [← log_div hlv.ne' hlu.ne']
    exact log_le_sub_one_of_pos (div_pos hlv hlu)
  have h2 : log v - log u ≤ v / u - 1 := by
    rw [← log_div (by linarith) hu0.ne']
    exact log_le_sub_one_of_pos (div_pos (by linarith) hu0)
  calc log (log v) - log (log u) ≤ log v / log u - 1 := h1
    _ = (log v - log u) / log u := by field_simp
    _ ≤ (v / u - 1) / log u := by gcongr
    _ = (v - u) / (u * log u) := by field_simp
noncomputable def clampPt (B A : ℝ) (j : ℕ) : ℝ := max B (min ((⌊B⌋₊ + j : ℕ) : ℝ) A)
theorem clampPt_mono (B A : ℝ) : Monotone (clampPt B A) := fun i j hij ↦ by
  unfold clampPt
  gcongr
theorem clampPt_zero {B A : ℝ} (hB : 0 ≤ B) : clampPt B A 0 = B := by
  unfold clampPt
  exact max_eq_left ((min_le_left _ _).trans (by simpa using Nat.floor_le hB))
theorem clampPt_last {B A : ℝ} (hBA : B ≤ A) :
    clampPt B A (⌊A⌋₊ - ⌊B⌋₊ + 1) = A := by
  unfold clampPt
  have h : ⌊B⌋₊ + (⌊A⌋₊ - ⌊B⌋₊ + 1) = ⌊A⌋₊ + 1 := by
    have := Nat.floor_le_floor (a := B) hBA; omega
  rw [h, min_eq_right (by push_cast; exact (Nat.lt_floor_add_one A).le), max_eq_right hBA]
theorem le_clampPt (B A : ℝ) (j : ℕ) : B ≤ clampPt B A j := le_max_left _ _
theorem clampPt_succ_le (B A : ℝ) (j : ℕ) : clampPt B A (j + 1) ≤ clampPt B A j + 1 := by
  unfold clampPt
  push_cast
  simp only [max_def, min_def]
  split_ifs <;> linarith
theorem clampPt_eq {B A : ℝ} {j : ℕ} (hj : 1 ≤ j)
    (hjA : ((⌊B⌋₊ + j : ℕ) : ℝ) ≤ A) : clampPt B A j = ((⌊B⌋₊ + j : ℕ) : ℝ) := by
  unfold clampPt
  rw [min_eq_left hjA, max_eq_right]
  have := Nat.lt_floor_add_one B
  have : (1 : ℝ) ≤ j := by exact_mod_cast hj
  push_cast
  linarith
theorem floor_clampPt {B A : ℝ} (hB : 0 ≤ B) (hBA : B ≤ A) (j : ℕ) :
    ⌊clampPt B A j⌋₊ = min (⌊B⌋₊ + j) ⌊A⌋₊ := by
  unfold clampPt
  set k := ⌊B⌋₊ + j with hk
  rcases le_or_gt (k : ℝ) A with hkA | hkA
  · rw [min_eq_left hkA, min_eq_left (Nat.le_floor hkA)]
    rcases le_or_gt B (k : ℝ) with hBk | hBk
    · rw [max_eq_right hBk, Nat.floor_natCast]
    · rw [max_eq_left hBk.le]
      have : k ≤ ⌊B⌋₊ := Nat.le_floor hBk.le
      omega
  · rw [min_eq_right hkA.le, max_eq_right hBA, min_eq_right]
    exact (Nat.cast_lt (α := ℝ)).1 ((Nat.floor_le (hB.trans hBA)).trans_lt hkA) |>.le
theorem S_eq_S_floor (x : ℝ) : S x = S (⌊x⌋₊ : ℝ) := by
  rw [S_eq_sum, S_eq_sum, Nat.floor_natCast]
theorem S_succ_sub (k : ℕ) :
    S ((k + 1 : ℕ) : ℝ) - S (k : ℝ) = if (k + 1).Prime then ((k + 1 : ℕ) : ℝ)⁻¹ else 0 := by
  rw [S_eq_sum, S_eq_sum, Nat.floor_natCast, Nat.floor_natCast, sum_range_succ]
  ring
noncomputable def primesIoc (B A : ℝ) : Finset ℕ := {p ∈ Ioc ⌊B⌋₊ ⌊A⌋₊ | p.Prime}
theorem le_floor_iff_of_prime {p : ℕ} (hp : p.Prime) {A : ℝ} : p ≤ ⌊A⌋₊ ↔ (p : ℝ) ≤ A := by
  rcases le_or_gt 0 A with hA | hA
  · exact Nat.le_floor_iff hA
  · rw [Nat.floor_of_nonpos hA.le]
    have : (0 : ℝ) < p := by exact_mod_cast hp.pos
    constructor <;> intro h
    · exact absurd h (by have := hp.pos; omega)
    · linarith
theorem floor_lt_iff_of_prime {p : ℕ} (hp : p.Prime) {B : ℝ} : ⌊B⌋₊ < p ↔ B < p := by
  rcases le_or_gt 0 B with hB | hB
  · exact Nat.floor_lt hB
  · rw [Nat.floor_of_nonpos hB.le]
    have : (0 : ℝ) < p := by exact_mod_cast hp.pos
    exact ⟨fun _ ↦ by linarith, fun _ ↦ hp.pos⟩
theorem mem_primesIoc {B A : ℝ} {p : ℕ} : p ∈ primesIoc B A ↔ p.Prime ∧ B < p ∧ (p : ℝ) ≤ A := by
  simp only [primesIoc, mem_filter, mem_Ioc]
  constructor
  · rintro ⟨⟨h1, h2⟩, hp⟩
    exact ⟨hp, (floor_lt_iff_of_prime hp).1 h1, (le_floor_iff_of_prime hp).1 h2⟩
  · rintro ⟨hp, h1, h2⟩
    exact ⟨⟨(floor_lt_iff_of_prime hp).2 h1, (le_floor_iff_of_prime hp).2 h2⟩, hp⟩
theorem sum_clampPt_eq (b : ℝ → ℝ) {B A : ℝ} (hB : 0 ≤ B) (hBA : B ≤ A) :
    ∑ j ∈ range (⌊A⌋₊ - ⌊B⌋₊ + 1),
        b (clampPt B A (j + 1)) * (S (clampPt B A (j + 1)) - S (clampPt B A j)) =
      ∑ p ∈ primesIoc B A, b p / p := by
  have hmN : ⌊B⌋₊ ≤ ⌊A⌋₊ := Nat.floor_le_floor hBA
  have hS : ∀ j, S (clampPt B A j) = S ((min (⌊B⌋₊ + j) ⌊A⌋₊ : ℕ) : ℝ) := fun j ↦ by
    rw [S_eq_S_floor, floor_clampPt hB hBA]
  rw [sum_range_succ, hS, hS, show min (⌊B⌋₊ + (⌊A⌋₊ - ⌊B⌋₊ + 1)) ⌊A⌋₊ = ⌊A⌋₊ by omega,
    show min (⌊B⌋₊ + (⌊A⌋₊ - ⌊B⌋₊)) ⌊A⌋₊ = ⌊A⌋₊ by omega, sub_self, mul_zero, add_zero,
    primesIoc, sum_filter, ← Finset.Ico_add_one_add_one_eq_Ioc, sum_Ico_eq_sum_range,
    show ⌊A⌋₊ + 1 - (⌊B⌋₊ + 1) = ⌊A⌋₊ - ⌊B⌋₊ by omega]
  refine sum_congr rfl fun j hj ↦ ?_
  have hj : j < ⌊A⌋₊ - ⌊B⌋₊ := mem_range.1 hj
  have hc : clampPt B A (j + 1) = ((⌊B⌋₊ + (j + 1) : ℕ) : ℝ) := by
    refine clampPt_eq (by omega) ?_
    exact (Nat.le_floor_iff (hB.trans hBA)).1 (by omega)
  rw [hS, hS, min_eq_left (by omega), min_eq_left (by omega), hc,
    show ⌊B⌋₊ + (j + 1) = ⌊B⌋₊ + j + 1 by ring, S_succ_sub,
    show ⌊B⌋₊ + 1 + j = ⌊B⌋₊ + j + 1 by ring]
  split_ifs <;> simp [div_eq_mul_inv]
theorem S_asymp_nonneg (hPNT : StrongPNTProp) : ∃ c₅ C : ℝ, 0 ≤ C ∧ ∀ x ≥ 2, |S x - log (log x) - c₅| ≤ C * pntE x := by
  obtain ⟨c₅, C, hC⟩ := (S_asymp hPNT)
  refine ⟨c₅, C, ?_, hC⟩
  exact nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hC 2 le_rfl)) (pntE_pos 2)
theorem lemma13_Ioc (hPNT : StrongPNTProp) : ∃ C, 0 ≤ C ∧ ∀ (b : ℝ → ℝ) (A B : ℝ), 2 ≤ B → B ≤ A →
    MonotoneOn b (Set.Icc B A) → (∀ x ∈ Set.Icc B A, 0 ≤ b x) →
    |∑ p ∈ primesIoc B A, b p / p - ∫ x in B..A, b x / (x * log x)| ≤ C * b A * pntE B := by
  obtain ⟨c₅, C, hC0, hC⟩ := (S_asymp_nonneg hPNT)
  refine ⟨2 + 2 * C, by linarith, fun b A B hB hBA hb hb0 ↦ ?_⟩
  set n := ⌊A⌋₊ - ⌊B⌋₊ + 1
  have h0 : clampPt B A 0 = B := clampPt_zero (by linarith)
  have hn : clampPt B A n = A := clampPt_last hBA
  have h2 : ∀ j, 2 ≤ clampPt B A j := fun j ↦ hB.trans (le_clampPt B A j)
  have hE : ∀ j, pntE (clampPt B A j) ≤ pntE B := fun j ↦
    pntE_le_pntE (by linarith) (le_clampPt B A j)
  have hFf : ∀ j < n, ∫ x in clampPt B A j..clampPt B A (j + 1), (x * log x)⁻¹ =
      (log (log (clampPt B A (j + 1))) + c₅) - (log (log (clampPt B A j)) + c₅) := by
    intro j _
    rw [integral_inv_mul_log (by linarith [h2 j]) (clampPt_mono B A (Nat.le_succ j))]
    ring
  have hδ : ∀ j < n, (log (log (clampPt B A (j + 1))) + c₅) - (log (log (clampPt B A j)) + c₅) ≤
      2 * pntE B := by
    intro j _
    have hj := h2 j
    have hlog : 0 < log (clampPt B A j) := log_pos (by linarith)
    calc _ = log (log (clampPt B A (j + 1))) - log (log (clampPt B A j)) := by ring
      _ ≤ (clampPt B A (j + 1) - clampPt B A j) / (clampPt B A j * log (clampPt B A j)) :=
          log_log_sub_log_log_le (by linarith) (clampPt_mono B A (Nat.le_succ j))
      _ ≤ 1 / (clampPt B A j * log (clampPt B A j)) := by
          gcongr
          linarith [clampPt_succ_le B A j]
      _ ≤ 2 * pntE (clampPt B A j) := one_div_mul_log_le_pntE hj
      _ ≤ 2 * pntE B := by linarith [hE j]
  have hε : ∀ j ≤ n, |S (clampPt B A j) - (log (log (clampPt B A j)) + c₅)| ≤ C * pntE B := by
    intro j _
    rw [← sub_sub]
    exact (hC _ (h2 j)).trans (mul_le_mul_of_nonneg_left (hE j) hC0)
  have key := abs_sum_sub_integral_le (n := n) (a := clampPt B A) (clampPt_mono B A)
    (b := b) (f := fun x ↦ (x * log x)⁻¹) (F := fun x ↦ log (log x) + c₅)
    (g := fun j ↦ S (clampPt B A j)) (by linarith [pntE_pos B]) (by rw [h0, hn]; exact hb)
    (by rw [h0]; exact hb0 B ⟨le_rfl, hBA⟩)
    (by
      rw [h0, hn]
      intro x hx
      have : 0 < log x := log_pos (by linarith [hx.1])
      have : 0 < x := by linarith [hx.1]
      positivity)
    (by rw [h0, hn]; exact continuousOn_inv_mul_log (by linarith)) hFf hδ hε
  rw [h0, hn, sum_clampPt_eq b (by linarith) hBA] at key
  simp_rw [div_eq_mul_inv (b _)]
  calc _ ≤ (2 * pntE B + 2 * (C * pntE B)) * b A := key
    _ = (2 + 2 * C) * b A * pntE B := by ring
theorem sum_of_forall_cast_eq {t : Finset ℕ} {v : ℝ} (h : ∀ p ∈ t, (p : ℝ) = v) (φ : ℝ → ℝ)
    (hφ : 0 ≤ φ v) : 0 ≤ ∑ p ∈ t, φ p ∧ ∑ p ∈ t, φ p ≤ φ v := by
  have hcard : t.card ≤ 1 := card_le_one.2 fun a ha b hb ↦ by
    exact_mod_cast (h a ha).trans (h b hb).symm
  have hcard' : (t.card : ℝ) ≤ 1 := by exact_mod_cast hcard
  rw [sum_congr rfl fun p hp ↦ by rw [h p hp], sum_const, nsmul_eq_mul]
  exact ⟨by positivity, by nlinarith⟩
theorem lemma13_mono_of_subset (hPNT : StrongPNTProp) : ∃ C, 0 ≤ C ∧ ∀ (b : ℝ → ℝ) (A B : ℝ) (s : Finset ℕ), 2 ≤ B →
    B ≤ A → MonotoneOn b (Set.Icc B A) → (∀ x ∈ Set.Icc B A, 0 ≤ b x) →
    (∀ p ∈ s, p.Prime ∧ B ≤ p ∧ (p : ℝ) ≤ A) → (∀ p : ℕ, p.Prime → B < p → (p : ℝ) < A → p ∈ s) →
    |∑ p ∈ s, b p / p - ∫ x in B..A, b x / (x * log x)| ≤ C * b A * pntE B := by
  obtain ⟨C, hC0, hC⟩ := (lemma13_Ioc hPNT)
  refine ⟨C + 1, by linarith, fun b A B s hB hBA hb hb0 hs1 hs2 ↦ ?_⟩
  have hB0 : 0 < B := by linarith
  have hbA : 0 ≤ b A := hb0 A ⟨hBA, le_rfl⟩
  have hbB : 0 ≤ b B := hb0 B ⟨le_rfl, hBA⟩
  have hbBA : b B ≤ b A := hb ⟨le_rfl, hBA⟩ ⟨hBA, le_rfl⟩ hBA
  have h1 := sum_of_forall_cast_eq (t := s \ primesIoc B A) (v := B) (fun p hp ↦ by
      rw [Finset.mem_sdiff, mem_primesIoc] at hp
      obtain ⟨hp1, hp2⟩ := hp
      obtain ⟨hpp, hBp, hpA⟩ := hs1 p hp1
      exact le_antisymm (not_lt.1 fun h ↦ hp2 ⟨hpp, h, hpA⟩) hBp)
    (fun x ↦ b x / x) (div_nonneg hbB hB0.le)
  have h2 := sum_of_forall_cast_eq (t := primesIoc B A \ s) (v := A) (fun p hp ↦ by
      rw [Finset.mem_sdiff, mem_primesIoc] at hp
      obtain ⟨⟨hpp, hBp, hpA⟩, hp2⟩ := hp
      exact le_antisymm hpA (not_lt.1 fun h ↦ hp2 (hs2 p hpp hBp h)))
    (fun x ↦ b x / x) (div_nonneg hbA (by linarith))
  have h3 : b B / B ≤ b A * pntE B := by
    calc b B / B ≤ b A / B := by gcongr
      _ = b A * B⁻¹ := div_eq_mul_inv _ _
      _ ≤ b A * pntE B := mul_le_mul_of_nonneg_left (inv_le_pntE hB) hbA
  have h4 : b A / A ≤ b A * pntE B := by
    calc b A / A ≤ b A / B := by gcongr
      _ = b A * B⁻¹ := div_eq_mul_inv _ _
      _ ≤ b A * pntE B := mul_le_mul_of_nonneg_left (inv_le_pntE hB) hbA
  have hdiff := sum_sdiff_sub_sum_sdiff (s₁ := primesIoc B A) (s₂ := s) (f := fun p : ℕ ↦ b p / p)
  have hI := hC b A B hB hBA hb hb0
  rw [abs_le] at hI ⊢
  constructor <;> nlinarith [pntE_pos B]
end IwaniecLinearSieve
end
section
open Real Filter Topology
namespace IwaniecLinearSieve
theorem log_le_div_eight {K : ℝ} (hK : 256 ≤ K) : log K ≤ K / 8 := by
  have hK0 : 0 < K := by linarith
  have hs : 16 ≤ √K := (le_sqrt (by norm_num) hK0.le).2 (by linarith)
  have h1 : log K = 2 * log √K := by rw [log_sqrt hK0.le]; ring
  have h2 := log_le_sub_one_of_pos (sqrt_pos.2 hK0)
  have h3 := sq_sqrt hK0.le
  nlinarith
theorem nth_prime_le (hPNT : StrongPNTProp) : ∃ C, ∀ r : ℕ, 2 ≤ r → (Nat.nth Nat.Prime (r - 1) : ℝ) ≤ C * r * log r := by
  obtain ⟨Cθ, -, hθ⟩ := (theta_asymp hPNT)
  obtain ⟨X, hX⟩ := eventually_atTop.1
    ((by simpa using tendsto_pntE.const_mul Cθ :
      Tendsto (fun x ↦ Cθ * pntE x) atTop (𝓝 0)).eventually (eventually_lt_nhds one_half_pos))
  set K := max X 256
  have hK : 256 ≤ K := le_max_right _ _
  refine ⟨K, fun r hr ↦ ?_⟩
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hlogr : 1 / 2 ≤ log r := by
    have := log_two_gt_d9
    have := log_le_log (by norm_num) hr'
    linarith
  set x := K * r * log r with hx
  have hxK : K ≤ x := by
    rw [hx, mul_assoc]
    refine le_mul_of_one_le_right (by linarith) ?_
    nlinarith
  have hx2 : 2 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hθx : x / 2 ≤ Chebyshev.theta x := by
    have h1 := hθ x hx2
    have h2 := hX x ((le_max_left _ _).trans hxK)
    rw [abs_le] at h1
    nlinarith
  have hlogx : log x ≤ K / 8 + 2 * log r := by
    have hlr0 : 0 < log r := by linarith
    rw [hx, log_mul (by positivity) hlr0.ne', log_mul (by positivity) (by positivity)]
    have h1 := log_le_div_eight hK
    have h2 := log_le_sub_one_of_pos hlr0
    linarith
  have hlogx0 : 0 < log x := log_pos (by linarith)
  have hπ : (r : ℝ) ≤ Nat.primeCounting ⌊x⌋₊ := by
    have h1 := Chebyshev.theta_le_pi_mul_log' x
    have h2 : (r : ℝ) * (2 * log x) ≤ x := by
      rw [hx]
      have : 2 * log x ≤ K * log r := by nlinarith
      nlinarith
    nlinarith
  have hcount : r - 1 < Nat.count Nat.Prime (⌊x⌋₊ + 1) := by
    have : r ≤ Nat.primeCounting ⌊x⌋₊ := by exact_mod_cast hπ
    simp only [Nat.primeCounting, Nat.primeCounting'] at this
    omega
  have hnth := Nat.nth_lt_of_lt_count hcount
  calc (Nat.nth Nat.Prime (r - 1) : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast Nat.lt_succ_iff.1 hnth
    _ ≤ x := Nat.floor_le hx0.le
end IwaniecLinearSieve
end
section
end
section
open Real Set Filter Topology MeasureTheory Finset
namespace IwaniecLinearSieve
theorem integral_comp_log_div {F : ℝ → ℝ} {y α β : ℝ} (hy : 1 < y) (hα : 0 < α) (hαβ : α ≤ β) :
    ∫ u in y ^ (1 / β)..y ^ (1 / α), F (log y / log u) / (u * log u) =
      ∫ t in α..β, F t / t := by
  set L := log y
  have hL : 0 < L := log_pos hy
  have hy0 : 0 < y := by linarith
  set f : ℝ → ℝ := fun t => exp (L * t⁻¹)
  set f' : ℝ → ℝ := fun t => exp (L * t⁻¹) * (L * -(t ^ 2)⁻¹)
  have hpos : ∀ x ∈ uIcc α β, 0 < x := fun x hx => by
    rw [uIcc_of_le hαβ] at hx; linarith [hx.1]
  have hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x := fun x hx =>
    ((hasDerivAt_inv hx.ne').const_mul L).exp
  have hfA : ∀ γ, f γ = y ^ (1 / γ) := fun γ => by
    simp only [f]; rw [rpow_def_of_pos hy0, one_div]
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos (a := α) (b := β) (f := f)
    (f' := f') (g := fun u => F (L / log u) / (u * log u))
    (continuousOn_of_forall_continuousAt fun x hx => (hderiv x (hpos x hx)).continuousAt)
    (fun x hx => hderiv x (by
      rw [min_eq_left hαβ] at hx; linarith [hx.1]))
    (fun x hx => by
      simp only [f']
      rw [mul_neg]
      exact mul_nonpos_of_nonneg_of_nonpos (exp_pos _).le
        (neg_nonpos.2 (mul_nonneg hL.le (by positivity))))
  rw [hfA, hfA, intervalIntegral.integral_symm (y ^ (1 / β)) (y ^ (1 / α))] at h
  have hcongr : ∫ x in α..β, ((fun u => F (L / log u) / (u * log u)) ∘ f) x * f' x =
      ∫ x in α..β, -(F x / x) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    have hx0 := hpos x hx
    simp only [Function.comp, f, f', log_exp]
    have : L / (L * x⁻¹) = x := by field_simp
    rw [this]
    have := exp_pos (L * x⁻¹)
    field_simp
  rw [hcongr, intervalIntegral.integral_neg, neg_inj] at h
  exact h.symm
theorem log_rpow_one_div {y : ℝ} (hy : 0 < y) (γ : ℝ) : log (y ^ (1 / γ)) = log y / γ := by
  rw [log_rpow hy]; ring
theorem div_log_mem_Icc {y α β u : ℝ} (hy : 1 < y) (hα : 0 < α) (hαβ : α ≤ β)
    (hu : u ∈ Icc (y ^ (1 / β)) (y ^ (1 / α))) : 0 < log u ∧ log y / log u ∈ Icc α β := by
  have hL : 0 < log y := log_pos hy
  have hy0 : 0 < y := by linarith
  have hβ : 0 < β := hα.trans_le hαβ
  have hB0 : 0 < y ^ (1 / β) := rpow_pos_of_pos hy0 _
  have hu0 : 0 < u := hB0.trans_le hu.1
  have h1 : log y / β ≤ log u := log_rpow_one_div hy0 β ▸ log_le_log hB0 hu.1
  have h2 : log u ≤ log y / α := log_rpow_one_div hy0 α ▸ log_le_log hu0 hu.2
  have hlu : 0 < log u := (div_pos hL hβ).trans_le h1
  refine ⟨hlu, ?_, ?_⟩
  · rw [le_div_iff₀ hlu]; rw [le_div_iff₀ hα] at h2; linarith
  · rw [div_le_iff₀ hlu]; rw [div_le_iff₀ hβ] at h1; linarith
theorem lemma13_param (hPNT : StrongPNTProp) : ∃ C, 0 ≤ C ∧ ∀ (F : ℝ → ℝ) (y α β : ℝ) (S : Finset ℕ), 1 < y → 0 < α →
    α ≤ β → 2 ≤ y ^ (1 / β) → AntitoneOn F (Icc α β) → (∀ t ∈ Icc α β, 0 ≤ F t) →
    (∀ p ∈ S, p.Prime ∧ y ^ (1 / β) ≤ p ∧ (p : ℝ) ≤ y ^ (1 / α)) →
    (∀ p : ℕ, p.Prime → y ^ (1 / β) < p → (p : ℝ) < y ^ (1 / α) → p ∈ S) →
    |∑ p ∈ S, F (log y / log p) / p - ∫ t in α..β, F t / t| ≤ C * F α * pntE (y ^ (1 / β)) := by
  obtain ⟨C, hC0, hC⟩ := (lemma13_mono_of_subset hPNT)
  refine ⟨C, hC0, fun F y α β S hy hα hαβ hB hF hF0 hS1 hS2 => ?_⟩
  have hL : 0 < log y := log_pos hy
  have hy0 : 0 < y := by linarith
  have hBA : y ^ (1 / β) ≤ y ^ (1 / α) :=
    rpow_le_rpow_of_exponent_le hy.le (one_div_le_one_div_of_le hα hαβ)
  have hmono : MonotoneOn (fun u => F (log y / log u)) (Icc (y ^ (1 / β)) (y ^ (1 / α))) := by
    intro u hu v hv huv
    obtain ⟨hlu, hmu⟩ := div_log_mem_Icc hy hα hαβ hu
    obtain ⟨hlv, hmv⟩ := div_log_mem_Icc hy hα hαβ hv
    exact hF hmv hmu (div_le_div_of_nonneg_left hL.le hlu
      (log_le_log (by linarith [hu.1]) huv))
  have h := hC (fun u => F (log y / log u)) (y ^ (1 / α)) (y ^ (1 / β)) S hB hBA hmono
    (fun u hu => hF0 _ (div_log_mem_Icc hy hα hαβ hu).2) hS1 hS2
  rwa [integral_comp_log_div hy hα hαβ, log_rpow_one_div hy0, div_div_cancel₀ hL.ne'] at h
theorem log_div_prime_eq {y : ℝ} {p : ℕ} (hy : 0 < y) (hp : 1 < p) :
    log (y / p) = log p * (log y / log p - 1) := by
  have hlp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp)
  rw [log_div hy.ne' (by positivity), mul_sub, mul_div_cancel₀ _ hlp.ne', mul_one]
theorem le_div_log_of_le_rpow {y α : ℝ} {p : ℕ} (hy : 1 < y) (hα : 0 < α) (hp : 1 < p)
    (hpA : (p : ℝ) ≤ y ^ (1 / α)) : α ≤ log y / log p := by
  have hlp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp)
  have h := log_le_log (by positivity) hpA
  rw [log_rpow_one_div (by linarith)] at h
  rw [le_div_iff₀ hlp]; rw [le_div_iff₀ hα] at h; linarith
theorem antitoneOn_div_sub_one : AntitoneOn (fun t : ℝ => t / (t - 1)) (Ioi 1) := by
  intro u hu v hv huv
  have hu1 : 0 < u - 1 := by linarith [hu.out]
  have hv1 : 0 < v - 1 := by linarith [hv.out]
  simp only
  rw [div_le_div_iff₀ hv1 hu1]; nlinarith
theorem cor1 (hPNT : StrongPNTProp) : ∃ C, 0 ≤ C ∧ ∀ (M : ℝ → ℝ) (y α β : ℝ), 1 < y → 2 ≤ α → α ≤ β →
    2 ≤ y ^ (1 / β) → AntitoneOn M (Icc (α - 1) (β - 1)) → (∀ t ∈ Icc (α - 1) (β - 1), 0 ≤ M t) →
    |∑ p ∈ (primesLT (y ^ (1 / α))).filter (fun p : ℕ => y ^ (1 / β) ≤ p),
        M (log y / log p - 1) / (p * log (y / p)) -
      (∫ t in α..β, M (t - 1) / (t - 1)) / log y| ≤
      C * M (α - 1) * pntE (y ^ (1 / β)) / log y := by
  obtain ⟨C, hC0, hC⟩ := (lemma13_param hPNT)
  refine ⟨2 * C, by linarith, fun M y α β hy hα hαβ hB hM hM0 => ?_⟩
  have hL : 0 < log y := log_pos hy
  have hy0 : 0 < y := by linarith
  set F : ℝ → ℝ := fun t => M (t - 1) * (t / (t - 1)) / log y with hFdef
  have hMt : AntitoneOn (fun t => M (t - 1)) (Icc α β) := fun u hu v hv huv =>
    hM ⟨by linarith [hu.1], by linarith [hu.2]⟩ ⟨by linarith [hv.1], by linarith [hv.2]⟩
      (by linarith)
  have hF : AntitoneOn F (Icc α β) := by
    have := antitoneOn_mul_of_nonneg hMt (antitoneOn_div_sub_one.mono fun t ht =>
      show (1 : ℝ) < t by linarith [ht.1])
      (fun t ht => hM0 _ ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      fun t ht => div_nonneg (by linarith [ht.1]) (by linarith [ht.1])
    exact fun u hu v hv huv => div_le_div_of_nonneg_right (this hu hv huv) hL.le
  have hF0 : ∀ t ∈ Icc α β, 0 ≤ F t := fun t ht =>
    div_nonneg (mul_nonneg (hM0 _ ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      (div_nonneg (by linarith [ht.1]) (by linarith [ht.1]))) hL.le
  have h := hC F y α β ((primesLT (y ^ (1 / α))).filter (fun p : ℕ => y ^ (1 / β) ≤ p)) hy
    (by linarith) hαβ hB hF hF0
    (fun p hp => by
      rw [mem_filter, mem_primesLT] at hp
      exact ⟨hp.1.1, hp.2, hp.1.2.le⟩)
    (fun p hp h1 h2 => by
      rw [mem_filter, mem_primesLT]; exact ⟨⟨hp, h2⟩, h1.le⟩)
  have hsum : ∑ p ∈ (primesLT (y ^ (1 / α))).filter (fun p : ℕ => y ^ (1 / β) ≤ p),
      F (log y / log p) / p = ∑ p ∈ (primesLT (y ^ (1 / α))).filter
        (fun p : ℕ => y ^ (1 / β) ≤ p), M (log y / log p - 1) / (p * log (y / p)) := by
    refine sum_congr rfl fun p hp => ?_
    rw [mem_filter, mem_primesLT] at hp
    have hp1 := hp.1.1.one_lt
    have hlp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp1)
    have ht := le_div_log_of_le_rpow hy (by linarith) hp1 hp.1.2.le
    rw [log_div_prime_eq hy0 hp1]
    simp only [F]
    have : (p : ℝ) ≠ 0 := by positivity
    field_simp
  have hint : ∫ t in α..β, F t / t = (∫ t in α..β, M (t - 1) / (t - 1)) / log y := by
    rw [← intervalIntegral.integral_div]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hαβ] at ht
    have : 0 < t := by linarith [ht.1]
    have : t - 1 ≠ 0 := by linarith [ht.1]
    simp only [F]
    field_simp
  have hFα : F α ≤ 2 * M (α - 1) / log y := by
    have hMα := hM0 (α - 1) ⟨le_rfl, by linarith⟩
    have : α / (α - 1) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    simp only [F]
    exact div_le_div_of_nonneg_right (by nlinarith) hL.le
  rw [hsum, hint] at h
  refine h.trans ?_
  calc C * F α * pntE (y ^ (1 / β)) ≤ C * (2 * M (α - 1) / log y) * pntE (y ^ (1 / β)) := by
        have := pntE_pos (y ^ (1 / β))
        gcongr
    _ = 2 * C * M (α - 1) * pntE (y ^ (1 / β)) / log y := by ring
theorem cor1_le (hPNT : StrongPNTProp) : ∃ C, 0 ≤ C ∧ ∀ (M : ℝ → ℝ) (y α β : ℝ), 1 < y → 2 ≤ α → α ≤ β →
    2 ≤ y ^ (1 / β) → AntitoneOn M (Icc (α - 1) (β - 1)) → (∀ t ∈ Icc (α - 1) (β - 1), 0 ≤ M t) →
    ∑ p ∈ (primesLT (y ^ (1 / α))).filter (fun p : ℕ => y ^ (1 / β) ≤ p),
        M (log y / log p - 1) / (p * log (y / p)) ≤
      (∫ t in α..β, M (t - 1) / (t - 1)) / log y + C * M (α - 1) * pntE (y ^ (1 / β)) / log y := by
  obtain ⟨C, hC0, hC⟩ := (cor1 hPNT)
  exact ⟨C, hC0, fun M y α β hy hα hαβ hB hM hM0 => by
    linarith [(abs_le.1 (hC M y α β hy hα hαβ hB hM hM0)).2]⟩
theorem errMaj_shift_sq_le (lower lower' : Bool) {s : ℝ} (hs : 2 ≤ s) :
    errMaj lower' (s - 1) * (s ^ 2 / (s - 1) ^ 2) ≤ 32 * s ^ 2 * errMaj lower s := by
  have hs1 : 0 < s - 1 := by linarith
  have hq : s ^ 2 / (s - 1) ^ 2 ≤ 4 := by
    rw [div_le_iff₀ (pow_pos hs1 2)]; nlinarith
  have hq0 : 0 ≤ s ^ 2 / (s - 1) ^ 2 := by positivity
  have hG' := errMaj_pos lower' (s - 1)
  have hG := (errMaj_mem lower s).1
  have h8 : errMaj lower' (s - 1) ≤ 8 * s ^ 2 * errMaj lower s := by
    rcases le_total 3 s with h3 | h3
    · have := (errMaj_mem lower' (s - 1)).2
      have := bigM_sub_one_lt h3
      nlinarith
    · have := errMaj_le_two lower' (s - 1)
      have hB : bigM 3 ≤ bigM s := bigM_antitone h3
      have := bigM_three_gt
      have : 1 / 2 ≤ errMaj lower s := by linarith
      nlinarith
  calc errMaj lower' (s - 1) * (s ^ 2 / (s - 1) ^ 2) ≤ 8 * s ^ 2 * errMaj lower s * 4 :=
        mul_le_mul h8 hq hq0 (by have := errMaj_pos lower s; positivity)
    _ = 32 * s ^ 2 * errMaj lower s := by ring
theorem growth_le_delta {y t a : ℝ} (ht : 1 ≤ t) (hta : t ≤ a) :
    (1 + t ^ 2 * log t ^ 5 / log y ^ 2) ^ (5 * (t - 1)) ≤ delta a y := by
  have hlt := log_nonneg ht
  have hla : log t ≤ log a := log_le_log (by linarith) hta
  have hx0 := lsx_nonneg (log y) ht
  have hxa : t ^ 2 * log t ^ 5 / log y ^ 2 ≤ a ^ 2 * log a ^ 5 / log y ^ 2 := by
    gcongr
  rw [delta]
  calc (1 + t ^ 2 * log t ^ 5 / log y ^ 2) ^ (5 * (t - 1))
      ≤ (1 + a ^ 2 * log a ^ 5 / log y ^ 2) ^ (5 * (t - 1)) :=
        rpow_le_rpow (by linarith) (by linarith) (by linarith)
    _ ≤ _ := rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
theorem cor3_summand_le {G : ℝ → ℝ} {y : ℝ} {p : ℕ} (hy : 1 < y) (hp : 1 < p)
    (ht : 2 ≤ log y / log p) (hG : 0 ≤ G (log y / log p - 1)) :
    delta (log y / log p - 1) (y / p) * G (log y / log p - 1) / (p * log (y / p) ^ 2) ≤
      (1 + (log y / log p) ^ 2 * log (log y / log p) ^ 5 / log y ^ 2) ^
        (5 * (log y / log p - 1)) * G (log y / log p - 1) *
        ((log y / log p) ^ 2 / (log y / log p - 1) ^ 2) / log y ^ 2 / p := by
  have hlp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp)
  have hy0 : 0 < y := by linarith
  have hyp := log_div_prime_eq hy0 hp
  set t := log y / log p with htdef
  have hLt : log y = log p * t := by rw [htdef]; field_simp
  have ht1 : 0 < t - 1 := by linarith
  have hp0 : (0 : ℝ) < p := by positivity
  have hb : (t - 1) ^ 2 * log (t - 1) ^ 5 / log (y / p) ^ 2 =
      t ^ 2 * log (t - 1) ^ 5 / log y ^ 2 := by
    rw [hyp, hLt]; field_simp
  have hl1 : 0 ≤ log (t - 1) := log_nonneg (by linarith)
  have hl2 : log (t - 1) ≤ log t := log_le_log ht1 (by linarith)
  have hbase : t ^ 2 * log (t - 1) ^ 5 / log y ^ 2 ≤ t ^ 2 * log t ^ 5 / log y ^ 2 := by
    gcongr
  have hb0 : 0 ≤ t ^ 2 * log (t - 1) ^ 5 / log y ^ 2 := by positivity
  rw [delta, hb]
  have hrest : G (t - 1) / (p * log (y / p) ^ 2) =
      G (t - 1) * (t ^ 2 / (t - 1) ^ 2) / log y ^ 2 / p := by
    rw [hyp, hLt]; field_simp
  calc (1 + t ^ 2 * log (t - 1) ^ 5 / log y ^ 2) ^ (5 * (t - 1)) * G (t - 1) /
        (p * log (y / p) ^ 2)
      = (1 + t ^ 2 * log (t - 1) ^ 5 / log y ^ 2) ^ (5 * (t - 1)) *
          (G (t - 1) / (p * log (y / p) ^ 2)) := by ring
    _ ≤ (1 + t ^ 2 * log t ^ 5 / log y ^ 2) ^ (5 * (t - 1)) *
          (G (t - 1) / (p * log (y / p) ^ 2)) := by
        gcongr
    _ = _ := by rw [hrest]; ring
theorem errMaj_not_eq_majG (lower : Bool) : errMaj (!lower) = majG (if lower then 1 else 0) := by
  cases lower
  · simp [majG_of_even (⟨0, rfl⟩ : Even 0)]
  · simp [majG_of_odd odd_one]
theorem errMaj_eq_majG_succ (lower : Bool) :
    errMaj lower = majG ((if lower then 1 else 0) + 1) := by
  cases lower
  · simp [majG_of_odd odd_one]
  · simp [majG_of_even (⟨1, rfl⟩ : Even 2)]
theorem cor3_large (hPNT : StrongPNTProp) : ∃ C, 0 ≤ C ∧ ∀ (lower : Bool) (y s b : ℝ) (S : Finset ℕ), 1 < y →
    exp 32 ≤ s → s ≤ b → 2 ≤ y ^ (1 / b) → b ^ 2 * log b ^ 4 ≤ log y ^ 2 / 160 →
    (∀ p ∈ S, p.Prime ∧ y ^ (1 / b) ≤ p ∧ (p : ℝ) ≤ y ^ (1 / s)) →
    (∀ p : ℕ, p.Prime → y ^ (1 / b) < p → (p : ℝ) < y ^ (1 / s) → p ∈ S) →
    ∑ p ∈ S, delta (log y / log p - 1) (y / p) * errMaj (!lower) (log y / log p - 1) /
        (p * log (y / p) ^ 2) ≤
      delta s y * errMaj lower s / log y ^ 2 * (1 + C * b ^ 2 * pntE (y ^ (1 / b))) := by
  obtain ⟨C, hC0, hC⟩ := (lemma13_param hPNT)
  refine ⟨32 * C, by linarith, fun lower y s b S hy hs hsb hB hb hS1 hS2 => ?_⟩
  set r : ℕ := if lower then 1 else 0
  have hG' := errMaj_not_eq_majG lower
  have hGs : errMaj lower s = majG (r + 1) s := by rw [errMaj_eq_majG_succ]
  have hL : 0 < log y := log_pos hy
  have hL2 : 0 < log y ^ 2 := by positivity
  have hs4 := four_lt_of_exp_le hs
  set Φ : ℝ → ℝ := fun t => (1 + t ^ 2 * log t ^ 5 / log y ^ 2) ^ (5 * (t - 1)) * majG r (t - 1) *
    (t ^ 2 / (t - 1) ^ 2) / log y ^ 2 with hΦdef
  have hΦ : AntitoneOn Φ (Icc s b) := fun u hu v hv huv =>
    div_le_div_of_nonneg_right (antitoneOn_cor3Weight r hs hb hu hv huv) hL2.le
  have hΦ0 : ∀ t ∈ Icc s b, 0 ≤ Φ t := fun t ht => by
    have ht1 : (1 : ℝ) ≤ t := by linarith [ht.1]
    have := lsx_nonneg (log y) ht1
    have := majG_pos r (t - 1)
    exact div_nonneg (mul_nonneg (mul_nonneg (rpow_pos_of_pos (by linarith) _).le this.le)
      (by positivity)) hL2.le
  have h13 := hC Φ y s b S hy (by linarith) hsb hB hΦ hΦ0 hS1 hS2
  have hsum : ∑ p ∈ S, delta (log y / log p - 1) (y / p) * errMaj (!lower) (log y / log p - 1) /
      (p * log (y / p) ^ 2) ≤ ∑ p ∈ S, Φ (log y / log p) / p := by
    refine sum_le_sum fun p hp => ?_
    obtain ⟨hpp, hpB, hpA⟩ := hS1 p hp
    have ht := (div_log_mem_Icc hy (by linarith) hsb ⟨hpB, hpA⟩).2
    rw [hG']
    exact cor3_summand_le hy hpp.one_lt (by linarith [ht.1]) (majG_pos _ _).le
  have hint : ∫ t in s..b, Φ t / t = (∫ t in s..b, (1 + t ^ 2 * log t ^ 5 / log y ^ 2) ^
      (5 * (t - 1)) * majG r (t - 1) * t / (t - 1) ^ 2) / log y ^ 2 := by
    rw [← intervalIntegral.integral_div]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hsb] at ht
    have : t ≠ 0 := by linarith [ht.1]
    have : t - 1 ≠ 0 := by linarith [ht.1]
    simp only [Φ]
    field_simp
  have h11 := lemma11 r hs hsb hb
  have hΦs : Φ s ≤ delta s y * (32 * s ^ 2 * majG (r + 1) s) / log y ^ 2 := by
    have h1 := growth_le_delta (y := y) (by linarith : (1 : ℝ) ≤ s) le_rfl
    have h2 := errMaj_shift_sq_le lower (!lower) (by linarith : (2 : ℝ) ≤ s)
    rw [hG', hGs] at h2
    have h3 : 0 ≤ majG r (s - 1) * (s ^ 2 / (s - 1) ^ 2) := by
      have := majG_pos r (s - 1); positivity
    show (1 + s ^ 2 * log s ^ 5 / log y ^ 2) ^ (5 * (s - 1)) * majG r (s - 1) *
      (s ^ 2 / (s - 1) ^ 2) / log y ^ 2 ≤ _
    rw [mul_assoc _ (majG r (s - 1))]
    exact div_le_div_of_nonneg_right (mul_le_mul h1 h2 h3 (delta_pos (by linarith) y).le)
      hL2.le
  rw [abs_le] at h13
  rw [hint] at h13
  have hpE := pntE_pos (y ^ (1 / b))
  have hδ := delta_pos (by linarith : (1 : ℝ) ≤ s) y
  have hG := majG_pos (r + 1) s
  have hsb2 : s ^ 2 ≤ b ^ 2 := by gcongr
  rw [hGs]
  have e1 : C * Φ s * pntE (y ^ (1 / b)) ≤
      C * (delta s y * (32 * s ^ 2 * majG (r + 1) s) / log y ^ 2) * pntE (y ^ (1 / b)) := by
    gcongr
  have e2 : C * (delta s y * (32 * s ^ 2 * majG (r + 1) s) / log y ^ 2) * pntE (y ^ (1 / b)) ≤
      delta s y * majG (r + 1) s / log y ^ 2 * (32 * C * b ^ 2 * pntE (y ^ (1 / b))) := by
    have h0 : 0 ≤ C * delta s y * majG (r + 1) s * pntE (y ^ (1 / b)) * 32 :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC0 hδ.le) hG.le) hpE.le) (by norm_num)
    calc C * (delta s y * (32 * s ^ 2 * majG (r + 1) s) / log y ^ 2) * pntE (y ^ (1 / b))
        = C * delta s y * majG (r + 1) s * pntE (y ^ (1 / b)) * 32 * s ^ 2 / log y ^ 2 := by
          ring
      _ ≤ C * delta s y * majG (r + 1) s * pntE (y ^ (1 / b)) * 32 * b ^ 2 / log y ^ 2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsb2 h0) hL2.le
      _ = _ := by ring
  have e3 : (∫ t in s..b, (1 + t ^ 2 * log t ^ 5 / log y ^ 2) ^ (5 * (t - 1)) *
      majG r (t - 1) * t / (t - 1) ^ 2) / log y ^ 2 ≤ delta s y * majG (r + 1) s / log y ^ 2 :=
    div_le_div_of_nonneg_right h11.le hL2.le
  calc _ ≤ ∑ p ∈ S, Φ (log y / log p) / p := hsum
    _ ≤ _ := by nlinarith
theorem cor3_small (hPNT : StrongPNTProp) : ∃ C, 0 ≤ C ∧ ∀ (lower : Bool) (y s a : ℝ) (S : Finset ℕ), 1 < y →
    errLower lower ≤ s → s ≤ a → a ≤ exp 32 → 2 ≤ y ^ (1 / a) →
    (∀ p ∈ S, p.Prime ∧ y ^ (1 / a) ≤ p ∧ (p : ℝ) ≤ y ^ (1 / s)) →
    (∀ p : ℕ, p.Prime → y ^ (1 / a) < p → (p : ℝ) < y ^ (1 / s) → p ∈ S) →
    ∑ p ∈ S, delta (log y / log p - 1) (y / p) * errMaj (!lower) (log y / log p - 1) /
        (p * log (y / p) ^ 2) ≤
      delta (exp 32) y / log y ^ 2 *
        (errMaj lower s - errMaj lower a + C * s ^ 2 * errMaj lower s * pntE (y ^ (1 / a))) := by
  obtain ⟨C, hC0, hC⟩ := (lemma13_param hPNT)
  refine ⟨32 * C, by linarith, fun lower y s a S hy hs hsa ha hB hS1 hS2 => ?_⟩
  have hs2 : 2 ≤ s := (two_le_errLower lower).trans hs
  have hL : 0 < log y := log_pos hy
  have hL2 : 0 < log y ^ 2 := by positivity
  set F : ℝ → ℝ := fun t => errMaj (!lower) (t - 1) * (t ^ 2 / (t - 1) ^ 2) with hFdef
  have hF : AntitoneOn F (Icc s a) :=
    antitoneOn_mul_of_nonneg (fun u _ v _ huv => errMaj_antitone _ (by linarith))
      (antitoneOn_sq_div_sq_sub_one.mono fun t ht => show (1 : ℝ) < t by linarith [ht.1])
      (fun t _ => (errMaj_pos _ _).le) fun t _ => by positivity
  have hF0 : ∀ t ∈ Icc s a, 0 ≤ F t := fun t _ => by
    have := errMaj_pos (!lower) (t - 1); positivity
  have h13 := hC F y s a S hy (by linarith) hsa hB hF hF0 hS1 hS2
  have hδ0 : 0 ≤ delta (exp 32) y :=
    (delta_pos (by linarith [four_lt_of_exp_le (le_refl (exp 32))]) y).le
  have hsum : ∑ p ∈ S, delta (log y / log p - 1) (y / p) * errMaj (!lower) (log y / log p - 1) /
      (p * log (y / p) ^ 2) ≤ delta (exp 32) y / log y ^ 2 * ∑ p ∈ S, F (log y / log p) / p := by
    rw [mul_sum]
    refine sum_le_sum fun p hp => ?_
    obtain ⟨hpp, hpB, hpA⟩ := hS1 p hp
    have ht := (div_log_mem_Icc hy (by linarith) hsa ⟨hpB, hpA⟩).2
    refine (cor3_summand_le hy hpp.one_lt (by linarith [ht.1]) (errMaj_pos _ _).le).trans ?_
    have hg := growth_le_delta (y := y) (by linarith [ht.1] : (1 : ℝ) ≤ log y / log p)
      (ht.2.trans ha)
    have hF1 : 0 ≤ F (log y / log p) := hF0 _ ht
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    calc _ = (1 + (log y / log p) ^ 2 * log (log y / log p) ^ 5 / log y ^ 2) ^
            (5 * (log y / log p - 1)) * F (log y / log p) / log y ^ 2 / p := by
          simp only [F]; ring
      _ ≤ delta (exp 32) y * F (log y / log p) / log y ^ 2 / p := by gcongr
      _ = _ := by ring
  have hint : ∫ t in s..a, F t / t = errMaj lower s - errMaj lower a := by
    rw [← integral_errMaj_shift lower hs hsa]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hsa] at ht
    have : t ≠ 0 := by linarith [ht.1]
    have : t - 1 ≠ 0 := by linarith [ht.1]
    simp only [F]
    field_simp
  have hFs : F s ≤ 32 * s ^ 2 * errMaj lower s := errMaj_shift_sq_le lower (!lower) hs2
  rw [abs_le, hint] at h13
  have hpE := pntE_pos (y ^ (1 / a))
  have hmain : ∑ p ∈ S, F (log y / log p) / p ≤
      errMaj lower s - errMaj lower a + 32 * C * s ^ 2 * errMaj lower s * pntE (y ^ (1 / a)) := by
    have : C * F s * pntE (y ^ (1 / a)) ≤
        C * (32 * s ^ 2 * errMaj lower s) * pntE (y ^ (1 / a)) := by gcongr
    linarith [h13.2]
  calc _ ≤ _ := hsum
    _ ≤ _ := mul_le_mul_of_nonneg_left hmain (div_nonneg hδ0 hL2.le)
theorem rpow_one_div_le_rpow_one_div {y u v : ℝ} (hy : 1 ≤ y) (hu : 0 < u) (huv : u ≤ v) :
    y ^ (1 / v) ≤ y ^ (1 / u) :=
  rpow_le_rpow_of_exponent_le hy (one_div_le_one_div_of_le hu huv)
theorem cor3_primesLT (hPNT : StrongPNTProp) : ∃ C, 0 ≤ C ∧ ∀ (lower : Bool) (y s b : ℝ), 1 < y →
    errLower lower ≤ s → exp 32 ≤ b → 2 ≤ y ^ (1 / b) → b ^ 2 * log b ^ 4 ≤ log y ^ 2 / 160 →
    ∑ p ∈ (primesLT (y ^ (1 / s))).filter (fun p : ℕ => y ^ (1 / b) ≤ p),
        delta (log y / log p - 1) (y / p) * errMaj (!lower) (log y / log p - 1) /
          (p * log (y / p) ^ 2) ≤
      delta (max s (exp 32)) y * errMaj lower s / log y ^ 2 *
        (1 + C * b ^ 2 * pntE (y ^ (1 / b))) := by
  obtain ⟨C₁, hC₁, h₁⟩ := (cor3_large hPNT)
  obtain ⟨C₂, hC₂, h₂⟩ := (cor3_small hPNT)
  refine ⟨C₁ + C₂, by linarith, fun lower y s b hy hs hb32 hB hb => ?_⟩
  set s₀ := exp 32 with hs₀
  have hs2 : 2 ≤ s := (two_le_errLower lower).trans hs
  have hs₀4 : 4 < s₀ := four_lt_of_exp_le le_rfl
  have hL2 : 0 < log y ^ 2 := by have := log_pos hy; positivity
  have hpE := pntE_pos (y ^ (1 / b))
  have hGs := errMaj_pos lower s
  set S := (primesLT (y ^ (1 / s))).filter (fun p : ℕ => y ^ (1 / b) ≤ p) with hS
  have hRHS : 0 ≤ delta (max s s₀) y * errMaj lower s / log y ^ 2 *
      (1 + (C₁ + C₂) * b ^ 2 * pntE (y ^ (1 / b))) := by
    have := delta_pos (by linarith [le_max_left s s₀] : (1 : ℝ) ≤ max s s₀) y
    have : 0 ≤ (C₁ + C₂) * b ^ 2 * pntE (y ^ (1 / b)) :=
      mul_nonneg (mul_nonneg (by linarith) (sq_nonneg b)) hpE.le
    positivity
  rcases lt_or_ge b s with hbs | hsb
  ·
    have hempty : S = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun p hp => ?_
      rw [hS, mem_filter, mem_primesLT] at hp
      have := rpow_one_div_le_rpow_one_div hy.le (by linarith) hbs.le
      linarith [hp.1.2, hp.2]
    rw [hempty, sum_empty]
    exact hRHS
  rcases le_total s₀ s with hs₀s | hss₀
  ·
    rw [max_eq_left hs₀s]
    refine (h₁ lower y s b S hy hs₀s hsb hB hb (fun p hp => ?_) fun p hp h1 h2 => ?_).trans ?_
    · rw [hS, mem_filter, mem_primesLT] at hp; exact ⟨hp.1.1, hp.2, hp.1.2.le⟩
    · rw [hS, mem_filter, mem_primesLT]; exact ⟨⟨hp, h2⟩, h1.le⟩
    · have := delta_pos (by linarith : (1 : ℝ) ≤ s) y
      gcongr
      linarith
  rw [max_eq_right hss₀]
  have hB₀ : y ^ (1 / b) ≤ y ^ (1 / s₀) := rpow_one_div_le_rpow_one_div hy.le (by linarith) hb32
  have hB₀s : y ^ (1 / s₀) ≤ y ^ (1 / s) := rpow_one_div_le_rpow_one_div hy.le (by linarith) hss₀
  rw [← sum_filter_add_sum_filter_not S (fun p : ℕ => y ^ (1 / s₀) ≤ p)]
  have e₁ := h₂ lower y s s₀ (S.filter fun p : ℕ => y ^ (1 / s₀) ≤ p) hy hs hss₀ le_rfl
    (by linarith) (fun p hp => by
      rw [mem_filter, hS, mem_filter, mem_primesLT] at hp
      exact ⟨hp.1.1.1, hp.2, hp.1.1.2.le⟩)
    (fun p hp h1 h2 => by
      rw [mem_filter, hS, mem_filter, mem_primesLT]
      exact ⟨⟨⟨hp, h2⟩, by linarith⟩, h1.le⟩)
  have e₂ := h₁ lower y s₀ b (S.filter fun p : ℕ => ¬ y ^ (1 / s₀) ≤ p) hy le_rfl hb32 hB hb
    (fun p hp => by
      rw [mem_filter, hS, mem_filter, mem_primesLT] at hp
      exact ⟨hp.1.1.1, hp.1.2, (not_le.1 hp.2).le⟩)
    (fun p hp h1 h2 => by
      rw [mem_filter, hS, mem_filter, mem_primesLT]
      exact ⟨⟨⟨hp, by linarith⟩, h1.le⟩, not_le.2 h2⟩)
  refine (add_le_add e₁ e₂).trans ?_
  have hδ := delta_pos (by linarith : (1 : ℝ) ≤ s₀) y
  have hG₀ := errMaj_pos lower s₀
  have hGG : errMaj lower s₀ ≤ errMaj lower s := errMaj_antitone lower hss₀
  have hpE₀ : pntE (y ^ (1 / s₀)) ≤ pntE (y ^ (1 / b)) :=
    pntE_le_pntE (by linarith) hB₀
  have hsb2 : s ^ 2 * pntE (y ^ (1 / s₀)) ≤ b ^ 2 * pntE (y ^ (1 / b)) := by
    have : s ^ 2 ≤ b ^ 2 := by gcongr
    exact mul_le_mul this hpE₀ (pntE_pos _).le (sq_nonneg b)
  have i1 : C₂ * errMaj lower s * (s ^ 2 * pntE (y ^ (1 / s₀))) ≤
      C₂ * errMaj lower s * (b ^ 2 * pntE (y ^ (1 / b))) :=
    mul_le_mul_of_nonneg_left hsb2 (mul_nonneg hC₂ hGs.le)
  have i2 : C₁ * (b ^ 2 * pntE (y ^ (1 / b))) * errMaj lower s₀ ≤
      C₁ * (b ^ 2 * pntE (y ^ (1 / b))) * errMaj lower s :=
    mul_le_mul_of_nonneg_left hGG (mul_nonneg hC₁ (mul_nonneg (sq_nonneg b) hpE.le))
  have hinner : errMaj lower s - errMaj lower s₀ +
      C₂ * s ^ 2 * errMaj lower s * pntE (y ^ (1 / s₀)) +
      errMaj lower s₀ * (1 + C₁ * b ^ 2 * pntE (y ^ (1 / b))) ≤
      errMaj lower s * (1 + (C₁ + C₂) * b ^ 2 * pntE (y ^ (1 / b))) := by
    nlinarith
  have hk : 0 ≤ delta s₀ y / log y ^ 2 := div_nonneg hδ.le hL2.le
  calc delta s₀ y / log y ^ 2 * (errMaj lower s - errMaj lower s₀ +
        C₂ * s ^ 2 * errMaj lower s * pntE (y ^ (1 / s₀))) +
      delta s₀ y * errMaj lower s₀ / log y ^ 2 * (1 + C₁ * b ^ 2 * pntE (y ^ (1 / b)))
      = delta s₀ y / log y ^ 2 * (errMaj lower s - errMaj lower s₀ +
        C₂ * s ^ 2 * errMaj lower s * pntE (y ^ (1 / s₀)) +
        errMaj lower s₀ * (1 + C₁ * b ^ 2 * pntE (y ^ (1 / b)))) := by ring
    _ ≤ delta s₀ y / log y ^ 2 *
        (errMaj lower s * (1 + (C₁ + C₂) * b ^ 2 * pntE (y ^ (1 / b)))) :=
        mul_le_mul_of_nonneg_left hinner hk
    _ = _ := by ring
theorem lt_rpow_one_div_max_three {y s x : ℝ} (hy : 1 < y) (hs : 0 < s) (hx : 0 ≤ x) :
    x < y ^ (1 / max s 3) ↔ x < y ^ (1 / s) ∧ x ^ 3 < y := by
  have h3 : x < y ^ (1 / (3 : ℝ)) ↔ x ^ 3 < y := by
    rw [one_div, lt_rpow_inv_iff_of_pos hx (by linarith) (by norm_num)]
    norm_cast
  rcases le_total s 3 with hs3 | hs3
  · rw [max_eq_right hs3, h3]
    have := rpow_one_div_le_rpow_one_div hy.le hs hs3
    constructor
    · intro h; exact ⟨lt_of_lt_of_le (h3.2 h) this, h⟩
    · exact fun h => h.2
  · rw [max_eq_left hs3]
    have := rpow_one_div_le_rpow_one_div hy.le (by norm_num) hs3
    exact ⟨fun h => ⟨h, h3.1 (lt_of_lt_of_le h this)⟩, fun h => h.1⟩
theorem cor3 (hPNT : StrongPNTProp) : ∃ C, 0 ≤ C ∧ ∀ (lower : Bool) (y s b : ℝ), 1 < y → sMin lower ≤ s →
    exp 32 ≤ b → 2 ≤ y ^ (1 / b) → b ^ 2 * log b ^ 4 ≤ log y ^ 2 / 160 →
    ∑ p ∈ (rosserPrimes lower y (y ^ (1 / s))).filter (fun p : ℕ => y ^ (1 / b) ≤ p),
        delta (log y / log p - 1) (y / p) * errMaj (!lower) (log y / log p - 1) /
          (p * log (y / p) ^ 2) ≤
      delta (max s (exp 32)) y * errMaj lower s / log y ^ 2 *
        (1 + C * b ^ 2 * pntE (y ^ (1 / b))) := by
  obtain ⟨C, hC0, hC⟩ := (cor3_primesLT hPNT)
  refine ⟨C, hC0, fun lower y s b hy hs hb32 hB hb => ?_⟩
  cases lower
  ·
    have hs1 : (1 : ℝ) ≤ s := hs
    have hset : (rosserPrimes false y (y ^ (1 / s))).filter (fun p : ℕ => y ^ (1 / b) ≤ p) =
        (primesLT (y ^ (1 / max s 3))).filter (fun p : ℕ => y ^ (1 / b) ≤ p) := by
      ext p
      simp only [mem_filter, mem_rosserPrimes, mem_primesLT, Bool.false_eq_true, false_or]
      rw [lt_rpow_one_div_max_three hy (by linarith) (Nat.cast_nonneg p)]
      tauto
    have hG : errMaj false (max s 3) = errMaj false s := by
      rcases le_total s 3 with h | h
      · rw [max_eq_right h, errMaj_false_of_le_three le_rfl, errMaj_false_of_le_three h]
      · rw [max_eq_left h]
    have hmax : max (max s 3) (exp 32) = max s (exp 32) := by
      have : (3 : ℝ) ≤ exp 32 := by linarith [four_lt_of_exp_le (le_refl (exp 32))]
      rw [max_assoc, max_eq_right this]
    rw [hset, ← hG, ← hmax]
    exact hC false y (max s 3) b hy (le_max_right _ _) hb32 hB hb
  · rw [rosserPrimes_true]
    exact hC true y s b hy hs hb32 hB hb
theorem cor3_xi (hPNT : StrongPNTProp) : ∃ C y₀ : ℝ, 0 ≤ C ∧ ∀ (lower : Bool) (y s : ℝ), y₀ ≤ y → sMin lower ≤ s →
    ∑ p ∈ (rosserPrimes lower y (y ^ (1 / s))).filter (fun p : ℕ => y ^ (1 / xi y) ≤ p),
        delta (log y / log p - 1) (y / p) * errMaj (!lower) (log y / log p - 1) /
          (p * log (y / p) ^ 2) ≤
      delta (max s (exp 32)) y * errMaj lower s / log y ^ 2 *
        (1 + C * xi y ^ 2 * pntE (y ^ (1 / xi y))) := by
  obtain ⟨C, hC0, hC⟩ := (cor3 hPNT)
  obtain ⟨y₀, hy₀⟩ := exists_xi_large
  refine ⟨C, y₀, hC0, fun lower y s hy hs => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hy₀ y hy
  exact hC lower y s (xi y) h1 hs h2 h4 h3
end IwaniecLinearSieve
end
section
open Finset Real
namespace IwaniecLinearSieve
def LeProdPrimesLT (r : ℕ) (y z : ℝ) : Prop :=
  ∀ T ⊆ primesLT z, #T = r → y ≤ ∏ p ∈ T, (p : ℝ)
variable {lower : Bool} {r : ℕ} {y z : ℝ} {p d : ℕ}
theorem one_le_prod_primes {T : Finset ℕ} {z : ℝ} (hT : T ⊆ primesLT z) :
    1 ≤ ∏ p ∈ T, (p : ℝ) :=
  one_le_prod₀ fun p hp ↦ by exact_mod_cast (prime_of_mem_primesLT (hT hp)).one_lt.le
theorem LeProdPrimesLT.div (h : LeProdPrimesLT (r + 1) y z) (hp : p ∈ primesLT z) :
    LeProdPrimesLT r (y / p) p := by
  intro T hT hcard
  have hpT : p ∉ T := fun h ↦ notMem_primesLT_self (hT h)
  have hpos : (0 : ℝ) < p := by exact_mod_cast (prime_of_mem_primesLT hp).pos
  have := h (insert p T) (insert_subset hp (hT.trans (primesLT_natCast_subset hp)))
    (by rw [card_insert_of_notMem hpT, hcard])
  rw [prod_insert hpT] at this
  rwa [div_le_iff₀' hpos]
theorem LeProdPrimesLT.succ (h : LeProdPrimesLT r y z) : LeProdPrimesLT (r + 1) y z := by
  intro T hT hcard
  obtain ⟨a, ha⟩ := card_pos.1 (by omega : 0 < #T)
  rw [← mul_prod_erase T _ ha]
  have h1 := h (T.erase a) ((erase_subset a T).trans hT) (by rw [card_erase_of_mem ha, hcard]; rfl)
  have h2 : (1 : ℝ) ≤ a := by exact_mod_cast (prime_of_mem_primesLT (hT ha)).one_lt.le
  have h3 := one_le_prod_primes ((erase_subset a T).trans hT)
  nlinarith
theorem LeProdPrimesLT.mono {s : ℕ} (h : LeProdPrimesLT r y z) (hrs : r ≤ s) :
    LeProdPrimesLT s y z := by
  induction s, hrs using Nat.le_induction with
  | base => exact h
  | succ s _ ih => exact ih.succ
theorem factorial_card_add_one_le_prod (T : Finset ℕ) (hT : ∀ n ∈ T, 2 ≤ n) :
    (#T + 1).factorial ≤ ∏ n ∈ T, n := by
  induction T using Finset.induction_on_max with
  | empty => simp
  | insert a T hlt ih =>
    have haT : a ∉ T := fun h ↦ lt_irrefl a (hlt a h)
    rw [card_insert_of_notMem haT, prod_insert haT, Nat.factorial_succ]
    have hsub : T ⊆ Ico 2 a := fun n hn ↦ mem_Ico.2 ⟨hT n (mem_insert_of_mem hn), hlt n hn⟩
    have hcard : #T + 2 ≤ a := by
      have := card_le_card hsub
      have h2 := hT a (mem_insert_self a T)
      simp only [Nat.card_Ico] at this
      omega
    exact Nat.mul_le_mul (by omega) (ih fun n hn ↦ hT n (mem_insert_of_mem hn))
theorem leProdPrimesLT_of_le_factorial (h : y ≤ (r + 1).factorial) : LeProdPrimesLT r y z := by
  intro T hT hcard
  refine h.trans ?_
  rw [← hcard]
  have h := (Nat.cast_le (α := ℝ)).2 (factorial_card_add_one_le_prod T fun n hn ↦
    (prime_of_mem_primesLT (hT hn)).two_le)
  push_cast at h
  exact h
theorem fail_succ_congr {a b : ℕ}
    (h : ∀ p ∈ rosserPrimes lower y z, fail (!lower) a (y / p) p = fail (!lower) b (y / p) p) :
    fail lower (a + 1) y z = fail lower (b + 1) y z := by
  cases lower <;> simp only [Bool.not_false, Bool.not_true] at h
  · rw [fail_false_succ, fail_false_succ]
    congr 1
    exact sum_congr rfl fun p hp ↦ by rw [h p hp]
  · rw [fail_true_succ, fail_true_succ]
    exact sum_congr rfl fun p hp ↦ by rw [h p (by simpa using hp)]
theorem fail_add_eq (hr : 2 ≤ r) (h : LeProdPrimesLT r y z) (j : ℕ) :
    fail lower (r + j) y z = fail lower r y z := by
  induction r, hr using Nat.le_induction generalizing lower y z with
  | base =>
    rw [show 2 + j = (1 + j) + 1 by omega]
    refine fail_succ_congr fun p hp ↦ ?_
    have hpz := rosserPrimes_subset hp
    have hpos : (0 : ℝ) < p := by exact_mod_cast (prime_of_mem_primesLT hpz).pos
    have h1 : ∀ q ∈ primesLT p, y / p ≤ q := fun q hq ↦ by
      have := (h.div hpz) {q} (singleton_subset_iff.2 hq) (card_singleton (α := ℕ) q)
      simpa using this
    rw [Nat.add_comm 1 j]
    cases lower
    ·
      rw [mem_rosserPrimes] at hp
      have hp3 : (p : ℝ) ^ 3 < y := hp.2.resolve_left (by simp)
      simp only [Bool.not_false, fail_true_succ]
      refine sum_congr rfl fun q hq ↦ absurd (h1 q hq) ?_
      have hqp := lt_of_mem_primesLT hq
      have hq0 : (0 : ℝ) ≤ q := q.cast_nonneg
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (prime_of_mem_primesLT hpz).one_lt.le
      rw [not_le, lt_div_iff₀' hpos]
      have h2 : (p : ℝ) * q < p * p := mul_lt_mul_of_pos_left hqp hpos
      have h3 : (p : ℝ) ^ 2 ≤ p ^ 3 := pow_le_pow_right₀ hp1 (by norm_num)
      nlinarith
    ·
      simp only [Bool.not_true, fail_false_succ]
      congr 1
      refine sum_congr rfl fun q hq ↦ absurd (h1 q (rosserPrimes_subset hq)) ?_
      rw [mem_rosserPrimes] at hq
      have hq3 : (q : ℝ) ^ 3 < y / p := hq.2.resolve_left (by simp)
      have hq1 : (1 : ℝ) ≤ q := by
        exact_mod_cast (prime_of_mem_primesLT hq.1).one_lt.le
      rw [not_le]
      have h2 : (q : ℝ) ≤ q ^ 3 := le_self_pow₀ hq1 (by norm_num)
      linarith
  | succ r hr ih =>
    rw [show r + 1 + j = (r + j) + 1 by omega]
    exact fail_succ_congr fun p hp ↦ ih (h.div (rosserPrimes_subset hp))
theorem fail_add_eq_of_le_factorial (hr : 2 ≤ r) (h : y ≤ (r + 1).factorial) (j : ℕ) :
    fail lower (r + j) y z = fail lower r y z :=
  fail_add_eq hr (leProdPrimesLT_of_le_factorial h) j
theorem lt_of_mem_rosserSet (hd : d ∈ rosserSet lower y z)
    (hω : (if lower then 2 else 1) ≤ #d.primeFactors) : (d : ℝ) < y := by
  induction z using primesLT_induction generalizing lower y d with
  | h z ih =>
    rcases mem_rosserSet.1 hd with rfl | ⟨p, hp, e, he, rfl⟩
    · cases lower <;> simp at hω
    have hpz := rosserPrimes_subset hp
    have hpp := prime_of_mem_primesLT hpz
    have hpos : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    rw [card_primeFactors_mul_of_mem_rosserSet hpp he] at hω
    have key : (if (!lower) then 2 else 1) ≤ #e.primeFactors → ((p * e : ℕ) : ℝ) < y := by
      intro h
      have := ih p hpz he h
      push_cast
      rwa [lt_div_iff₀' hpos] at this
    cases lower
    · rw [mem_rosserPrimes] at hp
      have hp3 : (p : ℝ) ^ 3 < y := hp.2.resolve_left (by simp)
      by_cases h2 : 2 ≤ #e.primeFactors
      · exact key (by simpa using h2)
      have he' : e ≤ p ^ #e.primeFactors := by
        conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree (squarefree_of_mem_rosserSet he)]
        exact prod_le_pow_card _ _ _ fun q hq ↦
          (Nat.cast_lt.1 (lt_of_mem_primesLT (primeFactors_subset_of_mem_rosserSet he hq))).le
      have hpe : p * e ≤ p ^ 3 := by
        calc p * e ≤ p * p ^ #e.primeFactors := Nat.mul_le_mul_left p he'
          _ = p ^ (#e.primeFactors + 1) := by ring
          _ ≤ p ^ 3 := Nat.pow_le_pow_right hpp.pos (by omega)
      exact lt_of_le_of_lt (by exact_mod_cast hpe) hp3
    · exact key (by simp at hω ⊢; omega)
theorem card_primeFactors_le_of_mem_rosserSet (hr : 1 ≤ r) (h : LeProdPrimesLT (r + 1) y z)
    (hd : d ∈ rosserSet lower y z) : #d.primeFactors ≤ r := by
  by_contra hlt
  obtain ⟨T, hT, hcard⟩ := exists_subset_card_eq (s := d.primeFactors) (n := r + 1) (by omega)
  have hdy := lt_of_mem_rosserSet hd (by split_ifs <;> omega)
  have hyT := h T (hT.trans (primeFactors_subset_of_mem_rosserSet hd)) hcard
  have hTd : ∏ p ∈ T, p ≤ d := by
    refine Nat.le_of_dvd (pos_of_mem_rosserSet hd) ?_
    conv_rhs => rw [← Nat.prod_primeFactors_of_squarefree (squarefree_of_mem_rosserSet hd)]
    exact prod_dvd_prod_of_subset _ _ _ hT
  have : (∏ p ∈ T, (p : ℝ)) ≤ d := by
    have h' := (Nat.cast_le (α := ℝ)).2 hTd
    push_cast at h'
    exact h'
  linarith
theorem card_filter_rosserSet_add_eq (hr : 1 ≤ r) (h : LeProdPrimesLT (r + 1) y z) (j : ℕ) :
    #((rosserSet lower y z).filter fun d ↦ #d.primeFactors ≤ r + j) =
      #((rosserSet lower y z).filter fun d ↦ #d.primeFactors ≤ r) := by
  congr 1
  refine filter_congr fun d hd ↦ ⟨fun _ ↦ card_primeFactors_le_of_mem_rosserSet hr h hd,
    fun h ↦ h.trans (Nat.le_add_right r j)⟩
theorem mul_log_sub_one_le_log_factorial (n : ℕ) :
    (n : ℝ) * (log n - 1) ≤ log n.factorial := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := pow_div_factorial_le_exp _ hn'.le n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  rw [div_le_iff₀ hf] at h
  have := log_le_log (by positivity) h
  rw [log_pow, log_mul (exp_pos _).ne' hf.ne', log_exp] at this
  linarith
theorem log_le_two_mul_sqrt {x : ℝ} (hx : 0 ≤ x) : log x ≤ 2 * √x := by
  have := log_le_rpow_div hx (by norm_num : (0 : ℝ) < 1 / 2)
  rw [← sqrt_eq_rpow] at this
  linarith
theorem exists_le_factorial : ∃ y₀ : ℝ, ∀ y ≥ y₀, ∀ r : ℕ,
    2 * log y / log (log y) < r + 2 → 2 ≤ r ∧ y ≤ (r + 1).factorial := by
  refine ⟨exp (exp 49), fun y hy r hr ↦ ?_⟩
  have hy0 : 0 < y := (exp_pos _).trans_le hy
  set L := log y with hL
  set ℓ := log L with hℓ
  have hL49 : exp 49 ≤ L := by rw [hL, le_log_iff_exp_le hy0]; exact hy
  have hL0 : 0 < L := (exp_pos _).trans_le hL49
  have hℓ49 : 49 ≤ ℓ := by rw [hℓ, le_log_iff_exp_le hL0]; exact hL49
  have hℓ0 : 0 < ℓ := by linarith
  have hsqrtL : 64 ≤ L := by
    have := quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 49)
    linarith
  have hℓL : 4 * ℓ ≤ L := by
    have h1 := log_le_two_mul_sqrt hL0.le
    have h2 : 8 ≤ √L := by
      rw [show (8 : ℝ) = √64 by rw [show (64 : ℝ) = 8 ^ 2 by norm_num, sqrt_sq (by norm_num)]]
      exact sqrt_le_sqrt hsqrtL
    have h3 : √L * √L = L := mul_self_sqrt hL0.le
    nlinarith
  have hratio : 4 ≤ L / ℓ := by rw [le_div_iff₀ hℓ0]; linarith
  have h2Lℓ : 2 * L / ℓ = 2 * (L / ℓ) := by ring
  refine ⟨by exact_mod_cast (by linarith : (2 : ℝ) ≤ r), ?_⟩
  have hlogℓ : 3 * log ℓ + 3 ≤ ℓ := by
    have h1 := log_le_two_mul_sqrt hℓ0.le
    have h2 : 7 ≤ √ℓ := by
      rw [show (7 : ℝ) = √49 by rw [show (49 : ℝ) = 7 ^ 2 by norm_num, sqrt_sq (by norm_num)]]
      exact sqrt_le_sqrt hℓ49
    have h3 : √ℓ * √ℓ = ℓ := mul_self_sqrt hℓ0.le
    nlinarith
  set m := 3 * L / (2 * ℓ) with hm
  have hm0 : 0 < m := by positivity
  set n : ℕ := r + 1 with hn
  have hn_cast : (n : ℝ) = r + 1 := by rw [hn]; push_cast; ring
  have hmn : m ≤ n := by
    rw [hn_cast, hm]
    have : 3 * L / (2 * ℓ) = 3 / 2 * (L / ℓ) := by field_simp
    rw [this]
    linarith
  have hlogm : ℓ - log ℓ ≤ log m := by
    rw [hm, log_div (by positivity) (by positivity), log_mul (by norm_num) hL0.ne',
      log_mul (by norm_num) hℓ0.ne', ← hℓ]
    have : log 2 ≤ log 3 := log_le_log (by norm_num) (by norm_num)
    linarith
  have hkey : L ≤ m * (log m - 1) := by
    have h1 : 2 * ℓ / 3 ≤ log m - 1 := by linarith
    calc L = m * (2 * ℓ / 3) := by rw [hm]; field_simp
      _ ≤ m * (log m - 1) := by gcongr
  have hmono : m * (log m - 1) ≤ n * (log n - 1) := by
    have h1 : log m ≤ log n := log_le_log hm0 hmn
    have h2 : 0 ≤ log m - 1 := by
      by_contra h
      have : m * (log m - 1) < 0 := mul_neg_of_pos_of_neg hm0 (not_le.1 h)
      linarith
    nlinarith
  have hfact := mul_log_sub_one_le_log_factorial n
  have : L ≤ log n.factorial := by linarith
  rw [hL, ← exp_le_exp, exp_log hy0, exp_log (by exact_mod_cast n.factorial_pos)] at this
  exact this
theorem exists_fail_add_eq : ∃ y₀ : ℝ, ∀ y ≥ y₀, ∀ (lower : Bool) (r : ℕ) (z : ℝ),
    2 * log y / log (log y) < r + 2 → ∀ j, fail lower (r + j) y z = fail lower r y z := by
  obtain ⟨y₀, hy₀⟩ := exists_le_factorial
  refine ⟨y₀, fun y hy lower r z hr j ↦ ?_⟩
  obtain ⟨h2, hf⟩ := hy₀ y hy r hr
  exact fail_add_eq_of_le_factorial h2 hf j
theorem exists_card_filter_rosserSet_add_eq : ∃ y₀ : ℝ, ∀ y ≥ y₀, ∀ (lower : Bool) (r : ℕ)
    (z : ℝ), 2 * log y / log (log y) < r + 2 → ∀ j,
      #((rosserSet lower y z).filter fun d ↦ #d.primeFactors ≤ r - 1 + j) =
        #((rosserSet lower y z).filter fun d ↦ #d.primeFactors ≤ r - 1) := by
  obtain ⟨y₀, hy₀⟩ := exists_le_factorial
  refine ⟨y₀, fun y hy lower r z hr j ↦ ?_⟩
  obtain ⟨h2, hf⟩ := hy₀ y hy r hr
  have h := leProdPrimesLT_of_le_factorial (z := z) hf
  rw [show r = r - 1 + 1 by omega] at h
  exact card_filter_rosserSet_add_eq (by omega) h j
end IwaniecLinearSieve
end
section
open Finset Real
namespace IwaniecLinearSieve
theorem pow_succ_add_mul_le_add_pow {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    a ^ (n + 1) + (n + 1) * a ^ n * b ≤ (a + b) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 0 ≤ a ^ n := pow_nonneg ha n
    have h2 : 0 ≤ (n + 1 : ℝ) * a ^ n * b * b := by positivity
    calc a ^ (n + 1 + 1) + ((n + 1 : ℕ) + 1 : ℝ) * a ^ (n + 1) * b
        ≤ (a + b) * (a ^ (n + 1) + (n + 1) * a ^ n * b) := by
          push_cast
          rw [pow_succ a (n + 1), pow_succ a n]
          nlinarith [mul_nonneg h1 hb]
      _ ≤ (a + b) * (a + b) ^ (n + 1) := by gcongr
      _ = (a + b) ^ (n + 1 + 1) := by ring
theorem sum_pow_sum_lt_mul_le (s : Finset ℕ) {w : ℕ → ℝ} (hw : ∀ p ∈ s, 0 ≤ w p) (n : ℕ) :
    ∑ p ∈ s, (∑ q ∈ s.filter (· < p), w q) ^ n * w p ≤ (∑ q ∈ s, w q) ^ (n + 1) / (n + 1) := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have has : a ∉ s := fun h ↦ lt_irrefl a (hlt a h)
    have hw' : ∀ p ∈ s, 0 ≤ w p := fun p hp ↦ hw p (mem_insert_of_mem hp)
    have hwa : 0 ≤ w a := hw a (mem_insert_self a s)
    have hfa : (insert a s).filter (· < a) = s := by
      ext q
      simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨rfl | hq, hqa⟩
        · exact absurd hqa (lt_irrefl _)
        · exact hq
      · intro hq
        exact ⟨Or.inr hq, hlt q hq⟩
    have hfp : ∀ p ∈ s, (insert a s).filter (· < p) = s.filter (· < p) := by
      intro p hp
      rw [filter_insert, ite_eq_right (not_lt.2 (hlt p hp).le)]
    have hsum : ∑ p ∈ s, (∑ q ∈ (insert a s).filter (· < p), w q) ^ n * w p =
        ∑ p ∈ s, (∑ q ∈ s.filter (· < p), w q) ^ n * w p :=
      sum_congr rfl fun p hp ↦ by rw [hfp p hp]
    rw [sum_insert has, sum_insert has, hfa, hsum]
    have hS : 0 ≤ ∑ q ∈ s, w q := sum_nonneg hw'
    have := pow_succ_add_mul_le_add_pow hS hwa n
    have hn : (0 : ℝ) < n + 1 := by positivity
    calc (∑ q ∈ s, w q) ^ n * w a + ∑ p ∈ s, (∑ q ∈ s.filter (· < p), w q) ^ n * w p
        ≤ (∑ q ∈ s, w q) ^ n * w a + (∑ q ∈ s, w q) ^ (n + 1) / (n + 1) := by
          gcongr
          exact ih hw'
      _ ≤ (w a + ∑ q ∈ s, w q) ^ (n + 1) / (n + 1) := by
          rw [add_comm (w a), le_div_iff₀ hn, add_mul, div_mul_cancel₀ _ hn.ne']
          nlinarith
theorem sum_SLT_pow_div_le (n : ℕ) (z : ℝ) :
    ∑ p ∈ primesLT z, SLT p ^ n / p ≤ SLT z ^ (n + 1) / (n + 1) := by
  have h := sum_pow_sum_lt_mul_le (primesLT z) (w := fun p ↦ (p : ℝ)⁻¹)
    (fun p _ ↦ by positivity) n
  refine le_of_eq_of_le (sum_congr rfl fun p hp ↦ ?_) h
  rw [filter_lt_primesLT hp, SLT, div_eq_mul_inv]
theorem sum_SLT_pow_div_factorial_div_le (n : ℕ) (z : ℝ) :
    ∑ p ∈ primesLT z, SLT p ^ n / n.factorial / p ≤
      SLT z ^ (n + 1) / (n + 1).factorial := by
  have h := sum_SLT_pow_div_le n z
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  calc ∑ p ∈ primesLT z, SLT p ^ n / n.factorial / p
      = (∑ p ∈ primesLT z, SLT p ^ n / p) / n.factorial := by
        rw [sum_div]
        exact sum_congr rfl fun p _ ↦ by ring
    _ ≤ SLT z ^ (n + 1) / (n + 1) / n.factorial := by gcongr
    _ = SLT z ^ (n + 1) / (n + 1).factorial := by
        rw [Nat.factorial_succ]
        push_cast
        rw [div_div, mul_comm]
theorem SLT_nonneg (z : ℝ) : 0 ≤ SLT z := sum_nonneg fun p _ ↦ by positivity
theorem R_le_one (z : ℝ) : R z ≤ 1 :=
  prod_le_one₀ (fun p hp ↦ sub_nonneg.2 <| inv_le_one_of_one_le₀ <| by
    exact_mod_cast (mem_primesLT.1 hp).1.one_lt.le) fun p _ ↦ one_sub_inv_le_one p
theorem fail_le_sum_ite (lower : Bool) (r : ℕ) (y z : ℝ) :
    fail lower r y z ≤ ∑ l ∈ range r,
      if y < z ^ (l + 3) then SLT z ^ (l + 1) / (l + 1).factorial else 0 := by
  induction r generalizing lower y z with
  | zero => simp
  | succ r ih =>
    have hA : ∑ p ∈ rosserPrimes lower y z, fail (!lower) r (y / p) p / p ≤
        ∑ l ∈ range r, if y < z ^ (l + 1 + 3) then
          SLT z ^ (l + 1 + 1) / (l + 1 + 1).factorial else 0 := by
      calc ∑ p ∈ rosserPrimes lower y z, fail (!lower) r (y / p) p / p
          ≤ ∑ p ∈ primesLT z, fail (!lower) r (y / p) p / p :=
            sum_le_sum_of_subset_of_nonneg rosserPrimes_subset fun p _ _ ↦
              div_nonneg (fail_nonneg _ _ _ _) p.cast_nonneg
        _ ≤ ∑ p ∈ primesLT z, (∑ l ∈ range r, if y / p < (p : ℝ) ^ (l + 3) then
              SLT p ^ (l + 1) / (l + 1).factorial else 0) / p := by
            gcongr with p
            exact ih _ _ _
        _ = ∑ l ∈ range r, ∑ p ∈ primesLT z, (if y / p < (p : ℝ) ^ (l + 3) then
              SLT p ^ (l + 1) / (l + 1).factorial else 0) / p := by
            simp_rw [sum_div]
            exact sum_comm
        _ ≤ _ := by
            refine sum_le_sum fun l _ ↦ ?_
            split_ifs with hyz
            · calc ∑ p ∈ primesLT z, (if y / p < (p : ℝ) ^ (l + 3) then
                    SLT p ^ (l + 1) / (l + 1).factorial else 0) / p
                  ≤ ∑ p ∈ primesLT z, SLT p ^ (l + 1) / (l + 1).factorial / p := by
                    gcongr with p
                    split_ifs
                    · exact le_rfl
                    · have := SLT_nonneg p
                      positivity
                _ ≤ _ := sum_SLT_pow_div_factorial_div_le (l + 1) z
            · refine (sum_eq_zero fun p hp ↦ ?_).le
              rw [ite_eq_right, zero_div]
              intro h
              have hpos : (0 : ℝ) < p := by exact_mod_cast (prime_of_mem_primesLT hp).pos
              rw [div_lt_iff₀ hpos, ← pow_succ] at h
              exact hyz (h.trans (pow_lt_pow_left₀ (lt_of_mem_primesLT hp) hpos.le
                (by omega)))
    have hE : ∑ p ∈ (primesLT z).filter (fun p : ℕ ↦ ¬ (p : ℝ) ^ 3 < y), R p / p ≤
        if y < z ^ (0 + 3) then SLT z ^ (0 + 1) / (0 + 1).factorial else 0 := by
      split_ifs with hyz
      · simp only [zero_add, pow_one, Nat.factorial_one, Nat.cast_one, div_one, SLT]
        calc ∑ p ∈ (primesLT z).filter (fun p : ℕ ↦ ¬ (p : ℝ) ^ 3 < y), R p / p
            ≤ ∑ p ∈ (primesLT z).filter (fun p : ℕ ↦ ¬ (p : ℝ) ^ 3 < y), (p : ℝ)⁻¹ := by
              gcongr with p
              rw [div_eq_mul_inv]
              exact mul_le_of_le_one_left (by positivity) (R_le_one p)
          _ ≤ ∑ p ∈ primesLT z, (p : ℝ)⁻¹ :=
              sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun p _ _ ↦ by positivity
      · refine (sum_eq_zero fun p hp ↦ ?_).le
        rw [mem_filter] at hp
        exact absurd ((not_lt.1 hp.2).trans_lt (pow_lt_pow_left₀ (lt_of_mem_primesLT hp.1)
          p.cast_nonneg (by norm_num))) hyz
    rw [sum_range_succ']
    cases lower
    · rw [fail_false_succ]
      exact add_le_add hA hE
    · rw [fail_true_succ, ← rosserPrimes_true, ← add_zero (∑ p ∈ _, _ / _)]
      refine add_le_add hA ?_
      have := SLT_nonneg z
      split_ifs <;> positivity
theorem fail_le_sum_SLT_pow (lower : Bool) (r : ℕ) (y z : ℝ) :
    fail lower r y z ≤ ∑ l ∈ Icc 1 r with y < z ^ (l + 2), SLT z ^ l / l.factorial := by
  refine (fail_le_sum_ite lower r y z).trans_eq ?_
  rw [sum_filter]
  refine sum_nbij' (· + 1) (· - 1) ?_ ?_ ?_ ?_ ?_
  · intro l hl
    simp only [mem_range, mem_Icc] at hl ⊢
    omega
  · intro l hl
    simp only [mem_range, mem_Icc] at hl ⊢
    omega
  · intro l _
    simp
  · intro l hl
    simp only [mem_Icc] at hl
    omega
  · intro l _
    simp only [show l + 3 = l + 1 + 2 by ring]
theorem pow_div_factorial_le_pow {X : ℝ} (hX : 0 ≤ X) (k : ℕ) :
    X ^ k / k.factorial ≤ (exp 1 * X / k) ^ k := by
  rcases k.eq_zero_or_pos with rfl | hk
  · simp
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  have h := pow_div_factorial_le_exp _ hk'.le k
  rw [div_le_iff₀ hf] at h
  rw [div_pow, mul_pow, ← exp_nat_mul, mul_one, div_le_div_iff₀ hf (by positivity)]
  calc X ^ k * k ^ k ≤ X ^ k * (exp k * k.factorial) := by gcongr
    _ = exp k * X ^ k * k.factorial := by ring
theorem sum_pow_div_factorial_le {X u : ℝ} (hX : 0 ≤ X) (hu : 0 < u) (h : 2 * exp 1 * X ≤ u)
    (s : Finset ℕ) (hs : ∀ l ∈ s, u < l) :
    ∑ l ∈ s, X ^ l / l.factorial ≤ 2 * (exp 1 * X / u) ^ u := by
  set k := ⌊u⌋₊ + 1 with hk
  have huk : u < k := by rw [hk]; push_cast; exact Nat.lt_floor_add_one u
  have hks : ∀ l ∈ s, k ≤ l := fun l hl ↦ by
    rw [hk, Nat.add_one_le_iff, Nat.floor_lt hu.le]
    exact hs l hl
  have he : 1 ≤ exp 1 := one_le_exp zero_le_one
  have h2X : 2 * X ≤ k + 1 := by nlinarith
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  have hterm : ∀ j : ℕ, X ^ (k + j) / (k + j).factorial ≤
      X ^ k / k.factorial * (1 / 2) ^ j := by
    intro j
    have h1 : ((k.factorial * (k + 1) ^ j : ℕ) : ℝ) ≤ (k + j).factorial := by
      exact_mod_cast Nat.factorial_mul_pow_le_factorial
    push_cast at h1
    have hpos : (0 : ℝ) < k.factorial * (k + 1) ^ j := by positivity
    calc X ^ (k + j) / (k + j).factorial ≤ X ^ (k + j) / (k.factorial * (k + 1) ^ j) := by
          gcongr
      _ = X ^ k / k.factorial * (X / (k + 1)) ^ j := by
          rw [pow_add, div_pow]
          field_simp
      _ ≤ X ^ k / k.factorial * (1 / 2) ^ j := by
          refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ j)
            (by positivity)
          rw [div_le_iff₀ (by positivity)]
          linarith
  set N := s.sup id + 1
  have hsub : s ⊆ Ico k N := fun l hl ↦
    mem_Ico.2 ⟨hks l hl, Nat.lt_succ_of_le (le_sup (f := id) hl)⟩
  calc ∑ l ∈ s, X ^ l / l.factorial
      ≤ ∑ l ∈ s, X ^ k / k.factorial * (1 / 2) ^ (l - k) := by
        refine sum_le_sum fun l hl ↦ ?_
        have := hterm (l - k)
        rwa [Nat.add_sub_cancel' (hks l hl)] at this
    _ ≤ ∑ l ∈ Ico k N, X ^ k / k.factorial * (1 / 2) ^ (l - k) :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ by positivity
    _ = X ^ k / k.factorial * ∑ j ∈ range (N - k), (1 / 2 : ℝ) ^ j := by
        rw [← mul_sum, sum_Ico_eq_sum_range]
        simp
    _ ≤ X ^ k / k.factorial * 2 := by
        gcongr
        exact sum_geometric_two_le _
    _ ≤ (exp 1 * X / k) ^ k * 2 := by gcongr; exact pow_div_factorial_le_pow hX k
    _ ≤ (exp 1 * X / u) ^ (k : ℝ) * 2 := by
        rw [rpow_natCast]
        gcongr
    _ ≤ (exp 1 * X / u) ^ u * 2 := by
        refine mul_le_mul_of_nonneg_right ?_ (by norm_num)
        refine rpow_le_rpow_of_exponent_ge' (by positivity) ?_ hu.le huk.le
        rw [div_le_one hu]
        nlinarith [exp_pos 1]
    _ = 2 * (exp 1 * X / u) ^ u := mul_comm _ _
theorem exp_one_mul_div_rpow {X u : ℝ} (hX : 0 < X) (hu : 0 < u) :
    (exp 1 * X / u) ^ u = exp (-(u * log u) + u * log X + u) := by
  rw [rpow_def_of_pos (by positivity), log_div (by positivity) hu.ne',
    log_mul (exp_pos 1).ne' hX.ne', log_exp]
  ring_nf
theorem fail_le_tail {lower : Bool} {r : ℕ} {y z X u : ℝ} (hz : 1 < z) (hu : 0 < u)
    (hyz : z ^ (u + 2) ≤ y) (hX : SLT z ≤ X) (h : 2 * exp 1 * X ≤ u) :
    fail lower r y z ≤ 2 * (exp 1 * X / u) ^ u := by
  refine (fail_le_sum_SLT_pow lower r y z).trans ((sum_le_sum fun l _ ↦ ?_).trans
    (sum_pow_div_factorial_le ((SLT_nonneg z).trans hX) hu h _ fun l hl ↦ ?_))
  · gcongr
    exact SLT_nonneg z
  · have hl := (mem_filter.1 hl).2
    rw [← rpow_natCast] at hl
    have := (rpow_lt_rpow_left_iff hz).1 (hyz.trans_lt hl)
    push_cast at this
    linarith
theorem fail_rpow_le_tail {lower : Bool} {r : ℕ} {y s X : ℝ} (hy : 1 < y) (hs : 2 < s)
    (hX : SLT (y ^ s⁻¹) ≤ X) (h : 2 * exp 1 * X ≤ s - 2) :
    fail lower r y (y ^ s⁻¹) ≤ 2 * (exp 1 * X / (s - 2)) ^ (s - 2) := by
  have hs0 : 0 < s := by linarith
  refine fail_le_tail (one_lt_rpow hy (inv_pos.2 hs0)) (by linarith) ?_ hX h
  rw [sub_add_cancel, ← rpow_mul (by linarith), inv_mul_cancel₀ hs0.ne', rpow_one]
theorem SLT_le_loglog (hPNT : StrongPNTProp) : ∃ C : ℝ, ∀ z ≥ 2, SLT z ≤ log (log z) + C := by
  obtain ⟨c₅, C, hC⟩ := (S_asymp hPNT)
  refine ⟨c₅ + |C|, fun z hz ↦ ?_⟩
  have h1 := (S_sub_SLT (by linarith : (0 : ℝ) < z)).1
  have h2 := (abs_le.1 (hC z hz)).2
  have h3 : C * pntE z ≤ |C| := by
    calc C * pntE z ≤ |C| * pntE z := by gcongr; exact pntE_nonneg z; exact le_abs_self C
      _ ≤ |C| * 1 := by gcongr; exact pntE_le_one z
      _ = |C| := mul_one _
  linarith
theorem sum_inv_filter_card_primeFactors_eq_le (lower : Bool) (y z : ℝ) (l : ℕ) :
    ∑ d ∈ (rosserSet lower y z).filter (fun d ↦ #d.primeFactors = l), (d : ℝ)⁻¹ ≤
      SLT z ^ l / l.factorial := by
  induction l generalizing lower y z with
  | zero =>
    rw [sum_filter, sum_rosserSet]
    simp only [Nat.primeFactors_one, card_empty, ite_true, Nat.cast_one, inv_one, pow_zero,
      Nat.factorial_zero, div_one]
    refine (add_eq_left.2 (sum_eq_zero fun p hp ↦ sum_eq_zero fun e he ↦ ?_)).le
    rw [card_primeFactors_mul_of_mem_rosserSet
      (prime_of_mem_primesLT (rosserPrimes_subset hp)) he, ite_eq_right (Nat.succ_ne_zero _)]
  | succ l ih =>
    rw [sum_filter, sum_rosserSet]
    simp only [Nat.primeFactors_one, card_empty, Nat.cast_one, inv_one]
    rw [ite_eq_right (Nat.succ_ne_zero l).symm, zero_add]
    calc ∑ p ∈ rosserPrimes lower y z, ∑ e ∈ rosserSet (!lower) (y / p) p,
          (if #(p * e).primeFactors = l + 1 then ((p * e : ℕ) : ℝ)⁻¹ else 0)
        = ∑ p ∈ rosserPrimes lower y z, (∑ e ∈ (rosserSet (!lower) (y / p) p).filter
            (fun e ↦ #e.primeFactors = l), (e : ℝ)⁻¹) / p := by
          refine sum_congr rfl fun p hp ↦ ?_
          rw [sum_filter, sum_div]
          refine sum_congr rfl fun e he ↦ ?_
          rw [card_primeFactors_mul_of_mem_rosserSet
            (prime_of_mem_primesLT (rosserPrimes_subset hp)) he]
          simp only [add_left_inj]
          split_ifs
          · push_cast
            rw [mul_inv, div_eq_mul_inv, mul_comm]
          · simp
      _ ≤ ∑ p ∈ rosserPrimes lower y z, SLT p ^ l / l.factorial / p := by
          gcongr with p
          exact ih _ _ _
      _ ≤ ∑ p ∈ primesLT z, SLT p ^ l / l.factorial / p :=
          sum_le_sum_of_subset_of_nonneg rosserPrimes_subset fun p _ _ ↦ by
            have := SLT_nonneg p
            positivity
      _ ≤ _ := sum_SLT_pow_div_factorial_div_le l z
theorem card_filter_le_mul_sum {lower : Bool} {y z : ℝ} {k : ℕ} (hy : 0 ≤ y)
    (hk : (if lower then 2 else 1) ≤ k) :
    (#((rosserSet lower y z).filter fun d ↦ k ≤ #d.primeFactors) : ℝ) ≤
      y * ∑ l ∈ Icc k #(primesLT z), SLT z ^ l / l.factorial := by
  set D := (rosserSet lower y z).filter fun d ↦ k ≤ #d.primeFactors
  calc (#D : ℝ) = ∑ d ∈ D, (1 : ℝ) := by simp
    _ ≤ ∑ d ∈ D, y * (d : ℝ)⁻¹ := by
        refine sum_le_sum fun d hd ↦ ?_
        obtain ⟨hd, hkd⟩ := mem_filter.1 hd
        have hdy := lt_of_mem_rosserSet hd (hk.trans hkd)
        have hd0 : (0 : ℝ) < d := by exact_mod_cast pos_of_mem_rosserSet hd
        rw [← div_eq_mul_inv, le_div_iff₀ hd0, one_mul]
        exact hdy.le
    _ = y * ∑ l ∈ Icc k #(primesLT z), ∑ d ∈ D.filter (fun d ↦ #d.primeFactors = l),
          (d : ℝ)⁻¹ := by
        rw [← mul_sum, sum_fiberwise_of_maps_to]
        intro d hd
        obtain ⟨hd, hkd⟩ := mem_filter.1 hd
        exact mem_Icc.2 ⟨hkd, card_le_card (primeFactors_subset_of_mem_rosserSet hd)⟩
    _ ≤ y * ∑ l ∈ Icc k #(primesLT z), SLT z ^ l / l.factorial := by
        gcongr with l
        refine le_trans ?_ (sum_inv_filter_card_primeFactors_eq_le lower y z l)
        refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ ↦ by positivity
        exact filter_subset_filter _ (filter_subset _ _)
theorem card_filter_le_tail {lower : Bool} {y z X u : ℝ} {k : ℕ} (hy : 0 ≤ y)
    (hk : (if lower then 2 else 1) ≤ k) (hu : 0 < u) (huk : u < k) (hX : SLT z ≤ X)
    (h : 2 * exp 1 * X ≤ u) :
    (#((rosserSet lower y z).filter fun d ↦ k ≤ #d.primeFactors) : ℝ) ≤
      2 * y * (exp 1 * X / u) ^ u := by
  refine (card_filter_le_mul_sum hy hk).trans ?_
  rw [mul_assoc, mul_left_comm]
  refine mul_le_mul_of_nonneg_left ((sum_le_sum fun l _ ↦ ?_).trans
    (sum_pow_div_factorial_le ((SLT_nonneg z).trans hX) hu h _ fun l hl ↦ ?_)) hy
  · gcongr
    exact SLT_nonneg z
  · exact huk.trans_le (by exact_mod_cast (mem_Icc.1 hl).1)
theorem card_filter_eq_le_pow_div (lower : Bool) (y z : ℝ) (l : ℕ) :
    (#((rosserSet lower y z).filter fun d ↦ #d.primeFactors = l) : ℝ) ≤
      (#(primesLT z) : ℝ) ^ l / l.factorial := by
  refine le_trans ?_ (Nat.choose_le_pow_div l _)
  have : #((rosserSet lower y z).filter fun d ↦ #d.primeFactors = l) ≤
      #((primesLT z).powersetCard l) := by
    refine card_le_card_of_injOn (fun d ↦ d.primeFactors) (fun d hd ↦ ?_) fun d hd e he h ↦ ?_
    · obtain ⟨hd, hl⟩ := mem_filter.1 hd
      exact mem_powersetCard.2 ⟨primeFactors_subset_of_mem_rosserSet hd, hl⟩
    · have hd' := squarefree_of_mem_rosserSet (mem_filter.1 hd).1
      have he' := squarefree_of_mem_rosserSet (mem_filter.1 he).1
      rw [← Nat.prod_primeFactors_of_squarefree hd', ← Nat.prod_primeFactors_of_squarefree he']
      exact congrArg (fun T ↦ ∏ p ∈ T, p) h
  rw [card_powersetCard] at this
  exact_mod_cast this
end IwaniecLinearSieve
end
section
open Real Set Filter Topology MeasureTheory Finset
namespace IwaniecLinearSieve.TheoremFour
theorem sum_R_div_eq {a b : ℝ} (hab : a ≤ b) :
    ∑ p ∈ (primesLT b).filter (fun p : ℕ => a ≤ p), R p / p = R a - R b := by
  have h := sum_filter_add_sum_filter_not (primesLT b) (fun p : ℕ => a ≤ (p : ℝ))
    (fun p => R p / p)
  have hs : (primesLT b).filter (fun p : ℕ => ¬ a ≤ (p : ℝ)) = primesLT a := by
    ext p
    simp only [mem_filter, mem_primesLT, not_le]
    constructor
    · rintro ⟨⟨hp, -⟩, h⟩; exact ⟨hp, h⟩
    · rintro ⟨hp, h⟩; exact ⟨⟨hp, h.trans_le hab⟩, h⟩
  rw [hs] at h
  have ha := R_eq a
  have hb := R_eq b
  linarith
noncomputable def src (lower : Bool) (y z : ℝ) : ℝ :=
  if lower then 0 else ∑ p ∈ (primesLT z).filter (fun p : ℕ ↦ ¬ (p : ℝ) ^ 3 < y), R p / p
theorem src_nonneg (lower : Bool) (y z : ℝ) : 0 ≤ src lower y z := by
  unfold src
  split_ifs
  · exact le_rfl
  · exact sum_nonneg fun p _ ↦ div_nonneg (R_nonneg _) p.cast_nonneg
theorem fail_succ_eq (lower : Bool) (r : ℕ) (y z : ℝ) :
    fail lower (r + 1) y z =
      ∑ p ∈ rosserPrimes lower y z, fail (!lower) r (y / p) p / p + src lower y z := by
  cases lower
  · rw [fail_false_succ, src]; rfl
  · rw [fail_true_succ, src, rosserPrimes_true]; simp
theorem not_cube_lt_iff {y x : ℝ} (hy : 0 ≤ y) (hx : 0 ≤ x) :
    ¬ x ^ 3 < y ↔ y ^ (1 / 3 : ℝ) ≤ x := by
  rw [not_lt, one_div, rpow_inv_le_iff_of_pos hy hx (by norm_num)]
  norm_cast
theorem src_le {cR CR : ℝ} (hR : ∀ z ≥ 2, |R z * log z - cR| ≤ CR * pntE z) {lower : Bool}
    {y s w : ℝ} (hy : 1 < y) (hs : 1 ≤ s) (hw : 2 ≤ w) (hwz : w ≤ y ^ (1 / s))
    (hw3 : w ≤ y ^ (1 / 3 : ℝ)) :
    src lower y (y ^ (1 / s)) ≤
      (if lower then 0 else cR * max (3 - s) 0 / log y) + 6 * CR * pntE w / log y := by
  have hL : 0 < log y := log_pos hy
  have hy0 : 0 < y := by linarith
  have hCR : 0 ≤ CR := by
    have h := (abs_nonneg _).trans (hR 2 le_rfl)
    exact nonneg_of_mul_nonneg_left h (pntE_pos 2)
  have hE : 0 ≤ 6 * CR * pntE w / log y := by have := pntE_pos w; positivity
  cases lower
  · simp only [src, Bool.false_eq_true, ite_false]
    have hset : (primesLT (y ^ (1 / s))).filter (fun p : ℕ ↦ ¬ (p : ℝ) ^ 3 < y) =
        (primesLT (y ^ (1 / s))).filter (fun p : ℕ ↦ y ^ (1 / 3 : ℝ) ≤ p) :=
      filter_congr fun p _ ↦ not_cube_lt_iff hy0.le p.cast_nonneg
    rw [hset]
    rcases le_total 3 s with h3 | h3
    ·
      have : (primesLT (y ^ (1 / s))).filter (fun p : ℕ ↦ y ^ (1 / 3 : ℝ) ≤ p) = ∅ := by
        refine eq_empty_of_forall_notMem fun p hp ↦ ?_
        rw [mem_filter, mem_primesLT] at hp
        have := rpow_one_div_le_rpow_one_div hy.le (by norm_num) h3
        linarith [hp.1.2]
      rw [this, sum_empty, max_eq_right (by linarith)]
      simpa using hE
    · rw [sum_R_div_eq (rpow_one_div_le_rpow_one_div hy.le (by linarith) h3),
        max_eq_left (by linarith)]
      have h1 := (abs_le.1 (hR _ (hw.trans hw3))).2
      have h2 := (abs_le.1 (hR _ (hw.trans hwz))).1
      rw [log_rpow_one_div hy0] at h1 h2
      have e1 : pntE (y ^ (1 / 3 : ℝ)) ≤ pntE w := pntE_le_pntE (by linarith) hw3
      have e2 : pntE (y ^ (1 / s)) ≤ pntE w := pntE_le_pntE (by linarith) hwz
      have hR1 : R (y ^ (1 / 3 : ℝ)) ≤ 3 * (cR + CR * pntE w) / log y := by
        rw [le_div_iff₀ hL]
        nlinarith
      have hR2 : s * (cR - CR * pntE w) / log y ≤ R (y ^ (1 / s)) := by
        rw [div_le_iff₀ hL]
        have : R (y ^ (1 / s)) * (log y / s) * s = R (y ^ (1 / s)) * log y := by
          field_simp
        have h2' : cR - CR * pntE w ≤ R (y ^ (1 / s)) * (log y / s) := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left h2' (by linarith : (0 : ℝ) ≤ s)]
      have : 3 * (cR + CR * pntE w) / log y - s * (cR - CR * pntE w) / log y ≤
          cR * (3 - s) / log y + 6 * CR * pntE w / log y := by
        rw [← sub_div, ← add_div]
        apply div_le_div_of_nonneg_right _ hL.le
        have := pntE_pos w
        nlinarith [mul_nonneg (mul_nonneg hCR this.le) (by linarith : (0 : ℝ) ≤ 3 - s)]
      linarith
  · simp only [src, ite_true]
    simpa using hE
theorem one_le_delta {s : ℝ} (hs : 1 ≤ s) (y : ℝ) : 1 ≤ delta s y := by
  rw [delta]
  exact one_le_rpow (by linarith [lsx_nonneg (log y) hs]) (by linarith)
theorem delta_le_delta {s s' : ℝ} (hs : 1 ≤ s) (hss' : s ≤ s') (y : ℝ) :
    delta s y ≤ delta s' y := by
  have hl := log_nonneg hs
  have hll : log s ≤ log s' := log_le_log (by linarith) hss'
  have hx0 := lsx_nonneg (log y) hs
  have hx : s ^ 2 * log s ^ 5 / log y ^ 2 ≤ s' ^ 2 * log s' ^ 5 / log y ^ 2 := by gcongr
  rw [delta, delta]
  calc (1 + s ^ 2 * log s ^ 5 / log y ^ 2) ^ (5 * s)
      ≤ (1 + s' ^ 2 * log s' ^ 5 / log y ^ 2) ^ (5 * s) :=
        rpow_le_rpow (by linarith) (by linarith) (by linarith)
    _ ≤ _ := rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
theorem delta_max_le {s a : ℝ} (hs : 1 ≤ s) (ha : 1 ≤ a) (y : ℝ) :
    delta (max s a) y ≤ delta a y * delta s y := by
  rcases le_total s a with h | h
  · rw [max_eq_right h]
    exact le_mul_of_one_le_right (by linarith [one_le_delta ha y]) (one_le_delta hs y)
  · rw [max_eq_left h]
    exact le_mul_of_one_le_left (by linarith [one_le_delta hs y]) (one_le_delta ha y)
theorem rpow_inner_eq {y : ℝ} {p : ℕ} (hp : 1 < p) (hpy : (p : ℝ) < y) :
    (y / p) ^ (1 / (log y / log p - 1)) = p := by
  have hp0 : (0 : ℝ) < p := by positivity
  have hy0 : 0 < y := hp0.trans hpy
  have hlp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp)
  have ht : 0 < log y / log p - 1 := by
    rw [sub_pos, one_lt_div hlp]; exact log_lt_log hp0 hpy
  rw [rpow_def_of_pos (div_pos hy0 hp0), log_div_prime_eq hy0 hp, mul_one_div,
    mul_div_cancel_right₀ _ ht.ne', exp_log hp0]
theorem lt_div_log_of_lt_rpow {y s : ℝ} {p : ℕ} (hy : 1 < y) (hs : 0 < s) (hp : 1 < p)
    (hpz : (p : ℝ) < y ^ (1 / s)) : s < log y / log p := by
  have hlp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp)
  have h := log_lt_log (by positivity) hpz
  rw [log_rpow_one_div (by linarith)] at h
  rw [lt_div_iff₀ hlp]; rw [lt_div_iff₀ hs] at h; linarith
theorem prime_lt_of_mem_rosserPrimes {lower : Bool} {y s : ℝ} {p : ℕ} (hy : 1 < y) (hs : 1 ≤ s)
    (hp : p ∈ rosserPrimes lower y (y ^ (1 / s))) : (p : ℝ) < y := by
  have h := lt_of_mem_primesLT (rosserPrimes_subset hp)
  calc (p : ℝ) < y ^ (1 / s) := h
    _ ≤ y ^ (1 / (1 : ℝ)) := rpow_one_div_le_rpow_one_div hy.le one_pos hs
    _ = y := by simp
theorem sMin_le_inner {lower : Bool} {y s : ℝ} {p : ℕ} (hy : 1 < y) (hs : sMin lower ≤ s)
    (hp : p ∈ rosserPrimes lower y (y ^ (1 / s))) : sMin (!lower) ≤ log y / log p - 1 := by
  have hpP := prime_of_mem_primesLT (rosserPrimes_subset hp)
  have hlp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hpP.one_lt)
  cases lower
  ·
    have h3 := ((mem_rosserPrimes.1 hp).2.resolve_left (by simp))
    have h := log_lt_log (by have := hpP.pos; positivity) h3
    rw [log_pow] at h
    have : 3 < log y / log p := by rw [lt_div_iff₀ hlp]; push_cast at h; linarith
    simp only [Bool.not_false, sMin]
    linarith
  · have hs2 : (2 : ℝ) ≤ s := hs
    have := lt_div_log_of_lt_rpow hy (by linarith) hpP.one_lt
      (lt_of_mem_primesLT (rosserPrimes_subset hp))
    simp only [Bool.not_true, sMin]
    linarith
theorem one_lt_log_three_mul {x : ℝ} (hx : 1 ≤ x) : 1 < log (3 * x) := by
  rw [lt_log_iff_exp_lt (by linarith)]
  have := exp_one_lt_d9
  linarith
theorem log_rpow_one_div_xi {y : ℝ} (hy : 1 < y) :
    log (y ^ (1 / xi y)) = log (log (3 * y)) ^ (11 / 5 : ℝ) := by
  have hL : 0 < log y := log_pos hy
  have hℓ : 0 < log (log (3 * y)) := log_pos (one_lt_log_three_mul hy.le)
  have hP : 0 < log (log (3 * y)) ^ (11 / 5 : ℝ) := rpow_pos_of_pos hℓ _
  rw [log_rpow_one_div (by linarith), xi, div_div_cancel₀ hL.ne']
theorem inner_le_xi {y : ℝ} {p : ℕ} (hy : 1 < y) (hp : 1 < p) (hpy : (p : ℝ) < y)
    (hw : y ^ (1 / xi y) ≤ p) : log y / log p - 1 ≤ xi (y / p) := by
  have hp0 : (0 : ℝ) < p := by positivity
  have hy0 : 0 < y := by linarith
  have hlp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp)
  have hℓ : 0 < log (log (3 * y)) := log_pos (one_lt_log_three_mul hy.le)
  have hyp1 : 1 < y / p := by rw [one_lt_div hp0]; exact hpy
  have hℓ' : 0 < log (log (3 * (y / p))) := log_pos (one_lt_log_three_mul hyp1.le)
  have hℓℓ' : log (log (3 * (y / p))) ≤ log (log (3 * y)) := by
    refine log_le_log (log_pos (by linarith)) (log_le_log (by positivity) ?_)
    gcongr
    exact div_le_self hy0.le (by exact_mod_cast hp.le)
  have hP' : 0 < log (log (3 * (y / p))) ^ (11 / 5 : ℝ) := rpow_pos_of_pos hℓ' _
  have hPP : log (log (3 * (y / p))) ^ (11 / 5 : ℝ) ≤ log (log (3 * y)) ^ (11 / 5 : ℝ) :=
    rpow_le_rpow hℓ'.le hℓℓ' (by norm_num)
  have hw' : log (log (3 * y)) ^ (11 / 5 : ℝ) ≤ log p := by
    rw [← log_rpow_one_div_xi hy]
    exact log_le_log (rpow_pos_of_pos hy0 _) hw
  have ht : 0 < log y / log p - 1 := by
    rw [sub_pos, one_lt_div hlp]; exact log_lt_log hp0 hpy
  rw [xi, log_div_prime_eq hy0 hp, le_div_iff₀ hP']
  calc (log y / log p - 1) * log (log (3 * (y / p))) ^ (11 / 5 : ℝ)
      ≤ (log y / log p - 1) * log p := by
        gcongr; exact hPP.trans hw'
    _ = log p * (log y / log p - 1) := mul_comm _ _
theorem rosserPrimes_filter_lt {lower : Bool} {y z w : ℝ} (hwz : w ≤ z) :
    (rosserPrimes lower y z).filter (fun p : ℕ ↦ ¬ w ≤ p) = rosserPrimes lower y w := by
  ext p
  simp only [mem_filter, mem_rosserPrimes, mem_primesLT, not_le]
  constructor
  · rintro ⟨⟨⟨hp, -⟩, h⟩, hw⟩; exact ⟨⟨hp, hw⟩, h⟩
  · rintro ⟨⟨hp, hw⟩, h⟩; exact ⟨⟨⟨hp, hw.trans_le hwz⟩, h⟩, hw⟩
theorem fail_succ_le_split (lower : Bool) (r : ℕ) {y z w : ℝ} (hwz : w ≤ z) :
    fail lower (r + 1) y z ≤ fail lower (r + 1) y w +
      ∑ p ∈ (rosserPrimes lower y z).filter (fun p : ℕ ↦ w ≤ p),
        fail (!lower) r (y / p) p / p + src lower y z := by
  rw [fail_succ_eq, fail_succ_eq lower r y w,
    ← sum_filter_add_sum_filter_not (rosserPrimes lower y z) (fun p : ℕ ↦ w ≤ (p : ℝ)),
    rosserPrimes_filter_lt hwz]
  linarith [src_nonneg lower y w]
end IwaniecLinearSieve.TheoremFour
end
section
open Real Set Filter Topology MeasureTheory Finset
namespace IwaniecLinearSieve.TheoremFour
theorem loglog_three_mul_pos {y : ℝ} (hy : 1 < y) : 0 < log (log (3 * y)) :=
  log_pos (one_lt_log_three_mul hy.le)
theorem log_add_log_three {y : ℝ} (hy : 1 < y) :
    log y + log 3 = exp (log (log (3 * y))) := by
  rw [exp_log (by linarith [one_lt_log_three_mul hy.le]), log_mul (by norm_num) (by linarith)]
  ring
theorem xi_mul_rpow {y : ℝ} (hy : 1 < y) :
    xi y * log (log (3 * y)) ^ (11 / 5 : ℝ) = log y := by
  rw [xi, div_mul_cancel₀ _ (rpow_pos_of_pos (loglog_three_mul_pos hy) _).ne']
theorem pntE_rpow_one_div_xi {y : ℝ} (hy : 1 < y) :
    pntE (y ^ (1 / xi y)) = exp (-pntκ * log (log (3 * y)) ^ (11 / 10 : ℝ)) := by
  rw [pntE, log_rpow_one_div_xi hy, sqrt_eq_rpow, ← rpow_mul (loglog_three_mul_pos hy).le]
  norm_num
theorem xi_nonneg {y : ℝ} (hy : 1 < y) : 0 ≤ xi y :=
  div_nonneg (log_pos hy).le (rpow_nonneg (loglog_three_mul_pos hy).le _)
theorem xi_le_log {y : ℝ} (hy : 1 < y) (hℓ : 1 ≤ log (log (3 * y))) : xi y ≤ log y :=
  div_le_self (log_pos hy).le (one_le_rpow hℓ (by norm_num))
theorem tendsto_lin_sub_rpow :
    Tendsto (fun ℓ : ℝ => 5 * ℓ - pntκ * ℓ ^ (11 / 10 : ℝ)) atTop atBot := by
  have h := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).eventually
    (eventually_ge_atTop (6 / pntκ))
  refine tendsto_atBot_mono' atTop ?_ tendsto_neg_atTop_atBot
  filter_upwards [h, eventually_gt_atTop 0] with ℓ h hℓ
  have hsplit : ℓ ^ (11 / 10 : ℝ) = ℓ * ℓ ^ (1 / 10 : ℝ) := by
    rw [show (11 / 10 : ℝ) = 1 + 1 / 10 by norm_num, rpow_add hℓ, rpow_one]
  have h6 : 6 ≤ pntκ * ℓ ^ (1 / 10 : ℝ) := by
    rw [div_le_iff₀ pntκ_pos] at h; linarith
  rw [hsplit]
  nlinarith
theorem tendsto_log_pow_pntE :
    Tendsto (fun y : ℝ => log y ^ 5 * pntE (y ^ (1 / xi y))) atTop (𝓝 0) := by
  have hT : Tendsto (fun y : ℝ => exp (5 * log (log (3 * y)) -
      pntκ * log (log (3 * y)) ^ (11 / 10 : ℝ))) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp (tendsto_lin_sub_rpow.comp tendsto_log_log_three_mul)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hT ?_ ?_
  · filter_upwards [eventually_gt_atTop 1] with y hy
    have := log_pos hy
    have := pntE_pos (y ^ (1 / xi y))
    positivity
  · filter_upwards [eventually_gt_atTop 1] with y hy
    have hL := log_pos hy
    have hLe : log y ≤ exp (log (log (3 * y))) := by
      rw [← log_add_log_three hy]; linarith [log_pos (by norm_num : (1 : ℝ) < 3)]
    rw [pntE_rpow_one_div_xi hy, sub_eq_add_neg, exp_add, ← neg_mul]
    gcongr
    calc log y ^ 5 ≤ exp (log (log (3 * y))) ^ 5 := by gcongr
      _ = _ := by rw [← exp_nat_mul]; norm_num
theorem eventually_one_le_loglog : ∀ᶠ y : ℝ in atTop, 1 ≤ log (log y) :=
  (tendsto_log_atTop.comp tendsto_log_atTop).eventually (eventually_ge_atTop 1)
theorem eventually_mul_pntE_le (K : ℝ) : ∀ᶠ y : ℝ in atTop,
    K * xi y ^ 2 * log y ^ 3 * pntE (y ^ (1 / xi y)) ≤ 1 := by
  have hK : (0 : ℝ) < 1 / (|K| + 1) := by positivity
  filter_upwards [tendsto_log_pow_pntE.eventually (eventually_le_nhds hK),
    eventually_gt_atTop 1, tendsto_log_log_three_mul.eventually (eventually_ge_atTop 1)]
    with y h1 hy hℓ
  have hL := log_pos hy
  have hξ0 := xi_nonneg hy
  have hξL := xi_le_log hy hℓ
  have hpE := pntE_pos (y ^ (1 / xi y))
  have hsq : xi y ^ 2 * log y ^ 3 ≤ log y ^ 5 := by
    have : xi y ^ 2 ≤ log y ^ 2 := by gcongr
    calc xi y ^ 2 * log y ^ 3 ≤ log y ^ 2 * log y ^ 3 := by gcongr
      _ = log y ^ 5 := by ring
  have h2 : |K| * (log y ^ 5 * pntE (y ^ (1 / xi y))) ≤ |K| * (1 / (|K| + 1)) := by gcongr
  have h3 : |K| * (1 / (|K| + 1)) ≤ 1 := by
    rw [mul_one_div, div_le_one (by positivity)]; linarith
  calc K * xi y ^ 2 * log y ^ 3 * pntE (y ^ (1 / xi y))
      ≤ |K| * (xi y ^ 2 * log y ^ 3) * pntE (y ^ (1 / xi y)) := by
        rw [mul_assoc K]; gcongr; exact le_abs_self K
    _ ≤ |K| * log y ^ 5 * pntE (y ^ (1 / xi y)) := by gcongr
    _ ≤ 1 := by rw [mul_assoc]; linarith
theorem exp_le_one_add_two_mul {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    exp v ≤ 1 + 2 * v := by
  have h := (abs_le.1 (abs_exp_sub_one_sub_id_le
    (by rw [abs_of_nonneg hv0]; exact hv1))).2
  nlinarith only [h, hv0, hv1]
theorem eventually_delta_mul_le (C : ℝ) (hC : 0 ≤ C) : ∀ᶠ y : ℝ in atTop,
    delta (exp 32) y * (1 + C * xi y ^ 2 * pntE (y ^ (1 / xi y))) ≤
      1 + log (log y) ^ 2 / (8 * log y ^ 2) := by
  set A : ℝ := 5 * exp 32 * (exp 32 ^ 2 * 32 ^ 5) with hA
  have hA0 : 0 ≤ A := by positivity
  have hsq := tendsto_pow_atTop (α := ℝ) (two_ne_zero)
  filter_upwards [eventually_mul_pntE_le (2 * C),
    tendsto_log_atTop.eventually (eventually_ge_atTop 1),
    (hsq.comp tendsto_log_atTop).eventually (eventually_ge_atTop (A + 1)),
    (hsq.comp (tendsto_log_atTop.comp tendsto_log_atTop)).eventually
      (eventually_ge_atTop (8 * (2 * A + 1)))] with y hPNT hL1 hL2 hΛ
  simp only [Function.comp] at hL2 hΛ
  set L := log y
  set b := C * xi y ^ 2 * pntE (y ^ (1 / xi y))
  have hL : 0 < L := by linarith only [hL1]
  have hLsq : 0 < L ^ 2 := by positivity
  have hpE := pntE_pos (y ^ (1 / xi y))
  have hb0 : 0 ≤ b := by positivity
  have hbL : b * L ^ 2 ≤ 1 / 2 := by
    have hbL3 : b * L ^ 3 ≤ 1 / 2 := by
      dsimp [b, L]
      nlinarith only [hPNT]
    calc b * L ^ 2 ≤ b * L ^ 3 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL1 (by norm_num : 2 ≤ 3)) hb0
      _ ≤ 1 / 2 := hbL3
  have hδ : delta (exp 32) y ≤ exp (A / L ^ 2) := by
    rw [delta, log_exp]
    set x := exp 32 ^ 2 * 32 ^ 5 / L ^ 2
    have hx : 0 ≤ x := by positivity
    rw [rpow_def_of_pos (by linarith only [hx])]
    apply exp_le_exp.2
    have hlog := log_le_sub_one_of_pos (by linarith only [hx] : 0 < 1 + x)
    calc log (1 + x) * (5 * exp 32) ≤ x * (5 * exp 32) := by
          gcongr
          linarith only [hlog]
      _ = A / L ^ 2 := by rw [hA]; simp only [x]; ring
  set v := A / L ^ 2 + b
  have hv0 : 0 ≤ v := by positivity
  have hvL : v * L ^ 2 ≤ A + 1 / 2 := by
    calc v * L ^ 2 = A + b * L ^ 2 := by simp only [v]; field_simp
      _ ≤ A + 1 / 2 := add_le_add le_rfl hbL
  have hv1 : v ≤ 1 := by
    have : v * L ^ 2 ≤ 1 * L ^ 2 := by linarith only [hvL, hL2]
    exact le_of_mul_le_mul_right this hLsq
  have h2v : 2 * v ≤ log (log y) ^ 2 / (8 * L ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    linarith only [hvL, hΛ]
  calc delta (exp 32) y * (1 + b) ≤ exp (A / L ^ 2) * exp b :=
        mul_le_mul hδ (by simpa only [add_comm] using add_one_le_exp b)
          (by linarith only [hb0]) (exp_pos _).le
    _ = exp v := by rw [← exp_add]
    _ ≤ 1 + 2 * v := exp_le_one_add_two_mul hv0 hv1
    _ ≤ _ := add_le_add le_rfl h2v
theorem mul_log_sub_le {ξ : ℝ} (hξ : 2 < ξ) :
    ξ * log ξ - (ξ - 2) * log (ξ - 2) ≤ 2 * log ξ + 2 := by
  have hu : 0 < ξ - 2 := by linarith
  have h := log_le_sub_one_of_pos (div_pos (by linarith : 0 < ξ) hu)
  rw [log_div (by linarith) hu.ne'] at h
  have h' : (ξ - 2) * (log ξ - log (ξ - 2)) ≤ (ξ - 2) * (ξ / (ξ - 2) - 1) :=
    mul_le_mul_of_nonneg_left h hu.le
  have e : (ξ - 2) * (ξ / (ξ - 2) - 1) = 2 := by field_simp; ring
  nlinarith
theorem crude_half_exponent_le {c ℓ L ξ X : ℝ} (hℓ_large : 2 ≤ ℓ) (hxi_large : 8 * ℓ ≤ ξ)
    (hlogL_upper : log L ≤ ℓ) (hlogX_nonneg : 0 ≤ log X) (hlogX_upper : log X ≤ log ℓ / 4)
    (hlog_shift_lower : log (ξ / 2) ≤ log (ξ - 2)) (hlog_half_lower : ℓ / 2 ≤ log (ξ / 2))
    (hloglog_half_upper : log (log (ξ / 2)) ≤ log ℓ)
    (herror_budget : 2 + c / 2 + 3 / 4 * log ℓ ≤ ℓ / 8) :
    log 2 + (-((ξ - 2) * log (ξ - 2)) + (ξ - 2) * log X + (ξ - 2)) + 4 * log L ≤
      -(ξ / 2 * log (ξ / 2)) - ξ / 2 * log (log (ξ / 2)) - c * (ξ / 2) := by
  have hxi_nonneg : 0 ≤ ξ := by linarith only [hℓ_large, hxi_large]
  have hshifted_log := mul_le_mul_of_nonneg_left hlog_shift_lower
    (by linarith only [hℓ_large, hxi_large] : 0 ≤ ξ - 2)
  have hweighted_logX := mul_le_mul_of_nonneg_left hlogX_upper hxi_nonneg
  have hhalf_log_gap := mul_le_mul_of_nonneg_left hlog_half_lower
    (by linarith only [hℓ_large, hxi_large] : 0 ≤ ξ / 2 - 2)
  have hweighted_loglog := mul_le_mul_of_nonneg_left hloglog_half_upper
    (by linarith only [hxi_nonneg] : 0 ≤ ξ / 2)
  have hweighted_budget := mul_le_mul_of_nonneg_left herror_budget hxi_nonneg
  have hlinear_gap : ξ / 4 * (ℓ / 2) ≤ (ξ / 2 - 2) * (ℓ / 2) :=
    mul_le_mul_of_nonneg_right (by linarith only [hℓ_large, hxi_large])
      (by linarith only [hℓ_large])
  have hdecay : ξ * (ℓ / 8) ≤ (ξ / 2 - 2) * log (ξ / 2) := by
    linarith only [hhalf_log_gap, hlinear_gap]
  calc log 2 + (-((ξ - 2) * log (ξ - 2)) + (ξ - 2) * log X + (ξ - 2)) + 4 * log L
      ≤ -(ξ / 2 * log (ξ / 2)) - ξ / 2 * log ℓ - c * (ξ / 2) := by
        linarith only [hshifted_log, hweighted_logX, hweighted_budget, hdecay,
          hlogX_nonneg, hlogL_upper, hxi_large, hℓ_large, log_two_lt_d9]
    _ ≤ -(ξ / 2 * log (ξ / 2)) - ξ / 2 * log (log (ξ / 2)) - c * (ξ / 2) := by
        linarith only [hweighted_loglog]
theorem crude_full_exponent_le {c ℓ L ξ X x : ℝ} (hℓ_large : 2 ≤ ℓ) (hxi_large : 8 * ℓ ≤ ξ)
    (hlogL_upper : log L ≤ ℓ) (hlogX_nonneg : 0 ≤ log X) (hlogX_upper : log X ≤ log ℓ / 4)
    (hlogxi_upper : log ξ ≤ ℓ) (hloglogxi_upper : log (log ξ) ≤ log ℓ)
    (hlogx_lower : 3 / 5 * log ℓ - 7 * log 2 ≤ log x)
    (herror_budget : 2 + c + 18 * log 2 ≤ log ℓ / 4) :
    log 2 + (-((ξ - 2) * log (ξ - 2)) + (ξ - 2) * log X + (ξ - 2)) + 4 * log L ≤
      log x * (5 * (ξ / 2)) + (-(ξ * log ξ) - ξ * log (log ξ) - c * ξ) := by
  have hxi_nonneg : 0 ≤ ξ := by linarith only [hℓ_large, hxi_large]
  have hweighted_logX := mul_le_mul_of_nonneg_left hlogX_upper hxi_nonneg
  have hweighted_loglog := mul_le_mul_of_nonneg_left hloglogxi_upper hxi_nonneg
  have hweighted_logx := mul_le_mul_of_nonneg_right hlogx_lower
    (by linarith only [hxi_nonneg] : 0 ≤ 5 * (ξ / 2))
  have hweighted_budget := mul_le_mul_of_nonneg_left herror_budget hxi_nonneg
  have hshift_loss := mul_log_sub_le (by linarith only [hℓ_large, hxi_large] : 2 < ξ)
  have hlog_two_margin : 0 ≤ (ξ / 2 - 1) * log 2 :=
    mul_nonneg (by linarith only [hℓ_large, hxi_large]) (log_nonneg (by norm_num))
  calc log 2 + (-((ξ - 2) * log (ξ - 2)) + (ξ - 2) * log X + (ξ - 2)) + 4 * log L
      ≤ log x * (5 * (ξ / 2)) + (-(ξ * log ξ) - ξ * log ℓ - c * ξ) := by
        linarith only [hweighted_logX, hweighted_logx, hweighted_budget, hshift_loss,
          hlog_two_margin, hlogX_nonneg, hlogL_upper, hlogxi_upper, hxi_large, hℓ_large]
    _ ≤ log x * (5 * (ξ / 2)) + (-(ξ * log ξ) - ξ * log (log ξ) - c * ξ) := by
        linarith only [hweighted_loglog]
theorem crude_alg {c C' ℓ L ξ : ℝ} (hc : 0 ≤ c) (hC' : 1 ≤ C') (hℓ : 2 ≤ ℓ)
    (hL : L + log 3 = exp ℓ) (hξ : ξ * ℓ ^ (11 / 5 : ℝ) = L) (h2 : 2 * log 3 ≤ exp ℓ)
    (h3 : 4 * ℓ ^ (11 / 5 : ℝ) ≤ exp (ℓ / 2)) (h4 : 11 / 5 * log ℓ + C' ≤ ℓ ^ (1 / 4 : ℝ))
    (h5 : 2 + c + 18 * log 2 ≤ log ℓ / 4) (h6 : 2 + c / 2 + 3 / 4 * log ℓ ≤ ℓ / 8) :
    0 < 11 / 5 * log ℓ + C' ∧ 2 * exp 1 * (11 / 5 * log ℓ + C') ≤ ξ - 2 ∧
    2 * (exp 1 * (11 / 5 * log ℓ + C') / (ξ - 2)) ^ (ξ - 2) * L ^ 4 ≤
      exp (-(ξ / 2 * log (ξ / 2)) - ξ / 2 * log (log (ξ / 2)) - c * (ξ / 2)) ∧
    2 * (exp 1 * (11 / 5 * log ℓ + C') / (ξ - 2)) ^ (ξ - 2) * L ^ 4 ≤
      (1 + (ξ / 2) ^ 2 * log (ξ / 2) ^ 5 / L ^ 2) ^ (5 * (ξ / 2)) *
        exp (-(ξ * log ξ) - ξ * log (log ξ) - c * ξ) := by
  set P := ℓ ^ (11 / 5 : ℝ) with hPdef
  set X := 11 / 5 * log ℓ + C'
  have hℓ0 : 0 < ℓ := by linarith only [hℓ]
  have hlℓ : 0 < log ℓ := log_pos (by linarith only [hℓ])
  have hPℓ : ℓ ≤ P := self_le_rpow_of_one_le (by linarith only [hℓ]) (by norm_num)
  have hP0 : 0 < P := by linarith only [hPℓ, hℓ]
  have hl3 : 0 < log 3 := log_pos (by norm_num)
  have hL0 : 0 < L := by linarith only [hL, h2, hl3]
  have hLe : L ≤ exp ℓ := by linarith only [hL, hl3]
  have hlogL : log L ≤ ℓ := by
    calc log L ≤ log (exp ℓ) := log_le_log hL0 hLe
      _ = ℓ := log_exp ℓ
  have hξdef : ξ = L / P := by rw [← hξ]; field_simp
  have hξ0 : 0 < ξ := by rw [hξdef]; exact div_pos hL0 hP0
  have hξL : ξ ≤ L := by rw [hξdef]; exact div_le_self hL0.le (by linarith only [hPℓ, hℓ])
  have hlogξ : log ξ ≤ ℓ := (log_le_log hξ0 hξL).trans hlogL
  have hE0 := exp_pos (ℓ / 2)
  have he2 : exp ℓ = exp (ℓ / 2) * exp (ℓ / 2) := by rw [← exp_add]; ring_nf
  have hξbig : 2 * exp (ℓ / 2) ≤ ξ := by
    rw [hξdef, le_div_iff₀ hP0]
    nlinarith only [hL, h2, he2, mul_le_mul_of_nonneg_left h3 hE0.le]
  have hξlarge : 8 * ℓ ≤ ξ := by linarith only [hξbig, h3, hPℓ]
  have hlogξ2 : ℓ / 2 ≤ log (ξ / 2) := by
    calc ℓ / 2 = log (exp (ℓ / 2)) := (log_exp _).symm
      _ ≤ log (ξ / 2) := log_le_log hE0 (by linarith only [hξbig])
  have hX1 : 1 ≤ X := by
    dsimp [X]; linarith only [hlℓ, hC']
  have hX0 : 0 < X := by linarith only [hX1]
  have hq : ℓ ^ (1 / 4 : ℝ) ≤ ℓ := rpow_le_self_of_one_le (by linarith only [hℓ]) (by norm_num)
  have hXℓ : X ≤ ℓ := h4.trans hq
  have hlogX0 : 0 ≤ log X := log_nonneg hX1
  have hlogX : log X ≤ log ℓ / 4 := by
    have := log_le_log hX0 h4
    rw [log_rpow hℓ0] at this; linarith only [this]
  have he : exp 1 < 2.72 := by have := exp_one_lt_d9; norm_num at this ⊢; linarith only [this]
  have h2e : 2 * exp 1 * X ≤ ξ - 2 := by
    have : exp 1 * X ≤ 2.72 * ℓ := mul_le_mul he.le hXℓ hX0.le (by norm_num)
    linarith only [this, hξlarge, hℓ]
  have hu0 : 0 < ξ - 2 := by linarith only [hξlarge, hℓ]
  have hL4 : L ^ 4 = exp (4 * log L) := by
    rw [show (4 : ℝ) * log L = log (L ^ 4) by rw [log_pow]; norm_num, exp_log (by positivity)]
  have hcr : 2 * (exp 1 * X / (ξ - 2)) ^ (ξ - 2) * L ^ 4 =
      exp (log 2 + (-((ξ - 2) * log (ξ - 2)) + (ξ - 2) * log X + (ξ - 2)) + 4 * log L) := by
    rw [exp_add, exp_add, exp_log two_pos, ← hL4, ← exp_one_mul_div_rpow hX0 hu0]
  have hlam0 : 0 < log (ξ / 2) := by linarith only [hlogξ2, hℓ]
  have hlogu : log (ξ / 2) ≤ log (ξ - 2) :=
    log_le_log (by positivity) (by linarith only [hξlarge, hℓ])
  have hlamξ : log (ξ / 2) ≤ log ξ := log_le_log (by positivity) (by linarith only [hξ0])
  have hlllam : log (log (ξ / 2)) ≤ log ℓ := log_le_log hlam0 (hlamξ.trans hlogξ)
  refine ⟨hX0, h2e, ?_, ?_⟩ <;> rw [hcr]
  ·
    apply exp_le_exp.2
    exact crude_half_exponent_le hℓ hξlarge hlogL hlogX0 hlogX hlogu hlogξ2 hlllam h6
  ·
    set x := (ξ / 2) ^ 2 * log (ξ / 2) ^ 5 / L ^ 2 with hx
    have hx0 : 0 < x := by positivity
    have h1 : exp (log x * (5 * (ξ / 2))) ≤ (1 + x) ^ (5 * (ξ / 2)) := by
      rw [← rpow_def_of_pos hx0]
      exact rpow_le_rpow hx0.le (by linarith only) (by positivity)
    refine le_trans ?_ (mul_le_mul_of_nonneg_right h1 (exp_pos _).le)
    rw [← exp_add]
    apply exp_le_exp.2
    have hlogx : log x = 2 * log (ξ / 2) + 5 * log (log (ξ / 2)) - 2 * log L := by
      rw [hx, log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity),
        log_pow, log_pow, log_pow]
      push_cast; ring
    have hlam : log (ξ / 2) = log L - log 2 - 11 / 5 * log ℓ := by
      rw [hξdef, div_div, log_div hL0.ne' (by positivity), log_mul hP0.ne' (by norm_num),
        hPdef, log_rpow hℓ0]
      ring
    have hlllam' : log ℓ - log 2 ≤ log (log (ξ / 2)) := by
      rw [← log_div hℓ0.ne' (by norm_num)]
      exact log_le_log (by positivity) hlogξ2
    have hlx : 3 / 5 * log ℓ - 7 * log 2 ≤ log x := by
      rw [hlogx]; linarith only [hlam, hlllam']
    have hlξ0 : 0 < log ξ := log_pos (by linarith only [hℓ, hξlarge])
    exact crude_full_exponent_le hℓ hξlarge hlogL hlogX0 hlogX hlogξ
      (log_le_log hlξ0 hlogξ) hlx h5
theorem eventually_crude_hyp (c C' : ℝ) : ∀ᶠ ℓ : ℝ in atTop,
    2 ≤ ℓ ∧ 2 * log 3 ≤ exp ℓ ∧ 4 * ℓ ^ (11 / 5 : ℝ) ≤ exp (ℓ / 2) ∧
    11 / 5 * log ℓ + C' ≤ ℓ ^ (1 / 4 : ℝ) ∧ 2 + c + 18 * log 2 ≤ log ℓ / 4 ∧
    2 + c / 2 + 3 / 4 * log ℓ ≤ ℓ / 8 := by
  have hF3 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (11 / 5) (1 / 2)
    (by norm_num)).eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have hF4 := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).bound
    (by norm_num : (0 : ℝ) < 1 / 5)
  have hF6 := isLittleO_log_id_atTop.bound (by norm_num : (0 : ℝ) < 1 / 16)
  filter_upwards [eventually_ge_atTop 2, tendsto_exp_atTop.eventually
      (eventually_ge_atTop (2 * log 3)), hF3, hF4, (tendsto_rpow_atTop
      (by norm_num : (0 : ℝ) < 1 / 4)).eventually (eventually_ge_atTop (2 * C')),
    tendsto_log_atTop.eventually (eventually_ge_atTop (4 * (2 + c + 18 * log 2))), hF6,
    eventually_ge_atTop (16 * (2 + |c|))] with ℓ h1 h2 h3 h4 h4' h5 h6 h6'
  have hℓ0 : 0 < ℓ := by linarith
  have hlℓ : 0 ≤ log ℓ := log_nonneg (by linarith)
  refine ⟨h1, h2, ?_, ?_, by linarith, ?_⟩
  · have := mul_le_mul_of_nonneg_right h3 (exp_pos (ℓ / 2)).le
    rw [mul_assoc, ← exp_add, show -(1 / 2) * ℓ + ℓ / 2 = 0 by ring, exp_zero, mul_one] at this
    linarith
  · have hq := rpow_nonneg hℓ0.le (1 / 4 : ℝ)
    rw [norm_of_nonneg hlℓ, norm_of_nonneg hq] at h4
    linarith
  · rw [norm_of_nonneg hlℓ, id, norm_of_nonneg hℓ0.le] at h6
    have := le_abs_self c
    have := abs_nonneg c
    linarith
theorem eventually_crude (c C' : ℝ) (hc : 0 ≤ c) (hC' : 1 ≤ C') : ∀ᶠ y : ℝ in atTop,
    0 < log (log (y ^ (1 / xi y))) + C' ∧
    2 * exp 1 * (log (log (y ^ (1 / xi y))) + C') ≤ xi y - 2 ∧
    2 * (exp 1 * (log (log (y ^ (1 / xi y))) + C') / (xi y - 2)) ^ (xi y - 2) * log y ^ 4 ≤
      exp (-(xi y / 2 * log (xi y / 2)) - xi y / 2 * log (log (xi y / 2)) - c * (xi y / 2)) ∧
    2 * (exp 1 * (log (log (y ^ (1 / xi y))) + C') / (xi y - 2)) ^ (xi y - 2) * log y ^ 4 ≤
      delta (xi y / 2) y * exp (-(xi y * log (xi y)) - xi y * log (log (xi y)) - c * xi y) := by
  filter_upwards [tendsto_log_log_three_mul.eventually (eventually_crude_hyp c C'),
    eventually_gt_atTop 1] with y h hy
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hlw : log (log (y ^ (1 / xi y))) = 11 / 5 * log (log (log (3 * y))) := by
    rw [log_rpow_one_div_xi hy, log_rpow (loglog_three_mul_pos hy)]
  rw [hlw, delta]
  exact crude_alg hc hC' h1 (log_add_log_three hy) (xi_mul_rpow hy) h2 h3 h4 h5 h6
end IwaniecLinearSieve.TheoremFour
end
section
open Real Set Filter Topology MeasureTheory Finset
namespace IwaniecLinearSieve.TheoremFour
def Bound (cR c₇ : ℝ) (r : ℕ) : Prop :=
  ∀ (lower : Bool) (y s : ℝ), 1 < y → sMin lower ≤ s → s ≤ xi y →
    fail lower r y (y ^ (1 / s)) ≤
      cR * (mainMaj lower s / log y +
        c₇ * ((r : ℝ) / (r + 1)) * delta s y * errMaj lower s / log y ^ 2)
theorem one_le_sMin (lower : Bool) : 1 ≤ sMin lower := by
  cases lower <;> norm_num [sMin]
theorem ih_term {cR c₇ : ℝ} {r : ℕ} (IH : Bound cR c₇ r) {lower : Bool} {y s : ℝ} {p : ℕ}
    (hy : 1 < y) (hs : sMin lower ≤ s) (hp : p ∈ rosserPrimes lower y (y ^ (1 / s)))
    (hw : y ^ (1 / xi y) ≤ p) :
    fail (!lower) r (y / p) p / p ≤
      cR * (mainMaj (!lower) (log y / log p - 1) / (p * log (y / p))) +
      cR * c₇ * ((r : ℝ) / (r + 1)) * (delta (log y / log p - 1) (y / p) *
        errMaj (!lower) (log y / log p - 1) / (p * log (y / p) ^ 2)) := by
  have hs1 : 1 ≤ s := (one_le_sMin lower).trans hs
  have hpy := prime_lt_of_mem_rosserPrimes hy hs1 hp
  have hp1 := (prime_of_mem_primesLT (rosserPrimes_subset hp)).one_lt
  have hp0 : (0 : ℝ) < p := by positivity
  have hyp : 1 < y / p := by rw [one_lt_div hp0]; exact hpy
  have h := IH (!lower) (y / p) (log y / log p - 1) hyp (sMin_le_inner hy hs hp)
    (inner_le_xi hy hp1 hpy hw)
  rw [rpow_inner_eq hp1 hpy] at h
  refine (div_le_div_of_nonneg_right h hp0.le).trans_eq ?_
  field_simp
theorem sum_ih_le {cR c₇ : ℝ} {r : ℕ} (IH : Bound cR c₇ r) {lower : Bool} {y s : ℝ}
    (hy : 1 < y) (hs : sMin lower ≤ s) :
    ∑ p ∈ (rosserPrimes lower y (y ^ (1 / s))).filter (fun p : ℕ => y ^ (1 / xi y) ≤ p),
        fail (!lower) r (y / p) p / p ≤
      cR * ∑ p ∈ (rosserPrimes lower y (y ^ (1 / s))).filter (fun p : ℕ => y ^ (1 / xi y) ≤ p),
          mainMaj (!lower) (log y / log p - 1) / (p * log (y / p)) +
      cR * c₇ * ((r : ℝ) / (r + 1)) *
        ∑ p ∈ (rosserPrimes lower y (y ^ (1 / s))).filter (fun p : ℕ => y ^ (1 / xi y) ≤ p),
          delta (log y / log p - 1) (y / p) * errMaj (!lower) (log y / log p - 1) /
            (p * log (y / p) ^ 2) := by
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun p hp => ?_
  rw [mem_filter] at hp
  exact ih_term IH hy hs hp.1 hp.2
theorem intervalIntegral_le_integral_Ioi {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : IntegrableOn f (Ioi a)) (hf0 : ∀ t ∈ Ioi a, 0 ≤ f t) :
    ∫ t in a..b, f t ≤ ∫ t in Ioi a, f t := by
  rw [intervalIntegral.integral_of_le hab]
  exact setIntegral_mono_set hf (ae_restrict_of_forall_mem measurableSet_Ioi hf0)
    Ioc_subset_Ioi_self.eventuallyLE
theorem cor1_part (hPNT : StrongPNTProp) : ∃ C, 0 ≤ C ∧ ∀ (lower : Bool) (y s : ℝ), 1 < y → sMin lower ≤ s →
    s ≤ xi y → 3 ≤ xi y → 2 ≤ y ^ (1 / xi y) →
    ∑ p ∈ (rosserPrimes lower y (y ^ (1 / s))).filter (fun p : ℕ => y ^ (1 / xi y) ≤ p),
        mainMaj (!lower) (log y / log p - 1) / (p * log (y / p)) ≤
      (mainMaj lower s - (if lower then 0 else max (3 - s) 0)) / log y +
        C * s ^ 2 * errMaj lower s * pntE (y ^ (1 / xi y)) / log y := by
  obtain ⟨C, hC0, hC⟩ := (cor1_le hPNT)
  refine ⟨432 * C, by positivity, fun lower y s hy hs hsξ hξ3 hw2 => ?_⟩
  have hL : 0 < log y := log_pos hy
  have hs1 : 1 ≤ s := (one_le_sMin lower).trans hs
  have hpE := pntE_pos (y ^ (1 / xi y))
  cases lower
  ·
    simp only [Bool.not_false, mainMaj_true, Bool.false_eq_true, ite_false]
    have hset : (rosserPrimes false y (y ^ (1 / s))).filter (fun p : ℕ => y ^ (1 / xi y) ≤ p) =
        (primesLT (y ^ (1 / max s 3))).filter (fun p : ℕ => y ^ (1 / xi y) ≤ p) := by
      ext p
      simp only [mem_filter, mem_rosserPrimes, mem_primesLT, Bool.false_eq_true, false_or]
      rw [lt_rpow_one_div_max_three hy (by linarith) (Nat.cast_nonneg p)]
      tauto
    rw [hset]
    have hα : max s 3 ≤ xi y := max_le hsξ hξ3
    have h := hC fSieve y (max s 3) (xi y) hy (by linarith [le_max_right s 3]) hα hw2
      (fSieve_antitone.antitoneOn _) (fun t _ => (fSieve_pos t).le)
    refine h.trans (add_le_add ?_ ?_)
    · have hint := intervalIntegral_le_integral_Ioi hα
        (integrableOn_fSieve_shift (le_max_right s 3))
        (fun t ht => div_nonneg (fSieve_pos _).le (by linarith [ht.out, le_max_right s 3]))
      have heq := mainMaj_false_eq_integral s
      exact div_le_div_of_nonneg_right (by linarith) hL.le
    · have h1 := mainMaj_sub_one_le true false (by linarith [le_max_right s 3] : 1 ≤ max s 3)
      rw [mainMaj_true] at h1
      have hG : errMaj false (max s 3) = errMaj false s := by
        rcases le_total s 3 with h | h
        · rw [max_eq_right h, errMaj_false_of_le_three le_rfl, errMaj_false_of_le_three h]
        · rw [max_eq_left h]
      rw [hG] at h1
      have hsq : max s 3 ^ 2 ≤ 9 * s ^ 2 := by
        rcases le_total s 3 with h | h
        · rw [max_eq_right h]; nlinarith
        · rw [max_eq_left h]; nlinarith
      have hGs := errMaj_pos false s
      have : fSieve (max s 3 - 1) ≤ 432 * s ^ 2 * errMaj false s := by nlinarith
      apply div_le_div_of_nonneg_right _ hL.le
      calc C * fSieve (max s 3 - 1) * pntE (y ^ (1 / xi y))
          ≤ C * (432 * s ^ 2 * errMaj false s) * pntE (y ^ (1 / xi y)) := by gcongr
        _ = 432 * C * s ^ 2 * errMaj false s * pntE (y ^ (1 / xi y)) := by ring
  ·
    simp only [Bool.not_true, rosserPrimes_true, ite_true, sub_zero]
    have hs2 : (2 : ℝ) ≤ s := hs
    have h := hC (mainMaj false) y s (xi y) hy hs2 hsξ hw2
      ((mainMaj_antitone false).antitoneOn _) (fun t _ => mainMaj_nonneg false t)
    refine h.trans (add_le_add ?_ ?_)
    · have hint := intervalIntegral_le_integral_Ioi hsξ (integrableOn_mainMaj_false_shift hs2)
        (fun t ht => div_nonneg (mainMaj_nonneg _ _) (by linarith [ht.out]))
      rw [mainMaj_true, fSieve_eq_integral_mainMaj hs2]
      exact div_le_div_of_nonneg_right hint hL.le
    · have h1 := mainMaj_sub_one_le false true hs1
      have hGs := errMaj_pos true s
      apply div_le_div_of_nonneg_right _ hL.le
      calc C * mainMaj false (s - 1) * pntE (y ^ (1 / xi y))
          ≤ C * (432 * s ^ 2 * errMaj true s) * pntE (y ^ (1 / xi y)) := by
            gcongr; nlinarith
        _ = 432 * C * s ^ 2 * errMaj true s * pntE (y ^ (1 / xi y)) := by ring
theorem src_le_of_le_xi {cR CR : ℝ} (hR : ∀ z ≥ 2, |R z * log z - cR| ≤ CR * pntE z) {lower : Bool}
    {y s : ℝ} (hy : 1 < y) (hs : sMin lower ≤ s) (hsξ : s ≤ xi y) (hξ3 : 3 ≤ xi y)
    (hw2 : 2 ≤ y ^ (1 / xi y)) :
    src lower y (y ^ (1 / s)) ≤ (if lower then 0 else cR * max (3 - s) 0 / log y) +
      6 * CR * s ^ 2 * errMaj lower s * pntE (y ^ (1 / xi y)) / log y := by
  have hs1 : 1 ≤ s := (one_le_sMin lower).trans hs
  have hL : 0 < log y := log_pos hy
  have hCR : 0 ≤ CR := by
    have h := (abs_nonneg _).trans (hR 2 le_rfl)
    exact nonneg_of_mul_nonneg_left h (pntE_pos 2)
  have hpE := pntE_pos (y ^ (1 / xi y))
  have hE : 0 ≤ 6 * CR * s ^ 2 * errMaj lower s * pntE (y ^ (1 / xi y)) / log y := by
    have := errMaj_pos lower s; positivity
  cases lower
  · simp only [Bool.false_eq_true, ite_false]
    rcases le_total 3 s with h3 | h3
    ·
      have : src false y (y ^ (1 / s)) = 0 := by
        rw [src, ite_eq_right_iff.2 (by simp)]
        refine sum_eq_zero fun p hp => ?_
        rw [mem_filter, mem_primesLT] at hp
        have hlt : (p : ℝ) < y ^ (1 / (3 : ℝ)) := hp.1.2.trans_le
          (rpow_one_div_le_rpow_one_div hy.le (by norm_num) h3)
        exact absurd ((not_cube_lt_iff (by linarith) p.cast_nonneg).1 hp.2) (not_le.2 hlt)
      rw [this, max_eq_right (by linarith)]
      simpa using hE
    · refine (src_le hR hy hs1 hw2 (rpow_one_div_le_rpow_one_div hy.le (by linarith) hsξ)
        (rpow_one_div_le_rpow_one_div hy.le (by norm_num) hξ3)).trans ?_
      simp only [Bool.false_eq_true, ite_false]
      rw [errMaj_false_of_le_three h3]
      have : 6 * CR * pntE (y ^ (1 / xi y)) ≤ 6 * CR * s ^ 2 * 1 * pntE (y ^ (1 / xi y)) := by
        have : 1 ≤ s ^ 2 := by nlinarith
        have := mul_nonneg hCR hpE.le
        nlinarith
      gcongr
  · simp only [src, ite_true, zero_add]
    exact hE
theorem main_sum_add_src_le {cR CR C₁ : ℝ} (hcR : 0 ≤ cR) {lower : Bool} {y s : ℝ}
    (hcor1 : ∑ p ∈ (rosserPrimes lower y (y ^ (1 / s))).filter
        (fun p : ℕ => y ^ (1 / xi y) ≤ p),
        mainMaj (!lower) (log y / log p - 1) / (p * log (y / p)) ≤
      (mainMaj lower s - (if lower then 0 else max (3 - s) 0)) / log y +
        C₁ * s ^ 2 * errMaj lower s * pntE (y ^ (1 / xi y)) / log y)
    (hsrc : src lower y (y ^ (1 / s)) ≤ (if lower then 0 else cR * max (3 - s) 0 / log y) +
      6 * CR * s ^ 2 * errMaj lower s * pntE (y ^ (1 / xi y)) / log y) :
    cR * ∑ p ∈ (rosserPrimes lower y (y ^ (1 / s))).filter
        (fun p : ℕ => y ^ (1 / xi y) ≤ p),
        mainMaj (!lower) (log y / log p - 1) / (p * log (y / p)) +
      src lower y (y ^ (1 / s)) ≤ cR * mainMaj lower s / log y +
        (cR * C₁ + 6 * CR) * s ^ 2 * errMaj lower s * pntE (y ^ (1 / xi y)) / log y := by
  refine (add_le_add (mul_le_mul_of_nonneg_left hcor1 hcR) hsrc).trans_eq ?_
  cases lower <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> ring
theorem SLT_mono {a b : ℝ} (hab : a ≤ b) : SLT a ≤ SLT b := by
  refine sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun p _ _ => by positivity
  rw [mem_primesLT] at hp ⊢
  exact ⟨hp.1, hp.2.trans_le hab⟩
theorem fail_le_exp_SLT (lower : Bool) (r : ℕ) (y z : ℝ) : fail lower r y z ≤ exp (SLT z) := by
  refine (fail_le_sum_SLT_pow lower r y z).trans ?_
  refine le_trans ?_ (Real.sum_le_exp_of_nonneg (SLT_nonneg z) (r + 1))
  refine sum_le_sum_of_subset_of_nonneg (fun l hl => ?_) fun l _ _ => ?_
  · rw [mem_filter, Finset.mem_Icc] at hl; rw [Finset.mem_range]; omega
  · have := SLT_nonneg z; positivity
theorem xi_le_of_le {y Y : ℝ} (hy : 1 < y) (hyY : y ≤ Y) :
    xi y ≤ log Y / log (log 3) ^ (11 / 5 : ℝ) := by
  have hl3 : 1 < log 3 := by
    rw [lt_log_iff_exp_lt (by norm_num)]; have := exp_one_lt_d9; linarith
  have hll : 0 < log (log 3) := log_pos hl3
  have hL : 0 < log y := log_pos hy
  have hP : 0 < log (log 3) ^ (11 / 5 : ℝ) := rpow_pos_of_pos hll _
  have hle : log (log 3) ^ (11 / 5 : ℝ) ≤ log (log (3 * y)) ^ (11 / 5 : ℝ) := by
    refine rpow_le_rpow hll.le (log_le_log (by linarith) (log_le_log (by norm_num) ?_))
      (by norm_num)
    linarith
  rw [xi]
  calc log y / log (log (3 * y)) ^ (11 / 5 : ℝ) ≤ log y / log (log 3) ^ (11 / 5 : ℝ) :=
        div_le_div_of_nonneg_left hL.le hP hle
    _ ≤ _ := div_le_div_of_nonneg_right (log_le_log (by linarith) hyY) hP.le
theorem small_y {cR c₇ Y : ℝ} (hcR : 0 < cR) (hY : 1 < Y)
    (hc₇ : 6 * exp (SLT Y) * log Y ^ 2 / (cR * bigM (log Y / log (log 3) ^ (11 / 5 : ℝ))) ≤ c₇)
    (r : ℕ) (lower : Bool) {y s : ℝ} (hy : 1 < y) (hyY : y ≤ Y) (hs : sMin lower ≤ s)
    (hsξ : s ≤ xi y) :
    fail lower (r + 1) y (y ^ (1 / s)) ≤
      cR * (mainMaj lower s / log y +
        c₇ * (((r + 1 : ℕ) : ℝ) / ((r + 1 : ℕ) + 1)) * delta s y * errMaj lower s /
          log y ^ 2) := by
  set Ξ := log Y / log (log 3) ^ (11 / 5 : ℝ)
  have hs1 : 1 ≤ s := (one_le_sMin lower).trans hs
  have hL : 0 < log y := log_pos hy
  have hLY : log y ≤ log Y := log_le_log (by linarith) hyY
  have hMΞ := bigM_pos Ξ
  have hG : bigM Ξ / 3 ≤ errMaj lower s :=
    le_trans (by gcongr; exact bigM_antitone (hsξ.trans (xi_le_of_le hy hyY)))
      (errMaj_mem lower s).1
  have hδ := one_le_delta hs1 y
  have hρ : (1 : ℝ) / 2 ≤ ((r + 1 : ℕ) : ℝ) / ((r + 1 : ℕ) + 1) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]; push_cast; linarith
  have hz : y ^ (1 / s) ≤ Y := by
    refine le_trans ?_ hyY
    calc y ^ (1 / s) ≤ y ^ (1 / (1 : ℝ)) := rpow_one_div_le_rpow_one_div hy.le one_pos hs1
      _ = y := by simp
  have hfail : fail lower (r + 1) y (y ^ (1 / s)) ≤ exp (SLT Y) :=
    (fail_le_exp_SLT _ _ _ _).trans (exp_le_exp.2 (SLT_mono hz))
  have hc₇0 : 0 ≤ c₇ := le_trans (by positivity) hc₇
  have hM := mainMaj_nonneg lower s
  have key : exp (SLT Y) ≤ cR * (c₇ * (((r + 1 : ℕ) : ℝ) / ((r + 1 : ℕ) + 1)) * delta s y *
      errMaj lower s / log y ^ 2) := by
    have h1 : exp (SLT Y) ≤ cR * c₇ * ((1 / 2) * (bigM Ξ / 3)) / log Y ^ 2 := by
      have hK : 6 * exp (SLT Y) * log Y ^ 2 ≤ c₇ * (cR * bigM Ξ) :=
        (div_le_iff₀ (mul_pos hcR hMΞ)).1 hc₇
      rw [le_div_iff₀ (by have := log_pos hY; positivity)]
      linarith
    have hnum : cR * c₇ * ((1 / 2) * (bigM Ξ / 3)) ≤
        cR * c₇ * ((((r + 1 : ℕ) : ℝ) / ((r + 1 : ℕ) + 1)) * delta s y * errMaj lower s) := by
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hcR.le hc₇0)
      have := hMΞ.le
      have := errMaj_pos lower s
      calc (1 / 2 : ℝ) * (bigM Ξ / 3) ≤ (((r + 1 : ℕ) : ℝ) / ((r + 1 : ℕ) + 1)) *
            (delta s y * errMaj lower s) := by
            refine mul_le_mul hρ ?_ (by positivity) (by positivity)
            nlinarith
        _ = _ := by ring
    have hc0 : 0 ≤ cR * c₇ * ((((r + 1 : ℕ) : ℝ) / ((r + 1 : ℕ) + 1)) * delta s y *
        errMaj lower s) := le_trans (by positivity) hnum
    have hLL : log y ^ 2 ≤ log Y ^ 2 := by gcongr
    refine h1.trans ((div_le_div₀ hc0 hnum (by positivity) hLL).trans_eq (by ring))
  have : 0 ≤ cR * (mainMaj lower s / log y) := by positivity
  calc fail lower (r + 1) y (y ^ (1 / s)) ≤ exp (SLT Y) := hfail
    _ ≤ _ := by rw [mul_add]; linarith
theorem crude_le (hPNT : StrongPNTProp) : ∃ y₁ : ℝ, ∀ y ≥ y₁, ∀ (lower : Bool) (n : ℕ) (s : ℝ), sMin lower ≤ s →
    s ≤ xi y → fail lower n y (y ^ (1 / xi y)) ≤ delta s y * errMaj lower s / log y ^ 4 := by
  obtain ⟨c, hc⟩ := majG_ge_exp
  obtain ⟨CS, hCS⟩ := (SLT_le_loglog hPNT)
  obtain ⟨yx, hyx⟩ := exists_xi_large
  set c' := max c 0
  set C' := |CS| + 1
  obtain ⟨y₁, hy₁⟩ := eventually_atTop.1 ((eventually_crude c' C' (le_max_right _ _)
    (by simp [C'])).and (eventually_ge_atTop yx))
  refine ⟨y₁, fun y hy lower n s hs hsξ => ?_⟩
  obtain ⟨⟨hX0, h2e, hA, hB⟩, hyx'⟩ := hy₁ y hy
  obtain ⟨hy1, hξ32, -, hw2⟩ := hyx y hyx'
  set ξ := xi y
  set X := log (log (y ^ (1 / ξ))) + C'
  have hs1 : 1 ≤ s := (one_le_sMin lower).trans hs
  have hξ4 : 6 ≤ ξ := by linarith [add_one_le_exp (32 : ℝ)]
  have hL4 : 0 < log y ^ 4 := by have := log_pos hy1; positivity
  have hfail : fail lower n y (y ^ (1 / ξ)) ≤
      2 * (exp 1 * X / (ξ - 2)) ^ (ξ - 2) := by
    rw [one_div]
    refine fail_rpow_le_tail hy1 (by linarith) ?_ h2e
    rw [← one_div]
    have := hCS _ hw2
    have : CS ≤ C' := by simp only [C']; linarith [le_abs_self CS]
    simp only [X]
    linarith
  have hG : ∀ t ≥ 3, exp (-(t * log t) - t * log (log t) - c' * t) ≤ errMaj lower t := by
    intro t ht
    rw [errMaj_eq_majG_succ]
    refine le_trans (exp_le_exp.2 ?_) (hc _ t ht)
    have : c * t ≤ c' * t := mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
    linarith
  have hGs := errMaj_pos lower s
  have hmain : 2 * (exp 1 * X / (ξ - 2)) ^ (ξ - 2) * log y ^ 4 ≤ delta s y * errMaj lower s := by
    rcases le_total s (ξ / 2) with h | h
    · refine hA.trans ((hG _ (by linarith)).trans ?_)
      calc errMaj lower (ξ / 2) ≤ errMaj lower s := errMaj_antitone lower h
        _ ≤ delta s y * errMaj lower s := le_mul_of_one_le_left hGs.le (one_le_delta hs1 y)
    · refine hB.trans ?_
      have hδ := delta_le_delta (by linarith : 1 ≤ ξ / 2) h y
      have hGG : exp (-(ξ * log ξ) - ξ * log (log ξ) - c' * ξ) ≤ errMaj lower s :=
        (hG ξ (by linarith)).trans (errMaj_antitone lower hsξ)
      exact mul_le_mul hδ hGG (exp_pos _).le (by linarith [one_le_delta hs1 y])
  rw [le_div_iff₀ hL4]
  calc fail lower n y (y ^ (1 / ξ)) * log y ^ 4
      ≤ 2 * (exp 1 * X / (ξ - 2)) ^ (ξ - 2) * log y ^ 4 := by gcongr
    _ ≤ _ := hmain
theorem ratio_le {r : ℕ} {ε : ℝ} (hε : ε * ((r : ℝ) + 1) ^ 2 ≤ 1) :
    (r : ℝ) / (r + 1) ≤ ((r + 1 : ℕ) : ℝ) / ((r + 1 : ℕ) + 1) * (1 - ε) := by
  rw [show ((r + 1 : ℕ) : ℝ) / ((r + 1 : ℕ) + 1) * (1 - ε) = ((r : ℝ) + 1) * (1 - ε) / (r + 2) by
    push_cast; ring]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith
theorem ratio_le_of_depth {r : ℕ} {L Λ : ℝ} (hL : 0 < L) (hΛ : 0 < Λ)
    (hdepth : (r : ℝ) + 2 ≤ 2 * L / Λ) :
    (r : ℝ) / (r + 1) ≤ ((r + 1 : ℕ) : ℝ) / ((r + 1 : ℕ) + 1) *
      (1 - Λ ^ 2 / (4 * L ^ 2)) := by
  apply ratio_le
  have hr : ((r : ℝ) + 2) * Λ ≤ 2 * L := (le_div_iff₀ hΛ).1 hdepth
  have hr' : ((r : ℝ) + 1) * Λ ≤ 2 * L :=
    (mul_le_mul_of_nonneg_right (by linarith only) hΛ.le).trans hr
  have hsq : (((r : ℝ) + 1) * Λ) ^ 2 ≤ (2 * L) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hr' 2
  calc
    Λ ^ 2 / (4 * L ^ 2) * ((r : ℝ) + 1) ^ 2 =
        (((r : ℝ) + 1) * Λ) ^ 2 / (2 * L) ^ 2 := by ring
    _ ≤ 1 := (div_le_one (by positivity)).2 hsq
theorem combine {cR c₇ L D M F cr E T ρ ρ' ε : ℝ}
    (hF : F ≤ cr + (cR * M / L + E) + cR * c₇ * ρ * T) (hcr : cr ≤ D / L ^ 2)
    (hE : E ≤ D / L ^ 2) (hT : T ≤ D * (1 + ε / 2)) (hρ : ρ ≤ ρ' * (1 - ε)) (hρ0 : 0 ≤ ρ)
    (hε0 : 0 ≤ ε) (hεL : 1 / (4 * L ^ 2) ≤ ε) (hρ' : 1 / 2 ≤ ρ') (hc : 32 ≤ cR * c₇)
    (hD : 0 ≤ D) (hL : 0 < L) :
    F ≤ cR * M / L + cR * c₇ * ρ' * D := by
  have hcc : 0 ≤ cR * c₇ := by linarith
  have hD' : 0 ≤ D * (1 + ε / 2) := by positivity
  have h1 : cR * c₇ * ρ * T ≤ cR * c₇ * ρ' * D * ((1 - ε) * (1 + ε / 2)) := by
    calc cR * c₇ * ρ * T ≤ cR * c₇ * ρ * (D * (1 + ε / 2)) :=
          mul_le_mul_of_nonneg_left hT (by positivity)
      _ ≤ cR * c₇ * (ρ' * (1 - ε)) * (D * (1 + ε / 2)) := by gcongr
      _ = _ := by ring
  have h2 : (1 - ε) * (1 + ε / 2) ≤ 1 - ε / 2 := by nlinarith
  have hρ'0 : 0 ≤ ρ' := by linarith
  have h3 : cR * c₇ * ρ' * D * ((1 - ε) * (1 + ε / 2)) ≤ cR * c₇ * ρ' * D * (1 - ε / 2) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have hL2 : 0 < L ^ 2 := by positivity
  have h4 : 4 / L ^ 2 ≤ cR * c₇ * ρ' * ε := by
    have e1 : 32 * (1 / 2) ≤ cR * c₇ * ρ' := mul_le_mul hc hρ' (by norm_num) hcc
    calc 4 / L ^ 2 = 32 * (1 / 2) * (1 / (4 * L ^ 2)) := by field_simp; norm_num
      _ ≤ cR * c₇ * ρ' * ε := mul_le_mul e1 hεL (by positivity) (by positivity)
  have h5 : 2 * (D / L ^ 2) ≤ cR * c₇ * ρ' * D * (ε / 2) := by
    have := mul_le_mul_of_nonneg_left h4 hD
    calc 2 * (D / L ^ 2) = D * (4 / L ^ 2) / 2 := by ring
      _ ≤ D * (cR * c₇ * ρ' * ε) / 2 := by linarith
      _ = _ := by ring
  nlinarith
theorem main_step {cR c₇ CR C₁ C₃ : ℝ} {r : ℕ} (IH : Bound cR c₇ r) (hcR : 0 < cR)
    (hc₇ : 32 ≤ cR * c₇) (hCR : 0 ≤ CR) (hC₁ : 0 ≤ C₁) (hC₃ : 0 ≤ C₃) {lower : Bool} {y s : ℝ}
    (hy : 1 < y) (hs : sMin lower ≤ s) (hsξ : s ≤ xi y)
    (hcor1 : ∑ p ∈ (rosserPrimes lower y (y ^ (1 / s))).filter (fun p : ℕ => y ^ (1 / xi y) ≤ p),
        mainMaj (!lower) (log y / log p - 1) / (p * log (y / p)) ≤
      (mainMaj lower s - (if lower then 0 else max (3 - s) 0)) / log y +
        C₁ * s ^ 2 * errMaj lower s * pntE (y ^ (1 / xi y)) / log y)
    (hsrc : src lower y (y ^ (1 / s)) ≤ (if lower then 0 else cR * max (3 - s) 0 / log y) +
      6 * CR * s ^ 2 * errMaj lower s * pntE (y ^ (1 / xi y)) / log y)
    (hcor3 : ∑ p ∈ (rosserPrimes lower y (y ^ (1 / s))).filter (fun p : ℕ => y ^ (1 / xi y) ≤ p),
        delta (log y / log p - 1) (y / p) * errMaj (!lower) (log y / log p - 1) /
          (p * log (y / p) ^ 2) ≤
      delta (max s (exp 32)) y * errMaj lower s / log y ^ 2 *
        (1 + C₃ * xi y ^ 2 * pntE (y ^ (1 / xi y))))
    (hcrude : fail lower (r + 1) y (y ^ (1 / xi y)) ≤ delta s y * errMaj lower s / log y ^ 4)
    (hΛ : 1 ≤ log (log y))
    (hδ : delta (exp 32) y * (1 + C₃ * xi y ^ 2 * pntE (y ^ (1 / xi y))) ≤
      1 + log (log y) ^ 2 / (8 * log y ^ 2))
    (hK : (cR * C₁ + 6 * CR) * xi y ^ 2 * log y ^ 3 * pntE (y ^ (1 / xi y)) ≤ 1)
    (hdepth : ¬ 2 * log y / log (log y) < r + 2) :
    fail lower (r + 1) y (y ^ (1 / s)) ≤
      cR * (mainMaj lower s / log y +
        c₇ * (((r + 1 : ℕ) : ℝ) / ((r + 1 : ℕ) + 1)) * delta s y * errMaj lower s /
          log y ^ 2) := by
  set L := log y
  set ξ := xi y
  set w := y ^ (1 / ξ)
  set Λ := log (log y)
  set G := errMaj lower s
  set ρ' := ((r + 1 : ℕ) : ℝ) / ((r + 1 : ℕ) + 1)
  set S := (rosserPrimes lower y (y ^ (1 / s))).filter (fun p : ℕ => w ≤ p)
  set M := ∑ p ∈ S, mainMaj (!lower) (L / log p - 1) / (p * log (y / p))
  set T := ∑ p ∈ S, delta (L / log p - 1) (y / p) * errMaj (!lower) (L / log p - 1) /
    (p * log (y / p) ^ 2)
  set D := delta s y * G / L ^ 2 with hD
  set ε := Λ ^ 2 / (4 * L ^ 2) with hε
  have hs1 : 1 ≤ s := (one_le_sMin lower).trans hs
  have hL : 0 < L := log_pos hy
  have hG := errMaj_pos lower s
  have hδs := one_le_delta hs1 y
  have hpE := pntE_pos w
  have hD0 : 0 ≤ D := by positivity
  set K := cR * C₁ + 6 * CR
  have hmain : cR * M + src lower y (y ^ (1 / s)) ≤
      cR * mainMaj lower s / L + K * s ^ 2 * G * pntE w / L :=
    main_sum_add_src_le hcR.le hcor1 hsrc
  have hE : K * s ^ 2 * G * pntE w / L ≤ D / L ^ 2 := by
    have hK0 : 0 ≤ K := by positivity
    have hsq : s ^ 2 ≤ ξ ^ 2 := by gcongr
    rw [hD, div_div, div_le_div_iff₀ hL (by positivity)]
    calc K * s ^ 2 * G * pntE w * (L ^ 2 * L ^ 2) = G * (K * s ^ 2 * L ^ 3 * pntE w) * L := by
          ring
      _ ≤ G * (K * ξ ^ 2 * L ^ 3 * pntE w) * L := by gcongr
      _ ≤ G * 1 * L := by gcongr
      _ ≤ delta s y * G * L := by
          simpa only [one_mul, mul_assoc] using
            mul_le_mul_of_nonneg_right hδs (by positivity : 0 ≤ G * L)
  have hT : T ≤ D * (1 + ε / 2) := by
    refine hcor3.trans ?_
    have hmax := delta_max_le hs1 (one_le_exp (by norm_num) : 1 ≤ exp 32) y
    have hb : 0 ≤ 1 + C₃ * ξ ^ 2 * pntE w := by positivity
    have hε2 : ε / 2 = Λ ^ 2 / (8 * L ^ 2) := by rw [hε]; ring
    calc delta (max s (exp 32)) y * G / L ^ 2 * (1 + C₃ * ξ ^ 2 * pntE w)
        ≤ delta (exp 32) y * delta s y * G / L ^ 2 * (1 + C₃ * ξ ^ 2 * pntE w) := by gcongr
      _ = D * (delta (exp 32) y * (1 + C₃ * ξ ^ 2 * pntE w)) := by rw [hD]; ring
      _ ≤ D * (1 + ε / 2) := by rw [hε2]; gcongr
  have hρ : (r : ℝ) / (r + 1) ≤ ρ' * (1 - ε) :=
    ratio_le_of_depth hL (zero_lt_one.trans_le hΛ) (not_lt.1 hdepth)
  have hεL : 1 / (4 * L ^ 2) ≤ ε := by
    rw [hε]
    exact div_le_div_of_nonneg_right (by nlinarith only [hΛ]) (by positivity)
  have hρ' : 1 / 2 ≤ ρ' := by
    simp only [ρ']
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]; push_cast; linarith
  have hcr : fail lower (r + 1) y w ≤ D / L ^ 2 := by
    refine hcrude.trans_eq ?_
    rw [hD, div_div]; ring
  have hwz : w ≤ y ^ (1 / s) := rpow_one_div_le_rpow_one_div hy.le (by linarith) hsξ
  have hF : fail lower (r + 1) y (y ^ (1 / s)) ≤ fail lower (r + 1) y w +
      (cR * mainMaj lower s / L + K * s ^ 2 * G * pntE w / L) +
      cR * c₇ * ((r : ℝ) / (r + 1)) * T := by
    calc
      _ ≤ fail lower (r + 1) y w + ∑ p ∈ S, fail (!lower) r (y / p) p / p +
          src lower y (y ^ (1 / s)) := fail_succ_le_split lower r hwz
      _ ≤ fail lower (r + 1) y w + (cR * M + cR * c₇ * ((r : ℝ) / (r + 1)) * T) +
          src lower y (y ^ (1 / s)) :=
        add_le_add (add_le_add le_rfl (sum_ih_le IH hy hs)) le_rfl
      _ = fail lower (r + 1) y w + (cR * M + src lower y (y ^ (1 / s))) +
          cR * c₇ * ((r : ℝ) / (r + 1)) * T := by ring
      _ ≤ _ := add_le_add (add_le_add le_rfl hmain) le_rfl
  calc
    _ ≤ cR * mainMaj lower s / L + cR * c₇ * ρ' * D :=
      combine hF hcr hE hT hρ (by positivity) (by positivity) hεL hρ' hc₇ hD0 hL
    _ = _ := by rw [hD]; ring
end IwaniecLinearSieve.TheoremFour
namespace IwaniecLinearSieve
open TheoremFour
theorem theorem4 (hPNT : StrongPNTProp) {cR CR : ℝ} (hcR : 0 < cR) (hR : ∀ z ≥ 2, |R z * log z - cR| ≤ CR * pntE z) :
    ∃ c₇ : ℝ, 0 ≤ c₇ ∧ ∀ (r : ℕ) (lower : Bool) (y s : ℝ), 1 < y → sMin lower ≤ s →
      s ≤ xi y → fail lower r y (y ^ (1 / s)) ≤
        cR * (mainMaj lower s / log y +
          c₇ * ((r : ℝ) / (r + 1)) * delta s y * errMaj lower s / log y ^ 2) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := (cor1_part hPNT)
  obtain ⟨C₃, y₃, hC₃0, hC₃⟩ := (cor3_xi hPNT)
  obtain ⟨yd, hyd⟩ := exists_fail_add_eq
  obtain ⟨yx, hyx⟩ := exists_xi_large
  obtain ⟨yc, hyc⟩ := (crude_le hPNT)
  have hCR : 0 ≤ CR :=
    nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hR 2 le_rfl)) (pntE_pos 2)
  obtain ⟨ye, hye⟩ := eventually_atTop.1 ((eventually_one_le_loglog.and
    (eventually_delta_mul_le C₃ hC₃0)).and (eventually_mul_pntE_le (cR * C₁ + 6 * CR)))
  set y₀ := max (max (max y₃ yd) (max yx yc)) (max ye 2) with hy₀
  set Ξ := log y₀ / log (log 3) ^ (11 / 5 : ℝ)
  set c₇ := max (32 / cR) (6 * exp (SLT y₀) * log y₀ ^ 2 / (cR * bigM Ξ))
  have hY : 1 < y₀ := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right ye 2) (le_max_right _ _))
  have hc₇0 : 0 ≤ c₇ := le_trans (by positivity) (le_max_left _ _)
  have hc₇ : 32 ≤ cR * c₇ := by
    have := le_max_left (32 / cR) (6 * exp (SLT y₀) * log y₀ ^ 2 / (cR * bigM Ξ))
    rw [div_le_iff₀ hcR] at this
    linarith
  refine ⟨c₇, hc₇0, fun r => ?_⟩
  change Bound cR c₇ r
  induction r with
  | zero =>
    intro lower y s hy _ _
    have := mainMaj_nonneg lower s
    have := log_pos hy
    simp only [fail_zero, Nat.cast_zero, zero_div, mul_zero, zero_mul, add_zero]
    positivity
  | succ r IH =>
    intro lower y s hy hs hsξ
    rcases le_or_gt y y₀ with hyY | hyY
    · exact small_y hcR hY (le_max_right _ _) r lower hy hyY hs hsξ
    have hle : ∀ a, a ≤ y₀ → a ≤ y := fun a ha => ha.trans hyY.le
    have hy₃ : y₃ ≤ y := hle _ (by simp [y₀])
    have hyd' : yd ≤ y := hle _ (by simp [y₀])
    have hyx' : yx ≤ y := hle _ (by simp [y₀])
    have hyc' : yc ≤ y := hle _ (by simp [y₀])
    have hye' : ye ≤ y := hle _ (by simp [y₀])
    have hs1 : 1 ≤ s := (one_le_sMin lower).trans hs
    by_cases hdeep : 2 * log y / log (log y) < r + 2
    ·
      rw [hyd y hyd' lower r (y ^ (1 / s)) hdeep 1]
      refine (IH lower y s hy hs hsξ).trans ?_
      have hab : (r : ℝ) / (r + 1) ≤ ((r + 1 : ℕ) : ℝ) / ((r + 1 : ℕ) + 1) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; push_cast; nlinarith
      have hL2 : 0 < log y ^ 2 := by have := log_pos hy; positivity
      refine mul_le_mul_of_nonneg_left (add_le_add_right (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hab hc₇0) (zero_le_one.trans (one_le_delta hs1 y)))
          (errMaj_pos lower s).le) hL2.le) _) hcR.le
    · obtain ⟨-, hξ32, -, hw2⟩ := hyx y hyx'
      have hξ3 : 3 ≤ xi y := by linarith [add_one_le_exp (32 : ℝ)]
      obtain ⟨⟨hΛ, hδ⟩, hK⟩ := hye y hye'
      exact main_step IH hcR hc₇ hCR hC₁0 hC₃0 hy hs hsξ (hC₁ lower y s hy hs hsξ hξ3 hw2)
        (src_le_of_le_xi hR hy hs hsξ hξ3 hw2) (hC₃ lower y s hy₃ hs)
        (hyc y hyc' lower (r + 1) s hs hsξ)
        hΛ hδ hK hdeep
end IwaniecLinearSieve
end
section
open Real Filter Topology
namespace IwaniecLinearSieve.TheoremFive
noncomputable def lam (y : ℝ) : ℝ := log (log (3 * y))
theorem xi_eq_lam (y : ℝ) : xi y = log y / lam y ^ (11 / 5 : ℝ) := rfl
theorem tendsto_lam : Tendsto lam atTop atTop := tendsto_log_log_three_mul
theorem eventually_add_mul_log_le (α β : ℝ) : ∀ᶠ x in atTop, α + β * log x ≤ x := by
  have hε : (0 : ℝ) < 1 / (2 * (|β| + 1)) := by positivity
  filter_upwards [isLittleO_log_id_atTop.bound hε, eventually_ge_atTop (2 * α),
    eventually_ge_atTop 1] with x hx hxα hx1
  have hl : 0 ≤ log x := log_nonneg hx1
  rw [norm_of_nonneg hl, id, norm_of_nonneg (by linarith)] at hx
  have h1 : β * log x ≤ |β| * log x := mul_le_mul_of_nonneg_right (le_abs_self β) hl
  have h2 : |β| * log x ≤ x / 2 := by
    have hq : |β| / (|β| + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    calc |β| * log x ≤ |β| * (1 / (2 * (|β| + 1)) * x) := by gcongr
      _ = |β| / (|β| + 1) * (x / 2) := by field_simp
      _ ≤ 1 * (x / 2) := by gcongr
      _ = x / 2 := one_mul _
  linarith
theorem one_lt_log_three : 1 < log 3 := by
  rw [lt_log_iff_exp_lt (by norm_num)]
  linarith [exp_one_lt_d9]
theorem lam_pos {y : ℝ} (hy : 1 < y) : 0 < lam y := by
  have h3 : log 3 + log y = log (3 * y) := (log_mul (by norm_num) (by linarith)).symm
  have := log_pos hy
  exact log_pos (by linarith [one_lt_log_three])
theorem log_xi_eq {y : ℝ} (hy : 1 < y) : log (xi y) = log (log y) - 11 / 5 * log (lam y) := by
  rw [xi_eq_lam, log_div (log_pos hy).ne' (rpow_pos_of_pos (lam_pos hy) _).ne',
    log_rpow (lam_pos hy)]
theorem xi_pos {y : ℝ} (hy : 1 < y) : 0 < xi y :=
  div_pos (log_pos hy) (rpow_pos_of_pos (lam_pos hy) _)
theorem eventually_scalar (c : ℝ) (hc : 100 ≤ c) : ∀ᶠ y in atTop,
    3 ≤ y ∧ c ≤ log (lam y) ∧ c ≤ lam y ^ (1 / 5 : ℝ) ∧ c ≤ lam y ∧
    log (log y) ≤ lam y ∧ lam y - 1 ≤ log (log y) ∧
    24 * lam y ≤ xi y ∧ 16 * lam y ^ 2 ≤ log y ∧ lam y / 2 ≤ log (xi y / 2) ∧
    4 * log (lam y) + c ≤ log (xi y) ∧ log (xi y) ≤ lam y := by
  filter_upwards [eventually_ge_atTop 3, tendsto_lam.eventually (eventually_ge_atTop c),
    (tendsto_log_atTop.comp tendsto_lam).eventually (eventually_ge_atTop c),
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp tendsto_lam).eventually
      (eventually_ge_atTop c),
    tendsto_lam.eventually (eventually_add_mul_log_le (c + 10) 8)] with y hy3 h1 h2 h3 h4
  simp only [Function.comp] at h2 h3
  have hy : 1 < y := by linarith
  have hL : 1 < log y := by
    have := log_le_log (by norm_num) hy3; linarith [one_lt_log_three]
  have hL0 : 0 < log y := by linarith
  have hlam := lam_pos hy
  have h3y : log (3 * y) = log 3 + log y := log_mul (by norm_num) (by linarith)
  have ha : 0 ≤ log (lam y) := by linarith
  have hℓ1 : log (log y) ≤ lam y := by
    unfold lam; exact log_le_log hL0 (by rw [h3y]; linarith [one_lt_log_three])
  have hℓ2 : lam y - 1 ≤ log (log y) := by
    have hle : log (3 * y) ≤ exp 1 * log y := by
      have : log 3 ≤ log y := log_le_log (by norm_num) hy3
      have : 2 ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
      rw [h3y]; nlinarith
    have := log_le_log (by rw [h3y]; linarith [one_lt_log_three]) hle
    rw [log_mul (exp_pos 1).ne' hL0.ne', log_exp] at this
    unfold lam; linarith
  have hlogξ := log_xi_eq hy
  have hξ := xi_pos hy
  have hl2 : log 2 ≤ 1 := by linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hl16 : log 16 ≤ 15 := by linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 16)]
  have hl24 : log 24 ≤ 23 := by linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 24)]
  refine ⟨hy3, h2, h3, h1, hℓ1, hℓ2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← log_le_log_iff (by positivity) hξ, log_mul (by norm_num) hlam.ne']
    linarith
  · have h := (log_le_log_iff (by positivity) hL0).1 (by
      rw [log_mul (by norm_num) (by positivity), log_pow]; push_cast
      linarith : log (16 * lam y ^ 2) ≤ log (log y))
    exact h
  · rw [log_div hξ.ne' (by norm_num)]
    linarith
  · linarith
  · linarith
theorem crude_exponent_le {L ℓ lam ξ a : ℝ} (hL : 0 < L) (hℓ : ℓ = log L) (hℓlam : ℓ ≤ lam)
    (hlam : 100 ≤ lam) (ha : 12 ≤ a) (hxilam : 4 * (ξ * lam ^ 2) ≤ L) (h24 : 24 * lam ≤ ξ)
    (h16 : 16 * lam ^ 2 ≤ L) (hlogξ : log ξ ≤ lam) :
    8 * L ^ 4 * (1 + exp (L + 2 * ξ - L / lam) + 2 * exp (L - ξ * log ξ + ξ * a + 5 * ξ)) ≤
      exp (L - ξ * log ξ + 3 / 2 * ξ * a) := by
  have hlam0 : 0 < lam := by linarith
  have hξ0 : 0 < ξ := by linarith
  have h8 : 8 * L ^ 4 = exp (log 8 + 4 * ℓ) := by
    rw [exp_add, exp_log (by norm_num), hℓ,
      show (4 : ℝ) * log L = log (L ^ 4) by rw [log_pow]; norm_num, exp_log (by positivity)]
  have hl3 : log 3 ≤ 2 := by linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)]
  have hl8 : log 8 ≤ 7 := by linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)]
  have hl2 : log 2 ≤ 1 := by linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  set T := L - ξ * log ξ + 3 / 2 * ξ * a with hT
  have h3 : exp T = 3 * exp (T - log 3) := by
    rw [exp_sub, exp_log (by norm_num)]; field_simp
  have hLl : ξ * log ξ + 2 * ξ ≤ L / (2 * lam) := by
    rw [le_div_iff₀ (by positivity)]
    have : ξ * log ξ ≤ ξ * lam := mul_le_mul_of_nonneg_left hlogξ hξ0.le
    nlinarith
  have hLm : 8 + 4 * lam ≤ L / (2 * lam) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hLlam : L / lam ≤ L := div_le_self hL.le (by linarith)
  have hξa : 0 ≤ ξ * a := by positivity
  have e1 : 8 * L ^ 4 ≤ exp (T - log 3) := by
    rw [h8, exp_le_exp, hT]
    have : L / lam = 2 * (L / (2 * lam)) := by field_simp
    nlinarith
  have e2 : 8 * L ^ 4 * exp (L + 2 * ξ - L / lam) ≤ exp (T - log 3) := by
    rw [h8, ← exp_add, exp_le_exp, hT]
    have : L / lam = 2 * (L / (2 * lam)) := by field_simp
    nlinarith
  have e3 : 8 * L ^ 4 * (2 * exp (L - ξ * log ξ + ξ * a + 5 * ξ)) ≤ exp (T - log 3) := by
    rw [h8, mul_left_comm, ← exp_add, ← exp_log (by norm_num : (0 : ℝ) < 2), ← exp_add,
      exp_le_exp, hT]
    have : 6 * ξ ≤ 1 / 2 * ξ * a := by nlinarith
    nlinarith
  rw [h3]
  nlinarith
theorem exists_slack (C : ℝ) (hC : 0 ≤ C) : ∃ y₀ : ℝ, ∀ y ≥ y₀,
    delta (exp 32) y * (1 + C * xi y ^ 2 * pntE (y ^ (1 / xi y))) - 1 ≤
      log (log y) ^ 2 / (8 * log y ^ 2) ∧ 1 ≤ log (log y) := by
  apply eventually_atTop.1
  filter_upwards [TheoremFour.eventually_delta_mul_le C hC,
    (tendsto_log_atTop.comp tendsto_log_atTop).eventually (eventually_ge_atTop (1 : ℝ))]
    with y hslack hloglog
  exact ⟨sub_le_iff_le_add'.2 hslack, hloglog⟩
end IwaniecLinearSieve.TheoremFive
end
section
open Real Filter Finset
namespace IwaniecLinearSieve.TheoremFive
variable {lower : Bool} {y z s : ℝ}
theorem lt_of_mem_rosserSet_rpow (hy : 1 < y) (hs : 1 ≤ s) {d : ℕ}
    (hd : d ∈ rosserSet lower y (y ^ (1 / s))) : (d : ℝ) < y := by
  by_cases hω : (if lower then 2 else 1) ≤ #d.primeFactors
  · exact lt_of_mem_rosserSet hd hω
  have hsq := squarefree_of_mem_rosserSet hd
  have hz : y ^ (1 / s) ≤ y := by
    conv_rhs => rw [← rpow_one y]
    exact rpow_le_rpow_of_exponent_le hy.le (by rw [div_le_one (by linarith)]; exact hs)
  rcases Nat.lt_or_ge #d.primeFactors 1 with h0 | h1
  · have : d.primeFactors = ∅ := card_eq_zero.1 (by omega)
    rw [Nat.primeFactors_eq_empty] at this
    have hd1 : d = 1 := by have := pos_of_mem_rosserSet hd; omega
    rw [hd1]; simpa using hy
  ·
    have h1' : #d.primeFactors = 1 := by split_ifs at hω <;> omega
    obtain ⟨q, hq⟩ := card_eq_one.1 h1'
    have hdq : d = q := by
      rw [← Nat.prod_primeFactors_of_squarefree hsq, hq, prod_singleton]
    have hqz := lt_of_mem_primesLT
      (primeFactors_subset_of_mem_rosserSet hd (by rw [hq]; exact mem_singleton_self q))
    rw [hdq]; linarith
theorem card_rosserSet_le (hy : 1 < y) (hs : 1 ≤ s) :
    (#(rosserSet lower y (y ^ (1 / s))) : ℝ) ≤ y := by
  have hsub : rosserSet lower y (y ^ (1 / s)) ⊆ Ico 1 ⌈y⌉₊ := fun d hd ↦ by
    have := lt_of_mem_rosserSet_rpow hy hs hd
    exact mem_Ico.2 ⟨pos_of_mem_rosserSet hd, Nat.lt_ceil.2 this⟩
  have h := card_le_card hsub
  rw [Nat.card_Ico] at h
  have hc := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ y)
  have : ((⌈y⌉₊ - 1 : ℕ) : ℝ) ≤ y := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 (by positivity))]
    push_cast; linarith
  exact (Nat.cast_le.2 h).trans this
theorem card_filter_succ_le (n : ℕ) (lower : Bool) (y z w : ℝ) :
    (#((rosserSet lower y z).filter fun d ↦ #d.primeFactors ≤ n + 1) : ℝ) ≤
      #(rosserSet lower y w) + ∑ p ∈ (rosserPrimes lower y z).filter (fun p : ℕ ↦ w ≤ p),
        (#((rosserSet (!lower) (y / p) p).filter fun d ↦ #d.primeFactors ≤ n) : ℝ) := by
  rw [card_filter_rosserSet_succ, ← sum_filter_add_sum_filter_not (rosserPrimes lower y z)
    (fun p : ℕ ↦ (p : ℝ) < w)]
  push_cast
  have hsub : (rosserPrimes lower y z).filter (fun p : ℕ ↦ (p : ℝ) < w) ⊆
      rosserPrimes lower y w := fun p hp ↦ by
    rw [mem_filter, mem_rosserPrimes, mem_primesLT] at hp
    rw [mem_rosserPrimes, mem_primesLT]
    exact ⟨⟨hp.1.1.1, hp.2⟩, hp.1.2⟩
  have h1 : (1 : ℝ) + ∑ p ∈ (rosserPrimes lower y z).filter (fun p : ℕ ↦ (p : ℝ) < w),
      (#((rosserSet (!lower) (y / p) p).filter fun d ↦ #d.primeFactors ≤ n) : ℝ) ≤
      #(rosserSet lower y w) := by
    calc _ ≤ (1 : ℝ) + ∑ p ∈ rosserPrimes lower y w,
          (#((rosserSet (!lower) (y / p) p).filter fun d ↦ #d.primeFactors ≤ n) : ℝ) := by
          gcongr
      _ = (#((rosserSet lower y w).filter fun d ↦ #d.primeFactors ≤ n + 1) : ℝ) := by
          rw [card_filter_rosserSet_succ, Nat.cast_add, Nat.cast_one, Nat.cast_sum]
      _ ≤ #(rosserSet lower y w) := by exact_mod_cast card_filter_le _ _
  have h2 : (rosserPrimes lower y z).filter (fun p : ℕ ↦ ¬ (p : ℝ) < w) =
      (rosserPrimes lower y z).filter (fun p : ℕ ↦ w ≤ p) :=
    filter_congr fun p _ ↦ not_lt
  rw [h2]
  linarith
theorem card_primesLT_le {w : ℝ} (hw : 0 ≤ w) : (#(primesLT w) : ℝ) ≤ w + 1 := by
  have h : #(primesLT w) ≤ ⌈w⌉₊ := by
    unfold primesLT Nat.primesBelow
    exact (card_filter_le _ _).trans (card_range _).le
  exact (Nat.cast_le.2 h).trans (Nat.ceil_lt_add_one hw).le
theorem card_filter_le_le (lower : Bool) (y : ℝ) {w : ℝ} (hw : 1 ≤ w) (K : ℕ) :
    (#((rosserSet lower y w).filter fun d ↦ #d.primeFactors ≤ K) : ℝ) ≤
      (K + 1) * (2 * w) ^ K := by
  set D := (rosserSet lower y w).filter fun d ↦ #d.primeFactors ≤ K
  have hmaps : Set.MapsTo (fun d ↦ #d.primeFactors) (D : Set ℕ) (range (K + 1)) := by
    intro d hd
    simp only [coe_filter, Set.mem_ofPred_eq, D] at hd
    simpa [Nat.lt_succ_iff] using hd.2
  rw [card_eq_sum_card_fiberwise hmaps]
  push_cast
  have hπ : (#(primesLT w) : ℝ) ≤ 2 * w := by linarith [card_primesLT_le (by linarith : 0 ≤ w)]
  calc ∑ l ∈ range (K + 1), (#(D.filter fun d ↦ #d.primeFactors = l) : ℝ)
      ≤ ∑ l ∈ range (K + 1), (2 * w) ^ K := by
        refine sum_le_sum fun l hl ↦ ?_
        have hlK : l ≤ K := Nat.lt_succ_iff.1 (mem_range.1 hl)
        have h1 : (#(D.filter fun d ↦ #d.primeFactors = l) : ℝ) ≤
            #((rosserSet lower y w).filter fun d ↦ #d.primeFactors = l) := by
          exact_mod_cast card_le_card (filter_subset_filter _ (filter_subset _ _))
        refine h1.trans ((card_filter_eq_le_pow_div lower y w l).trans ?_)
        have hf : (1 : ℝ) ≤ l.factorial := by exact_mod_cast l.factorial_pos
        calc (#(primesLT w) : ℝ) ^ l / l.factorial ≤ (#(primesLT w) : ℝ) ^ l :=
              div_le_self (by positivity) hf
          _ ≤ (2 * w) ^ l := by gcongr
          _ ≤ (2 * w) ^ K := pow_le_pow_right₀ (by linarith) hlK
    _ = (K + 1) * (2 * w) ^ K := by simp
theorem count_cutoff_ratio_le {ξ m : ℝ} (hm : 0 < m) (hξ : 1 < ξ) (hmξ : m ≤ ξ) :
    ξ * (1 - 2 / m) / (ξ - 1) ≤ 1 - 1 / m := by
  rw [div_le_iff₀ (sub_pos.2 hξ)]
  have hratio : 1 ≤ ξ / m := (le_div_iff₀ hm).2 (by simpa using hmξ)
  have hinv : 0 ≤ 1 / m := by positivity
  calc ξ * (1 - 2 / m) = ξ - 2 * (ξ / m) := by ring
    _ ≤ ξ - ξ / m - 1 + 1 / m := by linarith only [hratio, hinv]
    _ = (1 - 1 / m) * (ξ - 1) := by ring
theorem mul_log_count_cutoff_ge {ξ m : ℝ} (hm : 2 < m) (hξ : 0 < ξ) (hlogξ : log ξ ≤ m) :
    ξ * log ξ - 3 * ξ ≤ (ξ * (1 - 2 / m)) * log (ξ * (1 - 2 / m)) := by
  have hm0 : 0 < m := by linarith only [hm]
  set v := 1 - 2 / m with hv
  have hv0 : 0 < v := by
    have : 2 / m < 1 := (div_lt_one hm0).2 hm
    dsimp [v]
    linarith only [this]
  have hlogv : -1 ≤ v * log v := by
    have h := mul_le_mul_of_nonneg_left (neg_inv_le_log hv0.le) hv0.le
    simpa only [mul_neg, mul_inv_cancel₀ hv0.ne'] using h
  have hlog_loss : 2 / m * log ξ ≤ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hm0]
    linarith only [hlogξ]
  have hweighted_loss := mul_le_mul_of_nonneg_left hlog_loss hξ.le
  have hweighted_logv := mul_le_mul_of_nonneg_left hlogv hξ.le
  calc ξ * log ξ - 3 * ξ
      ≤ ξ * log ξ - ξ * (2 / m * log ξ) + ξ * (v * log v) := by
        linarith only [hweighted_loss, hweighted_logv]
    _ = (ξ * v) * log (ξ * v) := by rw [log_mul hξ.ne' hv0.ne', hv]; ring
theorem card_rosserSet_rpow_le (hy : 1 < y) (hw : 2 ≤ y ^ (1 / (xi y - 1)))
    (hSLT : SLT (y ^ (1 / (xi y - 1))) ≤ 2 * lam y) (hlam : 100 ≤ lam y)
    (h24 : 24 * lam y ≤ xi y) (hlogξ : log (xi y) ≤ lam y) :
    (#(rosserSet lower y (y ^ (1 / (xi y - 1)))) : ℝ) ≤
      exp (log y + 2 * xi y - log y / lam y) +
        2 * exp (log y - xi y * log (xi y) + xi y * log (lam y) + 5 * xi y) := by
  set L := log y with hL
  set ξ := xi y
  set m := lam y
  set w := y ^ (1 / (ξ - 1)) with hwdef
  have hL0 : 0 < L := log_pos hy
  have hm0 : 0 < m := by linarith only [hlam]
  have hξ1 : 1 < ξ := by linarith only [h24, hlam]
  set u := ξ * (1 - 2 / m) with hu
  have hv : 1 / 2 ≤ 1 - 2 / m := by
    have : 2 / m ≤ 1 / 2 := by rw [div_le_iff₀ hm0]; linarith only [hlam]
    linarith only [this]
  have hv1 : 1 - 2 / m ≤ 1 := sub_le_self _ (by positivity)
  have hu2 : ξ / 2 ≤ u := by
    have h := mul_le_mul_of_nonneg_left hv (by linarith only [hξ1] : 0 ≤ ξ)
    dsimp [u]
    linarith only [h]
  have huξ : u ≤ ξ := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hv1 (by linarith only [hξ1] : 0 ≤ ξ)
  have hu0 : 0 < u := by linarith only [hu2, hξ1]
  set K := ⌊u⌋₊ with hK
  have hKu : (K : ℝ) ≤ u := Nat.floor_le hu0.le
  have huK : u < K + 1 := Nat.lt_floor_add_one u
  have hK1 : 1 ≤ K := by
    rw [hK, Nat.one_le_floor_iff]
    linarith only [hu2, h24, hlam]
  rw [← card_filter_add_card_filter_not (fun d ↦ #d.primeFactors ≤ K)]
  push_cast
  gcongr
  ·
    refine (card_filter_le_le lower y (by linarith only [hw]) K).trans ?_
    have h2w : 1 ≤ 2 * w := by linarith only [hw]
    have hcount_factor : (K : ℝ) + 1 ≤ exp ξ := by
      linarith only [hKu, huξ, add_one_le_exp ξ]
    have htwo_power : (2 : ℝ) ^ u ≤ exp ξ := by
      rw [rpow_def_of_pos (by norm_num), exp_le_exp]
      have hlogtwo : log 2 ≤ 1 := by linarith only [log_le_sub_one_of_pos two_pos]
      calc log 2 * u ≤ 1 * u := mul_le_mul_of_nonneg_right hlogtwo hu0.le
        _ ≤ ξ := by simpa only [one_mul] using huξ
    have hcutoff_power : w ^ u ≤ exp (L - L / m) := by
      have hratio : u / (ξ - 1) ≤ 1 - 1 / m :=
        count_cutoff_ratio_le hm0 hξ1 (by linarith only [h24, hlam])
      rw [hwdef, ← rpow_mul (by linarith only [hy]),
        rpow_def_of_pos (by linarith only [hy]), exp_le_exp, ← hL]
      calc L * (1 / (ξ - 1) * u) = L * (u / (ξ - 1)) := by ring
        _ ≤ L * (1 - 1 / m) := mul_le_mul_of_nonneg_left hratio hL0.le
        _ = L - L / m := by ring
    have hpower : (2 * w) ^ K ≤ exp ξ * exp (L - L / m) := by
      rw [← rpow_natCast]
      calc (2 * w) ^ (K : ℝ) ≤ (2 * w) ^ u := rpow_le_rpow_of_exponent_le h2w hKu
        _ = 2 ^ u * w ^ u := mul_rpow (by norm_num) (by linarith only [hw])
        _ ≤ exp ξ * exp (L - L / m) :=
            mul_le_mul htwo_power hcutoff_power (by positivity) (exp_pos _).le
    calc ((K : ℝ) + 1) * (2 * w) ^ K ≤ exp ξ * (exp ξ * exp (L - L / m)) :=
          mul_le_mul hcount_factor hpower (by positivity) (exp_pos _).le
      _ = exp (L + 2 * ξ - L / m) := by rw [← exp_add, ← exp_add]; ring_nf
  ·
    have hfilt : ((rosserSet lower y w).filter fun d ↦ ¬ #d.primeFactors ≤ K) =
        (rosserSet lower y w).filter fun d ↦ K + 1 ≤ #d.primeFactors :=
      filter_congr fun d _ ↦ by omega
    rw [hfilt]
    have hX : 2 * exp 1 * (2 * m) ≤ u := by
      have he : exp 1 ≤ 3 := by linarith only [exp_one_lt_d9]
      calc 2 * exp 1 * (2 * m) ≤ 2 * 3 * (2 * m) := by gcongr
        _ ≤ ξ / 2 := by linarith only [h24]
        _ ≤ u := hu2
    refine (card_filter_le_tail (by linarith only [hy]) (by split_ifs <;> omega) hu0
      (by exact_mod_cast huK) hSLT hX).trans ?_
    rw [exp_one_mul_div_rpow (by positivity) hu0]
    have hy' : y = exp L := (exp_log (by linarith only [hy])).symm
    rw [hy', mul_assoc, ← exp_add]
    refine mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) (by norm_num)
    have hulog : ξ * log ξ - 3 * ξ ≤ u * log u :=
      mul_log_count_cutoff_ge (by linarith only [hlam]) (by linarith only [hξ1]) hlogξ
    have hlog2m : log (2 * m) ≤ 1 + log m := by
      rw [log_mul two_pos.ne' hm0.ne']
      linarith only [log_le_sub_one_of_pos two_pos]
    have hweighted_log : u * log (2 * m) ≤ ξ * (1 + log m) := by
      have h0 : 0 ≤ log (2 * m) := log_nonneg (by linarith only [hlam])
      calc u * log (2 * m) ≤ ξ * log (2 * m) := mul_le_mul_of_nonneg_right huξ h0
        _ ≤ ξ * (1 + log m) :=
            mul_le_mul_of_nonneg_left hlog2m (by linarith only [hξ1])
    linarith only [hulog, hweighted_log, huξ]
theorem one_le_of_sMin_le (hs : sMin lower ≤ s) : 1 ≤ s := by
  cases lower <;> simp [sMin] at hs <;> linarith
theorem one_le_delta (hs : 1 ≤ s) (y : ℝ) : 1 ≤ delta s y :=
  one_le_rpow (by linarith [lsx_nonneg (log y) hs]) (by linarith)
theorem exp_le_delta_of_half_le (hy : 1 < y) (hs : xi y / 2 ≤ s)
    (hlogs : lam y / 2 ≤ log s) :
    exp (s * (3 * log (lam y) - 5 * log 128)) ≤ delta s y := by
  set L := log y
  set ξ := xi y
  set m := lam y
  have hL0 : 0 < L := log_pos hy
  have hξ0 : 0 < ξ := xi_pos hy
  have hm0 : 0 < m := lam_pos hy
  have hs0 : 0 ≤ s := by linarith only [hs, hξ0]
  set a₀ := ξ ^ 2 * m ^ 5 / (128 * L ^ 2) with ha₀
  have ha₀0 : 0 < a₀ := by positivity
  have hx : a₀ ≤ s ^ 2 * log s ^ 5 / L ^ 2 := by
    calc a₀ = (ξ / 2) ^ 2 * (m / 2) ^ 5 / L ^ 2 := by rw [ha₀]; ring
      _ ≤ s ^ 2 * log s ^ 5 / L ^ 2 := by gcongr
  have hloga₀ : 5 * log a₀ = 3 * log m - 5 * log 128 := by
    rw [ha₀, log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity),
      log_mul (by norm_num) (by positivity), log_pow, log_pow, log_pow, log_xi_eq hy]
    push_cast
    ring
  calc exp (s * (3 * log m - 5 * log 128)) = a₀ ^ (5 * s) := by
        rw [rpow_def_of_pos ha₀0, ← hloga₀]
        ring_nf
    _ ≤ (1 + s ^ 2 * log s ^ 5 / L ^ 2) ^ (5 * s) :=
        rpow_le_rpow ha₀0.le (by linarith only [hx]) (by positivity)
    _ = delta s y := rfl
theorem exp_le_delta_errMaj {cG : ℝ} (hcG : 0 ≤ cG)
    (hG : ∀ (r : ℕ) (s : ℝ), 3 ≤ s → exp (-(s * log s) - s * log (log s) - cG * s) ≤ majG r s)
    (hy : 1 < y) (h2 : 2 * (cG + 5 * log 128) ≤ log (lam y)) (h6 : 6 ≤ xi y)
    (h8 : lam y / 2 ≤ log (xi y / 2)) (h9 : 4 * log (lam y) + cG ≤ log (xi y))
    (h10 : log (xi y) ≤ lam y) (lower : Bool) (hs : sMin lower ≤ s) (hsξ : s ≤ xi y) :
    exp (-(xi y * log (xi y)) + 3 / 2 * xi y * log (lam y)) ≤ delta s y * errMaj lower s := by
  set ξ := xi y
  set a := log (lam y)
  have h128 : 0 ≤ log 128 := log_nonneg (by norm_num)
  have ha0 : 0 ≤ a := by linarith only [h2, hcG, h128]
  have hs1 := one_le_of_sMin_le hs
  have hδ1 := one_le_delta hs1 y
  have hGl : ∀ t ≥ 3, exp (-(t * log t) - t * log (log t) - cG * t) ≤ errMaj lower t := by
    intro t ht; rw [errMaj_eq_majG_succ]; exact hG _ t ht
  have hll : ∀ t, 3 ≤ t → t ≤ ξ → log (log t) ≤ a := fun t ht htξ ↦
    log_le_log (log_pos (by linarith only [ht]))
      ((log_le_log (by linarith only [ht]) htξ).trans h10)
  rcases le_or_gt s (ξ / 2) with hsh | hsh
  ·
    set s' := max s 3
    have hs'3 : 3 ≤ s' := le_max_right _ _
    have hs'h : s' ≤ ξ / 2 := max_le hsh (by linarith only [h6])
    have hGs : errMaj lower s' ≤ errMaj lower s := errMaj_antitone lower (le_max_left _ _)
    have hl0 : 0 ≤ log s' := log_nonneg (by linarith only [hs'3])
    have hl1 : log s' ≤ log ξ :=
      log_le_log (by linarith only [hs'3]) (by linarith only [hs'h, h6])
    have hll' := hll s' hs'3 (by linarith only [hs'h, h6])
    have hmain_loss : s' * log s' ≤ ξ / 2 * log ξ :=
      mul_le_mul hs'h hl1 hl0 (by linarith only [h6])
    have hloglog_loss : s' * log (log s') ≤ ξ / 2 * a :=
      (mul_le_mul_of_nonneg_left hll' (by linarith only [hs'3])).trans
        (mul_le_mul_of_nonneg_right hs'h ha0)
    have hconstant_loss : cG * s' ≤ cG * (ξ / 2) := mul_le_mul_of_nonneg_left hs'h hcG
    have hmargin : 0 ≤ ξ / 2 * (log ξ - 4 * a - cG) :=
      mul_nonneg (by linarith only [h6]) (by linarith only [h9])
    have hhalf_exponent : -(ξ * log ξ) + 3 / 2 * ξ * a ≤
        -(s' * log s') - s' * log (log s') - cG * s' := by
      linarith only [hmain_loss, hloglog_loss, hconstant_loss, hmargin]
    calc exp (-(ξ * log ξ) + 3 / 2 * ξ * a)
        ≤ exp (-(s' * log s') - s' * log (log s') - cG * s') := exp_le_exp.2 hhalf_exponent
      _ ≤ errMaj lower s' := hGl s' hs'3
      _ ≤ errMaj lower s := hGs
      _ = 1 * errMaj lower s := (one_mul _).symm
      _ ≤ delta s y * errMaj lower s :=
          mul_le_mul_of_nonneg_right hδ1 (errMaj_pos lower s).le
  ·
    have hs3 : 3 ≤ s := by linarith only [hsh, h6]
    have hs0 : 0 ≤ s := by linarith only [hs3]
    have hlogs : lam y / 2 ≤ log s :=
      h8.trans (log_le_log (by linarith only [h6]) hsh.le)
    have hδ := exp_le_delta_of_half_le hy hsh.le hlogs
    have hGs : exp (-(s * log s) - s * a - cG * s) ≤ errMaj lower s := by
      refine le_trans (exp_le_exp.2 ?_) (hGl s hs3)
      have hloglog_loss := mul_le_mul_of_nonneg_left (hll s hs3 hsξ) hs0
      linarith only [hloglog_loss]
    set c₁ := cG + 5 * log 128 with hc₁
    have hendpoint : 0 ≤ log ξ - 2 * a + c₁ := by
      dsimp [c₁]
      linarith only [h9, ha0, hcG, h128]
    have hcombined_loss : s * (log s - 2 * a + c₁) ≤ ξ * (log ξ - 2 * a + c₁) := by
      have hlog : log s ≤ log ξ := log_le_log (by linarith only [hs3]) hsξ
      calc s * (log s - 2 * a + c₁) ≤ s * (log ξ - 2 * a + c₁) :=
            mul_le_mul_of_nonneg_left (by linarith only [hlog]) hs0
        _ ≤ ξ * (log ξ - 2 * a + c₁) := mul_le_mul_of_nonneg_right hsξ hendpoint
    have hconstant_margin : ξ * (2 * c₁) ≤ ξ * a :=
      mul_le_mul_of_nonneg_left h2 (by linarith only [h6])
    have hfull_exponent : -(ξ * log ξ) + 3 / 2 * ξ * a ≤
        s * (3 * a - 5 * log 128) + (-(s * log s) - s * a - cG * s) := by
      rw [hc₁] at hcombined_loss hconstant_margin
      linarith only [hcombined_loss, hconstant_margin]
    calc exp (-(ξ * log ξ) + 3 / 2 * ξ * a)
        ≤ exp (s * (3 * a - 5 * log 128) + (-(s * log s) - s * a - cG * s)) :=
          exp_le_exp.2 hfull_exponent
      _ = exp (s * (3 * a - 5 * log 128)) * exp (-(s * log s) - s * a - cG * s) := exp_add _ _
      _ ≤ delta s y * errMaj lower s :=
          mul_le_mul hδ hGs (exp_pos _).le (delta_pos hs1 y).le
theorem exists_card_small (hPNT : StrongPNTProp) : ∃ y₀ : ℝ, ∀ y ≥ y₀, ∀ (lower : Bool) (s : ℝ), sMin lower ≤ s →
    s ≤ xi y → 1 + (#(rosserSet lower y (y ^ (1 / (xi y - 1)))) : ℝ) ≤
      delta s y * errMaj lower s * y / (8 * log y ^ 4) := by
  obtain ⟨cG₀, hG₀⟩ := majG_ge_exp
  set cG := max cG₀ 0 with hcG
  have hcG0 : 0 ≤ cG := le_max_right _ _
  have hG : ∀ (r : ℕ) (s : ℝ), 3 ≤ s →
      exp (-(s * log s) - s * log (log s) - cG * s) ≤ majG r s := by
    intro r s hs
    refine le_trans (exp_le_exp.2 ?_) (hG₀ r s hs)
    have : cG₀ * s ≤ cG * s := mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
    linarith
  obtain ⟨C₅, hC₅⟩ := (SLT_le_loglog hPNT)
  obtain ⟨y₁, hy₁⟩ := exists_xi_large
  set c := max 100 (max (2 * (cG + 5 * log 128)) (max cG (max C₅ 12))) with hc
  have hc1 := le_max_left 100 (max (2 * (cG + 5 * log 128)) (max cG (max C₅ 12)))
  have hc2 := le_max_right 100 (max (2 * (cG + 5 * log 128)) (max cG (max C₅ 12)))
  have hc3 := le_max_left (2 * (cG + 5 * log 128)) (max cG (max C₅ 12))
  have hc4 := le_max_right (2 * (cG + 5 * log 128)) (max cG (max C₅ 12))
  have hc5 := le_max_left cG (max C₅ 12)
  have hc6 := le_max_right cG (max C₅ 12)
  have hc7 := le_max_left C₅ 12
  have hc8 := le_max_right C₅ 12
  obtain ⟨y₀, hy₀⟩ := eventually_atTop.1
    ((eventually_scalar c hc1).and (eventually_ge_atTop y₁))
  refine ⟨y₀, fun y hy lower s hs hsξ ↦ ?_⟩
  obtain ⟨⟨hy3, ha, hμ, hlam, hℓ1, -, h24, h16, h8, h9, h10⟩, hyy₁⟩ := hy₀ y hy
  obtain ⟨hy1, -, -, hw2⟩ := hy₁ y hyy₁
  have hL0 : 0 < log y := log_pos hy1
  have hm0 := lam_pos hy1
  have hξ := xi_pos hy1
  have hξ1 : 0 < xi y - 1 := by linarith
  have hw : 2 ≤ y ^ (1 / (xi y - 1)) :=
    hw2.trans (rpow_one_div_le_rpow_one_div hy1.le hξ1 (by linarith))
  have hwy : y ^ (1 / (xi y - 1)) ≤ y := by
    conv_rhs => rw [← rpow_one y]
    exact rpow_le_rpow_of_exponent_le hy1.le (by rw [div_le_one hξ1]; linarith)
  have hSLT : SLT (y ^ (1 / (xi y - 1))) ≤ 2 * lam y := by
    have h1 := hC₅ _ hw
    have h2 : log (log (y ^ (1 / (xi y - 1)))) ≤ log (log y) :=
      log_le_log (log_pos (by linarith)) (log_le_log (by linarith) hwy)
    linarith
  have hcard := card_rosserSet_rpow_le (lower := lower) hy1 hw hSLT (by linarith) h24 h10
  have hxl : 4 * (xi y * lam y ^ 2) ≤ log y := by
    have hsplit : lam y ^ (11 / 5 : ℝ) = lam y ^ 2 * lam y ^ (1 / 5 : ℝ) := by
      rw [← rpow_natCast, ← rpow_add hm0]; norm_num
    rw [xi_eq_lam, hsplit]
    have hμ0 : 0 < lam y ^ (1 / 5 : ℝ) := rpow_pos_of_pos hm0 _
    rw [div_mul_eq_mul_div, mul_div_assoc', div_le_iff₀ (by positivity)]
    have : 4 ≤ lam y ^ (1 / 5 : ℝ) := by linarith
    nlinarith [mul_pos hL0 (pow_pos hm0 2)]
  have hcrude := crude_exponent_le hL0 rfl hℓ1 (by linarith) (a := log (lam y)) (by linarith)
    hxl h24 h16 h10
  have hB := exp_le_delta_errMaj hcG0 hG hy1 (by linarith) (by linarith) h8 (by linarith) h10
    lower hs hsξ
  have hy' : exp (log y - xi y * log (xi y) + 3 / 2 * xi y * log (lam y)) =
      y * exp (-(xi y * log (xi y)) + 3 / 2 * xi y * log (lam y)) := by
    rw [← exp_log (by linarith : 0 < y), ← exp_add, exp_log (by linarith)]; ring_nf
  rw [le_div_iff₀ (by positivity)]
  calc (1 + (#(rosserSet lower y (y ^ (1 / (xi y - 1)))) : ℝ)) * (8 * log y ^ 4)
      ≤ 8 * log y ^ 4 * (1 + exp (log y + 2 * xi y - log y / lam y) +
          2 * exp (log y - xi y * log (xi y) + xi y * log (lam y) + 5 * xi y)) := by
        nlinarith [pow_pos hL0 4]
    _ ≤ y * exp (-(xi y * log (xi y)) + 3 / 2 * xi y * log (lam y)) := hcrude.trans hy'.le
    _ ≤ y * (delta s y * errMaj lower s) := by gcongr
    _ = delta s y * errMaj lower s * y := by ring
end IwaniecLinearSieve.TheoremFive
end
section
open Real Filter Finset
namespace IwaniecLinearSieve.TheoremFive
def Bound (c₇ : ℝ) (r : ℕ) : Prop :=
  ∀ (lower : Bool) (y s : ℝ), 1 < y → sMin lower ≤ s → s ≤ xi y →
    (#{d ∈ rosserSet lower y (y ^ (1 / s)) | #d.primeFactors ≤ r} : ℝ) ≤
      c₇ * ((r + 1) / (r + 2)) * delta s y * errMaj lower s * y / log y ^ 2
theorem rosserPrimes_facts {lower : Bool} {y s : ℝ} {p : ℕ} (hy : 1 < y) (hs : sMin lower ≤ s)
    (hp : p ∈ rosserPrimes lower y (y ^ (1 / s))) :
    1 < p ∧ (p : ℝ) < y ∧ sMin (!lower) ≤ log y / log p - 1 := by
  exact ⟨(prime_of_mem_primesLT (rosserPrimes_subset hp)).one_lt,
    TheoremFour.prime_lt_of_mem_rosserPrimes hy (one_le_of_sMin_le hs) hp,
    TheoremFour.sMin_le_inner hy hs hp⟩
theorem sub_one_le_xi_div {y : ℝ} {p : ℕ} (hy : 1 < y) (hp : 1 < p) (hpy : (p : ℝ) < y)
    (ht : log y / log p ≤ xi y) : log y / log p - 1 ≤ xi (y / p) := by
  apply TheoremFour.inner_le_xi hy hp hpy
  have hp0 : (0 : ℝ) < p := by positivity
  have hlp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp)
  rw [← log_le_log_iff (rpow_pos_of_pos (zero_lt_one.trans hy) _) hp0,
    log_rpow_one_div (zero_lt_one.trans hy), div_le_iff₀ (xi_pos hy)]
  simpa only [mul_comm] using (div_le_iff₀ hlp).1 ht
theorem rpow_inv_sub_one_eq {y : ℝ} {p : ℕ} (hy : 0 < y) (hp : 1 < p) (hpy : (p : ℝ) < y) :
    (y / p) ^ (1 / (log y / log p - 1)) = p := by
  exact TheoremFour.rpow_inner_eq hp hpy
theorem inner_le {c₇ : ℝ} {r : ℕ} (ih : Bound c₇ r) {lower : Bool} {y s : ℝ} (hy : 1 < y)
    (hs : sMin lower ≤ s) {p : ℕ} (hp : p ∈ rosserPrimes lower y (y ^ (1 / s)))
    (ht : log y / log p ≤ xi y) :
    (#{d ∈ rosserSet (!lower) (y / p) p | #d.primeFactors ≤ r} : ℝ) ≤
      c₇ * ((r + 1) / (r + 2)) * y * (delta (log y / log p - 1) (y / p) *
        errMaj (!lower) (log y / log p - 1) / (p * log (y / p) ^ 2)) := by
  obtain ⟨hp1, hpy, hsp⟩ := rosserPrimes_facts hy hs hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (zero_lt_one.trans hp1)
  have hyp : 1 < y / p := by rw [lt_div_iff₀ hp0]; linarith
  have h := ih (!lower) (y / p) (log y / log p - 1) hyp hsp (sub_one_le_xi_div hy hp1 hpy ht)
  rw [rpow_inv_sub_one_eq (by linarith) hp1 hpy] at h
  refine h.trans (le_of_eq ?_)
  field_simp
theorem sum_inner_le {c₇ : ℝ} (hc₇ : 0 ≤ c₇) {r : ℕ} (ih : Bound c₇ r)
    {lower : Bool} {y s : ℝ} (hy : 1 < y) (hs : sMin lower ≤ s) (hξ : 1 < xi y) :
    ∑ p ∈ (rosserPrimes lower y (y ^ (1 / s))).filter
        (fun p : ℕ => y ^ (1 / (xi y - 1)) ≤ p),
        (#{d ∈ rosserSet (!lower) (y / p) p | #d.primeFactors ≤ r} : ℝ) ≤
      c₇ * ((r + 1) / (r + 2)) * y *
        ∑ p ∈ (rosserPrimes lower y (y ^ (1 / s))).filter
            (fun p : ℕ => y ^ (1 / xi y) ≤ p),
          delta (log y / log p - 1) (y / p) * errMaj (!lower) (log y / log p - 1) /
            (p * log (y / p) ^ 2) := by
  set P := rosserPrimes lower y (y ^ (1 / s))
  set w := y ^ (1 / (xi y - 1)) with hw
  set φ : ℝ := ((r : ℝ) + 1) / (r + 2)
  set term : ℕ → ℝ := fun p => delta (log y / log p - 1) (y / p) *
    errMaj (!lower) (log y / log p - 1) / (p * log (y / p) ^ 2) with hterm
  have hφ0 : 0 ≤ φ := by positivity
  calc
    _ ≤ ∑ p ∈ P.filter (fun p : ℕ => w ≤ p), c₇ * φ * y * term p := by
      refine sum_le_sum fun p hp => ?_
      obtain ⟨hpP, hwp⟩ := mem_filter.1 hp
      obtain ⟨hp1, -, -⟩ := rosserPrimes_facts hy hs hpP
      have hp1' : (1 : ℝ) < p := by exact_mod_cast hp1
      have hlp : 0 < log (p : ℝ) := log_pos hp1'
      have ht : log y / log p ≤ xi y := by
        have hlog := log_le_log (by positivity) hwp
        rw [hw, log_rpow_one_div (by linarith)] at hlog
        rw [div_le_iff₀ (by linarith)] at hlog
        rw [div_le_iff₀ hlp]
        nlinarith only [hlog, hlp]
      exact inner_le ih hy hs hpP ht
    _ ≤ ∑ p ∈ P.filter (fun p : ℕ => y ^ (1 / xi y) ≤ p), c₇ * φ * y * term p := by
      refine sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun p hp _ => ?_
      · obtain ⟨hpP, hwp⟩ := mem_filter.1 hp
        exact mem_filter.2 ⟨hpP, (rpow_one_div_le_rpow_one_div hy.le (by linarith)
          (by linarith)).trans hwp⟩
      · obtain ⟨-, -, hsp⟩ := rosserPrimes_facts hy hs (mem_filter.1 hp).1
        have := delta_pos (one_le_of_sMin_le hsp) (y / p)
        have := errMaj_pos (!lower) (log y / log p - 1)
        simp only [hterm]
        positivity
    _ = _ := (mul_sum ..).symm
theorem delta_max_le {s s₀ : ℝ} (hs : 1 ≤ s) (hs₀ : 1 ≤ s₀) (y : ℝ) :
    delta (max s s₀) y ≤ delta s y * delta s₀ y := by
  simpa only [mul_comm] using TheoremFour.delta_max_le hs hs₀ y
theorem gap_le {r : ℕ} {L ℓ : ℝ} (hL : 0 < L) (hℓ : 0 < ℓ) (h : (r : ℝ) + 3 ≤ 2 * L / ℓ) :
    2 * (ℓ ^ 2 / (8 * L ^ 2)) ≤ ((r : ℝ) + 1 + 1) / (r + 1 + 2) - (r + 1) / (r + 2) := by
  have hr : (0 : ℝ) ≤ r := r.cast_nonneg
  have e : ((r : ℝ) + 1 + 1) / (r + 1 + 2) - (r + 1) / (r + 2) = 1 / ((r + 2) * (r + 3)) := by
    field_simp; ring
  rw [e, le_div_iff₀ (by positivity)]
  rw [le_div_iff₀ hℓ] at h
  have h2 : ((r + 3) * ℓ) ^ 2 ≤ (2 * L) ^ 2 := by gcongr
  have : (r + 2) * (r + 3) * ℓ ^ 2 ≤ 4 * L ^ 2 := by nlinarith [sq_nonneg ℓ]
  rw [show 2 * (ℓ ^ 2 / (8 * L ^ 2)) * ((r + 2) * (r + 3)) =
    (r + 2) * (r + 3) * ℓ ^ 2 / (4 * L ^ 2) by field_simp; ring]
  rw [div_le_one (by positivity)]
  exact this
theorem close_step {c₇ φ φ' Q X ε : ℝ} (hc₇ : 1 ≤ c₇) (hQ : 0 ≤ Q) (hφ1 : φ ≤ 1)
    (hX0 : 0 ≤ X) (hX : X ≤ ε) (hgap : 2 * ε ≤ φ' - φ) :
    Q * ε + c₇ * φ * Q * (1 + X) ≤ c₇ * φ' * Q := by
  have hε : 0 ≤ ε := hX0.trans hX
  have h1 : φ * X ≤ ε := (mul_le_of_le_one_left hX0 hφ1).trans hX
  have h2 : ε ≤ φ' - φ - φ * X := by linarith
  have h3 : c₇ * ε ≤ c₇ * (φ' - φ - φ * X) := mul_le_mul_of_nonneg_left h2 (by linarith)
  have h4 : ε ≤ c₇ * ε := le_mul_of_one_le_left hε hc₇
  nlinarith [mul_le_mul_of_nonneg_left (h4.trans h3) hQ]
theorem step_main {c₇ C : ℝ} (hc₇ : 1 ≤ c₇) {r : ℕ} (ih : Bound c₇ r) {lower : Bool} {y s : ℝ}
    (hy : 1 < y) (hs : sMin lower ≤ s) (hξ32 : exp 32 ≤ xi y)
    (hsmall : 1 + (#(rosserSet lower y (y ^ (1 / (xi y - 1)))) : ℝ) ≤
      delta s y * errMaj lower s * y / (8 * log y ^ 4))
    (hcor : ∑ p ∈ (rosserPrimes lower y (y ^ (1 / s))).filter (fun p : ℕ => y ^ (1 / xi y) ≤ p),
        delta (log y / log p - 1) (y / p) * errMaj (!lower) (log y / log p - 1) /
          (p * log (y / p) ^ 2) ≤
      delta (max s (exp 32)) y * errMaj lower s / log y ^ 2 *
        (1 + C * xi y ^ 2 * pntE (y ^ (1 / xi y))))
    (hC : 0 ≤ C)
    (hslack : delta (exp 32) y * (1 + C * xi y ^ 2 * pntE (y ^ (1 / xi y))) - 1 ≤
      log (log y) ^ 2 / (8 * log y ^ 2))
    (hℓ : 1 ≤ log (log y)) (hmain : (r : ℝ) + 3 ≤ 2 * log y / log (log y)) :
    (#{d ∈ rosserSet lower y (y ^ (1 / s)) | #d.primeFactors ≤ r + 1} : ℝ) ≤
      c₇ * ((((r + 1 : ℕ) : ℝ) + 1) / (((r + 1 : ℕ) : ℝ) + 2)) * delta s y * errMaj lower s * y /
        log y ^ 2 := by
  have hL0 : 0 < log y := log_pos hy
  have hs1 := one_le_of_sMin_le hs
  have hξ1 : 1 < xi y := by linarith only [four_lt_of_exp_le hξ32]
  set L := log y
  set w := y ^ (1 / (xi y - 1))
  set φ : ℝ := ((r : ℝ) + 1) / (r + 2) with hφ
  set E := C * xi y ^ 2 * pntE (y ^ (1 / xi y))
  set Q := delta s y * errMaj lower s * y / L ^ 2 with hQ
  set ε := log (log y) ^ 2 / (8 * L ^ 2) with hε
  set X := delta (exp 32) y * (1 + E) - 1 with hX
  have hδs := delta_pos hs1 y
  have hGs := errMaj_pos lower s
  have hQ0 : 0 ≤ Q := by positivity
  have hφ0 : 0 ≤ φ := by positivity
  have hφ1 : φ ≤ 1 := by rw [hφ, div_le_one (by positivity)]; linarith
  have hE0 : 0 ≤ E := by have := pntE_pos (y ^ (1 / xi y)); positivity
  have hs₀ : (1 : ℝ) ≤ exp 32 := one_le_exp (by norm_num)
  have hδ₀ := one_le_delta hs₀ y
  have hX0 : 0 ≤ X := by
    rw [hX]
    nlinarith only [hδ₀, hE0]
  have hsmallPart : (#(rosserSet lower y w) : ℝ) ≤ Q * ε := by
    calc
      _ ≤ 1 + (#(rosserSet lower y w) : ℝ) := by linarith only
      _ ≤ delta s y * errMaj lower s * y / (8 * L ^ 4) := hsmall
      _ = Q * (1 / (8 * L ^ 2)) := by rw [hQ]; ring
      _ ≤ Q * ε := by
        rw [hε]
        have : (1 : ℝ) ≤ log (log y) ^ 2 := by nlinarith only [hℓ]
        gcongr
  have hlargePart : ∑ p ∈ (rosserPrimes lower y (y ^ (1 / s))).filter
        (fun p : ℕ => w ≤ p),
        (#{d ∈ rosserSet (!lower) (y / p) p | #d.primeFactors ≤ r} : ℝ) ≤
      c₇ * φ * Q * (1 + X) := by
    refine (sum_inner_le (zero_le_one.trans hc₇) ih hy hs hξ1).trans ?_
    calc
      _ ≤ c₇ * φ * y *
          (delta (max s (exp 32)) y * errMaj lower s / L ^ 2 * (1 + E)) := by
        exact mul_le_mul_of_nonneg_left hcor (by positivity)
      _ = c₇ * φ * (y * errMaj lower s / L ^ 2 * (1 + E)) *
          delta (max s (exp 32)) y := by ring
      _ ≤ c₇ * φ * (y * errMaj lower s / L ^ 2 * (1 + E)) *
          (delta s y * delta (exp 32) y) := by
        exact mul_le_mul_of_nonneg_left (delta_max_le hs1 hs₀ y) (by positivity)
      _ = c₇ * φ * Q * (1 + X) := by rw [hQ, hX]; ring
  have hgap := gap_le (r := r) hL0 (zero_lt_one.trans_le hℓ) hmain
  have hgoal : c₇ * ((((r + 1 : ℕ) : ℝ) + 1) / (((r + 1 : ℕ) : ℝ) + 2)) * delta s y *
      errMaj lower s * y / L ^ 2 = c₇ * (((r : ℝ) + 1 + 1) / (r + 1 + 2)) * Q := by
    rw [hQ]; push_cast; ring
  rw [hgoal]
  calc
    _ ≤ #(rosserSet lower y w) + ∑ p ∈ (rosserPrimes lower y (y ^ (1 / s))).filter
        (fun p : ℕ => w ≤ p),
        (#{d ∈ rosserSet (!lower) (y / p) p | #d.primeFactors ≤ r} : ℝ) :=
      card_filter_succ_le r lower y (y ^ (1 / s)) w
    _ ≤ Q * ε + c₇ * φ * Q * (1 + X) := add_le_add hsmallPart hlargePart
    _ ≤ _ := close_step hc₇ hQ0 hφ1 hX0 hslack hgap
theorem xi_le_of_lt {y c₈ : ℝ} (hy : 1 < y) (hyc : y < c₈) :
    xi y ≤ log c₈ / log (log 3) ^ (11 / 5 : ℝ) := by
  have h3 := one_lt_log_three
  have hll : 0 < log (log 3) := log_pos h3
  have hlam : log (log 3) ≤ lam y := by
    unfold lam
    exact log_le_log (by linarith) (log_le_log (by norm_num) (by linarith))
  rw [xi_eq_lam]
  exact div_le_div₀ (log_nonneg (by linarith)) (log_le_log (by linarith) hyc.le)
    (rpow_pos_of_pos hll _) (rpow_le_rpow hll.le hlam (by norm_num))
theorem small_le {c₈ c₇ : ℝ}
    (hc₇ : 2 * log c₈ ^ 2 / min (errMaj true (log c₈ / log (log 3) ^ (11 / 5 : ℝ)))
      (errMaj false (log c₈ / log (log 3) ^ (11 / 5 : ℝ))) ≤ c₇)
    (r : ℕ) (lower : Bool) {y s : ℝ} (hy : 1 < y) (hyc : y < c₈) (hs : sMin lower ≤ s)
    (hsξ : s ≤ xi y) :
    (#{d ∈ rosserSet lower y (y ^ (1 / s)) | #d.primeFactors ≤ r} : ℝ) ≤
      c₇ * ((r + 1) / (r + 2)) * delta s y * errMaj lower s * y / log y ^ 2 := by
  set Ξ := log c₈ / log (log 3) ^ (11 / 5 : ℝ) with hΞ
  set Gm := min (errMaj true Ξ) (errMaj false Ξ) with hGm
  have hGm0 : 0 < Gm := lt_min (errMaj_pos _ _) (errMaj_pos _ _)
  have hs1 := one_le_of_sMin_le hs
  have hL0 : 0 < log y := log_pos hy
  have hLc : log y ≤ log c₈ := log_le_log (by linarith) hyc.le
  have hG : Gm ≤ errMaj lower s := by
    have h1 : errMaj lower Ξ ≤ errMaj lower s :=
      errMaj_antitone lower (hsξ.trans (xi_le_of_lt hy hyc))
    cases lower
    · exact (min_le_right _ _).trans h1
    · exact (min_le_left _ _).trans h1
  have hδ := one_le_delta hs1 y
  have hφ : (1 : ℝ) / 2 ≤ ((r : ℝ) + 1) / (r + 2) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith [r.cast_nonneg (α := ℝ)]
  have hc₇' : 2 * log c₈ ^ 2 ≤ c₇ * Gm := by rwa [div_le_iff₀ hGm0] at hc₇
  have hcount : (#{d ∈ rosserSet lower y (y ^ (1 / s)) | #d.primeFactors ≤ r} : ℝ) ≤ y :=
    (Nat.cast_le.2 (card_filter_le _ _)).trans (card_rosserSet_le hy hs1)
  refine hcount.trans ?_
  rw [le_div_iff₀ (by positivity)]
  have hc₇0 : 0 ≤ c₇ := by
    have := mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg (log c₈))
    nlinarith
  have key : log y ^ 2 ≤ c₇ * (((r : ℝ) + 1) / (r + 2)) * delta s y * errMaj lower s := by
    have h1 : log y ^ 2 ≤ log c₈ ^ 2 := by gcongr
    have h2 : c₇ * Gm / 2 ≤ c₇ * (((r : ℝ) + 1) / (r + 2)) * delta s y * errMaj lower s := by
      have : c₇ * Gm / 2 = c₇ * (1 / 2) * 1 * Gm := by ring
      rw [this]
      gcongr
    linarith
  nlinarith
theorem exists_bound (hPNT : StrongPNTProp) : ∃ c₇ : ℝ, 1 ≤ c₇ ∧ ∀ r, Bound c₇ r := by
  obtain ⟨y₁, hsmall⟩ := (exists_card_small hPNT)
  obtain ⟨C, y₂, hC0, hcor⟩ := (cor3_xi hPNT)
  obtain ⟨y₃, hslack⟩ := exists_slack C hC0
  obtain ⟨y₄, hdepth⟩ := exists_card_filter_rosserSet_add_eq
  obtain ⟨y₅, hxi⟩ := exists_xi_large
  have hlarge := (eventually_ge_atTop (3 : ℝ)).and
    ((eventually_atTop.2 ⟨y₁, hsmall⟩).and
      ((eventually_atTop.2 ⟨y₂, fun y hy lower s hs ↦ hcor lower y s hy hs⟩).and
        ((eventually_atTop.2 ⟨y₃, hslack⟩).and
          ((eventually_atTop.2 ⟨y₄, hdepth⟩).and (eventually_atTop.2 ⟨y₅, hxi⟩)))))
  obtain ⟨c₈, hlarge⟩ := eventually_atTop.1 hlarge
  set c₇ := max 1 (2 * log c₈ ^ 2 / min (errMaj true (log c₈ / log (log 3) ^ (11 / 5 : ℝ)))
    (errMaj false (log c₈ / log (log 3) ^ (11 / 5 : ℝ)))) with hc₇
  have hc₇1 : 1 ≤ c₇ := le_max_left _ _
  refine ⟨c₇, hc₇1, fun r => ?_⟩
  induction r with
  | zero =>
    intro lower y s hy hs hsξ
    rcases lt_or_ge y c₈ with hyc | hyc
    · exact small_le (le_max_right _ _) 0 lower hy hyc hs hsξ
    obtain ⟨hy3, hsmall, -, -, -, -⟩ := hlarge y hyc
    have hL1 : 1 ≤ log y := by
      have := log_le_log (by norm_num) hy3
      linarith [one_lt_log_three]
    have h := hsmall lower s hs hsξ
    rw [card_filter_rosserSet_zero]
    have hN : (0 : ℝ) ≤ #(rosserSet lower y (y ^ (1 / (xi y - 1)))) := Nat.cast_nonneg _
    have hQ : 0 ≤ delta s y * errMaj lower s * y := by
      have := delta_pos (one_le_of_sMin_le hs) y
      have := errMaj_pos lower s
      have : 0 < y := by linarith
      positivity
    push_cast
    have : delta s y * errMaj lower s * y / (8 * log y ^ 4) ≤
        c₇ * ((0 + 1) / (0 + 2)) * delta s y * errMaj lower s * y / log y ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h4 : log y ^ 2 ≤ 4 * log y ^ 4 := by
        have h1 : 1 ≤ log y ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg (log y))]
      have h5 : delta s y * errMaj lower s * y * log y ^ 2 ≤
          delta s y * errMaj lower s * y * (4 * log y ^ 4) :=
        mul_le_mul_of_nonneg_left h4 hQ
      nlinarith [mul_le_mul_of_nonneg_right hc₇1 (mul_nonneg hQ (pow_pos (by linarith :
        (0 : ℝ) < log y) 4).le)]
    linarith
  | succ r ih =>
    intro lower y s hy hs hsξ
    rcases lt_or_ge y c₈ with hyc | hyc
    · exact small_le (le_max_right _ _) (r + 1) lower hy hyc hs hsξ
    obtain ⟨-, hsmall, hcor, hslack, hdepth, hxi⟩ := hlarge y hyc
    by_cases hdeep : 2 * log y / log (log y) < ((r + 1 : ℕ) : ℝ) + 2
    ·
      have h := hdepth lower (r + 1) (y ^ (1 / s)) hdeep 1
      simp only [Nat.add_sub_cancel] at h
      rw [h]
      refine (ih lower y s hy hs hsξ).trans ?_
      have hQ : 0 ≤ delta s y * errMaj lower s * y / log y ^ 2 := by
        have := delta_pos (one_le_of_sMin_le hs) y
        have := errMaj_pos lower s
        have : 0 < y := by linarith
        positivity
      have hφ : ((r : ℝ) + 1) / (r + 2) ≤ (((r + 1 : ℕ) : ℝ) + 1) / (((r + 1 : ℕ) : ℝ) + 2) := by
        push_cast
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
      calc c₇ * ((r + 1) / (r + 2)) * delta s y * errMaj lower s * y / log y ^ 2
          = c₇ * ((r + 1) / (r + 2)) * (delta s y * errMaj lower s * y / log y ^ 2) := by ring
        _ ≤ c₇ * ((((r + 1 : ℕ) : ℝ) + 1) / (((r + 1 : ℕ) : ℝ) + 2)) *
            (delta s y * errMaj lower s * y / log y ^ 2) := by gcongr
        _ = _ := by ring
    ·
      obtain ⟨-, hξ32, -, -⟩ := hxi
      obtain ⟨hsl, hℓ⟩ := hslack
      have hmain : (r : ℝ) + 3 ≤ 2 * log y / log (log y) := by
        push_cast at hdeep; linarith
      exact step_main hc₇1 ih hy hs hξ32 (hsmall lower s hs hsξ)
        (hcor lower s hs) hC0 hsl hℓ hmain
end IwaniecLinearSieve.TheoremFive
namespace IwaniecLinearSieve
open Finset TheoremFive
theorem theorem5 (hPNT : StrongPNTProp) : ∃ c₇ : ℝ, 0 ≤ c₇ ∧ ∀ (r : ℕ) (lower : Bool) (y s : ℝ), 1 < y →
    sMin lower ≤ s → s ≤ xi y →
    (#{d ∈ rosserSet lower y (y ^ (1 / s)) | #d.primeFactors ≤ r} : ℝ) ≤
      c₇ * ((r + 1) / (r + 2)) * delta s y * errMaj lower s * y / Real.log y ^ 2 := by
  obtain ⟨c₇, hc₇, h⟩ := (exists_bound hPNT)
  exact ⟨c₇, by linarith, fun r => h r⟩
theorem delta_le_of_le_three {s y : ℝ} (hs1 : 1 ≤ s) (hs3 : s ≤ 3) (hy : 1 ≤ Real.log y) :
    delta s y ≤ (1 + 9 * Real.log 3 ^ 5) ^ (15 : ℝ) := by
  have hl0 : 0 ≤ Real.log s := Real.log_nonneg hs1
  have hl3 : Real.log s ≤ Real.log 3 := Real.log_le_log (by linarith) hs3
  have hx : s ^ 2 * Real.log s ^ 5 / Real.log y ^ 2 ≤ 9 * Real.log 3 ^ 5 := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : s ^ 2 ≤ 9 := by nlinarith
    have h2 : Real.log s ^ 5 ≤ Real.log 3 ^ 5 := by gcongr
    have h3 : 1 ≤ Real.log y ^ 2 := by nlinarith
    have h4 : s ^ 2 * Real.log s ^ 5 ≤ 9 * Real.log 3 ^ 5 :=
      mul_le_mul h1 h2 (by positivity) (by norm_num)
    have h5 : 0 ≤ Real.log 3 ^ 5 := by positivity
    nlinarith
  have hx0 : 0 ≤ s ^ 2 * Real.log s ^ 5 / Real.log y ^ 2 := by positivity
  rw [delta]
  calc (1 + s ^ 2 * Real.log s ^ 5 / Real.log y ^ 2) ^ (5 * s)
      ≤ (1 + 9 * Real.log 3 ^ 5) ^ (5 * s) := Real.rpow_le_rpow (by linarith) (by linarith)
        (by linarith)
    _ ≤ (1 + 9 * Real.log 3 ^ 5) ^ (15 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
theorem theorem5_card_rosserSet_le (hPNT : StrongPNTProp) : ∃ K y₀ : ℝ, ∀ y ≥ y₀, ∀ s ∈ Set.Icc (2 : ℝ) 3,
    (#(rosserSet true y (y ^ (1 / s))) : ℝ) ≤ K * y / Real.log y ^ 2 := by
  obtain ⟨c₇, hc₇, h5⟩ := (theorem5 hPNT)
  obtain ⟨y₅, hxi⟩ := exists_xi_large
  set D := (1 + 9 * Real.log 3 ^ 5) ^ (15 : ℝ) with hD
  refine ⟨c₇ * D * 2, max y₅ 3, fun y hy s hs => ?_⟩
  obtain ⟨hy1, hξ, -, -⟩ := hxi y (le_of_max_le_left hy)
  have hy3 : 3 ≤ y := le_of_max_le_right hy
  have hL1 : 1 ≤ Real.log y := by
    have := Real.log_le_log (by norm_num) hy3
    linarith [one_lt_log_three]
  have hsξ : s ≤ xi y := hs.2.trans (by linarith [Real.add_one_le_exp (32 : ℝ)])
  set z := y ^ (1 / s)
  have hall : (rosserSet true y z).filter (fun d => #d.primeFactors ≤ #(primesLT z)) =
      rosserSet true y z :=
    filter_true_of_mem fun d hd => card_le_card (primeFactors_subset_of_mem_rosserSet hd)
  have h := h5 #(primesLT z) true y s hy1 hs.1 hsξ
  rw [hall] at h
  refine h.trans ?_
  have hδ := delta_le_of_le_three (by linarith [hs.1]) hs.2 hL1 (y := y)
  have hδ0 := delta_pos (by linarith [hs.1] : (1 : ℝ) ≤ s) y
  have hG := errMaj_le_two true s
  have hG0 := errMaj_pos true s
  have hφ : ((#(primesLT z) : ℕ) + 1 : ℝ) / ((#(primesLT z) : ℕ) + 2) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hφ0 : (0 : ℝ) ≤ ((#(primesLT z) : ℕ) + 1 : ℝ) / ((#(primesLT z) : ℕ) + 2) := by positivity
  have hyL : 0 ≤ y / Real.log y ^ 2 := by positivity
  calc c₇ * ((#(primesLT z) + 1) / (#(primesLT z) + 2)) * delta s y * errMaj true s * y /
        Real.log y ^ 2
      = c₇ * ((#(primesLT z) + 1) / (#(primesLT z) + 2)) * delta s y * errMaj true s *
          (y / Real.log y ^ 2) := by ring
    _ ≤ c₇ * 1 * D * 2 * (y / Real.log y ^ 2) := by gcongr
    _ = c₇ * D * 2 * y / Real.log y ^ 2 := by ring
end IwaniecLinearSieve
end
section
open Real Filter Finset
namespace IwaniecLinearSieve
def LinearSieveEstimate : Prop :=
  ∃ C₀ c K z₀ : ℝ, 0 < c ∧ ∀ z ≥ z₀,
    R z - rosserMain true (C₀ * z ^ 2) z ≤ R z * (1 - c / log z) ∧
      (#(rosserSet true (C₀ * z ^ 2) z) : ℝ) ≤ K * z ^ 2 / log z ^ 2
theorem rpow_one_div_log_div {y z : ℝ} (hy : 0 < y) (hz : 1 < z) (hyl : log y ≠ 0) :
    y ^ (1 / (log y / log z)) = z := by
  have hlz : log z ≠ 0 := (log_pos hz).ne'
  rw [rpow_def_of_pos hy, show log y * (1 / (log y / log z)) = log z by field_simp,
    exp_log (by linarith)]
theorem div_one_add_le_log_one_add {x : ℝ} (hx : 0 ≤ x) : x / (1 + x) ≤ log (1 + x) := by
  have h := log_le_sub_one_of_pos (show 0 < (1 + x)⁻¹ by positivity)
  rw [log_inv] at h
  have : (1 + x)⁻¹ - 1 = -(x / (1 + x)) := by field_simp; ring
  linarith
theorem two_mul_div_three_le_log_sub_one {x s : ℝ} (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2)
    (hs : 2 + x ≤ s) : 2 * x / 3 ≤ log (s - 1) := by
  calc 2 * x / 3 = x / (3 / 2) := by ring
    _ ≤ x / (1 + x) :=
        div_le_div_of_nonneg_left hx (by positivity) (by linarith only [hxhalf])
    _ ≤ log (1 + x) := div_one_add_le_log_one_add hx
    _ ≤ log (s - 1) := log_le_log (by positivity) (by linarith only [hs])
theorem tendsto_pntE_mul_log : Tendsto (fun z => pntE z * log z) atTop (nhds 0) := by
  have hu : Tendsto (fun z : ℝ => pntκ * √(log z)) atTop atTop :=
    (tendsto_sqrt_atTop.comp tendsto_log_atTop).const_mul_atTop pntκ_pos
  have h := (tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp hu
  have h' := h.div_const (pntκ ^ 2)
  rw [zero_div] at h'
  refine h'.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with z hz
  have hl : 0 ≤ log z := log_nonneg hz
  simp only [Function.comp, pntE]
  rw [mul_pow, sq_sqrt hl, neg_mul]
  field_simp [pntκ_pos.ne']
theorem sieve_error_absorption {A B s ℓ : ℝ} (hA : A = B + 5) (hB : 0 ≤ B)
    (hs2 : 2 ≤ s) (hs25 : s ≤ 5 / 2) (hℓ : 0 < ℓ) :
    (s - 2 * A / ℓ) / (s * ℓ) + B / (s * ℓ) ^ 2 ≤ 1 / ℓ - 4 / ℓ ^ 2 := by
  have hs0 : 0 < s := by linarith only [hs2]
  have hkey : 4 * s ^ 2 ≤ 2 * A * s - B := by
    have hmargin : 2 * A * s - B - 4 * s ^ 2 =
        B * (2 * s - 1) + 2 * s * (5 - 2 * s) := by rw [hA]; ring
    have hBterm := mul_nonneg hB (by linarith only [hs2] : (0 : ℝ) ≤ 2 * s - 1)
    have hsterm := mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * s)
      (by linarith only [hs25] : (0 : ℝ) ≤ 5 - 2 * s)
    linarith only [hmargin, hBterm, hsterm]
  have hsaving : 4 / ℓ ^ 2 ≤ (2 * A * s - B) / (s ^ 2 * ℓ ^ 2) := by
    calc 4 / ℓ ^ 2 = (4 * s ^ 2) / (s ^ 2 * ℓ ^ 2) := by field_simp
      _ ≤ (2 * A * s - B) / (s ^ 2 * ℓ ^ 2) :=
          div_le_div_of_nonneg_right hkey (by positivity)
  calc (s - 2 * A / ℓ) / (s * ℓ) + B / (s * ℓ) ^ 2 =
      1 / ℓ - (2 * A * s - B) / (s ^ 2 * ℓ ^ 2) := by field_simp; ring
    _ ≤ 1 / ℓ - 4 / ℓ ^ 2 := sub_le_sub le_rfl hsaving
theorem pnt_error_absorption {c e ℓ : ℝ} (hℓ : 0 < ℓ) (he0 : 0 ≤ e)
    (he : e * ℓ ≤ 3 * c) :
    c / ℓ - 4 * c / ℓ ^ 2 ≤ (c - e) / ℓ * (1 - 1 / ℓ) := by
  have herror : e / ℓ ≤ 3 * c / ℓ ^ 2 := by
    calc e / ℓ = (e * ℓ) / ℓ ^ 2 := by field_simp
      _ ≤ 3 * c / ℓ ^ 2 := div_le_div_of_nonneg_right he (sq_nonneg ℓ)
  have hremaining : 0 ≤ e / ℓ ^ 2 := div_nonneg he0 (sq_nonneg ℓ)
  have hsplit : 4 * c / ℓ ^ 2 = c / ℓ ^ 2 + 3 * c / ℓ ^ 2 := by ring
  calc c / ℓ - 4 * c / ℓ ^ 2
      ≤ c / ℓ - c / ℓ ^ 2 - e / ℓ + e / ℓ ^ 2 := by
        linarith only [herror, hremaining, hsplit]
    _ = (c - e) / ℓ * (1 - 1 / ℓ) := by field_simp; ring
theorem linearSieveEstimate (hPNT : StrongPNTProp) : LinearSieveEstimate := by
  obtain ⟨cR, hcR, CR, hR⟩ := (R_asymp hPNT)
  have hCR : 0 ≤ CR := by
    have h2 := hR 2 le_rfl
    exact nonneg_of_mul_nonneg_left ((abs_nonneg _).trans h2) (pntE_pos 2)
  obtain ⟨c₇, hc₇, h4⟩ := (theorem4 hPNT) hcR hR
  obtain ⟨K, y₀, h5⟩ := (theorem5_card_rosserSet_le hPNT)
  set D := (1 + 9 * Real.log 3 ^ 5) ^ (15 : ℝ) with hD
  have hD0 : 0 ≤ D := by positivity
  set B := 2 * c₇ * D with hB
  have hB0 : 0 ≤ B := by positivity
  set A := B + 5 with hA
  set C₀ := exp A with hC₀
  have hC₀0 : 0 < C₀ := exp_pos A
  clear_value D B A C₀
  have hyz : Tendsto (fun z : ℝ => C₀ * z ^ 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).const_mul_atTop hC₀0
  have hev : ∀ᶠ z : ℝ in atTop, 2 * A ≤ log z ∧ 2 ≤ z ∧ CR * pntE z * log z ≤ 3 * cR ∧
      y₀ ≤ C₀ * z ^ 2 ∧ 3 ≤ xi (C₀ * z ^ 2) := by
    refine (tendsto_log_atTop.eventually_ge_atTop (2 * A)).and
      ((eventually_ge_atTop 2).and ?_)
    refine (((tendsto_pntE_mul_log.const_mul CR).eventually
      (eventually_le_nhds (show CR * 0 < 3 * cR by linarith))).mono
        fun z hz => by linarith).and ?_
    exact (hyz.eventually_ge_atTop y₀).and ((tendsto_xi.comp hyz).eventually_ge_atTop 3)
  obtain ⟨z₀, hz₀⟩ := eventually_atTop.1 hev
  refine ⟨C₀, 1, |K| * C₀, z₀, one_pos, fun z hz => ?_⟩
  obtain ⟨hlz, hz2, hpnt, hy₀, hxi⟩ := hz₀ z hz
  set ℓ := log z with hℓ
  set y := C₀ * z ^ 2 with hy
  have hA5 : 5 ≤ A := by linarith
  have hℓ10 : 10 ≤ ℓ := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hz1 : 1 < z := by linarith
  have hy0 : 0 < y := by positivity
  have hL : log y = A + 2 * ℓ := by
    rw [hy, log_mul hC₀0.ne' (by positivity), log_pow, hC₀, log_exp]; push_cast; ring
  set s := log y / ℓ with hs
  have hsℓ : s * ℓ = log y := by rw [hs]; field_simp
  have hs2 : 2 ≤ s := by rw [hs, le_div_iff₀ hℓ0]; linarith
  have hs25 : s ≤ 5 / 2 := by rw [hs, div_le_iff₀ hℓ0]; linarith
  have hzs : y ^ (1 / s) = z := rpow_one_div_log_div hy0 hz1 (by rw [hL]; positivity)
  clear_value s y ℓ
  have hL1 : 1 ≤ log y := by rw [hL]; linarith
  constructor
  ·
    set r := #(primesLT z) + 1
    have hfail := (fail_eq_of_card_lt (z := z) (r := r) (by omega) y).1
    have hy1 : 1 < y := by
      have hz21 : 1 < z ^ 2 := by nlinarith
      have hC₀1 : 1 ≤ C₀ := by rw [hC₀]; exact one_le_exp (by linarith)
      rw [hy]; nlinarith
    have h4' := h4 r true y s hy1 (by simpa [sMin] using hs2) (by linarith)
    rw [hzs, hfail] at h4'
    have hf : fSieve s ≤ s - 3 * log (s - 1) := by
      have := one_sub_fSieve_div_ge s ⟨hs2, by linarith⟩
      have hs0 : 0 < s := by linarith
      rw [ge_iff_le, div_le_iff₀ hs0, sub_mul, div_mul_cancel₀ _ hs0.ne'] at this
      linarith
    have hlog : 2 * A / (3 * ℓ) ≤ log (s - 1) := by
      have hx : s - 1 = 1 + A / ℓ := by
        rw [hs, hL]; field_simp; ring
      have hxA : A / ℓ ≤ 1 / 2 := by rw [div_le_iff₀ hℓ0]; linarith only [hlz]
      calc 2 * A / (3 * ℓ) = 2 * (A / ℓ) / 3 := by ring
        _ ≤ log (s - 1) :=
            two_mul_div_three_le_log_sub_one (by positivity) hxA (by linarith only [hx])
    have herr : c₇ * ((r : ℝ) / (r + 1)) * delta s y * errMaj true s ≤ B := by
      have hδ : delta s y ≤ D := hD ▸ delta_le_of_le_three (s := s) (by linarith) (by linarith) hL1
      have hδ0 := delta_pos (by linarith : (1 : ℝ) ≤ s) y
      have hG := errMaj_le_two true s
      have hG0 := (errMaj_pos true s).le
      have hφ : (r : ℝ) / (r + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      have hφ0 : (0 : ℝ) ≤ (r : ℝ) / (r + 1) := by positivity
      calc c₇ * ((r : ℝ) / (r + 1)) * delta s y * errMaj true s ≤ c₇ * 1 * D * 2 := by
            gcongr
        _ = B := by rw [hB]; ring
    have hdef : R z - rosserMain true y z ≤ cR / ℓ - 4 * cR / ℓ ^ 2 := by
      refine h4'.trans ?_
      have hmain : mainMaj true s / log y + c₇ * ((r : ℝ) / (r + 1)) * delta s y *
          errMaj true s / log y ^ 2 ≤ (s - 2 * A / ℓ) / log y + B / log y ^ 2 := by
        rw [mainMaj_true]
        have h3 : 3 * (2 * A / (3 * ℓ)) = 2 * A / ℓ := by field_simp
        gcongr
        linarith only [hf, hlog, h3]
      have hfin : (s - 2 * A / ℓ) / log y + B / log y ^ 2 ≤ 1 / ℓ - 4 / ℓ ^ 2 := by
        rw [← hsℓ]
        exact sieve_error_absorption hA hB0 hs2 hs25 hℓ0
      calc cR * (mainMaj true s / log y + c₇ * ((r : ℝ) / (r + 1)) * delta s y *
            errMaj true s / log y ^ 2) ≤ cR * (1 / ℓ - 4 / ℓ ^ 2) := by
            exact mul_le_mul_of_nonneg_left (hmain.trans hfin) hcR.le
        _ = cR / ℓ - 4 * cR / ℓ ^ 2 := by ring
    have hRz : (cR - CR * pntE z) / ℓ ≤ R z := by
      rw [div_le_iff₀ hℓ0]
      have hRlower := (abs_le.1 (hR z hz2)).1
      rw [← hℓ] at hRlower
      linarith only [hRlower]
    have h1 : 0 ≤ 1 - 1 / ℓ := by
      rw [sub_nonneg, div_le_one hℓ0]; linarith
    calc R z - rosserMain true y z ≤ cR / ℓ - 4 * cR / ℓ ^ 2 := hdef
      _ ≤ (cR - CR * pntE z) / ℓ * (1 - 1 / ℓ) :=
          pnt_error_absorption hℓ0 (mul_nonneg hCR (pntE_pos z).le) hpnt
      _ ≤ R z * (1 - 1 / ℓ) := mul_le_mul_of_nonneg_right hRz h1
  ·
    have h := h5 y hy₀ s ⟨hs2, by linarith⟩
    rw [hzs] at h
    refine h.trans ?_
    have hLℓ : ℓ ^ 2 ≤ log y ^ 2 := by
      rw [hL]; exact pow_le_pow_left₀ hℓ0.le (by linarith) 2
    calc K * y / log y ^ 2 ≤ |K| * y / log y ^ 2 := by
          gcongr; exact le_abs_self K
      _ ≤ |K| * y / ℓ ^ 2 := by
          gcongr
      _ = |K| * C₀ * z ^ 2 / ℓ ^ 2 := by rw [hy]; ring
end IwaniecLinearSieve
end
section
open Finset Real
namespace IwaniecLinearSieve
theorem exists_covering_length_le (hL : LinearSieveEstimate)
    (hR : ∃ c > 0, ∀ z ≥ 2, c / log z ≤ R z) :
    ∃ K z₁ : ℝ, ∀ z ≥ z₁, ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → #S = #(primesLT z) →
      ∀ (x : ℤ) (m : ℕ), (∀ k < m, ∃ p ∈ S, (p : ℤ) ∣ x + k) → (m : ℝ) ≤ K * z ^ 2 := by
  obtain ⟨C₀, c, K, z₀, hc, hL⟩ := hL
  obtain ⟨c', hc', hR⟩ := hR
  refine ⟨K / (c * c'), max z₀ 2, fun z hz S hS hcard x m hm ↦ ?_⟩
  have hz0 : z₀ ≤ z := (le_max_left _ _).trans hz
  have hz2 : 2 ≤ z := (le_max_right _ _).trans hz
  have hlog : 0 < log z := log_pos (by linarith)
  have hRz := R_pos z
  set M := rosserMain true (C₀ * z ^ 2) z
  obtain ⟨hmain, hcount⟩ := hL z hz0
  have hsieve := shiftedSieve (C₀ * z ^ 2) hS hcard x m
  have hzero : (range m).filter (fun k : ℕ ↦ ∀ q ∈ S, ¬ (q : ℤ) ∣ x + k) = ∅ := by
    rw [filter_eq_empty_iff]
    intro k hk h
    obtain ⟨q, hq, hqk⟩ := hm k (mem_range.1 hk)
    exact h q hq hqk
  rw [hzero, card_empty, Nat.cast_zero] at hsieve
  have hM : R z * (c / log z) ≤ M := by nlinarith
  have hM0 : 0 ≤ M := (mul_nonneg hRz.le (div_pos hc hlog).le).trans hM
  have hprod := R_le_prod_of_card_eq hS hcard
  have h1 : (m : ℝ) * M ≤ #(rosserSet true (C₀ * z ^ 2) z) := by
    have : (m : ℝ) * M ≤ m * (∏ q ∈ S, (1 - (q : ℝ)⁻¹)) * (M / R z) := by
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ m.cast_nonneg
      calc M = R z * (M / R z) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right hprod (div_nonneg hM0 hRz.le)
    linarith
  have hRlog : c' ≤ R z * log z := by
    have := hR z hz2
    rwa [div_le_iff₀ hlog] at this
  have h2 : (m : ℝ) * (c * c') ≤ K * z ^ 2 := by
    have hm0 : (0 : ℝ) ≤ m := m.cast_nonneg
    have e1 : (m : ℝ) * (c * c') ≤ (m : ℝ) * (R z * (c / log z)) * log z ^ 2 := by
      have : (m : ℝ) * (R z * (c / log z)) * log z ^ 2 = m * c * (R z * log z) := by
        field_simp
      rw [this, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left hRlog (mul_nonneg hm0 hc.le)
    have e2 : (m : ℝ) * (R z * (c / log z)) * log z ^ 2 ≤ K * z ^ 2 / log z ^ 2 * log z ^ 2 := by
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      exact (mul_le_mul_of_nonneg_left hM hm0).trans (h1.trans hcount)
    have e3 : K * z ^ 2 / log z ^ 2 * log z ^ 2 = K * z ^ 2 := by
      field_simp
    linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ (mul_pos hc hc')]
  linarith
theorem card_primesLT_nth_prime_add_one (n : ℕ) :
    #(primesLT ((Nat.nth Nat.Prime n : ℝ) + 1)) = n + 1 := by
  rw [primesLT, show (Nat.nth Nat.Prime n : ℝ) + 1 = ((Nat.nth Nat.Prime n + 1 : ℕ) : ℝ) by
    push_cast; ring, Nat.ceil_natCast, Nat.primesBelow_card_eq_primeCounting', Nat.primeCounting',
    Nat.count_succ_eq_succ_count (Nat.prime_nth_prime n),
    Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime]
theorem exists_superset_card_eq {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {N : ℕ} (hN : #S ≤ N) :
    ∃ S' : Finset ℕ, S ⊆ S' ∧ (∀ p ∈ S', p.Prime) ∧ #S' = N := by
  set U := primesLT ((Nat.nth Nat.Prime N : ℝ) + 1)
  have hU : #U = N + 1 := card_primesLT_nth_prime_add_one N
  have : N - #S ≤ #(U \ S) := (Nat.sub_le_sub_right (by omega) _).trans (le_card_sdiff S U)
  obtain ⟨T, hTU, hT⟩ := exists_subset_card_eq this
  refine ⟨S ∪ T, subset_union_left, fun p hp ↦ ?_, ?_⟩
  · rcases mem_union.1 hp with hp | hp
    · exact hS p hp
    · exact prime_of_mem_primesLT (sdiff_subset (hTU hp))
  · rw [card_union_of_disjoint (disjoint_of_subset_right hTU disjoint_sdiff), hT]
    omega
theorem iwaniecBound_of_estimates (hL : LinearSieveEstimate)
    (hR : ∃ c > 0, ∀ z ≥ 2, c / log z ≤ R z)
    (hp : ∃ C, ∀ r ≥ 2, (Nat.nth Nat.Prime (r - 1) : ℝ) ≤ C * r * log r) :
    ∃ C : ℝ, ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → 2 ≤ S.card →
      ∀ (x : ℤ) (m : ℕ), (∀ k < m, ∃ p ∈ S, (p : ℤ) ∣ x + k) →
        (m : ℝ) ≤ C * ((S.card : ℝ) * Real.log S.card) ^ 2 := by
  obtain ⟨K, z₁, hK⟩ := exists_covering_length_le hL hR
  obtain ⟨Cp, hCp⟩ := hp
  set N₀ : ℕ := ⌈z₁⌉₊ + 2
  set B : ℝ := N₀ * (log N₀ / log 2 + 1)
  refine ⟨max K 0 * (|Cp| * B + 1) ^ 2, fun S hS hr x m hm ↦ ?_⟩
  set r := #S
  set N := N₀ * r
  have hrN : r ≤ N := Nat.le_mul_of_pos_left r (by omega)
  have hN2 : 2 ≤ N := hr.trans hrN
  obtain ⟨S', hSS', hS', hcard'⟩ := exists_superset_card_eq hS hrN
  set p := Nat.nth Nat.Prime (N - 1)
  set z : ℝ := p + 1
  have hcardz : #(primesLT z) = N := by
    rw [card_primesLT_nth_prime_add_one]
    omega
  have hz : z₁ ≤ z := by
    have h1 := Nat.add_two_le_nth_prime (N - 1)
    have h2 : N₀ ≤ N := Nat.le_mul_of_pos_right _ (by omega)
    have h3 : z₁ ≤ ⌈z₁⌉₊ := Nat.le_ceil z₁
    have h4 : (⌈z₁⌉₊ : ℝ) + 1 ≤ p := by exact_mod_cast (by omega : ⌈z₁⌉₊ + 1 ≤ p)
    simp only [z]
    linarith
  have hmz := hK z hz S' hS' (hcard'.trans hcardz.symm) x m fun k hk ↦
    let ⟨q, hq, h⟩ := hm k hk
    ⟨q, hSS' hq, h⟩
  have hlog2 : (0.69 : ℝ) < log 2 := by linarith [Real.log_two_gt_d9]
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hlogr : log 2 ≤ log r := log_le_log (by norm_num) hr'
  have hrlogr : 1 ≤ (r : ℝ) * log r := by nlinarith
  have hN₀ : (1 : ℝ) ≤ N₀ := by exact_mod_cast (by omega : 1 ≤ N₀)
  have hlogN : log N ≤ (log N₀ / log 2 + 1) * log r := by
    rw [Nat.cast_mul, log_mul (by positivity) (by positivity)]
    have : log N₀ ≤ log N₀ / log 2 * log r := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
      exact mul_le_mul_of_nonneg_left hlogr (log_nonneg hN₀)
    linarith
  have hN : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNlogN0 : 0 ≤ (N : ℝ) * log N := mul_nonneg (by linarith) (log_nonneg (by linarith))
  have hpN : (p : ℝ) ≤ |Cp| * (B * (r * log r)) := by
    have h1 := hCp N hN2
    have h2 : (N : ℝ) * log N ≤ B * (r * log r) := by
      calc (N : ℝ) * log N = N₀ * r * log N := by simp [N]
        _ ≤ N₀ * r * ((log N₀ / log 2 + 1) * log r) :=
          mul_le_mul_of_nonneg_left hlogN (by positivity)
        _ = B * (r * log r) := by ring
    calc (p : ℝ) ≤ Cp * N * log N := h1
      _ = Cp * (N * log N) := by ring
      _ ≤ |Cp| * (N * log N) := mul_le_mul_of_nonneg_right (le_abs_self _) hNlogN0
      _ ≤ |Cp| * (B * (r * log r)) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  have hz' : z ≤ (|Cp| * B + 1) * (r * log r) := by
    simp only [z]
    nlinarith
  have hz0 : 0 ≤ z := by positivity
  calc (m : ℝ) ≤ K * z ^ 2 := hmz
    _ ≤ max K 0 * z ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    _ ≤ max K 0 * ((|Cp| * B + 1) * (r * log r)) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz0 hz' 2) (le_max_right _ _)
    _ = _ := by ring
end IwaniecLinearSieve
end
section
namespace IwaniecLinearSieve
theorem iwaniecBound (hPNT : StrongPNTProp) :
    ∃ C : ℝ, ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → 2 ≤ S.card →
      ∀ (x : ℤ) (m : ℕ), (∀ k < m, ∃ p ∈ S, (p : ℤ) ∣ x + k) →
        (m : ℝ) ≤ C * ((S.card : ℝ) * Real.log S.card) ^ 2 :=
  iwaniecBound_of_estimates (linearSieveEstimate hPNT) (R_lower hPNT) (nth_prime_le hPNT)
end IwaniecLinearSieve
end


theorem OMA.solution : OMA.R_Erdos929_erdos_929_variants_rosser_R1_H1_R1.H2 := fun h => IwaniecLinearSieve.iwaniecBound h
