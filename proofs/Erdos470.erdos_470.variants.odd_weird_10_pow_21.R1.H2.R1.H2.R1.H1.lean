import OMAReductions.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H2_R1_H2_R1
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Forall2
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Log
import Mathlib.Data.Set.Card
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.FactorisationProperties
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OddWeirdSubproblems

open Finset

abbrev Coordinates := List (ℕ × ℕ)

def powerSum (p : ℕ) : ℕ → ℕ
  | 0 => 1
  | e + 1 => powerSum p e + p ^ (e + 1)

theorem powerSum_eq_sum (p e : ℕ) : powerSum p e = ∑ i ∈ range (e + 1), p ^ i := by
  induction e with
  | zero => simp [powerSum]
  | succ e ih => rw [powerSum, sum_range_succ, ih]

def number (fs : Coordinates) : ℕ := (fs.map fun (p, e) => p ^ e).prod

def divisorSum (fs : Coordinates) : ℕ := (fs.map fun (p, e) => powerSum p e).prod

def index (p e : ℕ) : ℚ := (powerSum p e : ℚ) / (p : ℚ) ^ e

def limitingIndex (p : ℕ) : ℚ := (p : ℚ) / ((p : ℚ) - 1)

structure Slot where
  prime : ℕ
  exponent : ℕ
  fixed : Bool

def Slot.Fits (s : Slot) (x : ℕ × ℕ) : Prop :=
  x.1.Prime ∧ s.prime = x.1 ∧ s.exponent ≤ x.2 ∧ (s.fixed = true → s.exponent = x.2)

def Slot.upper (s : Slot) : ℚ :=
  if s.fixed then index s.prime s.exponent else limitingIndex s.prime

def Slot.minimum (s : Slot) : ℕ × ℕ := (s.prime, s.exponent)

def TailFits : ℕ → Coordinates → Prop
  | _, [] => True
  | p, (q, e) :: qs => p ≤ q ∧ 2 < q ∧ q.Prime ∧ Odd q ∧ 0 < e ∧ TailFits (q + 2) qs

def tailUpper : ℕ → ℕ → ℚ
  | _, 0 => 1
  | p, r + 1 => limitingIndex p * tailUpper (p + 2) r

theorem index_le_limitingIndex {p e : ℕ} (hp : 1 < p) :
    index p e ≤ limitingIndex p := by
  have hpq : (1 : ℚ) < p := by exact_mod_cast hp
  have hpow : (0 : ℚ) < (p : ℚ) ^ e := pow_pos (by linarith) _
  unfold index limitingIndex
  rw [powerSum_eq_sum]
  push_cast
  rw [div_le_div_iff₀ hpow (sub_pos.mpr hpq), geom_sum_mul, pow_succ]
  linarith

theorem limitingIndex_antitone {p q : ℕ} (hp : 1 < p) (hpq : p ≤ q) :
    limitingIndex q ≤ limitingIndex p := by
  have hp' : (1 : ℚ) < p := by exact_mod_cast hp
  have hpq' : (p : ℚ) ≤ q := by exact_mod_cast hpq
  unfold limitingIndex
  rw [div_le_div_iff₀ (sub_pos.mpr (hp'.trans_le hpq')) (sub_pos.mpr hp')]
  nlinarith

theorem slot_index_le {s : Slot} {x : ℕ × ℕ} (h : s.Fits x) :
    index x.1 x.2 ≤ s.upper := by
  obtain ⟨hp, hs, _, he⟩ := h
  cases hf : s.fixed
  · simpa [Slot.upper, hf, hs] using (index_le_limitingIndex (e := x.2) hp.one_lt)
  · simp [Slot.upper, hf, hs, he hf]

theorem index_nonneg (p e : ℕ) : 0 ≤ index p e := by unfold index; positivity

theorem limitingIndex_nonneg {p : ℕ} (hp : 1 < p) : 0 ≤ limitingIndex p := by
  have hp' : (1 : ℚ) < p := by exact_mod_cast hp
  exact div_nonneg (by positivity) (sub_nonneg.mpr hp'.le)

theorem coordinate_index_eq (xs : Coordinates) :
    (xs.map fun x => index x.1 x.2).prod = (divisorSum xs : ℚ) / (number xs : ℚ) := by
  induction xs with
  | nil => simp [divisorSum, number]
  | cons x xs ih =>
    rcases x with ⟨p, e⟩
    simp only [List.map_cons, List.prod_cons, ih]
    simp only [index, divisorSum, number, List.map_cons, List.prod_cons, Nat.cast_mul,
      Nat.cast_pow, div_mul_div_comm]

theorem coordinate_prod_nonneg (xs : Coordinates) :
    0 ≤ (xs.map fun x => index x.1 x.2).prod := by
  induction xs with
  | nil => norm_num
  | cons x xs ih => exact mul_nonneg (index_nonneg _ _) ih

theorem slot_prod_upper {ss : List Slot} {xs : Coordinates}
    (h : List.Forall₂ Slot.Fits ss xs) :
    (xs.map fun x => index x.1 x.2).prod ≤ (ss.map Slot.upper).prod := by
  induction h with
  | nil => simp
  | cons h₁ _ ih =>
    simp only [List.map_cons, List.prod_cons]
    refine mul_le_mul (slot_index_le h₁) ih ?_ ((index_nonneg _ _).trans (slot_index_le h₁))
    exact coordinate_prod_nonneg _

theorem tailUpper_nonneg {p : ℕ} (hp : 1 < p) (r : ℕ) : 0 ≤ tailUpper p r := by
  induction r generalizing p with
  | zero => simp [tailUpper]
  | succ r ih => exact mul_nonneg (limitingIndex_nonneg hp) (ih (by omega))

theorem tailUpper_antitone {p q : ℕ} (hp : 1 < p) (hpq : p ≤ q) (r : ℕ) :
    tailUpper q r ≤ tailUpper p r := by
  induction r generalizing p q with
  | zero => simp [tailUpper]
  | succ r ih =>
    exact mul_le_mul (limitingIndex_antitone hp hpq) (ih (by omega) (by omega))
      (tailUpper_nonneg (show 1 < q + 2 by omega) r) (limitingIndex_nonneg hp)

theorem tail_prod_upper {p : ℕ} {xs : Coordinates} (hp : 1 < p) (h : TailFits p xs) :
    (xs.map fun x => index x.1 x.2).prod ≤ tailUpper p xs.length := by
  induction xs generalizing p with
  | nil => simp [tailUpper]
  | cons x xs ih =>
    rcases x with ⟨q, e⟩
    obtain ⟨hpq, _, hq, _, _, ht⟩ := h
    simp only [List.map_cons, List.prod_cons, List.length_cons, tailUpper]
    exact mul_le_mul ((index_le_limitingIndex hq.one_lt).trans (limitingIndex_antitone hp hpq))
      ((ih (show 1 < q + 2 by omega) ht).trans
        (tailUpper_antitone (show 1 < p + 2 by omega) (by omega) xs.length))
      (coordinate_prod_nonneg xs) (limitingIndex_nonneg hp)

theorem tailFits_of_sorted {xs : Coordinates} {p : ℕ}
    (hp : 2 < p)
    (hlo : ∀ x ∈ xs, p ≤ x.1)
    (hlocal : ∀ x ∈ xs, x.1.Prime ∧ Odd x.1 ∧ 0 < x.2)
    (horder : xs.Pairwise (fun x y => x.1 < y.1)) : TailFits p xs := by
  induction xs generalizing p with
  | nil => trivial
  | cons x xs ih =>
    obtain ⟨q, e⟩ := x
    have hq := hlo (q, e) (by simp)
    obtain ⟨hprime, hodd, he⟩ := hlocal (q, e) (by simp)
    change p ≤ q at hq
    obtain ⟨horder, htail⟩ := List.pairwise_cons.mp horder
    refine ⟨hq, by omega, hprime, hodd, he, ih (by omega) ?_ ?_ htail⟩
    · intro z hz
      have hlt := horder z hz
      have hzodd := (hlocal z (List.mem_cons_of_mem _ hz)).2.1
      obtain ⟨a, ha⟩ := hodd
      obtain ⟨b, hb⟩ := hzodd
      change q < z.1 at hlt
      omega
    · intro z hz
      exact hlocal z (List.mem_cons_of_mem _ hz)

def PrimeCoordinates (xs : Coordinates) : Prop :=
  (∀ x ∈ xs, x.1.Prime) ∧ xs.Pairwise (fun x y => x.1 < y.1)

theorem number_cons (x : ℕ × ℕ) (xs : Coordinates) :
    number (x :: xs) = x.1 ^ x.2 * number xs := rfl

theorem number_append (xs ys : Coordinates) : number (xs ++ ys) = number xs * number ys := by
  simp [number, List.prod_append]

theorem divisorSum_append (xs ys : Coordinates) :
    divisorSum (xs ++ ys) = divisorSum xs * divisorSum ys := by
  simp [divisorSum, List.prod_append]

theorem number_pos {xs : Coordinates} (h : ∀ x ∈ xs, Nat.Prime x.1) : 0 < number xs := by
  induction xs with
  | nil => decide
  | cons x xs ih =>
    rw [number_cons]
    exact Nat.mul_pos (pow_pos (h x (by simp)).pos _)
      (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))

theorem divisorSum_eq {xs : Coordinates} (hs : PrimeCoordinates xs) :
    divisorSum xs = ∑ d ∈ (number xs).divisors, d := by
  induction xs with
  | nil => decide
  | cons x xs ih =>
    obtain ⟨hp, hlt⟩ := hs
    obtain ⟨horder, htail⟩ := List.pairwise_cons.mp hlt
    have hp' : ∀ y ∈ xs, Nat.Prime y.1 := fun y hy => hp y (List.mem_cons_of_mem _ hy)
    have hcop : (x.1 ^ x.2).Coprime (number xs) := by
      apply Nat.coprime_list_prod_right_iff.mpr
      intro m hm
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hm
      exact Nat.coprime_pow_primes _ _ (hp x (by simp)) (hp' y hy) (horder y hy).ne
    rw [number_cons, hcop.sum_divisors_mul, ← ih ⟨hp', htail⟩,
      ← ArithmeticFunction.sigma_one_apply, ArithmeticFunction.sigma_one_apply_prime_pow (hp x (by simp))]
    change powerSum x.1 x.2 * divisorSum xs = _
    rw [powerSum_eq_sum]

theorem deficient_iff_divisorSum_lt {xs : Coordinates} (hs : PrimeCoordinates xs) :
    (number xs).Deficient ↔ divisorSum xs < 2 * number xs := by
  rw [divisorSum_eq hs, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  unfold Nat.Deficient
  omega

theorem slot_fits_split {s : Slot} {x : ℕ × ℕ} (h : s.Fits x) (hf : s.fixed = false) :
    ({s with fixed := true} : Slot).Fits x ∨ ({s with exponent := s.exponent + 1} : Slot).Fits x := by
  obtain ⟨hp, hq, he, _⟩ := h
  by_cases eq : s.exponent = x.2
  · exact Or.inl ⟨hp, hq, he, fun _ => eq⟩
  · exact Or.inr ⟨hp, hq, by dsimp; omega, by simp [hf]⟩

theorem minimum_dvd {ss : List Slot} {xs : Coordinates} (h : List.Forall₂ Slot.Fits ss xs) :
    number (ss.map Slot.minimum) ∣ number xs := by
  induction h with
  | nil => exact dvd_rfl
  | @cons s x ss xs hfit _ ih =>
    simp only [List.map_cons, number_cons, Slot.minimum, hfit.2.1]
    exact Nat.mul_dvd_mul (pow_dvd_pow _ hfit.2.2.1) ih

theorem exists_fit_of_mem {s : Slot} {ss : List Slot} {xs : Coordinates}
    (h : List.Forall₂ Slot.Fits ss xs) (hm : s ∈ ss) : ∃ x ∈ xs, s.Fits x := by
  induction h with
  | nil => simp at hm
  | @cons t x ts xs hfit ht ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨x, by simp, hfit⟩
    · obtain ⟨y, hy, hsy⟩ := ih hm
      exact ⟨y, List.mem_cons_of_mem _ hy, hsy⟩

theorem minimum_valid {ss : List Slot} {xs : Coordinates}
    (h : List.Forall₂ Slot.Fits ss xs) (hxs : PrimeCoordinates xs) :
    PrimeCoordinates (ss.map Slot.minimum) := by
  induction h with
  | nil => simp [PrimeCoordinates]
  | @cons s x ss xs hfit ht ih =>
    obtain ⟨hp, hpw⟩ := hxs
    obtain ⟨horder, htail⟩ := List.pairwise_cons.mp hpw
    obtain ⟨htp, htw⟩ := ih ⟨fun y hy => hp y (List.mem_cons_of_mem _ hy), htail⟩
    constructor
    · simp only [List.map_cons, List.mem_cons, forall_eq_or_imp]
      exact ⟨by simpa only [Slot.minimum, hfit.2.1] using hfit.1, htp⟩
    · simp only [List.map_cons, List.pairwise_cons]
      refine ⟨?_, htw⟩
      intro y hy
      obtain ⟨t, htmem, rfl⟩ := List.mem_map.mp hy
      obtain ⟨z, hzmem, hzfit⟩ := exists_fit_of_mem ht htmem
      simpa only [Slot.minimum, hfit.2.1, hzfit.2.1] using horder z hzmem

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

structure Box where
  slots : List Slot
  next : ℕ
  remaining : ℕ

def Box.Matches (b : Box) (xs ys : Coordinates) : Prop :=
  List.Forall₂ Slot.Fits b.slots xs ∧ TailFits b.next ys ∧ ys.length = b.remaining

def Box.Closed (b : Box) : Prop :=
  ∀ xs ys, b.Matches xs ys → PrimeCoordinates (xs ++ ys) →
    (number (xs ++ ys)).Weird →
    (∀ d ∈ (number (xs ++ ys)).properDivisors, d.Deficient) → False

def Box.minimum (b : Box) : Coordinates := b.slots.map Slot.minimum

def Box.upper (b : Box) : ℚ := (b.slots.map Slot.upper).prod * tailUpper b.next b.remaining

def Slot.upperNum (s : Slot) : ℕ :=
  if s.fixed then powerSum s.prime s.exponent else s.prime

def Slot.upperDen (s : Slot) : ℕ :=
  if s.fixed then s.prime ^ s.exponent else s.prime - 1

def tailNum : ℕ → ℕ → ℕ
  | _, 0 => 1
  | p, r + 1 => p * tailNum (p + 2) r

def tailDen : ℕ → ℕ → ℕ
  | _, 0 => 1
  | p, r + 1 => (p - 1) * tailDen (p + 2) r

def Box.upperNum (b : Box) : ℕ := (b.slots.map Slot.upperNum).prod * tailNum b.next b.remaining

def Box.upperDen (b : Box) : ℕ := (b.slots.map Slot.upperDen).prod * tailDen b.next b.remaining

theorem Slot.upper_eq (s : Slot) (hp : 1 < s.prime) :
    s.upper = (s.upperNum : ℚ) / (s.upperDen : ℚ) := by
  cases hs : s.fixed
  · have h : 1 ≤ s.prime := by omega
    simp [Slot.upper, Slot.upperNum, Slot.upperDen, hs, limitingIndex, Nat.cast_sub h]
  · simp [Slot.upper, Slot.upperNum, Slot.upperDen, hs, index]

theorem slot_upper_eq {ss : List Slot} (h : ∀ s ∈ ss, 1 < s.prime) :
    (ss.map Slot.upper).prod = ((ss.map Slot.upperNum).prod : ℚ) /
      ((ss.map Slot.upperDen).prod : ℚ) := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    simp only [List.map_cons, List.prod_cons, Nat.cast_mul]
    rw [s.upper_eq (h s (by simp)), ih (fun t ht => h t (by simp [ht])), div_mul_div_comm]

theorem tailUpper_eq {p : ℕ} (hp : 1 < p) (r : ℕ) :
    tailUpper p r = (tailNum p r : ℚ) / (tailDen p r : ℚ) := by
  induction r generalizing p with
  | zero => simp [tailUpper, tailNum, tailDen]
  | succ r ih =>
    simp only [tailUpper, tailNum, tailDen, Nat.cast_mul, limitingIndex]
    rw [ih (by omega), div_mul_div_comm, Nat.cast_sub (show 1 ≤ p by omega)]
    simp

theorem Slot.upperDen_pos (s : Slot) (hp : 1 < s.prime) : 0 < s.upperDen := by
  unfold Slot.upperDen
  split
  · exact pow_pos (by omega) _
  · omega

theorem slot_den_pos {ss : List Slot} (h : ∀ s ∈ ss, 1 < s.prime) :
    0 < (ss.map Slot.upperDen).prod := by
  induction ss with
  | nil => decide
  | cons s ss ih =>
    exact Nat.mul_pos (s.upperDen_pos (h s (by simp))) (ih (fun t ht => h t (by simp [ht])))

theorem tail_den_pos {p : ℕ} (hp : 1 < p) (r : ℕ) : 0 < tailDen p r := by
  induction r generalizing p with
  | zero => simp [tailDen]
  | succ r ih => exact Nat.mul_pos (by omega) (ih (by omega))

theorem close_of_upper_le_two {b : Box} (hnext : 1 < b.next) (hbound : b.upper ≤ 2) :
    b.Closed := by
  intro xs ys ⟨hxs, hys, hylen⟩ hvalid hw _
  have hprod :
      ((xs ++ ys).map fun x => index x.1 x.2).prod ≤ b.upper := by
    rw [List.map_append, List.prod_append, Box.upper, ← hylen]
    have h := slot_prod_upper hxs
    exact mul_le_mul h (tail_prod_upper hnext hys) (coordinate_prod_nonneg _)
      ((coordinate_prod_nonneg _).trans h)
  rw [coordinate_index_eq, divisorSum_eq hvalid, ← Nat.abundancyIndex] at hprod
  exact (Nat.abundant_iff_two_lt_abundancyIndex.mp hw.1).not_ge (hprod.trans hbound)

theorem close_of_upperNum_le {b : Box} (hnext : 1 < b.next)
    (hbound : b.upperNum ≤ 2 * b.upperDen) : b.Closed := by
  intro xs ys hmatch hcoord hw hprim
  have hslot (s : Slot) (hs : s ∈ b.slots) : 1 < s.prime := by
    obtain ⟨x, _, hfit⟩ := exists_fit_of_mem hmatch.1 hs
    rw [hfit.2.1]
    exact hfit.1.one_lt
  have hden : 0 < b.upperDen := Nat.mul_pos (slot_den_pos hslot) (tail_den_pos hnext _)
  have h : b.upper ≤ 2 := by
    rw [Box.upper, slot_upper_eq hslot, tailUpper_eq hnext, div_mul_div_comm, ← Nat.cast_mul, ← Nat.cast_mul]
    change (b.upperNum : ℚ) / (b.upperDen : ℚ) ≤ 2
    rw [div_le_iff₀ (by exact_mod_cast hden)]
    exact_mod_cast hbound
  exact close_of_upper_le_two hnext h xs ys hmatch hcoord hw hprim

theorem primeCoordinates_left {xs ys : Coordinates} (h : PrimeCoordinates (xs ++ ys)) :
    PrimeCoordinates xs :=
  ⟨fun x hx => h.1 x (List.mem_append_left _ hx), (List.pairwise_append.mp h.2).1⟩

theorem close_at_nondeficient_minimum {b : Box}
    (hnondef : 2 * number b.minimum ≤ divisorSum b.minimum)
    (hpoint : ¬ (number b.minimum).Abundant ∨ (number b.minimum).Pseudoperfect ∨
      ∃ d ∈ (number b.minimum).properDivisors, ¬ d.Deficient) :
    b.Closed := by
  intro xs ys ⟨hfit, _, _⟩ hvalid hw hprimitive
  have hdvd : number b.minimum ∣ number (xs ++ ys) := by
    rw [number_append]
    exact dvd_mul_of_dvd_left (minimum_dvd hfit) _
  have hmin : PrimeCoordinates b.minimum := minimum_valid hfit (primeCoordinates_left hvalid)
  have hnd : ¬ (number b.minimum).Deficient :=
    fun h => (deficient_iff_divisorSum_lt hmin).mp h |>.not_ge hnondef
  obtain hlt | heq := lt_or_eq_of_le (Nat.le_of_dvd hw.1.pos hdvd)
  · exact hnd (hprimitive _ (Nat.mem_properDivisors.mpr ⟨hdvd, hlt⟩))
  · rw [heq] at hpoint
    rcases hpoint with h | h | ⟨d, hd, h⟩
    · exact h hw.1
    · exact hw.2 h
    · exact h (hprimitive d hd)

def tightlySorted : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: as => decide (a < b) && tightlySorted (b :: as)

theorem tightlySorted_pairwise {ds : List ℕ} (h : tightlySorted ds = true) :
    ds.Pairwise (· < ·) := by
  induction ds with
  | nil => exact .nil
  | cons a ds ih =>
    cases ds with
    | nil => exact .cons (by simp) .nil
    | cons b ds =>
      simp only [tightlySorted, Bool.and_eq_true, decide_eq_true_eq] at h
      have hpw := ih h.2
      refine .cons ?_ hpw
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact h.1
      · exact h.1.trans ((List.pairwise_cons.mp hpw).1 c hc)

theorem tightlySorted_nodup {ds : List ℕ} (h : tightlySorted ds = true) : ds.Nodup :=
  (tightlySorted_pairwise h).imp Nat.ne_of_lt

theorem pseudoperfect_of_excess_list {n : ℕ} {ds : List ℕ}
    (hn : 0 < n) (hnodup : ds.Nodup) (hdivs : ∀ d ∈ ds, d ∣ n ∧ d < n)
    (hsum : ∑ d ∈ n.divisors, d = 2 * n + ds.sum) : n.Pseudoperfect := by
  have hds : ∑ d ∈ ds.toFinset, d = ds.sum := by
    clear hsum hdivs
    induction ds with
    | nil => simp
    | cons d ds ih =>
      obtain ⟨hd, hnd⟩ := List.nodup_cons.mp hnodup
      have hd' : d ∉ ds.toFinset := by simpa using hd
      rw [List.toFinset_cons, sum_insert hd', List.sum_cons, ih hnd]
  have hsub : ds.toFinset ⊆ n.properDivisors := by
    intro d hd
    exact Nat.mem_properDivisors.mpr (hdivs d (List.mem_toFinset.mp hd))
  refine ⟨hn, n.properDivisors \ ds.toFinset, sdiff_subset, ?_⟩
  have hdiff := sum_sdiff (f := fun d : ℕ => d) hsub
  rw [Nat.sum_divisors_eq_sum_properDivisors_add_self] at hsum
  omega

theorem close_minimum_eq_two {b : Box}
    (h : divisorSum b.minimum = 2 * number b.minimum) : b.Closed := by
  intro xs ys hmatch hvalid hw hproper
  have hv : PrimeCoordinates b.minimum := minimum_valid hmatch.1 (primeCoordinates_left hvalid)
  have hp : ¬ (number b.minimum).Abundant := by
    rw [Nat.abundant_iff_sum_divisors, ← divisorSum_eq hv, h]
    exact lt_irrefl _
  exact close_at_nondeficient_minimum h.ge (Or.inl hp) xs ys hmatch hvalid hw hproper

theorem close_minimum_witness {b : Box} {ds : List ℕ}
    (hnodup : ds.Nodup) (hdivs : ∀ d ∈ ds, d ∣ number b.minimum ∧ d < number b.minimum)
    (hsum : divisorSum b.minimum = 2 * number b.minimum + ds.sum) : b.Closed := by
  intro xs ys hmatch hvalid hw hproper
  have hv : PrimeCoordinates b.minimum := minimum_valid hmatch.1 (primeCoordinates_left hvalid)
  have hnondef : 2 * number b.minimum ≤ divisorSum b.minimum := by omega
  have h : (number b.minimum).Pseudoperfect := pseudoperfect_of_excess_list
    (number_pos hv.1) hnodup hdivs (divisorSum_eq hv ▸ hsum)
  exact close_at_nondeficient_minimum hnondef (Or.inr (Or.inl h)) xs ys hmatch hvalid hw hproper

theorem close_minimum_has_nondeficient_divisor {b : Box} {d : ℕ}
    (hnondef : 2 * number b.minimum ≤ divisorSum b.minimum)
    (hdvd : d ∣ number b.minimum) (hdlt : d < number b.minimum) (hd : ¬ d.Deficient) :
    b.Closed :=
  close_at_nondeficient_minimum hnondef (Or.inr (Or.inr
    ⟨d, Nat.mem_properDivisors.mpr ⟨hdvd, hdlt⟩, hd⟩))

theorem forall₂_slot_split {ss : List Slot} {xs : Coordinates} {i : ℕ} {s : Slot}
    (h : List.Forall₂ Slot.Fits ss xs) (hi : ss[i]? = some s) (hf : s.fixed = false) :
    List.Forall₂ Slot.Fits (ss.set i {s with fixed := true}) xs ∨
    List.Forall₂ Slot.Fits (ss.set i {s with exponent := s.exponent + 1}) xs := by
  induction h generalizing i with
  | nil => simp at hi
  | @cons t x ss xs hfit _ ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst t
      rcases slot_fits_split hfit hf with h | h
      · exact Or.inl (.cons h (by assumption))
      · exact Or.inr (.cons h (by assumption))
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      rcases ih hi with h | h
      · exact Or.inl (.cons hfit h)
      · exact Or.inr (.cons hfit h)

theorem close_split_slot {b : Box} {i : ℕ} {s : Slot}
    (hi : b.slots[i]? = some s) (hf : s.fixed = false)
    (h₁ : ({b with slots := b.slots.set i {s with fixed := true}} : Box).Closed)
    (h₂ : ({b with slots := b.slots.set i {s with exponent := s.exponent + 1}} : Box).Closed) :
    b.Closed := by
  intro xs ys ⟨hf₂, ht, hr⟩ hp hw hprim
  rcases forall₂_slot_split hf₂ hi hf with h | h
  · exact h₁ xs ys ⟨h, ht, hr⟩ hp hw hprim
  · exact h₂ xs ys ⟨h, ht, hr⟩ hp hw hprim

theorem close_split_next {ss : List Slot} {p r : ℕ} (hodd : Odd p)
    (hskip : (⟨ss, p + 2, r + 1⟩ : Box).Closed)
    (htake : p.Prime → (⟨ss ++ [⟨p, 1, false⟩], p + 2, r⟩ : Box).Closed) :
    (⟨ss, p, r + 1⟩ : Box).Closed := by
  intro xs ys ⟨hx, hy, hlen⟩ hcoord hw hprim
  cases ys with
  | nil => simp at hlen
  | cons y ys =>
    obtain ⟨q, e⟩ := y
    obtain ⟨hpq, hqlo, hq, hqodd, he, ht⟩ := hy
    change p ≤ q at hpq
    by_cases heq : q = p
    · subst q
      have hfit : Slot.Fits ⟨p, 1, false⟩ (p, e) :=
        ⟨hq, rfl, he, by simp⟩
      have eq : xs ++ (p, e) :: ys = (xs ++ [(p, e)]) ++ ys := by
        simp [List.append_assoc]
      rw [eq] at hcoord hw hprim
      exact htake hq (xs ++ [(p, e)]) ys
        ⟨List.rel_append hx (.cons hfit .nil), ht, by simpa using hlen⟩ hcoord hw hprim
    · have hlt : p + 2 ≤ q := by
        obtain ⟨a, ha⟩ := hodd
        obtain ⟨b, hb⟩ := hqodd
        omega
      exact hskip xs ((q, e) :: ys) ⟨hx, ⟨hlt, hqlo, hq, hqodd, he, ht⟩, hlen⟩ hcoord hw hprim

theorem number_gt_one_of_tail {p : ℕ} {ys : Coordinates} (h : TailFits p ys)
    (hne : ys ≠ []) : 1 < number ys := by
  induction ys generalizing p with
  | nil => contradiction
  | cons y ys ih =>
    obtain ⟨q, e⟩ := y
    obtain ⟨_, hq, hprime, _, he, ht⟩ := h
    have hpow : 1 < q ^ e := one_lt_pow₀ (by omega) he.ne'
    rw [number_cons]
    change 1 < q ^ e * number ys
    by_cases hnil : ys = []
    · simpa [hnil, number] using hpow
    · exact hpow.trans_le (Nat.le_mul_of_pos_right _ (ih ht hnil).pos)

theorem close_minimum_with_tail {b : Box} (hr : 0 < b.remaining)
    (hnondef : 2 * number b.minimum ≤ divisorSum b.minimum) : b.Closed := by
  intro xs ys ⟨hfit, htail, hylen⟩ hvalid hw hprimitive
  have hne : ys ≠ [] := by
    rintro rfl
    simp at hylen
    omega
  have hlarge := number_gt_one_of_tail htail hne
  have hxs : 0 < number xs := number_pos (primeCoordinates_left hvalid).1
  have hdvd := minimum_dvd hfit
  have hlt : number b.minimum < number (xs ++ ys) := by
    rw [number_append]
    exact (Nat.le_of_dvd hxs hdvd).trans_lt (by
      simpa using (Nat.mul_lt_mul_of_pos_left hlarge hxs))
  have hmem : number b.minimum ∈ (number (xs ++ ys)).properDivisors :=
    Nat.mem_properDivisors.mpr ⟨by
      rw [number_append]
      exact dvd_mul_of_dvd_left hdvd _, hlt⟩
  have hv : PrimeCoordinates b.minimum := minimum_valid hfit (primeCoordinates_left hvalid)
  exact (deficient_iff_divisorSum_lt hv).mp (hprimitive _ hmem) |>.not_ge hnondef

def decrement : Coordinates → ℕ → Coordinates
  | [], _ => []
  | (p, e) :: xs, 0 => (p, e - 1) :: xs
  | x :: xs, i + 1 => x :: decrement xs i

theorem decrement_primes (xs : Coordinates) (i : ℕ) :
    (decrement xs i).map Prod.fst = xs.map Prod.fst := by
  induction xs generalizing i with
  | nil => simp [decrement]
  | cons x xs ih =>
    rcases x with ⟨p, e⟩
    cases i with
    | zero => rfl
    | succ i => simp [decrement, ih i]

theorem decrement_coordinates {xs : Coordinates} (h : PrimeCoordinates xs) (i : ℕ) :
    PrimeCoordinates (decrement xs i) := by
  have hprime (ls : Coordinates) :
      (∀ x ∈ ls, Nat.Prime x.1) ↔ ∀ p ∈ ls.map Prod.fst, Nat.Prime p := by simp
  have hordered (ls : Coordinates) :
      ls.Pairwise (fun x y => x.1 < y.1) ↔ (ls.map Prod.fst).Pairwise (· < ·) :=
    List.pairwise_map.symm
  rw [PrimeCoordinates, hprime, hordered, decrement_primes]
  exact ⟨(hprime xs).mp h.1, (hordered xs).mp h.2⟩

theorem decrement_dvd (xs : Coordinates) (i : ℕ) :
    number (decrement xs i) ∣ number xs := by
  induction xs generalizing i with
  | nil => simp [decrement]
  | cons x xs ih =>
    rcases x with ⟨p, e⟩
    cases i with
    | zero =>
      simp only [decrement, number_cons]
      exact Nat.mul_dvd_mul (pow_dvd_pow p (Nat.sub_le e 1)) dvd_rfl
    | succ i =>
      exact Nat.mul_dvd_mul dvd_rfl (ih i)

theorem close_minimum_decrement {b : Box} {i : ℕ}
    (hnondef : 2 * number b.minimum ≤ divisorSum b.minimum)
    (hlt : number (decrement b.minimum i) < number b.minimum)
    (hdec : 2 * number (decrement b.minimum i) ≤ divisorSum (decrement b.minimum i)) :
    b.Closed := by
  intro xs ys hfit hvalid hw hprim
  have hv : PrimeCoordinates b.minimum := minimum_valid hfit.1 (primeCoordinates_left hvalid)
  have hd : ¬ (number (decrement b.minimum i)).Deficient :=
    fun h => (deficient_iff_divisorSum_lt (decrement_coordinates hv i)).mp h |>.not_ge hdec
  exact close_minimum_has_nondeficient_divisor hnondef (decrement_dvd b.minimum i)
    hlt hd xs ys hfit hvalid hw hprim

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def witnessOk (n s : ℕ) (ds : List ℕ) : Bool :=
  ds.all (fun d => decide (d ∣ n ∧ d < n)) && tightlySorted ds && decide (s = 2 * n + ds.sum)

theorem witnessOk_closes {b : Box} {ds : List ℕ}
    (h : witnessOk (number b.minimum) (divisorSum b.minimum) ds = true) :
    b.Closed := by
  simp only [witnessOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact close_minimum_witness (tightlySorted_nodup h.1.2) (by simpa using h.1.1) h.2

def decrementOk (fs : Coordinates) (i : ℕ) : Bool :=
  let ds := decrement fs i
  decide (number ds < number fs ∧ 2 * number ds ≤ divisorSum ds)

def minimumOk (witness : ℕ → List ℕ) (b : Box) : Bool :=
  let n := number b.minimum
  let s := divisorSum b.minimum
  decide (0 < b.remaining) || decide (s = 2 * n) ||
    (List.range b.slots.length).any (decrementOk b.minimum) || witnessOk n s (witness n)

theorem minimumOk_closes {witness : ℕ → List ℕ} {b : Box}
    (hnondef : 2 * number b.minimum ≤ divisorSum b.minimum)
    (h : minimumOk witness b = true) : b.Closed := by
  simp only [minimumOk, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at h
  rcases h with ((h | h) | h) | h
  · exact close_minimum_with_tail h hnondef
  · exact close_minimum_eq_two h
  · obtain ⟨i, _, hi⟩ := h
    simp only [decrementOk, decide_eq_true_eq] at hi
    exact close_minimum_decrement hnondef hi.1 hi.2
  · exact witnessOk_closes h

def chooseSlot (b : Box) : Option ℕ :=
  ((b.slots.zipIdx.filter (fun (s, _) => !s.fixed)).foldl
    (fun best (s, i) =>
      let key := s.prime ^ (s.exponent + 1)
      if (b.remaining == 0 || key < b.next) && key < best.1
      then (key, some i) else best)
    (b.slots.foldl (fun n s => max n (s.prime ^ (s.exponent + 1) + 1)) 1, none)).2

def replay (witness : ℕ → List ℕ) : ℕ → Box → Bool
  | 0, _ => false
  | fuel + 1, b =>
    if 2 * number b.minimum ≤ divisorSum b.minimum then minimumOk witness b
    else if b.upperNum ≤ 2 * b.upperDen then true
    else match (chooseSlot b).bind (fun i => b.slots[i]?.map (fun s => (i, s))) with
    | some (i, s) =>
      if s.fixed then false else
      replay witness fuel {b with slots := b.slots.set i {s with fixed := true}} &&
      replay witness fuel {b with slots := b.slots.set i {s with exponent := s.exponent + 1}}
    | none =>
      match b.remaining with
      | 0 => false
      | r + 1 =>
        replay witness fuel ⟨b.slots, b.next + 2, r + 1⟩ &&
        if b.next.minFac = b.next then
          replay witness fuel ⟨b.slots ++ [⟨b.next, 1, false⟩], b.next + 2, r⟩
        else true

theorem replay_closes {witness : ℕ → List ℕ} {fuel : ℕ} {b : Box}
    (hlo : 1 < b.next) (hodd : Odd b.next) (h : replay witness fuel b = true) :
    b.Closed := by
  induction fuel generalizing b with
  | zero => simp [replay] at h
  | succ fuel ih =>
    rw [replay] at h
    split at h
    · exact minimumOk_closes ‹_› h
    split at h
    · exact close_of_upperNum_le hlo ‹_›
    split at h
    next i s hs =>
      have hi : b.slots[i]? = some s := by
        have hb := Option.bind_eq_some_iff.mp hs
        obtain ⟨j, _, hj⟩ := hb
        cases hg : b.slots[j]? <;> simp_all
      split at h
      · contradiction
      · have hf : s.fixed = false := by simp_all
        obtain ⟨h₁, h₂⟩ := Bool.and_eq_true_iff.mp h
        exact close_split_slot hi hf (ih hlo hodd h₁) (ih hlo hodd h₂)
    next =>
      rcases b with ⟨ss, p, r⟩
      cases r with
      | zero => contradiction
      | succ r =>
        obtain ⟨hskip, htake⟩ := Bool.and_eq_true_iff.mp h
        have hodd' : Odd (p + 2) := by
          obtain ⟨k, hk⟩ := hodd
          exact ⟨k + 1, by dsimp at hk; omega⟩
        have hlo' : 1 < p + 2 := by dsimp at hlo; omega
        apply close_split_next hodd (ih hlo' hodd' hskip)
        intro hp
        exact ih hlo' hodd' (by simpa only [if_pos hp.minFac_eq] using htake)

def slotEqual (a b : Slot) : Bool :=
  decide ((a.prime, a.exponent, a.fixed) = (b.prime, b.exponent, b.fixed))

theorem slotEqual_iff_eq (a b : Slot) : slotEqual a b = true ↔ a = b := by
  cases a; cases b; simp [slotEqual, Slot.mk.injEq]

def slotsEqual : List Slot → List Slot → Bool
  | [], [] => true
  | a :: as, b :: bs => slotEqual a b && slotsEqual as bs
  | _, _ => false

theorem slotsEqual_iff_eq (as bs : List Slot) : slotsEqual as bs = true ↔ as = bs := by
  induction as generalizing bs <;> cases bs <;>
    simp [slotsEqual, slotEqual_iff_eq, *]

def boxEqual (a b : Box) : Bool :=
  slotsEqual a.slots b.slots && decide (a.next = b.next) && decide (a.remaining = b.remaining)

theorem boxEqual_iff_eq (a b : Box) : boxEqual a b = true ↔ a = b := by
  cases a; cases b; simp [boxEqual, slotsEqual_iff_eq, Box.mk.injEq, and_assoc]

def replayWithCuts (witness : ℕ → List ℕ) (cut : Box → Bool) : ℕ → Box → Bool
  | 0, _ => false
  | fuel + 1, b =>
    if cut b then true
    else if 2 * number b.minimum ≤ divisorSum b.minimum then minimumOk witness b
    else if b.upperNum ≤ 2 * b.upperDen then true
    else match (chooseSlot b).bind (fun i => b.slots[i]?.map (fun s => (i, s))) with
    | some (i, s) =>
      if s.fixed then false else
      replayWithCuts witness cut fuel {b with slots := b.slots.set i {s with fixed := true}} &&
      replayWithCuts witness cut fuel {b with slots := b.slots.set i {s with exponent := s.exponent + 1}}
    | none =>
      match b.remaining with
      | 0 => false
      | r + 1 =>
        replayWithCuts witness cut fuel ⟨b.slots, b.next + 2, r + 1⟩ &&
        if b.next.minFac = b.next then
          replayWithCuts witness cut fuel ⟨b.slots ++ [⟨b.next, 1, false⟩], b.next + 2, r⟩
        else true

theorem replayWithCuts_closes {witness : ℕ → List ℕ} {cut : Box → Bool} {fuel : ℕ} {b : Box}
    (hcut : ∀ box, cut box = true → box.Closed)
    (hlo : 1 < b.next) (hodd : Odd b.next) (h : replayWithCuts witness cut fuel b = true) :
    b.Closed := by
  induction fuel generalizing b with
  | zero => simp [replayWithCuts] at h
  | succ fuel ih =>
    rw [replayWithCuts] at h
    split at h
    · exact hcut b ‹_›
    split at h
    · exact minimumOk_closes ‹_› h
    split at h
    · exact close_of_upperNum_le hlo ‹_›
    split at h
    next i s hs =>
      have hi : b.slots[i]? = some s := by
        obtain ⟨j, _, hj⟩ := Option.bind_eq_some_iff.mp hs
        cases hg : b.slots[j]? <;> simp_all
      split at h
      · contradiction
      · have hf : s.fixed = false := by simp_all
        obtain ⟨h₁, h₂⟩ := Bool.and_eq_true_iff.mp h
        exact close_split_slot hi hf (ih hlo hodd h₁) (ih hlo hodd h₂)
    next =>
      rcases b with ⟨ss, p, r⟩
      cases r with
      | zero => contradiction
      | succ r =>
        obtain ⟨hskip, htake⟩ := Bool.and_eq_true_iff.mp h
        have hodd' : Odd (p + 2) := by
          obtain ⟨k, hk⟩ := hodd
          exact ⟨k + 1, by dsimp at hk; omega⟩
        have hlo' : 1 < p + 2 := by dsimp at hlo; omega
        apply close_split_next hodd (ih hlo' hodd' hskip)
        intro hp
        exact ih hlo' hodd' (by simpa only [if_pos hp.minFac_eq] using htake)

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open scoped BigOperators

/-- The prime factorization of `n` as an increasing list of prime and exponent pairs. -/
def primeCoordinates (n : ℕ) : List (ℕ × ℕ) :=
  n.primeFactors.sort.map (fun p => (p, n.factorization p))

theorem mem_primeCoordinates {n p a : ℕ} :
    (p, a) ∈ primeCoordinates n ↔ p ∈ n.primeFactors ∧ a = n.factorization p := by
  simp only [primeCoordinates, List.mem_map, Finset.mem_sort, Prod.mk.injEq]
  constructor
  · rintro ⟨q, hq, rfl, rfl⟩
    exact ⟨hq, rfl⟩
  · rintro ⟨hp, rfl⟩
    exact ⟨p, hp, rfl, rfl⟩

theorem primeCoordinates_pairwise (n : ℕ) :
    (primeCoordinates n).Pairwise (fun x y => x.1 < y.1) := by
  simpa only [primeCoordinates, List.pairwise_map] using n.primeFactors.sortedLT_sort.pairwise

theorem primeCoordinates_length (n : ℕ) :
    (primeCoordinates n).length = n.primeFactors.card := by
  simp [primeCoordinates, Finset.length_sort]

theorem primeCoordinates_prime_pos {n : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ primeCoordinates n) : x.1.Prime ∧ 0 < x.2 := by
  obtain ⟨p, a⟩ := x
  obtain ⟨hp, rfl⟩ := mem_primeCoordinates.mp hx
  exact ⟨Nat.prime_of_mem_primeFactors hp, by
    rw [Nat.pos_iff_ne_zero, ← Finsupp.mem_support_iff, Nat.support_factorization]
    exact hp⟩

theorem primeCoordinates_odd {n : ℕ} (hn : Odd n) {x : ℕ × ℕ}
    (hx : x ∈ primeCoordinates n) : Odd x.1 := by
  obtain ⟨p, a⟩ := x
  exact hn.of_dvd_nat (Nat.dvd_of_mem_primeFactors (mem_primeCoordinates.mp hx).1)

theorem primeCoordinates_prod_map (n : ℕ) (f : ℕ × ℕ → ℕ) :
    ((primeCoordinates n).map f).prod =
      ∏ p ∈ n.primeFactors, f (p, n.factorization p) := by
  rw [primeCoordinates, List.map_map, ← List.prod_toFinset _ (Finset.sort_nodup _ _),
    Finset.sort_toFinset]
  rfl

theorem primeCoordinates_prod {n : ℕ} (hn : n ≠ 0) :
    ((primeCoordinates n).map (fun x => x.1 ^ x.2)).prod = n := by
  rw [primeCoordinates_prod_map]
  exact (Nat.prod_primeFactors_pow_factorization hn).symm

theorem primeCoordinates_sigma {n : ℕ} (hn : n ≠ 0) :
    ((primeCoordinates n).map (fun x => ∑ i ∈ Finset.range (x.2 + 1), x.1 ^ i)).prod =
      ArithmeticFunction.sigma 1 n := by
  rw [primeCoordinates_prod_map,
    ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn]
  simp

/-- A nonzero natural number has an exact increasing coordinate list for its
prime powers and divisor sum. When the number is odd, so is every row prime. -/
theorem exists_primeCoordinates {n : ℕ} (hn : n ≠ 0) :
    ∃ xs : List (ℕ × ℕ),
      xs.Pairwise (fun x y => x.1 < y.1) ∧
      (∀ x ∈ xs, x.1.Prime ∧ 0 < x.2 ∧ (Odd n → Odd x.1)) ∧
      xs.length = n.primeFactors.card ∧
      (xs.map (fun x => x.1 ^ x.2)).prod = n ∧
      (xs.map (fun x => ∑ i ∈ Finset.range (x.2 + 1), x.1 ^ i)).prod =
        ArithmeticFunction.sigma 1 n := by
  refine ⟨primeCoordinates n, primeCoordinates_pairwise n, ?_,
    primeCoordinates_length n, primeCoordinates_prod hn, primeCoordinates_sigma hn⟩
  intro x hx
  exact ⟨(primeCoordinates_prime_pos hx).1, (primeCoordinates_prime_pos hx).2,
    fun ho => primeCoordinates_odd ho hx⟩

/-- The first two coordinates in the branch with exact valuation one at three
and a factor of five. All remaining coordinates start at seven. -/
theorem primeCoordinates_three_one_five {n : ℕ} (hodd : Odd n)
    (hthree : n.factorization 3 = 1) (hfive : 5 ∣ n) :
    ∃ xs : List (ℕ × ℕ), primeCoordinates n = (3, 1) :: (5, n.factorization 5) :: xs ∧
      0 < n.factorization 5 ∧ ∀ x ∈ xs, 7 ≤ x.1 := by
  have hn : n ≠ 0 := by
    rcases hodd with ⟨k, hk⟩
    omega
  have h3 : 3 ∈ n.primeFactors := by
    rw [← Nat.support_factorization, Finsupp.mem_support_iff, hthree]
    decide
  have h5 : 5 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨by decide, hfive, hn⟩
  have h5' : 5 ∈ n.primeFactors.erase 3 := Finset.mem_erase.mpr ⟨by decide, h5⟩
  let tail := (n.primeFactors.erase 3).erase 5
  have htail (p : ℕ) (hp : p ∈ tail) : 7 ≤ p := by
    have ⟨hp5, hp'⟩ := Finset.mem_erase.mp hp
    have ⟨hp3, hp''⟩ := Finset.mem_erase.mp hp'
    have hp1 := (Nat.prime_of_mem_primeFactors hp'').one_lt
    obtain ⟨k, hk⟩ := hodd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp'')
    omega
  have h3bound : ∀ p ∈ insert 5 tail, 3 ≤ p := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · decide
    · exact (by decide : 3 ≤ 7).trans (htail p hp)
  have h5bound : ∀ p ∈ tail, 5 ≤ p := fun p hp => (by decide : 5 ≤ 7).trans (htail p hp)
  have hn3 : 3 ∉ insert 5 tail := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · contradiction
    · have := htail 3 h
      omega
  have hn5 : 5 ∉ tail := by
    intro h
    exact (Finset.mem_erase.mp h).1 rfl
  have hfac : n.primeFactors = insert 3 (insert 5 tail) := by
    rw [show insert 5 tail = n.primeFactors.erase 3 from Finset.insert_erase h5',
      Finset.insert_erase h3]
  refine ⟨tail.sort.map (fun p => (p, n.factorization p)), ?_,
    Nat.Prime.factorization_pos_of_dvd (by decide) hn hfive, ?_⟩
  · rw [primeCoordinates, hfac, Finset.sort_insert (· ≤ ·) h3bound hn3,
      Finset.sort_insert (· ≤ ·) h5bound hn5]
    simp [hthree]
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact htail p ((Finset.mem_sort (· ≤ ·)).mp hp)

/-- The ordered prime coordinates of an odd multiple of three begin with
the exact valuation at three. -/
theorem primeCoordinates_three {n : ℕ} (hodd : Odd n) (hthree : 3 ∣ n) :
    ∃ xs : List (ℕ × ℕ), primeCoordinates n = (3, n.factorization 3) :: xs ∧
      ∀ x ∈ xs, 5 ≤ x.1 := by
  have hp : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr
    ⟨by decide, hthree, hodd.pos.ne'⟩
  let tail := n.primeFactors.erase 3
  have htail (p : ℕ) (hp' : p ∈ tail) : 5 ≤ p := by
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hp'
    have hmin := (Nat.prime_of_mem_primeFactors hmem).one_lt
    obtain ⟨k, hk⟩ := hodd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hmem)
    omega
  have hlo : ∀ p ∈ tail, 3 ≤ p := fun p hp' => (show 3 ≤ 5 by decide).trans (htail p hp')
  have hn3 : 3 ∉ tail := Finset.notMem_erase _ _
  refine ⟨tail.sort.map (fun p => (p, n.factorization p)), ?_, ?_⟩
  · rw [primeCoordinates, ← Finset.insert_erase hp, Finset.sort_insert (· ≤ ·) hlo hn3]
    rfl
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact htail p ((Finset.mem_sort (· ≤ ·)).mp hp)

end OddWeirdSubproblems

namespace OddWeirdSubproblems

/-- The product of the least possible distinct odd primes after the slots. -/
def tailMinimum : ℕ → ℕ → ℕ
  | _, 0 => 1
  | p, r + 1 => p * tailMinimum (p + 2) r

theorem tailMinimum_mono {p q : ℕ} (hpq : p ≤ q) (r : ℕ) :
    tailMinimum p r ≤ tailMinimum q r := by
  induction r generalizing p q with
  | zero => simp [tailMinimum]
  | succ r ih => exact Nat.mul_le_mul hpq (ih (by omega))

theorem tailMinimum_le_number {ys : Coordinates} {p : ℕ} (h : TailFits p ys) :
    tailMinimum p ys.length ≤ number ys := by
  induction ys generalizing p with
  | nil => simp [tailMinimum, number]
  | cons y ys ih =>
    obtain ⟨q, e⟩ := y
    obtain ⟨hpq, _, hprime, _, he, ht⟩ := h
    rw [number_cons]
    simp only [List.length_cons, tailMinimum]
    refine Nat.mul_le_mul (hpq.trans ?_) ?_
    · simpa using (Nat.pow_le_pow_right hprime.pos (show 1 ≤ e by omega))
    · exact (tailMinimum_mono (show p + 2 ≤ q + 2 by omega) _).trans (ih ht)

def Box.ClosedBelow (b : Box) (B : ℕ) : Prop :=
  ∀ xs ys, b.Matches xs ys → PrimeCoordinates (xs ++ ys) →
    number (xs ++ ys) < B → (number (xs ++ ys)).Weird →
    (∀ d ∈ (number (xs ++ ys)).properDivisors, d.Deficient) → False

theorem closeBelow_of_minimum_ge {b : Box} {B : ℕ}
    (hB : B ≤ number b.minimum * tailMinimum b.next b.remaining) :
    b.ClosedBelow B := by
  intro xs ys ⟨hf, ht, hy⟩ hcoord hlt hw _
  have hxpos : 0 < number xs := number_pos (primeCoordinates_left hcoord).1
  have hx : number b.minimum ≤ number xs := Nat.le_of_dvd hxpos (minimum_dvd hf)
  have hy' := tailMinimum_le_number ht
  rw [hy] at hy'
  rw [number_append] at hlt
  exact hlt.not_ge (hB.trans (Nat.mul_le_mul hx hy'))

theorem closedBelow_of_closed {b : Box} (h : b.Closed) (B : ℕ) : b.ClosedBelow B :=
  fun xs ys hm hv _ hw hp => h xs ys hm hv hw hp

/-- A root with no fixed coordinates covers every odd integer of the given
support, and the lower product bound rules out sufficiently long supports. -/
theorem noPrimitiveWeirdBelow_of_roots {B k : ℕ}
    (hsize : B ≤ tailMinimum 3 (k + 1))
    (hroots : ∀ r ≤ k, (⟨[], 3, r⟩ : Box).ClosedBelow B)
    {n : ℕ} (hn : n < B) (ho : Odd n) (hw : n.Weird)
    (hproper : ∀ d ∈ n.properDivisors, d.Deficient) : False := by
  obtain ⟨ys, horder, hprime, _, hprod, _⟩ := exists_primeCoordinates ho.pos.ne'
  have hlocal (x : ℕ × ℕ) (hx : x ∈ ys) : x.1.Prime ∧ Odd x.1 ∧ 0 < x.2 :=
    ⟨(hprime x hx).1, (hprime x hx).2.2 ho, (hprime x hx).2.1⟩
  have ht : TailFits 3 ys := by
    apply tailFits_of_sorted (by decide : 2 < 3) _ hlocal horder
    intro x hx
    have hp := ((hlocal x hx).1.one_lt)
    obtain ⟨a, ha⟩ := (hlocal x hx).2.1
    omega
  have heq : number ys = n := hprod
  have hlength : ys.length ≤ k := by
    by_contra! hl
    have hmono : ∀ s t : ℕ, s ≤ t → ∀ p : ℕ, 0 < p →
        tailMinimum p s ≤ tailMinimum p t := by
      intro s t h
      induction h with
      | refl => intros; rfl
      | @step t h ih =>
        intro p hp
        exact (ih p hp).trans (by
          rw [tailMinimum]
          exact (tailMinimum_mono (show p ≤ p + 2 by omega) t).trans
            (Nat.le_mul_of_pos_left _ hp))
    have hh := hsize.trans ((hmono _ _ (by omega) 3 (by decide)).trans
      (tailMinimum_le_number ht))
    omega
  exact hroots ys.length hlength [] ys ⟨.nil, ht, rfl⟩
    ⟨fun x hx => (hprime x hx).1, horder⟩ (heq.symm ▸ hn)
    (heq.symm ▸ hw) (heq.symm ▸ hproper)

def replayBelow (B : ℕ) (witness : ℕ → List ℕ) : ℕ → Box → Bool
  | 0, _ => false
  | fuel + 1, b =>
    if B ≤ number b.minimum * tailMinimum b.next b.remaining then true
    else if 2 * number b.minimum ≤ divisorSum b.minimum then minimumOk witness b
    else if b.upperNum ≤ 2 * b.upperDen then true
    else match (chooseSlot b).bind (fun i => b.slots[i]?.map (fun s => (i, s))) with
    | some (i, s) =>
      if s.fixed then false else
      replayBelow B witness fuel {b with slots := b.slots.set i {s with fixed := true}} &&
      replayBelow B witness fuel {b with slots := b.slots.set i {s with exponent := s.exponent + 1}}
    | none =>
      match b.remaining with
      | 0 => false
      | r + 1 =>
        replayBelow B witness fuel ⟨b.slots, b.next + 2, r + 1⟩ &&
        if b.next.minFac = b.next then
          replayBelow B witness fuel ⟨b.slots ++ [⟨b.next, 1, false⟩], b.next + 2, r⟩
        else true

theorem closeBelow_split_slot {b : Box} {B i : ℕ} {s : Slot}
    (hi : b.slots[i]? = some s) (hf : s.fixed = false)
    (h₁ : ({b with slots := b.slots.set i {s with fixed := true}} : Box).ClosedBelow B)
    (h₂ : ({b with slots := b.slots.set i {s with exponent := s.exponent + 1}} : Box).ClosedBelow B) :
    b.ClosedBelow B := by
  intro xs ys ⟨hf₂, ht, hr⟩ hp hlt hw hprim
  rcases forall₂_slot_split hf₂ hi hf with h | h
  · exact h₁ xs ys ⟨h, ht, hr⟩ hp hlt hw hprim
  · exact h₂ xs ys ⟨h, ht, hr⟩ hp hlt hw hprim

theorem closeBelow_split_next {ss : List Slot} {B p r : ℕ} (hodd : Odd p)
    (hskip : (⟨ss, p + 2, r + 1⟩ : Box).ClosedBelow B)
    (htake : p.Prime → (⟨ss ++ [⟨p, 1, false⟩], p + 2, r⟩ : Box).ClosedBelow B) :
    (⟨ss, p, r + 1⟩ : Box).ClosedBelow B := by
  intro xs ys ⟨hx, hy, hlen⟩ hcoord hlt hw hprim
  cases ys with
  | nil => simp at hlen
  | cons y ys =>
    obtain ⟨q, e⟩ := y
    obtain ⟨hpq, hqlo, hq, hqodd, he, ht⟩ := hy
    change p ≤ q at hpq
    by_cases heq : q = p
    · subst q
      have hfit : Slot.Fits ⟨p, 1, false⟩ (p, e) := ⟨hq, rfl, he, by simp⟩
      have eq : xs ++ (p, e) :: ys = (xs ++ [(p, e)]) ++ ys := by simp [List.append_assoc]
      rw [eq] at hcoord hlt hw hprim
      exact htake hq (xs ++ [(p, e)]) ys
        ⟨List.rel_append hx (.cons hfit .nil), ht, by simpa using hlen⟩ hcoord hlt hw hprim
    · have hqmin : p + 2 ≤ q := by
        obtain ⟨a, ha⟩ := hodd
        obtain ⟨b, hb⟩ := hqodd
        omega
      exact hskip xs ((q, e) :: ys) ⟨hx, ⟨hqmin, hqlo, hq, hqodd, he, ht⟩, hlen⟩
        hcoord hlt hw hprim

theorem replayBelow_closes {B : ℕ} {witness : ℕ → List ℕ} {fuel : ℕ} {b : Box}
    (hlo : 1 < b.next) (hodd : Odd b.next) (h : replayBelow B witness fuel b = true) :
    b.ClosedBelow B := by
  induction fuel generalizing b with
  | zero => simp [replayBelow] at h
  | succ fuel ih =>
    rw [replayBelow] at h
    split at h
    · exact closeBelow_of_minimum_ge ‹_›
    split at h
    · exact closedBelow_of_closed (minimumOk_closes ‹_› h) B
    split at h
    · exact closedBelow_of_closed (close_of_upperNum_le hlo ‹_›) B
    split at h
    next i s hs =>
      have hi : b.slots[i]? = some s := by
        obtain ⟨j, _, hj⟩ := Option.bind_eq_some_iff.mp hs
        cases hg : b.slots[j]? <;> simp_all
      split at h
      · contradiction
      · have hf : s.fixed = false := by simp_all
        obtain ⟨h₁, h₂⟩ := Bool.and_eq_true_iff.mp h
        exact closeBelow_split_slot hi hf (ih hlo hodd h₁) (ih hlo hodd h₂)
    next =>
      rcases b with ⟨ss, p, r⟩
      cases r with
      | zero => contradiction
      | succ r =>
        obtain ⟨hskip, htake⟩ := Bool.and_eq_true_iff.mp h
        have hodd' : Odd (p + 2) := by
          obtain ⟨k, hk⟩ := hodd
          exact ⟨k + 1, by dsimp at hk; omega⟩
        have hlo' : 1 < p + 2 := by dsimp at hlo; omega
        apply closeBelow_split_next hodd (ih hlo' hodd' hskip)
        intro hp
        exact ih hlo' hodd' (by simpa only [if_pos hp.minFac_eq] using htake)

end OddWeirdSubproblems

namespace OddWeirdSubproblems

/-- A rank list specifies a lower bound for each initial prime coordinate.
When fewer coordinates occur, the unused lower bounds have no effect. -/
def RankFloor : List ℕ → Coordinates → Prop
  | [], _ => True
  | _ :: _, [] => True
  | p :: ps, x :: xs => p ≤ x.1 ∧ RankFloor ps xs

def gapOk (lo hi : ℕ) : Bool :=
  (List.range (hi - lo)).all (fun j => decide ((lo + j).minFac ≠ lo + j))

def floorSteps : List ℕ → Bool
  | p :: q :: ps => gapOk (p + 2) q && floorSteps (q :: ps)
  | _ => true

theorem no_prime_of_gapOk {lo hi q : ℕ} (h : gapOk lo hi = true)
    (hlo : lo ≤ q) (hhi : q < hi) (hp : q.Prime) : False := by
  simp only [gapOk, List.all_eq_true, decide_eq_true_eq] at h
  have hn := h (q - lo) (List.mem_range.mpr (by omega))
  rw [show lo + (q - lo) = q by omega] at hn
  exact hn hp.minFac_eq

theorem tailFits_weaken {p q : ℕ} {xs : Coordinates} (hp : p ≤ q) (h : TailFits q xs) :
    TailFits p xs := by
  cases xs with
  | nil => trivial
  | cons x xs =>
    obtain ⟨r, e⟩ := x
    obtain ⟨hlo, hpos, hprime, hodd, he, ht⟩ := h
    exact ⟨hp.trans hlo, hpos, hprime, hodd, he, ht⟩

theorem tailFits_gap {p q : ℕ} {xs : Coordinates} (h : gapOk p q = true) (ht : TailFits p xs) :
    TailFits q xs := by
  cases xs with
  | nil => trivial
  | cons x xs =>
    obtain ⟨r, e⟩ := x
    obtain ⟨hlo, hpos, hprime, hodd, he, hx⟩ := ht
    have hq : q ≤ r := Nat.le_of_not_gt fun hlt => no_prime_of_gapOk h hlo hlt hprime
    exact ⟨hq, hpos, hprime, hodd, he, hx⟩

theorem rankFloor_of_steps {p : ℕ} {ps : List ℕ} {xs : Coordinates}
    (hsteps : floorSteps (p :: ps) = true) (ht : TailFits p xs) : RankFloor (p :: ps) xs := by
  induction ps generalizing p xs with
  | nil =>
    cases xs with
    | nil => trivial
    | cons x xs =>
      obtain ⟨q, e⟩ := x
      exact ⟨ht.1, trivial⟩
  | cons r ps ih =>
    cases xs with
    | nil => trivial
    | cons x xs =>
      obtain ⟨q, e⟩ := x
      obtain ⟨hpq, _, _, _, _, ht⟩ := ht
      obtain ⟨hg, hnext⟩ := Bool.and_eq_true_iff.mp hsteps
      refine ⟨hpq, ih hnext ?_⟩
      exact tailFits_gap hg (tailFits_weaken (by omega : p + 2 ≤ q + 2) ht)

theorem number_ge_floor_product {ps : List ℕ} {xs : Coordinates}
    (hr : RankFloor ps xs) (hlen : ps.length ≤ xs.length)
    (hp : ∀ x ∈ xs, x.1.Prime ∧ 0 < x.2) : ps.prod ≤ number xs := by
  induction ps generalizing xs with
  | nil => exact number_pos (fun x hx => (hp x hx).1)
  | cons p ps ih =>
    cases xs with
    | nil => simp at hlen
    | cons x xs =>
      obtain ⟨q, e⟩ := x
      obtain ⟨hle, ht⟩ := hr
      obtain ⟨hq, he⟩ := hp (q, e) (by simp)
      have hpq : p ≤ q ^ e := hle.trans (by
        simpa using Nat.pow_le_pow_right hq.pos (show 1 ≤ e by omega))
      exact Nat.mul_le_mul hpq
        (ih ht (by simpa using hlen) (fun y hy => hp y (List.mem_cons_of_mem _ hy)))

theorem one_le_limitingIndex {p : ℕ} (hp : 1 < p) : 1 ≤ limitingIndex p := by
  have hp' : (1 : ℚ) < p := by exact_mod_cast hp
  unfold limitingIndex
  rw [le_div_iff₀ (sub_pos.mpr hp')]
  linarith

theorem floorIndex_ge_one {ps : List ℕ} (hp : ∀ p ∈ ps, 1 < p) :
    1 ≤ (ps.map limitingIndex).prod := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.prod_cons]
    exact one_le_mul_of_one_le_of_one_le (one_le_limitingIndex (hp p (by simp)))
      (ih (fun q hq => hp q (by simp [hq])))

theorem floorIndex_upper {ps : List ℕ} {xs : Coordinates}
    (hr : RankFloor ps xs) (hlen : xs.length ≤ ps.length)
    (hp : ∀ p ∈ ps, 1 < p) :
    (xs.map fun x => index x.1 x.2).prod ≤ (ps.map limitingIndex).prod := by
  induction ps generalizing xs with
  | nil =>
    have hn : xs = [] := by simpa using hlen
    simp [hn]
  | cons p ps ih =>
    cases xs with
    | nil => exact floorIndex_ge_one hp
    | cons x xs =>
      obtain ⟨q, e⟩ := x
      obtain ⟨hpq, ht⟩ := hr
      have hp' := hp p (by simp)
      have hq : 1 < q := hp'.trans_le hpq
      exact mul_le_mul ((index_le_limitingIndex hq).trans (limitingIndex_antitone hp' hpq))
        (ih ht (by simpa using hlen) (fun r hr => hp r (by simp [hr])))
        (coordinate_prod_nonneg _) (limitingIndex_nonneg hp')

private def roughFloors : List ℕ := [7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59]

/-- Fang's two starting primes are sufficient below 10^21. The bound uses
the smallest possible ordered support and the limiting prime-power indices. -/
theorem smallOddAbundant_has_three_or_five {n : ℕ} (hn : n < 10 ^ 21)
    (ho : Odd n) (ha : n.Abundant) : 3 ∣ n ∨ 5 ∣ n := by
  by_contra! h
  obtain ⟨xs, horder, hcoord, _, hprod, _⟩ := exists_primeCoordinates ho.pos.ne'
  have hnumber : number xs = n := hprod
  have ht : TailFits 7 xs := by
    apply tailFits_of_sorted (by decide : 2 < 7) _ _ horder
    · intro x hx
      have hprime := (hcoord x hx).1
      have ho' := (hcoord x hx).2.2 ho
      have hd : x.1 ∣ n := by
        have hpow : x.1 ^ x.2 ∣ number xs := by
          apply List.dvd_prod (List.mem_map.mpr ⟨x, hx, rfl⟩)
        have he := (hcoord x hx).2.1
        exact (dvd_pow_self _ he.ne').trans (hnumber ▸ hpow)
      have h3 : x.1 ≠ 3 := fun eq => h.1 (eq ▸ hd)
      have h5 : x.1 ≠ 5 := fun eq => h.2 (eq ▸ hd)
      have hp := hprime.one_lt
      obtain ⟨k, hk⟩ := ho'
      omega
    · intro x hx
      obtain ⟨hp, he, hodd⟩ := hcoord x hx
      exact ⟨hp, hodd ho, he⟩
  have hlen : xs.length ≤ roughFloors.length := by
    by_contra! hl
    have hr : RankFloor (roughFloors ++ [61]) xs :=
      rankFloor_of_steps (by decide +kernel) ht
    have hb := number_ge_floor_product hr (by simp; omega) (fun x hx =>
      ⟨(hcoord x hx).1, (hcoord x hx).2.1⟩)
    have hh : 10 ^ 21 ≤ (roughFloors ++ [61]).prod := by decide +kernel
    rw [hnumber] at hb
    omega
  have hr : RankFloor roughFloors xs := rankFloor_of_steps (by decide +kernel) ht
  have hbound := floorIndex_upper hr hlen (by
    intro p hp
    simp only [roughFloors, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)
  have hrat : (roughFloors.map limitingIndex).prod < 2 := by decide +kernel
  rw [coordinate_index_eq, divisorSum_eq ⟨fun x hx => (hcoord x hx).1, horder⟩,
    hnumber, ← Nat.abundancyIndex] at hbound
  exact (Nat.abundant_iff_two_lt_abundancyIndex.mp ha).not_ge (hbound.trans hrat.le)

theorem support_lt_of_floor_product {p B n : ℕ} {ps : List ℕ}
    (hn : n < B) (ho : Odd n) (hp : 2 < p)
    (hfloor : ∀ q ∈ n.primeFactors, p ≤ q)
    (hsteps : floorSteps (p :: ps) = true)
    (hprod : B ≤ (p :: ps).prod) :
    n.primeFactors.card < (p :: ps).length := by
  let xs := primeCoordinates n
  have hlocal (x : ℕ × ℕ) (hx : x ∈ xs) : x.1.Prime ∧ Odd x.1 ∧ 0 < x.2 := by
    have h := primeCoordinates_prime_pos hx
    exact ⟨h.1, primeCoordinates_odd ho hx, h.2⟩
  have ht : TailFits p xs := by
    apply tailFits_of_sorted hp _ hlocal (primeCoordinates_pairwise n)
    intro x hx
    obtain ⟨q, e⟩ := x
    exact hfloor q (mem_primeCoordinates.mp hx).1
  have hr := rankFloor_of_steps hsteps ht
  have hlen : xs.length = n.primeFactors.card := primeCoordinates_length n
  have heq : number xs = n := primeCoordinates_prod ho.pos.ne'
  by_contra! hc
  have h := number_ge_floor_product hr (by omega) (fun x hx =>
    ⟨(hlocal x hx).1, (hlocal x hx).2.2⟩)
  omega

private def floorTo61 : List ℕ := 5 :: roughFloors ++ [61]

theorem oddBelow10Pow21_primeFactors_card_le_sixteen {n : ℕ}
    (hn : n < 10 ^ 21) (ho : Odd n) : n.primeFactors.card ≤ 16 := by
  have hf (q : ℕ) (hq : q ∈ n.primeFactors) : 3 ≤ q := by
    have hprime := Nat.prime_of_mem_primeFactors hq
    obtain ⟨k, hk⟩ := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hq)
    have hmin := hprime.one_lt
    omega
  have h := support_lt_of_floor_product (ps := floorTo61) hn ho (by decide) hf
    (by decide +kernel) (by decide +kernel)
  have h17 : n.primeFactors.card < 17 := by simpa [floorTo61, roughFloors] using h
  omega

theorem coprimeThreeOddBelow10Pow21_primeFactors_card_le_fifteen {n : ℕ}
    (hn : n < 10 ^ 21) (ho : Odd n) (h3 : ¬ 3 ∣ n) : n.primeFactors.card ≤ 15 := by
  have hf (q : ℕ) (hq : q ∈ n.primeFactors) : 5 ≤ q := by
    have hprime := Nat.prime_of_mem_primeFactors hq
    have hd := Nat.dvd_of_mem_primeFactors hq
    obtain ⟨k, hk⟩ := ho.of_dvd_nat hd
    have hmin := hprime.one_lt
    have hneq : q ≠ 3 := fun heq => h3 (heq ▸ hd)
    omega
  have h := support_lt_of_floor_product (ps := roughFloors ++ [61]) hn ho (by decide) hf
    (by decide +kernel) (by decide +kernel)
  have h16 : n.primeFactors.card < 16 := by simpa [roughFloors] using h
  omega

theorem coprimeThree_oddAbundant_primeFactors_card_ge_seven {n : ℕ} (ho : Odd n)
    (ha : n.Abundant) (h3 : ¬ 3 ∣ n) : 7 ≤ n.primeFactors.card := by
  by_contra! hc
  let xs := primeCoordinates n
  have hlocal (x : ℕ × ℕ) (hx : x ∈ xs) : x.1.Prime ∧ Odd x.1 ∧ 0 < x.2 := by
    have h := primeCoordinates_prime_pos hx
    exact ⟨h.1, primeCoordinates_odd ho hx, h.2⟩
  have ht : TailFits 5 xs := by
    apply tailFits_of_sorted (by decide : 2 < 5) _ hlocal (primeCoordinates_pairwise n)
    intro x hx
    obtain ⟨p, e⟩ := x
    have hd := Nat.dvd_of_mem_primeFactors (mem_primeCoordinates.mp hx).1
    have hp : p ≠ 3 := fun heq => h3 (heq ▸ hd)
    have hlo := (hlocal (p, e) hx).1.one_lt
    obtain ⟨a, ha⟩ := (hlocal (p, e) hx).2.1
    omega
  have hf : RankFloor [5, 7, 11, 13, 17, 19] xs :=
    rankFloor_of_steps (by decide +kernel) ht
  have hlen : xs.length ≤ 6 := by
    have h := primeCoordinates_length n
    change xs.length = n.primeFactors.card at h
    omega
  have h := floorIndex_upper hf hlen (by
    intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have he : number xs = n := primeCoordinates_prod ho.pos.ne'
  rw [coordinate_index_eq, divisorSum_eq ⟨fun x hx => (hlocal x hx).1,
    primeCoordinates_pairwise n⟩, he, ← Nat.abundancyIndex] at h
  have hlt : ([5, 7, 11, 13, 17, 19].map limitingIndex).prod < 2 := by decide +kernel
  exact (Nat.abundant_iff_two_lt_abundancyIndex.mp ha).not_ge (h.trans hlt.le)

/-- Exact ranked bound using the five smallest permitted prime divisors. -/
theorem oddCoprimeThreeAtMostFive_abundancyIndex_le {n : ℕ} (ho : Odd n)
    (h3 : ¬ 3 ∣ n) (hc : n.primeFactors.card ≤ 5) :
    n.abundancyIndex ≤ (5 / 4) * (7 / 6) * (11 / 10) * (13 / 12) * (17 / 16) := by
  let xs := primeCoordinates n
  have hlocal (x : ℕ × ℕ) (hx : x ∈ xs) : x.1.Prime ∧ Odd x.1 ∧ 0 < x.2 := by
    have h := primeCoordinates_prime_pos hx
    exact ⟨h.1, primeCoordinates_odd ho hx, h.2⟩
  have ht : TailFits 5 xs := by
    apply tailFits_of_sorted (by decide : 2 < 5) _ hlocal (primeCoordinates_pairwise n)
    intro x hx
    obtain ⟨p, e⟩ := x
    have hd := Nat.dvd_of_mem_primeFactors (mem_primeCoordinates.mp hx).1
    have hp : p ≠ 3 := fun heq => h3 (heq ▸ hd)
    have hlo := (hlocal (p, e) hx).1.one_lt
    obtain ⟨a, ha⟩ := (hlocal (p, e) hx).2.1
    omega
  have hf : RankFloor [5, 7, 11, 13, 17] xs :=
    rankFloor_of_steps (by decide +kernel) ht
  have hlen : xs.length ≤ 5 := (primeCoordinates_length n).symm ▸ hc
  have h := floorIndex_upper hf hlen (by
    intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide)
  have he : number xs = n := primeCoordinates_prod ho.pos.ne'
  rw [coordinate_index_eq, divisorSum_eq ⟨fun x hx => (hlocal x hx).1,
    primeCoordinates_pairwise n⟩, he, ← Nat.abundancyIndex] at h
  exact h.trans (by decide +kernel)

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

/-- Scaling a representing subset preserves distinctness and proper divisibility. -/
theorem pseudoperfectOfDvd {d n : ℕ} (hn : 0 < n) (hd : d ∣ n)
    (hp : d.Pseudoperfect) : n.Pseudoperfect := by
  obtain ⟨k, rfl⟩ := hd
  obtain ⟨_, s, hsub, hsum⟩ := hp
  have hk := Nat.pos_of_mul_pos_left hn
  let scale : ℕ ↪ ℕ := ⟨(· * k), fun _ _ h => Nat.eq_of_mul_eq_mul_right hk h⟩
  refine ⟨hn, s.map scale, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_map.mp hx
    obtain ⟨had, halt⟩ := Nat.mem_properDivisors.mp (hsub ha)
    exact Nat.mem_properDivisors.mpr
      ⟨Nat.mul_dvd_mul_right had k, Nat.mul_lt_mul_of_pos_right halt hk⟩
  · rw [sum_map]
    change (∑ a ∈ s, a * k) = d * k
    rw [← sum_mul, hsum]

/-- Choose the least nondeficient divisor. A perfect divisor already gives a
pseudoperfect representation, so the selected divisor is weird and primitive.
The relation `d ∣ n` lets callers transfer their own restrictions. -/
theorem primitiveWeirdDivisor {n : ℕ} (hw : n.Weird) :
    ∃ d : ℕ, d ∣ n ∧ d.Weird ∧ ∀ k ∈ d.properDivisors, k.Deficient := by
  have hex : ∃ d : ℕ, d ∣ n ∧ ¬ d.Deficient :=
    ⟨n, dvd_rfl, fun h => (not_lt_of_gt hw.1) h⟩
  let d := Nat.find hex
  have hd : d ∣ n := (Nat.find_spec hex).1
  have hnd : ¬ d.Deficient := (Nat.find_spec hex).2
  have hpos : 0 < d := Nat.pos_of_dvd_of_pos hd hw.1.pos
  have hnp : ¬ d.Pseudoperfect := fun hp => hw.2 (pseudoperfectOfDvd hw.1.pos hd hp)
  refine ⟨d, hd, ⟨?_, hnp⟩, ?_⟩
  · by_contra hna
    exact hnp (((Nat.perfect_iff_not_abundant_and_not_deficient hpos.ne).2
      ⟨hna, hnd⟩).pseudoperfect)
  · intro k hk
    obtain ⟨hkd, hlt⟩ := Nat.mem_properDivisors.mp hk
    by_contra! hndef
    exact (not_le_of_gt hlt) (Nat.find_min' hex ⟨hkd.trans hd, hndef⟩)

/-- The target's set cardinality counts precisely the distinct prime factors. -/
theorem primeDivisorNcard (n : ℕ) :
    {p : ℕ | p ∈ n.divisors ∧ p.Prime}.ncard = n.primeFactors.card := by
  have hs : {p : ℕ | p ∈ n.divisors ∧ p.Prime} = (n.primeFactors : Set ℕ) := by
    ext p
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Nat.mem_primeFactors, Nat.mem_divisors]
    tauto
  rw [hs, Set.ncard_coe_finset]

/-- A primitive-abundant exclusion through five distinct primes suffices for
the first Erdős 470 variant. -/
theorem atLeastSixOfPrimitive
    (verify : ∀ m : ℕ, Odd m → m.Abundant → m.primeFactors.card ≤ 5 →
      (∀ d ∈ m.properDivisors, d.Deficient) → m.Pseudoperfect) :
    ∀ n : ℕ, Odd n → n.Weird → 6 ≤ {p : ℕ | p ∈ n.divisors ∧ p.Prime}.ncard := by
  intro n ho hw
  rw [primeDivisorNcard]
  by_contra! hc
  obtain ⟨d, hd, hdw, hproper⟩ := primitiveWeirdDivisor hw
  have hcard := Finset.card_le_card (Nat.primeFactors_mono hd hw.1.pos.ne')
  exact hdw.2 (verify d (ho.of_dvd_nat hd) hdw.1 (by omega) hproper)

/-- The strict cutoff also passes to the primitive divisor. -/
theorem noOddWeirdBelowOfPrimitive {B : ℕ}
    (verify : ∀ m < B, Odd m → m.Abundant →
      (∀ d ∈ m.properDivisors, d.Deficient) → m.Pseudoperfect) :
    ∀ n < B, Odd n → ¬ n.Weird := by
  intro n hn ho hw
  obtain ⟨d, hd, hdw, hproper⟩ := primitiveWeirdDivisor hw
  have hlt := (Nat.le_of_dvd hw.1.pos hd).trans_lt hn
  exact hdw.2 (verify d hlt (ho.of_dvd_nat hd) hdw.1 hproper)

end OddWeirdSubproblems

namespace OddWeirdSubproblems

/-- Start sorted coordinates at a known least prime divisor. -/
theorem primeCoordinates_start {n p : ℕ} (hm : p ∈ n.primeFactors)
    (hp : ∀ q ∈ n.primeFactors, p ≤ q) :
    ∃ xs, primeCoordinates n = (p, n.factorization p) :: xs := by
  let rest := n.primeFactors.erase p
  have hlo : ∀ q ∈ rest, p ≤ q := fun q hq => hp q (Finset.mem_erase.mp hq).2
  have hnot : p ∉ rest := Finset.notMem_erase _ _
  refine ⟨rest.sort.map (fun q => (q, n.factorization q)), ?_⟩
  rw [primeCoordinates, ← Finset.insert_erase hm, Finset.sort_insert (· ≤ ·) hlo hnot]
  rfl

theorem fangRoots_cover {n : ℕ} (hn : n < 10 ^ 21) (ho : Odd n) (ha : n.Abundant) :
    ∃ p a ys, (p = 3 ∨ p = 5) ∧
      primeCoordinates n = [(p, a)] ++ ys ∧
      Slot.Fits ⟨p, 1, false⟩ (p, a) ∧ TailFits (p + 2) ys ∧
      ys.length + 1 = n.primeFactors.card := by
  have h35 := smallOddAbundant_has_three_or_five hn ho ha
  let p := if 3 ∣ n then 3 else 5
  have hp : p = 3 ∨ p = 5 := by unfold p; split <;> simp
  have hprime : p.Prime := by
    rcases hp with h | h <;> rw [h] <;> decide
  have hd : p ∣ n := by
    unfold p
    split <;> rename_i h
    · exact h
    · exact h35.resolve_left h
  have hm : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hprime, hd, ho.pos.ne'⟩
  have hleast (q : ℕ) (hq : q ∈ n.primeFactors) : p ≤ q := by
    have hqprime := Nat.prime_of_mem_primeFactors hq
    have hqd := Nat.dvd_of_mem_primeFactors hq
    have hmin := hqprime.one_lt
    obtain ⟨i, hi⟩ := ho.of_dvd_nat hqd
    unfold p
    split <;> rename_i h
    · omega
    · have hne : q ≠ 3 := fun he => h (he ▸ hqd)
      omega
  obtain ⟨ys, heq⟩ := primeCoordinates_start hm hleast
  let a := n.factorization p
  have hlen : ys.length + 1 = n.primeFactors.card := by
    have h := primeCoordinates_length n
    rw [heq, List.length_cons] at h
    exact h
  have hpw := primeCoordinates_pairwise n
  rw [heq, List.pairwise_cons] at hpw
  have hx (x : ℕ × ℕ) (hx : x ∈ ys) : x ∈ primeCoordinates n := by
    rw [heq]
    exact List.mem_cons_of_mem _ hx
  have hpo : Odd p := ho.of_dvd_nat hd
  have htail : TailFits (p + 2) ys := by
    apply tailFits_of_sorted (by omega : 2 < p + 2) _ _ hpw.2
    · intro x h
      have hq := hpw.1 x h
      obtain ⟨i, hi⟩ := hpo
      obtain ⟨j, hj⟩ := primeCoordinates_odd ho (hx x h)
      change p < x.1 at hq
      omega
    · intro x h
      have h' := primeCoordinates_prime_pos (hx x h)
      exact ⟨h'.1, primeCoordinates_odd ho (hx x h), h'.2⟩
  exact ⟨p, a, ys, hp, heq, ⟨hprime, rfl,
    hprime.factorization_pos_of_dvd ho.pos.ne' hd, by simp⟩, htail, hlen⟩

/-- A bounded root at five discharges its matching support and exponent range. -/
theorem noPrimitiveWeird10Pow21_coprimeThree_of_exponentRoot {n r e : ℕ} {fixed : Bool}
    (root : (⟨[⟨5, e, fixed⟩], 7, r⟩ : Box).ClosedBelow (10 ^ 21))
    (hn : n < 10 ^ 21) (ho : Odd n) (h3 : ¬ 3 ∣ n)
    (hc : n.primeFactors.card = r + 1)
    (hproper : ∀ d ∈ n.properDivisors, d.Deficient)
    (hlo : e ≤ n.factorization 5) (hfix : fixed = true → e = n.factorization 5) :
    ¬ n.Weird := by
  intro hw
  obtain ⟨p, a, ys, hp, heq, hfit, ht, hlen⟩ := fangRoots_cover hn ho hw.1
  have hlen' : ys.length = r := by omega
  have hp5 : p = 5 := by
    rcases hp with rfl | h
    · have hm : (3, a) ∈ primeCoordinates n := by rw [heq]; simp
      exact (h3 (Nat.dvd_of_mem_primeFactors (mem_primeCoordinates.mp hm).1)).elim
    · exact h
  subst p
  have hnum : number ([(5, a)] ++ ys) = n := by
    rw [← heq]
    exact primeCoordinates_prod ho.pos.ne'
  have hcoords : PrimeCoordinates ([(5, a)] ++ ys) := by
    rw [← heq]
    exact ⟨fun x hx => (primeCoordinates_prime_pos hx).1, primeCoordinates_pairwise n⟩
  have heq5 := (mem_primeCoordinates.mp (show (5, a) ∈ primeCoordinates n by rw [heq]; simp)).2
  have hfit' : Slot.Fits ⟨5, e, fixed⟩ (5, a) := by
    rw [heq5]
    exact ⟨(by decide : (5 : ℕ).Prime), rfl, hlo, hfix⟩
  exact root [(5, a)] ys ⟨.cons hfit' .nil, ht, hlen'⟩ hcoords
    (hnum.symm ▸ hn) (hnum.symm ▸ hw) (hnum.symm ▸ hproper)

/-- A bounded root at five discharges the matching support coprime to three. -/
theorem noPrimitiveWeird10Pow21_coprimeThree_of_root {n r : ℕ}
    (root : (⟨[⟨5, 1, false⟩], 7, r⟩ : Box).ClosedBelow (10 ^ 21))
    (hn : n < 10 ^ 21) (ho : Odd n) (h3 : ¬ 3 ∣ n)
    (hc : n.primeFactors.card = r + 1)
    (hproper : ∀ d ∈ n.properDivisors, d.Deficient) : ¬ n.Weird := by
  intro hw
  have hFive := (smallOddAbundant_has_three_or_five hn ho hw.1).resolve_left h3
  have hlo := (by decide : (5 : ℕ).Prime).factorization_pos_of_dvd ho.pos.ne' hFive
  exact noPrimitiveWeird10Pow21_coprimeThree_of_exponentRoot root hn ho h3 hc hproper hlo
    (by simp) hw

/-- Fang's two starting primes and the support window after proving the first
variant suffice for the bounded exclusion. -/
theorem noOddWeird10Pow21_of_support_and_fangRoots
    (h6 : ∀ n : ℕ, Odd n → n.Weird → 6 ≤ n.primeFactors.card)
    (h3 : ∀ r, 5 ≤ r → r ≤ 15 → (⟨[⟨3, 1, false⟩], 5, r⟩ : Box).ClosedBelow (10 ^ 21))
    (h5 : ∀ r, 6 ≤ r → r ≤ 14 → (⟨[⟨5, 1, false⟩], 7, r⟩ : Box).ClosedBelow (10 ^ 21)) :
    ∀ n < 10 ^ 21, Odd n → ¬ n.Weird := by
  intro n hn ho hw
  obtain ⟨d, hdn, hdw, hproper⟩ := primitiveWeirdDivisor hw
  have hdlt : d < 10 ^ 21 := (Nat.le_of_dvd hw.1.pos hdn).trans_lt hn
  have hdodd : Odd d := ho.of_dvd_nat hdn
  obtain ⟨p, a, ys, hp, heq, hfit, ht, hlen⟩ := fangRoots_cover hdlt hdodd hdw.1
  have hlow := h6 d hdodd hdw
  have hrlow : 5 ≤ ys.length := by omega
  have hnum : number ([(p, a)] ++ ys) = d := by
    rw [← heq]
    exact primeCoordinates_prod hdodd.pos.ne'
  have hcoord : PrimeCoordinates ([(p, a)] ++ ys) := by
    rw [← heq]
    exact ⟨fun x hx => (primeCoordinates_prime_pos hx).1, primeCoordinates_pairwise d⟩
  have hc : (⟨[⟨p, 1, false⟩], p + 2, ys.length⟩ : Box).ClosedBelow (10 ^ 21) := by
    rcases hp with rfl | rfl
    · have hhi := oddBelow10Pow21_primeFactors_card_le_sixteen hdlt hdodd
      exact h3 ys.length hrlow (by omega)
    · have hnot3 : ¬ 3 ∣ d := by
        intro h3
        obtain ⟨zs, hz, _⟩ := primeCoordinates_three hdodd h3
        rw [hz] at heq
        simp at heq
      have hhi := coprimeThreeOddBelow10Pow21_primeFactors_card_le_fifteen hdlt hdodd hnot3
      have hlo := coprimeThree_oddAbundant_primeFactors_card_ge_seven hdodd hdw.1 hnot3
      exact h5 ys.length (by omega) (by omega)
  exact hc [(p, a)] ys ⟨.cons hfit .nil, ht, rfl⟩ hcoord
    (hnum.symm ▸ hdlt) (hnum.symm ▸ hdw) (hnum.symm ▸ hproper)

end OddWeirdSubproblems

/-! The largest supports permitted by the size cutoff close through
minimum size, abundancy, and primitive-divisor pruning alone. -/

namespace OddWeirdSubproblems

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem fangThreeFifteenRoot_closed :
    (⟨[⟨3, 1, false⟩], 5, 14⟩ : Box).ClosedBelow (10 ^ 21) := by
  apply replayBelow_closes (witness := fun _ => []) (fuel := 150)
  · decide
  · exact ⟨2, rfl⟩
  · decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem fangThreeSixteenRoot_closed :
    (⟨[⟨3, 1, false⟩], 5, 15⟩ : Box).ClosedBelow (10 ^ 21) := by
  apply replayBelow_closes (witness := fun _ => []) (fuel := 150)
  · decide
  · exact ⟨2, rfl⟩
  · decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem fangFiveFifteenRoot_closed :
    (⟨[⟨5, 1, false⟩], 7, 14⟩ : Box).ClosedBelow (10 ^ 21) := by
  apply replayBelow_closes (witness := fun _ => []) (fuel := 150)
  · decide
  · exact ⟨3, rfl⟩
  · decide +kernel

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

/-- Multiplication by a new prime gives an affine equation for the excess over twice the number. -/
theorem squarefreeExcess {m q s : ℕ} (hq : q.Prime) (hfresh : ¬ q ∣ m)
    (hs : (∑ d ∈ m.divisors, d) = s) (hdef : s ≤ 2 * m) :
    (∑ d ∈ (m * q).divisors, d) + (2 * m - s) * q = 2 * (m * q) + s := by
  have hc : m.Coprime q := (hq.coprime_iff_not_dvd.mpr hfresh).symm
  have hqsum : (∑ d ∈ q.divisors, d) = 1 + q := by
    rw [hq.divisors]
    simp [hq.ne_one.symm]
  have hadd := congrArg (· * q) (Nat.sub_add_cancel hdef)
  rw [Nat.add_mul, Nat.mul_assoc] at hadd
  rw [hc.sum_divisors_mul, hs, hqsum, Nat.mul_add, Nat.mul_one]
  omega

/-- A core subset sum may be extended by one multiple of the new prime to
represent the excess of the squarefree extension. -/
theorem squarefreePseudoperfectOfSubset {m q s h : ℕ} (hq : q.Prime) (hfresh : ¬ q ∣ m)
    (hs : (∑ d ∈ m.divisors, d) = s) (hdef : s ≤ 2 * m)
    (hh : h = 0 ∨ h ∈ m.properDivisors) {t : Finset ℕ} (ht : t ⊆ m.divisors)
    (htsum : (∑ d ∈ t, d) + (2 * m - s + h) * q = s) :
    (m * q).Pseudoperfect := by
  have hm : 0 < m := Nat.pos_of_ne_zero (fun hm => hfresh (hm ▸ dvd_zero q))
  have hmq : 0 < m * q := Nat.mul_pos hm hq.pos
  have hltmq : m < m * q := by simpa using Nat.mul_lt_mul_of_pos_left hq.one_lt hm
  have heq := squarefreeExcess hq hfresh hs hdef
  rw [Nat.add_mul] at htsum
  have hbase : t ⊆ (m * q).properDivisors := by
    intro d hd
    have hdvd := (Nat.mem_divisors.mp (ht hd)).1
    exact Nat.mem_properDivisors.mpr
      ⟨hdvd.trans (dvd_mul_right m q),
        (Nat.le_of_dvd hm hdvd).trans_lt hltmq⟩
  suffices hex : ∃ u ⊆ (m * q).properDivisors, ∑ d ∈ u, d = (∑ d ∈ t, d) + h * q by
    obtain ⟨u, hu, hus⟩ := hex
    refine ⟨hmq, (m * q).properDivisors \ u, Finset.sdiff_subset, ?_⟩
    have hc := Finset.sum_sdiff (f := fun d : ℕ => d) hu
    rw [Nat.sum_divisors_eq_sum_properDivisors_add_self] at heq
    omega
  rcases hh with rfl | hh
  · exact ⟨t, hbase, by simp⟩
  · obtain ⟨hdiv, hlt⟩ := Nat.mem_properDivisors.mp hh
    have hmem : h * q ∈ (m * q).properDivisors := Nat.mem_properDivisors.mpr
      ⟨Nat.mul_dvd_mul_right hdiv q, Nat.mul_lt_mul_of_pos_right hlt hq.pos⟩
    have hnot : h * q ∉ t := fun htq =>
      hfresh ((dvd_mul_left q h).trans (Nat.mem_divisors.mp (ht htq)).1)
    refine ⟨insert (h * q) t, Finset.insert_subset hmem hbase, ?_⟩
    rw [Finset.sum_insert hnot, Nat.add_comm]

/-- A certified interval of core subset sums excludes all supported prime extensions. -/
theorem squarefreePseudoperfectOfInterval {m q s h a b : ℕ} (hq : q.Prime)
    (hfresh : ¬ q ∣ m) (hs : (∑ d ∈ m.divisors, d) = s) (hdef : s ≤ 2 * m)
    (hh : h = 0 ∨ h ∈ m.properDivisors)
    (hcover : ∀ x, a ≤ x → x ≤ b → ∃ t ⊆ m.divisors, ∑ d ∈ t, d = x)
    (hlo : a + (2 * m - s + h) * q ≤ s)
    (hhi : s ≤ b + (2 * m - s + h) * q) : (m * q).Pseudoperfect := by
  obtain ⟨t, ht, hsum⟩ := hcover (s - (2 * m - s + h) * q) (by omega) (by omega)
  exact squarefreePseudoperfectOfSubset hq hfresh hs hdef hh ht (by omega)

/-- A fresh divisor extends a covered interval whenever its two translates touch. -/
theorem subsetSumIntervalInsert {D : Finset ℕ} {v a b : ℕ} (hv : v ∉ D)
    (hcover : ∀ x, a ≤ x → x ≤ b → ∃ t ⊆ D, ∑ d ∈ t, d = x)
    (htouch : a + v ≤ b + 1) :
    ∀ x, a ≤ x → x ≤ b + v → ∃ t ⊆ insert v D, ∑ d ∈ t, d = x := by
  intro x ha hb
  by_cases hx : x ≤ b
  · obtain ⟨t, ht, hs⟩ := hcover x ha hx
    exact ⟨t, ht.trans (Finset.subset_insert v D), hs⟩
  · obtain ⟨t, ht, hs⟩ := hcover (x - v) (by omega) (by omega)
    refine ⟨insert v t, Finset.insert_subset_insert _ ht, ?_⟩
    rw [Finset.sum_insert (fun h => hv (ht h)), hs]
    omega

/-- Complementing within the divisor set reflects an interval of covered sums. -/
theorem subsetSumIntervalReflect {D : Finset ℕ} {a b : ℕ}
    (hcover : ∀ x, a ≤ x → x ≤ b → ∃ t ⊆ D, ∑ d ∈ t, d = x)
    (hab : a ≤ b) (hb : b ≤ ∑ d ∈ D, d) :
    ∀ x, (∑ d ∈ D, d) - b ≤ x → x ≤ (∑ d ∈ D, d) - a →
      ∃ t ⊆ D, ∑ d ∈ t, d = x := by
  intro x hlow hhigh
  obtain ⟨t, ht, hs⟩ := hcover ((∑ d ∈ D, d) - x) (by omega) (by omega)
  refine ⟨D \ t, Finset.sdiff_subset, ?_⟩
  have htotal := Finset.sum_sdiff (f := fun d : ℕ => d) ht
  omega

/-- A proper-divisor interval may be shifted by the core before adjoining the prime. -/
theorem squarefreePseudoperfectOfProperInterval {m q s h a b c : ℕ} (hq : q.Prime)
    (hfresh : ¬ q ∣ m) (hs : (∑ d ∈ m.divisors, d) = s) (hdef : s ≤ 2 * m)
    (hh : h = 0 ∨ h ∈ m.properDivisors) (hc : c = 0 ∨ c = m)
    (hcover : ∀ x, a ≤ x → x ≤ b → ∃ t ⊆ m.properDivisors, ∑ d ∈ t, d = x)
    (hlo : a + c + (2 * m - s + h) * q ≤ s)
    (hhi : s ≤ b + c + (2 * m - s + h) * q) : (m * q).Pseudoperfect := by
  refine squarefreePseudoperfectOfInterval hq hfresh hs hdef hh ?_ hlo hhi
  intro x hx hy
  have hm : m ≠ 0 := fun hm => hfresh (hm ▸ dvd_zero q)
  obtain ⟨t, ht, hsum⟩ := hcover (x - c) (by omega) (by omega)
  have hbase : t ⊆ m.divisors := fun d hd =>
    Nat.mem_divisors.mpr ⟨(Nat.mem_properDivisors.mp (ht hd)).1, hm⟩
  rcases hc with hz | he
  · subst c
    exact ⟨t, hbase, by simpa using hsum⟩
  · subst c
    have hnot : m ∉ t := fun h => (lt_irrefl m) (Nat.mem_properDivisors.mp (ht h)).2
    refine ⟨insert m t, Finset.insert_subset (Nat.mem_divisors.mpr ⟨dvd_rfl, hm⟩) hbase, ?_⟩
    rw [Finset.sum_insert hnot, hsum]
    omega

end OddWeirdSubproblems

namespace OddWeirdSubproblems

/-- A jump covers every possible head prime in the skipped interval. -/
theorem close_jump_next {ss : List Slot} {p stop r : ℕ}
    (hskip : (⟨ss, stop, r + 1⟩ : Box).Closed)
    (htake : ∀ q, p ≤ q → q < stop → q.Prime → Odd q →
      (⟨ss ++ [⟨q, 1, false⟩], q + 2, r⟩ : Box).Closed) :
    (⟨ss, p, r + 1⟩ : Box).Closed := by
  intro xs ys ⟨hx, hy, hlen⟩ hcoord hw hprim
  cases ys with
  | nil => simp at hlen
  | cons y ys =>
    obtain ⟨q, e⟩ := y
    obtain ⟨hpq, hqlo, hq, hqodd, he, ht⟩ := hy
    by_cases hqcut : q < stop
    · have hfit : Slot.Fits ⟨q, 1, false⟩ (q, e) :=
        ⟨hq, rfl, he, by simp⟩
      have eq : xs ++ (q, e) :: ys = (xs ++ [(q, e)]) ++ ys := by simp [List.append_assoc]
      rw [eq] at hcoord hw hprim
      exact htake q hpq hqcut hq hqodd (xs ++ [(q, e)]) ys
        ⟨List.rel_append hx (.cons hfit .nil), ht, by simpa using hlen⟩ hcoord hw hprim
    · exact hskip xs ((q, e) :: ys)
        ⟨hx, ⟨Nat.le_of_not_gt hqcut, hqlo, hq, hqodd, he, ht⟩, hlen⟩ hcoord hw hprim

theorem forall₂_append_singleton {ss : List Slot} {s : Slot} {xs : Coordinates}
    (h : List.Forall₂ Slot.Fits (ss ++ [s]) xs) :
    ∃ as x, xs = as ++ [x] ∧ List.Forall₂ Slot.Fits ss as ∧ s.Fits x := by
  induction ss generalizing xs with
  | nil =>
    simp only [List.nil_append, List.forall₂_cons_left_iff, List.forall₂_nil_left_iff] at h
    obtain ⟨x, _, hx, rfl, rfl⟩ := h
    exact ⟨[], x, rfl, .nil, hx⟩
  | cons t ss ih =>
    simp only [List.cons_append, List.forall₂_cons_left_iff] at h
    obtain ⟨x, xs, hx, hxs, rfl⟩ := h
    obtain ⟨as, y, rfl, ht, hy⟩ := ih hxs
    exact ⟨x :: as, y, rfl, .cons hx ht, hy⟩

/-- When the fresh prime is small, the minimum with exponent one is already
nondeficient. A pseudoperfect certificate for that minimum closes the entire
box, including all greater exponents of the fresh or old primes. -/
theorem close_squarefree_interval
    {ss : List Slot} {q next : ℕ} {m s h a b c : ℕ}
    (hm : number (ss.map Slot.minimum) = m)
    (hs : divisorSum (ss.map Slot.minimum) = s)
    (hdef : s ≤ 2 * m)
    (hh : h = 0 ∨ (h ∣ m ∧ h < m)) (hc : c = 0 ∨ c = m)
    (hcover : ∀ x, a ≤ x → x ≤ b → ∃ t ⊆ m.properDivisors, ∑ d ∈ t, d = x)
    (hlo : a + c + (2 * m - s + h) * q ≤ s)
    (hhi : s ≤ b + c + (2 * m - s + h) * q)
    (hnd : (2 * m - s) * q ≤ s) :
    (⟨ss ++ [⟨q, 1, false⟩], next, 0⟩ : Box).Closed := by
  let box : Box := ⟨ss ++ [⟨q, 1, false⟩], next, 0⟩
  intro xs ys hmatch hvalid hw hprim
  have hminimum : PrimeCoordinates box.minimum :=
    minimum_valid hmatch.1 (primeCoordinates_left hvalid)
  have hcoords : box.minimum = ss.map Slot.minimum ++ [(q, 1)] := by
    simp [box, Box.minimum, Slot.minimum]
  rw [hcoords] at hminimum
  have hq : q.Prime := hminimum.1 (q, 1) (by simp)
  have hqcop : q.Coprime m := by
    rw [← hm]
    apply Nat.coprime_list_prod_right_iff.mpr
    intro w hw
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hw
    have hyq := (List.pairwise_append.mp hminimum.2).2.2 y hy (q, 1) (by simp)
    rw [← pow_one q]
    exact Nat.coprime_pow_primes _ _ hq (hminimum.1 y (List.mem_append_left _ hy)) (Ne.symm hyq.ne)
  have hsum : ∑ d ∈ m.divisors, d = s := by
    rw [← hm, ← divisorSum_eq (primeCoordinates_left hminimum), hs]
  have hnot : ¬ q ∣ m := hq.coprime_iff_not_dvd.mp hqcop
  have hpp : (m * q).Pseudoperfect := squarefreePseudoperfectOfProperInterval hq hnot
    hsum hdef (hh.imp_right Nat.mem_properDivisors.mpr) hc hcover hlo hhi
  have hn : number box.minimum = m * q := by
    rw [hcoords, number_append, hm]
    simp [number]
  have hd : 2 * number box.minimum ≤ divisorSum box.minimum := by
    rw [divisorSum_eq (hcoords.symm ▸ hminimum), hn]
    have he := squarefreeExcess hq hnot hsum hdef
    omega
  exact close_at_nondeficient_minimum hd (Or.inr (Or.inl (hn.symm ▸ hpp)))
    xs ys hmatch hvalid hw hprim

/-- If a fresh factor makes the minimum nondeficient while another distinct
prime is still required, every member of the branch has a nondeficient divisor. -/
theorem close_nondeficient_squarefree_prefix {ss : List Slot} {q next r : ℕ}
    (hr : 0 < r)
    (hnondef : 2 * number (ss.map Slot.minimum) * q ≤
      divisorSum (ss.map Slot.minimum) * (1 + q)) :
    (⟨ss ++ [⟨q, 1, false⟩], next, r⟩ : Box).Closed := by
  apply close_minimum_with_tail (b := ⟨ss ++ [({ prime := q, exponent := 1, fixed := false } : Slot)], next, r⟩) hr
  change 2 * number ((ss ++ [({ prime := q, exponent := 1, fixed := false } : Slot)]).map Slot.minimum) ≤
    divisorSum ((ss ++ [({ prime := q, exponent := 1, fixed := false } : Slot)]).map Slot.minimum)
  rw [List.map_append, number_append, divisorSum_append, ← Nat.mul_assoc]
  simpa [Slot.minimum, number, divisorSum, powerSum] using hnondef

def HeadRangeClosed (ss : List Slot) (r lo hi : ℕ) : Prop :=
  ∀ q, lo ≤ q → q < hi → q.Prime → Odd q →
    (⟨ss ++ [⟨q, 1, false⟩], q + 2, r⟩ : Box).Closed

theorem headRange_join {ss : List Slot} {r lo mid hi : ℕ}
    (h₁ : HeadRangeClosed ss r lo mid) (h₂ : HeadRangeClosed ss r mid hi) :
    HeadRangeClosed ss r lo hi := by
  intro q hqlo hqhi hp ho
  by_cases h : q < mid
  · exact h₁ q hqlo h hp ho
  · exact h₂ q (Nat.le_of_not_gt h) hqhi hp ho

theorem headRange_single {ss : List Slot} {r q : ℕ}
    (h : q.Prime → Odd q → (⟨ss ++ [⟨q, 1, false⟩], q + 2, r⟩ : Box).Closed) :
    HeadRangeClosed ss r q (q + 1) := by
  intro p hlo hhi hp ho
  have e : p = q := by omega
  subst p
  exact h hp ho

theorem headRange_empty_of_composites {ss : List Slot} {r lo hi : ℕ}
    (h : ((List.range (hi - lo)).all (fun i => decide ((lo + i).minFac ≠ lo + i))) = true) :
    HeadRangeClosed ss r lo hi := by
  intro q hlo hhi hp _
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  have hbad := h (q - lo) (List.mem_range.mpr (by omega))
  rw [show lo + (q - lo) = q by omega] at hbad
  exact (hbad hp.minFac_eq).elim

theorem headRange_squarefree {ss : List Slot} {m s h a b c lo hi : ℕ}
    (hm : number (ss.map Slot.minimum) = m)
    (hs : divisorSum (ss.map Slot.minimum) = s)
    (hdef : s ≤ 2 * m)
    (hh : h = 0 ∨ (h ∣ m ∧ h < m)) (hc : c = 0 ∨ c = m)
    (hcover : ∀ x, a ≤ x → x ≤ b → ∃ t ⊆ m.properDivisors, ∑ d ∈ t, d = x)
    (hlow : s ≤ b + c + (2 * m - s + h) * lo)
    (hhigh : a + c + (2 * m - s + h) * (hi - 1) ≤ s) :
    HeadRangeClosed ss 0 lo hi := by
  intro q hqlo hqhi _ _
  have hu : q ≤ hi - 1 := by omega
  have ha := Nat.mul_le_mul_left (2 * m - s + h) hu
  have hb := Nat.mul_le_mul_left (2 * m - s + h) hqlo
  have hc' := Nat.mul_le_mul_right q (show 2 * m - s ≤ 2 * m - s + h by omega)
  exact close_squarefree_interval hm hs hdef hh hc hcover (by omega) (by omega) (by omega)

theorem headRange_nondeficient_prefix {ss : List Slot} {r lo hi m s : ℕ}
    (hr : 0 < r) (hm : number (ss.map Slot.minimum) = m)
    (hs : divisorSum (ss.map Slot.minimum) = s)
    (hcut : (2 * m - s) * (hi - 1) ≤ s) :
    HeadRangeClosed ss r lo hi := by
  intro q _ hqhi _ _
  apply close_nondeficient_squarefree_prefix hr
  rw [hm, hs, Nat.mul_add, Nat.mul_one]
  have hq : q ≤ hi - 1 := by omega
  have h₁ := (Nat.mul_le_mul_left (2 * m - s) hq).trans hcut
  have h₂ := Nat.mul_le_mul_right q (show 2 * m ≤ 2 * m - s + s by omega)
  rw [Nat.add_mul] at h₂
  omega

theorem decrement_append_left {xs ys : Coordinates} {i : ℕ} (hi : i < xs.length) :
    decrement (xs ++ ys) i = decrement xs i ++ ys := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    rcases x with ⟨p, e⟩
    cases i with
    | zero => rfl
    | succ i =>
      have hi' : i < xs.length := by simpa using hi
      simp [decrement, ih hi']

theorem product_after_head (ss : List Slot) (q : ℕ) :
    number ((ss ++ [({ prime := q, exponent := 1, fixed := false } : Slot)]).map Slot.minimum)
    = number (ss.map Slot.minimum) * q := by
  rw [List.map_append, number_append]
  simp [number, Slot.minimum]

theorem sigma_after_head (ss : List Slot) (q : ℕ) :
    divisorSum ((ss ++ [({ prime := q, exponent := 1, fixed := false } : Slot)]).map Slot.minimum)
    = divisorSum (ss.map Slot.minimum) * (1 + q) := by
  rw [List.map_append, divisorSum_append]
  simp [divisorSum, powerSum, Slot.minimum]

theorem headRange_decrement_nondeficient {ss : List Slot} {r lo hi i z t : ℕ}
    (hi' : i < ss.length)
    (hz : number (decrement (ss.map Slot.minimum) i) = z)
    (ht : divisorSum (decrement (ss.map Slot.minimum) i) = t)
    (hzlt : z < number (ss.map Slot.minimum))
    (hcut : (2 * z - t) * (hi - 1) ≤ t) :
    HeadRangeClosed ss r lo hi := by
  intro q _ hqhi hq _
  let b : Box := ⟨ss ++ [⟨q, 1, false⟩], q + 2, r⟩
  intro xs ys hfit hcoord hw hprim
  have hv : PrimeCoordinates b.minimum :=
    minimum_valid hfit.1 (primeCoordinates_left hcoord)
  have hminimum : b.minimum = ss.map Slot.minimum ++ [(q, 1)] := by
    simp [b, Box.minimum, Slot.minimum]
  have hcut' : 2 * (z * q) ≤ t * (1 + q) := by
    have hq' : q ≤ hi - 1 := by omega
    have h₁ := (Nat.mul_le_mul_left (2 * z - t) hq').trans hcut
    have h₂ := Nat.mul_le_mul_right q (show 2 * z ≤ 2 * z - t + t by omega)
    rw [Nat.add_mul] at h₂
    rw [← Nat.mul_assoc, Nat.mul_add] 
    simp only [Nat.mul_one]
    omega
  have hdcoords : decrement b.minimum i = decrement (ss.map Slot.minimum) i ++ [(q, 1)] := by
    rw [hminimum, decrement_append_left (by simpa using hi')]
  have hdn : number (decrement b.minimum i) = z * q := by
    rw [hdcoords, number_append, hz]
    simp [number]
  have hds : divisorSum (decrement b.minimum i) = t * (1 + q) := by
    rw [hdcoords, divisorSum_append, ht]
    simp [divisorSum, powerSum]
  have hdnd : ¬ (number (decrement b.minimum i)).Deficient := by
    rw [deficient_iff_divisorSum_lt (decrement_coordinates hv i), hdn, hds]
    exact hcut'.not_gt
  have hdnlt : number (decrement b.minimum i) < number b.minimum := by
    rw [hdn, show number b.minimum = _ from product_after_head ss q]
    exact Nat.mul_lt_mul_of_pos_right hzlt hq.pos
  have hminDvd : number b.minimum ∣ number (xs ++ ys) := by
    rw [number_append]
    exact dvd_mul_of_dvd_left (minimum_dvd hfit.1) _
  have hdvd := (decrement_dvd b.minimum i).trans hminDvd
  have hlt := hdnlt.trans_le (Nat.le_of_dvd hw.1.pos hminDvd)
  exact hdnd (hprim _ (Nat.mem_properDivisors.mpr ⟨hdvd, hlt⟩))

end OddWeirdSubproblems

namespace OddWeirdSubproblems

/-- A jump at a fixed size cutoff closes the skipped heads and the continuation. -/
theorem closeBelow_jump_next {ss : List Slot} {B p stop r : ℕ}
    (hskip : (⟨ss, stop, r + 1⟩ : Box).ClosedBelow B)
    (htake : ∀ q, p ≤ q → q < stop → q.Prime → Odd q →
      (⟨ss ++ [⟨q, 1, false⟩], q + 2, r⟩ : Box).ClosedBelow B) :
    (⟨ss, p, r + 1⟩ : Box).ClosedBelow B := by
  intro xs ys ⟨hx, hy, hlen⟩ hcoord hsize hw hprim
  cases ys with
  | nil => simp at hlen
  | cons y ys =>
    obtain ⟨q, e⟩ := y
    obtain ⟨hpq, hqlo, hq, hqodd, he, ht⟩ := hy
    by_cases hqcut : q < stop
    · have hfit : Slot.Fits ⟨q, 1, false⟩ (q, e) := ⟨hq, rfl, he, by simp⟩
      have hsplit : xs ++ (q, e) :: ys = (xs ++ [(q, e)]) ++ ys := by simp [List.append_assoc]
      rw [hsplit] at hcoord hsize hw hprim
      exact htake q hpq hqcut hq hqodd (xs ++ [(q, e)]) ys
        ⟨List.rel_append hx (.cons hfit .nil), ht, by simpa using hlen⟩ hcoord hsize hw hprim
    · exact hskip xs ((q, e) :: ys)
        ⟨hx, ⟨Nat.le_of_not_gt hqcut, hqlo, hq, hqodd, he, ht⟩, hlen⟩ hcoord hsize hw hprim

private theorem tailMinimum_pos_of_pos (p r : ℕ) (hp : 0 < p) : 0 < tailMinimum p r := by
  induction r generalizing p with
  | zero => simp [tailMinimum]
  | succ r ih =>
    rw [tailMinimum]
    exact Nat.mul_pos hp (ih _ (by omega))

/-- If the head of a nonempty tail is at least `stop`, then the slot minimum
multiplied by `stop` is a lower bound for the completed number. -/
theorem minimum_mul_head_le_of_matches {ss : List Slot} {xs ys : Coordinates} {stop r : ℕ}
    (hmatch : (⟨ss, stop, r + 1⟩ : Box).Matches xs ys) (hcoord : PrimeCoordinates (xs ++ ys)) :
    number (ss.map Slot.minimum) * stop ≤ number (xs ++ ys) := by
  obtain ⟨hfit, ht, hlen⟩ := hmatch
  have hslots : number (ss.map Slot.minimum) ≤ number xs :=
    Nat.le_of_dvd (number_pos (primeCoordinates_left hcoord).1) (minimum_dvd hfit)
  have htail := tailMinimum_le_number ht
  change ys.length = r + 1 at hlen
  rw [hlen, tailMinimum] at htail
  have hstop : stop ≤ number ys :=
    (Nat.le_mul_of_pos_right stop (tailMinimum_pos_of_pos (stop + 2) r (by omega))).trans htail
  rw [number_append]
  exact Nat.mul_le_mul hslots hstop

/-- A finite head range closes the box below `B` once the slot minimum
times the first unchecked head reaches `B`. Taking `r = 0` gives the
last-prime cutoff. -/
theorem closeBelow_of_headRange_size_stop {ss : List Slot} {B p stop r : ℕ}
    (hrange : HeadRangeClosed ss r p stop)
    (hsize : B ≤ number (ss.map Slot.minimum) * stop) :
    (⟨ss, p, r + 1⟩ : Box).ClosedBelow B := by
  apply closeBelow_jump_next (stop := stop)
  · intro xs ys hmatch hcoord hlt _ _
    exact hlt.not_ge (hsize.trans (minimum_mul_head_le_of_matches hmatch hcoord))
  · intro q hqlo hqhi hq hodd
    exact closedBelow_of_closed (hrange q hqlo hqhi hq hodd) B

end OddWeirdSubproblems

namespace OddWeirdSubproblems

/-- A structurally recursive composite test for certificate replay. Finding
any proper factor is sufficient to omit a prime branch. -/
def hasOddFactor (n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, d =>
    if n < d * d then false
    else if n % d = 0 then true
    else hasOddFactor n fuel (d + 2)

theorem hasOddFactor_false_of_prime {n : ℕ} (hp : n.Prime) (fuel d : ℕ)
    (hd : 2 ≤ d) : hasOddFactor n fuel d = false := by
  induction fuel generalizing d with
  | zero => rfl
  | succ fuel ih =>
    rw [hasOddFactor]
    split
    · rfl
    · next h =>
      have hlt : d < n := by
        have h₂ := Nat.mul_le_mul_right d hd
        omega
      have hmod : n % d ≠ 0 := by
        intro hmod
        rcases (Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero hmod) with h₁ | hn
        · omega
        · omega
      exact (if_neg hmod).trans (ih (d + 2) (by omega))

def mayBeOddPrime (n : ℕ) : Bool := !hasOddFactor n n 3

theorem mayBeOddPrime_of_prime {n : ℕ} (hp : n.Prime) : mayBeOddPrime n = true := by
  simp [mayBeOddPrime, hasOddFactor_false_of_prime hp]

end OddWeirdSubproblems

/-! Certified dynamic lower bounds for the distinct primes in a tail. -/

namespace OddWeirdSubproblems

/-- Advance past at most `fuel` odd composite numbers. A stopped scan is
still a lower bound, whether or not its returned endpoint is prime. -/
def firstAllowedOdd (p : ℕ) : ℕ → ℕ
  | 0 => p
  | fuel + 1 => if mayBeOddPrime p then p else firstAllowedOdd (p + 2) fuel

theorem firstAllowedOdd_ge (p fuel : ℕ) : p ≤ firstAllowedOdd p fuel := by
  induction fuel generalizing p with
  | zero => rfl
  | succ fuel ih =>
    rw [firstAllowedOdd]
    split
    · rfl
    · exact (Nat.le_add_right _ _).trans (ih _)

theorem firstAllowedOdd_odd {p : ℕ} (hp : Odd p) (fuel : ℕ) : Odd (firstAllowedOdd p fuel) := by
  induction fuel generalizing p with
  | zero => exact hp
  | succ fuel ih =>
    rw [firstAllowedOdd]
    split
    · exact hp
    · exact ih (by obtain ⟨k, hk⟩ := hp; exact ⟨k + 1, by omega⟩)

theorem firstAllowedOdd_le_prime {p q : ℕ} (hp : Odd p) (hq : Odd q)
    (hprime : q.Prime) (hle : p ≤ q) (fuel : ℕ) : firstAllowedOdd p fuel ≤ q := by
  induction fuel generalizing p with
  | zero => exact hle
  | succ fuel ih =>
    rw [firstAllowedOdd]
    split
    · exact hle
    · next h =>
      have hneq : p ≠ q := by
        intro he
        subst q
        exact h (mayBeOddPrime_of_prime hprime)
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := hq
      exact ih ⟨a + 1, by omega⟩ (by omega)

def tailPrimeFloor (p : ℕ) : ℕ → List ℕ
  | 0 => []
  | r + 1 =>
    let q := firstAllowedOdd p 32
    q :: tailPrimeFloor (q + 2) r

theorem tailPrimeFloor_length (p r : ℕ) : (tailPrimeFloor p r).length = r := by
  induction r generalizing p with
  | zero => rfl
  | succ r ih => simp only [tailPrimeFloor, List.length_cons, ih]

theorem tailPrimeFloor_gt_one {p : ℕ} (hp : 1 < p) (r : ℕ) :
    ∀ q ∈ tailPrimeFloor p r, 1 < q := by
  induction r generalizing p with
  | zero => simp [tailPrimeFloor]
  | succ r ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hp.trans_le (firstAllowedOdd_ge _ _)
    · apply ih (hp.trans_le ((firstAllowedOdd_ge _ _).trans (Nat.le_add_right _ _))) _ hq

theorem tailPrimeFloor_correct {p : ℕ} (hp : Odd p) {xs : Coordinates} (ht : TailFits p xs)
    (r : ℕ) : RankFloor (tailPrimeFloor p r) xs := by
  induction r generalizing p xs with
  | zero => trivial
  | succ r ih =>
    cases xs with
    | nil => trivial
    | cons x xs =>
      obtain ⟨q, e⟩ := x
      obtain ⟨hlo, _, hprime, hodd, _, ht'⟩ := ht
      have hfirst := firstAllowedOdd_le_prime hp hodd hprime hlo 32
      have hodd' : Odd (firstAllowedOdd p 32 + 2) := by
        obtain ⟨k, hk⟩ := firstAllowedOdd_odd hp 32
        exact ⟨k + 1, by omega⟩
      exact ⟨hfirst, ih hodd' (tailFits_weaken (by omega) ht')⟩

private theorem tailFits_prime_pos {p : ℕ} {xs : Coordinates} (ht : TailFits p xs) :
    ∀ x ∈ xs, x.1.Prime ∧ 0 < x.2 := by
  induction xs generalizing p with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨q, e⟩ := x
    obtain ⟨_, _, hq, _, he, htail⟩ := ht
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨hq, he⟩
    · exact ih htail y hy

theorem tailPrimeFloor_product_le {p : ℕ} (hp : Odd p) {xs : Coordinates} (ht : TailFits p xs)
    {r : ℕ} (hr : r ≤ xs.length) : (tailPrimeFloor p r).prod ≤ number xs := by
  exact number_ge_floor_product (tailPrimeFloor_correct hp ht _)
    (by simpa only [tailPrimeFloor_length] using hr) (tailFits_prime_pos ht)

theorem closeBelow_of_ranked_minimum_ge {b : Box} {B : ℕ} (hodd : Odd b.next)
    (hB : B ≤ number b.minimum * (tailPrimeFloor b.next b.remaining).prod) : b.ClosedBelow B := by
  intro xs ys ⟨hf, ht, hy⟩ hcoord hlt _ _
  have hx := Nat.le_of_dvd (number_pos (primeCoordinates_left hcoord).1) (minimum_dvd hf)
  have hy' := tailPrimeFloor_product_le hodd ht hy.ge
  rw [number_append] at hlt
  exact hlt.not_ge (hB.trans (Nat.mul_le_mul hx hy'))

def rankedUpperNum (b : Box) : ℕ :=
  (b.slots.map Slot.upperNum).prod * (tailPrimeFloor b.next b.remaining).prod

def rankedUpperDen (b : Box) : ℕ :=
  (b.slots.map Slot.upperDen).prod * ((tailPrimeFloor b.next b.remaining).map (· - 1)).prod

private theorem ranked_indices_eq {ps : List ℕ} (h : ∀ p ∈ ps, 1 < p) :
    (ps.map limitingIndex).prod = (ps.prod : ℚ) / (((ps.map (· - 1)).prod : ℕ) : ℚ) := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    have hp : 1 ≤ p := (h p (by simp)).le.trans (by omega)
    simp only [List.map_cons, List.prod_cons, Nat.cast_mul]
    rw [ih (fun q hq => h q (by simp [hq])), ← div_mul_div_comm, limitingIndex, Nat.cast_sub hp]
    simp

private theorem ranked_floor_den_pos {ps : List ℕ} (h : ∀ p ∈ ps, 1 < p) :
    0 < (ps.map (· - 1)).prod := by
  induction ps with
  | nil => decide
  | cons p ps ih =>
    have hp := h p (by simp)
    exact Nat.mul_pos (by omega : 0 < p - 1) (ih (fun q hq => h q (by simp [hq])))

theorem close_of_ranked_upper {b : Box} (hnext : 1 < b.next) (hodd : Odd b.next)
    (hbound : rankedUpperNum b ≤ 2 * rankedUpperDen b) : b.Closed := by
  intro xs ys ⟨hslots, htail, hlen⟩ hvalid hw _
  let ps := tailPrimeFloor b.next b.remaining
  have hp : ∀ q ∈ ps, 1 < q := tailPrimeFloor_gt_one hnext _
  have hslot (s : Slot) (hs : s ∈ b.slots) : 1 < s.prime := by
    obtain ⟨x, _, hx⟩ := exists_fit_of_mem hslots hs
    rw [hx.2.1]
    exact hx.1.one_lt
  have hden : 0 < rankedUpperDen b := Nat.mul_pos (slot_den_pos hslot) (ranked_floor_den_pos hp)
  have hupper : (b.slots.map Slot.upper).prod * (ps.map limitingIndex).prod ≤ 2 := by
    rw [slot_upper_eq hslot, ranked_indices_eq hp, div_mul_div_comm, ← Nat.cast_mul, ← Nat.cast_mul]
    change (rankedUpperNum b : ℚ) / (rankedUpperDen b : ℚ) ≤ 2
    rw [div_le_iff₀ (by exact_mod_cast hden)]
    exact_mod_cast hbound
  have hrat := floorIndex_upper (tailPrimeFloor_correct hodd htail b.remaining)
    (by simpa only [tailPrimeFloor_length] using hlen.le) hp
  have hle : ((xs ++ ys).map (fun x => index x.1 x.2)).prod ≤ 2 := by
    rw [List.map_append, List.prod_append]
    exact (mul_le_mul (slot_prod_upper hslots) hrat (coordinate_prod_nonneg _)
      ((coordinate_prod_nonneg _).trans (slot_prod_upper hslots))).trans hupper
  rw [coordinate_index_eq, divisorSum_eq hvalid, ← Nat.abundancyIndex] at hle
  exact (Nat.abundant_iff_two_lt_abundancyIndex.mp hw.1).not_ge hle

end OddWeirdSubproblems

/-! Use the size cutoff to fix an exponent before testing divisor coverage. -/

namespace OddWeirdSubproblems

/-- This split need only be searched at its fixed exponent if raising
the exponent makes the minimum possible completion too large. -/
theorem closeBelow_fix_slot_of_size {b : Box} {B i : ℕ} {s : Slot}
    (hi : b.slots[i]? = some s) (hf : s.fixed = false) (hodd : Odd b.next)
    (hB : B ≤ number ({b with slots := b.slots.set i {s with exponent := s.exponent + 1}} : Box).minimum *
      (tailPrimeFloor b.next b.remaining).prod)
    (hfixed : ({b with slots := b.slots.set i {s with fixed := true}} : Box).ClosedBelow B) :
    b.ClosedBelow B :=
  closeBelow_split_slot hi hf hfixed (closeBelow_of_ranked_minimum_ge hodd hB)

/-- Find the first open slot whose next exponent would exceed the size budget. -/
def sizeFixedSlot (B : ℕ) (b : Box) : Option (ℕ × Slot) :=
  let floor := (tailPrimeFloor b.next b.remaining).prod
  ((List.range b.slots.length).filterMap fun i => b.slots[i]?.map fun s => (i, s)).find?
    fun (i, s) => !s.fixed &&
      decide (B ≤ number ({b with slots := b.slots.set i {s with exponent := s.exponent + 1}} : Box).minimum * floor)

theorem sizeFixedSlot_closes {B i : ℕ} {b : Box} {s : Slot}
    (h : sizeFixedSlot B b = some (i, s)) (hodd : Odd b.next)
    (hfixed : ({b with slots := b.slots.set i {s with fixed := true}} : Box).ClosedBelow B) :
    b.ClosedBelow B := by
  unfold sizeFixedSlot at h
  have hmem := List.find?_some h
  have hprune := List.mem_of_find?_eq_some h
  obtain ⟨j, _, hslot⟩ := List.mem_filterMap.mp hprune
  obtain ⟨u, hu, he⟩ := Option.map_eq_some_iff.mp hslot
  cases he
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hmem
  exact closeBelow_fix_slot_of_size hu hmem.1 hodd hmem.2 hfixed

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

/-- The additional exponent budget is measured relative to the minimum
product of all old slots and all ranked fresh prime floors. -/
def exponentBudget (B : ℕ) (b : Box) : ℕ :=
  (B - 1) / (number b.minimum * (tailPrimeFloor b.next b.remaining).prod)

private def floorSlot (p : ℕ) : Slot := ⟨p, 1, false⟩

private def exponentCapSlot (R : ℕ) (s : Slot) : ℕ × ℕ :=
  (s.prime, if s.fixed then s.exponent else s.exponent + Nat.log s.prime R)

/-- Keep fixed exponents and cap each open exponent by the integer logarithm
of the leftover size budget. Fresh slots use the ranked prime floors. -/
def exponentCapCoordinates (B : ℕ) (b : Box) : Coordinates :=
  ((b.slots ++ (tailPrimeFloor b.next b.remaining).map floorSlot).map
    (exponentCapSlot (exponentBudget B b)))

/-- The finite cap is checked with natural cross-products. -/
def exponentCapOk (B : ℕ) (b : Box) : Bool :=
  let cs := exponentCapCoordinates B b
  decide (divisorSum cs ≤ 2 * number cs)

private theorem index_succ_of_pos {p e : ℕ} (hp : 0 < p) :
    index p (e + 1) = index p e + 1 / (p : ℚ) ^ (e + 1) := by
  have hsum : powerSum p (e + 1) = p * powerSum p e + 1 := by
    simp only [powerSum_eq_sum]
    exact geom_sum_succ
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  unfold index
  rw [hsum, Nat.cast_add, Nat.cast_mul, Nat.cast_one, add_div, pow_succ',
    mul_div_mul_left _ _ hp0]

private theorem index_mono_exponent {p : ℕ} (hp : 0 < p) : Monotone (index p) := by
  apply monotone_nat_of_le_succ
  intro e
  rw [index_succ_of_pos hp]
  exact le_add_of_nonneg_right (by positivity)

private theorem index_antitone_base {p q : ℕ} (hp : 0 < p) (hpq : p ≤ q) (e : ℕ) :
    index q e ≤ index p e := by
  induction e with
  | zero => simp [index, powerSum]
  | succ e ih =>
    rw [index_succ_of_pos hp, index_succ_of_pos (hp.trans_le hpq)]
    have hpR : (0 : ℚ) < p := by exact_mod_cast hp
    have hpqR : (p : ℚ) ≤ q := by exact_mod_cast hpq
    exact add_le_add ih (one_div_le_one_div_of_le (pow_pos hpR _)
      (pow_le_pow_left₀ hpR.le hpqR _))

private def NumericalFit (s : Slot) (x : ℕ × ℕ) : Prop :=
  1 < s.prime ∧ s.prime ≤ x.1 ∧ s.exponent ≤ x.2 ∧ (s.fixed = true → s.exponent = x.2)

private theorem numericalFit_of_slotFits {ss : List Slot} {xs : Coordinates}
    (h : List.Forall₂ Slot.Fits ss xs) : List.Forall₂ NumericalFit ss xs := by
  apply h.imp
  intro s x hx
  obtain ⟨hp, hq, he, hfix⟩ := hx
  exact ⟨hq ▸ hp.one_lt, hq.le, he, hfix⟩

private theorem numericalFit_of_rankFloor {ps : List ℕ} {xs : Coordinates} {p : ℕ}
    (hr : RankFloor ps xs) (hl : ps.length = xs.length)
    (hps : ∀ q ∈ ps, 1 < q) (ht : TailFits p xs) :
    List.Forall₂ NumericalFit (ps.map floorSlot) xs := by
  induction ps generalizing xs p with
  | nil =>
    have hx : xs = [] := List.length_eq_zero_iff.mp hl.symm
    subst xs
    exact .nil
  | cons q ps ih =>
    cases xs with
    | nil => simp at hl
    | cons x xs =>
      obtain ⟨t, e⟩ := x
      obtain ⟨hle, htail⟩ := hr
      obtain ⟨_, _, _, _, he, ht'⟩ := ht
      exact .cons ⟨hps q (by simp), hle, he, by simp [floorSlot]⟩
        (ih htail (by simpa using hl) (fun q' hq' => hps q' (List.mem_cons_of_mem _ hq')) ht')

private theorem numericalFit_pow_le {s : Slot} {x : ℕ × ℕ} (h : NumericalFit s x) :
    s.prime ^ s.exponent ≤ x.1 ^ x.2 :=
  (Nat.pow_le_pow_right (Nat.zero_lt_one.trans h.1) h.2.2.1).trans
    (Nat.pow_le_pow_left h.2.1 _)

private theorem numericalFit_minimum_pos_le {ss : List Slot} {xs : Coordinates}
    (h : List.Forall₂ NumericalFit ss xs) :
    0 < number (ss.map Slot.minimum) ∧ number (ss.map Slot.minimum) ≤ number xs := by
  induction h with
  | nil => exact ⟨Nat.one_pos, le_rfl⟩
  | @cons s x ss xs hx _ ih =>
    simp only [List.map_cons, number_cons, Slot.minimum]
    exact ⟨Nat.mul_pos (pow_pos (Nat.zero_lt_one.trans hx.1) _) ih.1,
      Nat.mul_le_mul (numericalFit_pow_le hx) ih.2⟩

private theorem numericalFit_cap {ss : List Slot} {xs : Coordinates} {R : ℕ}
    (h : List.Forall₂ NumericalFit ss xs)
    (hsize : number xs < number (ss.map Slot.minimum) * (R + 1)) :
    List.Forall₂ (fun s x => NumericalFit s x ∧ x.2 ≤ (exponentCapSlot R s).2) ss xs := by
  induction h with
  | nil => exact .nil
  | @cons s x ss xs hx ht ih =>
    simp only [List.map_cons, number_cons, Slot.minimum] at hsize
    have htail := numericalFit_minimum_pos_le ht
    have hp : 0 < s.prime := Nat.zero_lt_one.trans hx.1
    have hsizeTail : number xs < number (ss.map Slot.minimum) * (R + 1) := by
      apply Nat.lt_of_mul_lt_mul_left (a := s.prime ^ s.exponent)
      rw [← Nat.mul_assoc]
      exact (Nat.mul_le_mul_right _ (numericalFit_pow_le hx)).trans_lt hsize
    have hpower : s.prime ^ (x.2 - s.exponent) ≤ R := by
      by_contra! hh
      have hmul : (s.prime ^ s.exponent * number (ss.map Slot.minimum)) *
          s.prime ^ (x.2 - s.exponent) ≤ x.1 ^ x.2 * number xs := by
        calc
          _ = s.prime ^ x.2 * number (ss.map Slot.minimum) := by
            rw [mul_right_comm, ← pow_add, Nat.add_sub_of_le hx.2.2.1]
          _ ≤ _ := Nat.mul_le_mul (Nat.pow_le_pow_left hx.2.1 _) htail.2
      exact hsize.not_ge ((Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hh)).trans hmul)
    have he : x.2 ≤ (exponentCapSlot R s).2 := by
      cases hf : s.fixed
      · have hh := Nat.le_log_of_pow_le hx.1 hpower
        simp only [exponentCapSlot, hf, Bool.false_eq_true, if_false]
        have hle := hx.2.2.1
        omega
      · simp [exponentCapSlot, hf, hx.2.2.2 hf]
    exact .cons ⟨hx, he⟩ (ih hsizeTail)

private theorem indices_le_exponentCap {ss : List Slot} {xs : Coordinates} {R : ℕ}
    (h : List.Forall₂ (fun s x => NumericalFit s x ∧ x.2 ≤ (exponentCapSlot R s).2) ss xs) :
    (xs.map (fun x => index x.1 x.2)).prod ≤
      ((ss.map (exponentCapSlot R)).map (fun x => index x.1 x.2)).prod := by
  induction h with
  | nil => simp
  | @cons s x ss xs hx _ ih =>
    have hp : 0 < s.prime := Nat.zero_lt_one.trans hx.1.1
    have hhead : index x.1 x.2 ≤ index (exponentCapSlot R s).1 (exponentCapSlot R s).2 :=
      (index_antitone_base hp hx.1.2.1 _).trans (index_mono_exponent hp hx.2)
    simp only [List.map_cons, List.prod_cons]
    exact mul_le_mul hhead ih (coordinate_prod_nonneg xs) (index_nonneg _ _)

private theorem match_capped_numericalFit {b : Box} {B : ℕ} {xs ys : Coordinates}
    (hnext : 1 < b.next) (hodd : Odd b.next) (hmatch : b.Matches xs ys)
    (hsize : number (xs ++ ys) < B) :
    List.Forall₂ (fun s x => NumericalFit s x ∧ x.2 ≤ (exponentCapSlot (exponentBudget B b) s).2)
      (b.slots ++ (tailPrimeFloor b.next b.remaining).map floorSlot) (xs ++ ys) := by
  obtain ⟨hslots, ht, hl⟩ := hmatch
  let ps := tailPrimeFloor b.next b.remaining
  let ss := b.slots ++ ps.map floorSlot
  let A := number b.minimum * ps.prod
  let R := exponentBudget B b
  have hfit : List.Forall₂ NumericalFit ss (xs ++ ys) :=
    List.rel_append (numericalFit_of_slotFits hslots)
      (numericalFit_of_rankFloor (tailPrimeFloor_correct hodd ht b.remaining)
        ((tailPrimeFloor_length b.next b.remaining).trans hl.symm)
        (tailPrimeFloor_gt_one hnext _) ht)
  have hAeq : number (ss.map Slot.minimum) = A := by
    simp only [ss, A, Box.minimum, List.map_append, number_append]
    congr 1
    induction ps with
    | nil => rfl
    | cons p ps ih => simp only [List.map_cons, number_cons, List.prod_cons, Slot.minimum, floorSlot,
        pow_one, ih]
  have hA : 0 < A := hAeq ▸ (numericalFit_minimum_pos_le hfit).1
  have hnextSize : B - 1 < A * (R + 1) := by
    rw [Nat.mul_comm, ← Nat.div_lt_iff_lt_mul hA]
    exact Nat.lt_succ_self _
  have hR : number (xs ++ ys) < number (ss.map Slot.minimum) * (R + 1) := by
    rw [hAeq]
    omega
  exact numericalFit_cap hfit hR

/-- The abundancy index of a completion below `B` is bounded by the product
of its independently size-capped prime-power indices. -/
theorem abundancyIndex_le_exponentCap_of_matches_below {b : Box} {B : ℕ} {xs ys : Coordinates}
    (hnext : 1 < b.next) (hodd : Odd b.next) (hmatch : b.Matches xs ys)
    (hcoords : PrimeCoordinates (xs ++ ys)) (hsize : number (xs ++ ys) < B) :
    (number (xs ++ ys)).abundancyIndex ≤
      (divisorSum (exponentCapCoordinates B b) : ℚ) / (number (exponentCapCoordinates B b) : ℚ) := by
  have h := indices_le_exponentCap (match_capped_numericalFit hnext hodd hmatch hsize)
  change _ ≤ ((exponentCapCoordinates B b).map (fun x => index x.1 x.2)).prod at h
  rw [coordinate_index_eq, coordinate_index_eq, divisorSum_eq hcoords, ← Nat.abundancyIndex] at h
  exact h

/-- A size-capped upper product at most two closes the box below `B`. -/
theorem closeBelow_of_exponentCap {b : Box} {B : ℕ} (hnext : 1 < b.next) (hodd : Odd b.next)
    (hcap : divisorSum (exponentCapCoordinates B b) ≤ 2 * number (exponentCapCoordinates B b)) :
    b.ClosedBelow B := by
  intro xs ys hmatch hcoords hsize hw _
  have h := abundancyIndex_le_exponentCap_of_matches_below hnext hodd hmatch hcoords hsize
  let z := (number (exponentCapCoordinates B b) : ℚ)
  have hz : 0 ≤ z := by positivity
  have hh : (divisorSum (exponentCapCoordinates B b) : ℚ) ≤ 2 * z := by
    dsimp only [z]
    exact_mod_cast hcap
  have hle : (divisorSum (exponentCapCoordinates B b) : ℚ) / z ≤ 2 := by
    refine (div_le_div_of_nonneg_right hh hz).trans ?_
    by_cases h0 : z = 0
    · simp [h0]
    · simp [h0]
  exact (Nat.abundant_iff_two_lt_abundancyIndex.mp hw.1).not_ge (h.trans hle)

theorem exponentCapOk_closes {b : Box} {B : ℕ} (hnext : 1 < b.next) (hodd : Odd b.next)
    (h : exponentCapOk B b = true) : b.ClosedBelow B :=
  closeBelow_of_exponentCap hnext hodd (of_decide_eq_true h)

private def freezeSlot (R : ℕ) (s : Slot) : Slot :=
  {s with fixed := s.fixed || decide (R < s.prime)}

/-- Fix all old exponents that cannot grow below the size cutoff in one pass.
The minimum value and the count of fresh factors stay the same. -/
def freezeSizeSlots (B : ℕ) (b : Box) : Box :=
  {b with slots := b.slots.map (freezeSlot (exponentBudget B b))}

private theorem slots_fit_frozen {ss : List Slot} {xs : Coordinates} {R : ℕ}
    (hf : List.Forall₂ Slot.Fits ss xs)
    (hcap : List.Forall₂ (fun s x => NumericalFit s x ∧ x.2 ≤ (exponentCapSlot R s).2) ss xs) :
    List.Forall₂ Slot.Fits (ss.map (freezeSlot R)) xs := by
  induction hf with
  | nil => exact .nil
  | @cons s x ss xs hs _ ih =>
    cases hcap with
    | cons hc hcs =>
      refine .cons ⟨hs.1, hs.2.1, hs.2.2.1, ?_⟩ (ih hcs)
      intro hfix
      change (s.fixed || decide (R < s.prime)) = true at hfix
      obtain hf | hsmall := Bool.or_eq_true_iff.mp hfix
      · exact hs.2.2.2 hf
      · have hlog : Nat.log s.prime R = 0 := Nat.log_of_lt (of_decide_eq_true hsmall)
        apply Nat.le_antisymm hs.2.2.1
        have hre := hc.2
        simp only [exponentCapSlot, hlog, Nat.add_zero, ite_self] at hre
        exact hre

theorem freezeSizeSlots_closes {B : ℕ} {b : Box} (hnext : 1 < b.next) (hodd : Odd b.next)
    (h : (freezeSizeSlots B b).ClosedBelow B) : b.ClosedBelow B := by
  intro xs ys hmatch hcoords hsize hw hproper
  have hslots := List.forall₂_take b.slots.length
    (match_capped_numericalFit hnext hodd hmatch hsize)
  rw [hmatch.1.length_eq] at hslots
  have hx : (b.slots ++ (tailPrimeFloor b.next b.remaining).map floorSlot).take xs.length = b.slots := by
    rw [← hmatch.1.length_eq]
    simp
  rw [hx, List.take_left] at hslots
  exact h xs ys ⟨slots_fit_frozen hmatch.1 hslots, hmatch.2⟩ hcoords hsize hw hproper

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

def Covered (D : Finset ℕ) (a b : ℕ) : Prop :=
  ∀ x, a ≤ x → x ≤ b → ∃ t ⊆ D, ∑ d ∈ t, d = x

def bitsStep (bits value : ℕ) : ℕ := bits ||| (bits <<< value)

def subsetBits : List ℕ → ℕ
  | [] => 1
  | w :: ws => bitsStep (subsetBits ws) w

theorem testBit_subsetBits {ds : List ℕ} (hnodup : ds.Nodup) {x : ℕ}
    (h : (subsetBits ds).testBit x = true) :
    ∃ t ⊆ ds.toFinset, ∑ d ∈ t, d = x := by
  induction ds generalizing x with
  | nil =>
    have hx : x = 0 := by
      cases x with
      | zero => rfl
      | succ x =>
        change (1 : ℕ).testBit (x + 1) = true at h
        simp [Nat.testBit_succ] at h
    exact ⟨∅, by simp, by simp [hx]⟩
  | cons w ws ih =>
    obtain ⟨hnmem, hnd⟩ := List.nodup_cons.mp hnodup
    simp only [subsetBits, bitsStep, Nat.testBit_or, Nat.testBit_shiftLeft,
      Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with hl | ⟨hlo, hr⟩
    · obtain ⟨t, ht, hs⟩ := ih hnd hl
      exact ⟨t, ht.trans (by simp), hs⟩
    · obtain ⟨t, ht, hs⟩ := ih hnd hr
      have hnot : w ∉ t := fun hmem => hnmem (List.mem_toFinset.mp (ht hmem))
      refine ⟨insert w t, by simpa using Finset.insert_subset_insert w ht, ?_⟩
      rw [sum_insert hnot, hs]
      omega

def bitIntervalOk (ds : List ℕ) (a b : ℕ) : Bool :=
  let mask := 2 ^ (b + 1 - a) - 1
  decide (((subsetBits ds >>> a) &&& mask) = mask)

theorem cover_of_bitIntervalOk {ds : List ℕ} {a b : ℕ}
    (hnodup : ds.Nodup) (h : bitIntervalOk ds a b = true) :
    Covered ds.toFinset a b := by
  intro x hlo hhi
  simp only [bitIntervalOk, decide_eq_true_eq] at h
  have hb := congrArg (fun k : ℕ => k.testBit (x - a)) h
  have hj : x - a < b + 1 - a := by omega
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one,
    decide_eq_true hj, Bool.and_true] at hb
  rw [show a + (x - a) = x by omega] at hb
  exact testBit_subsetBits hnodup hb

/-- Verify that each next divisor touches the current interval, then extend. -/
def growIntervalOk (a : ℕ) : ℕ → List ℕ → Bool
  | _, [] => true
  | b, w :: ws => decide (a + w ≤ b + 1) && growIntervalOk a (b + w) ws

theorem cover_of_growIntervalOk {ds ws : List ℕ} {a b : ℕ}
    (hnodup : (ds ++ ws).Nodup) (hcover : Covered ds.toFinset a b)
    (h : growIntervalOk a b ws = true) :
    Covered (ds ++ ws).toFinset a (b + ws.sum) := by
  induction ws generalizing ds b with
  | nil => simpa using hcover
  | cons w ws ih =>
    simp only [growIntervalOk, Bool.and_eq_true, decide_eq_true_eq] at h
    have heq : ds ++ w :: ws = (ds ++ [w]) ++ ws := by simp [List.append_assoc]
    rw [heq] at hnodup ⊢
    rw [List.sum_cons, ← Nat.add_assoc]
    apply ih hnodup _ h.2
    have hnot : w ∉ ds.toFinset := by
      intro hw
      have hnd : (ds ++ [w]).Nodup := (List.nodup_append.mp hnodup).1
      exact (List.nodup_append.mp hnd).2.2 _ (List.mem_toFinset.mp hw) _ (by simp) rfl
    have heq' : (ds ++ [w]).toFinset = insert w ds.toFinset := by
      ext d
      simp
    rw [heq']
    exact subsetSumIntervalInsert hnot hcover h.1

theorem cover_of_verified_divisor_interval {n a b : ℕ} {ds ws : List ℕ}
    (hnodup : (ds ++ ws).Nodup)
    (hdiv : ∀ d ∈ ds ++ ws, d ∣ n ∧ d < n)
    (hbit : bitIntervalOk ds a b = true)
    (hgrow : growIntervalOk a b ws = true) :
    Covered n.properDivisors a (b + ws.sum) := by
  have hnd := (List.nodup_append.mp hnodup).1
  have hc := cover_of_growIntervalOk hnodup (cover_of_bitIntervalOk hnd hbit) hgrow
  intro x hlo hhi
  obtain ⟨t, ht, hs⟩ := hc x hlo hhi
  exact ⟨t, fun d hd => Nat.mem_properDivisors.mpr (hdiv d (List.mem_toFinset.mp (ht hd))), hs⟩

theorem cover_mono {D E : Finset ℕ} {a b : ℕ} (hDE : D ⊆ E)
    (h : Covered D a b) : Covered E a b := by
  intro x hx hy
  obtain ⟨t, ht, hs⟩ := h x hx hy
  exact ⟨t, ht.trans hDE, hs⟩

def divisorListOk (n : ℕ) (ds : List ℕ) : Bool :=
  tightlySorted ds && ds.all (fun d => decide (d ∣ n ∧ d < n))

theorem divisorListOk_sound {n : ℕ} {ds : List ℕ} (h : divisorListOk n ds = true) :
    ds.Nodup ∧ ds.toFinset ⊆ n.properDivisors := by
  simp only [divisorListOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨tightlySorted_nodup h.1, fun d hd => Nat.mem_properDivisors.mpr (h.2 d (List.mem_toFinset.mp hd))⟩

theorem cover_of_validated_bits {n a b : ℕ} {ds : List ℕ}
    (hd : divisorListOk n ds = true) (hb : bitIntervalOk ds a b = true) :
    Covered n.properDivisors a b :=
  cover_mono (divisorListOk_sound hd).2 (cover_of_bitIntervalOk (divisorListOk_sound hd).1 hb)

theorem cover_of_validated_growth {n a b : ℕ} {ds ws : List ℕ}
    (hd : divisorListOk n (ds ++ ws) = true)
    (hb : bitIntervalOk ds a b = true) (hg : growIntervalOk a b ws = true) :
    Covered n.properDivisors a (b + ws.sum) := by
  obtain ⟨hnodup, hsub⟩ := divisorListOk_sound hd
  exact cover_mono hsub (cover_of_growIntervalOk hnodup
    (cover_of_bitIntervalOk (List.nodup_append.mp hnodup).1 hb) hg)

theorem sum_toFinset_of_nodup {ds : List ℕ} (h : ds.Nodup) :
    ∑ d ∈ ds.toFinset, d = ds.sum := by
  simpa using List.sum_toFinset (fun x : ℕ => x) h

theorem cover_reflected_bits {n a b : ℕ} {small ds : List ℕ}
    (hd : divisorListOk n ds = true) (hsmall : small.toFinset ⊆ ds.toFinset)
    (hs : small.Nodup) (hb : bitIntervalOk small a b = true)
    (hab : a ≤ b) (hb' : b ≤ ds.sum) :
    Covered n.properDivisors (ds.sum - b) (ds.sum - a) := by
  obtain ⟨hnd, hsub⟩ := divisorListOk_sound hd
  have hc := cover_mono hsmall (cover_of_bitIntervalOk hs hb)
  rw [← sum_toFinset_of_nodup hnd] at hb' ⊢
  exact cover_mono hsub (subsetSumIntervalReflect hc hab hb')

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def divisorsFromCoordinates : Coordinates → List ℕ
  | [] => [1]
  | (p, e) :: fs =>
    let ds := divisorsFromCoordinates fs
    (List.range (e + 1)).flatMap (fun i => ds.map (fun d => d * p ^ i))

def mergeDivisors : ℕ → List ℕ → List ℕ → List ℕ
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, xs, [] => xs
  | fuel + 1, x :: xs, y :: ys =>
    if x ≤ y then x :: mergeDivisors fuel xs (y :: ys)
    else y :: mergeDivisors fuel (x :: xs) ys

def sortDivisors : ℕ → List ℕ → List ℕ
  | 0, ds => ds
  | fuel + 1, ds =>
    if ds.length < 2 then ds
    else
      let mid := ds.length / 2
      mergeDivisors ds.length (sortDivisors fuel (ds.take mid)) (sortDivisors fuel (ds.drop mid))

def sortedDivisors (fs : Coordinates) : List ℕ :=
  sortDivisors 30 (divisorsFromCoordinates fs)

def smallPrefix : ℕ → List ℕ → List ℕ
  | _, [] => []
  | room, d :: ds => if d ≤ room then d :: smallPrefix (room - d) ds else []

def growPrefix (a : ℕ) : ℕ → List ℕ → List ℕ
  | _, [] => []
  | b, d :: ds =>
    if a + d ≤ b + 1 then d :: growPrefix a (b + d) ds else []

def highestPresent : ℕ → ℕ → ℕ → ℕ
  | 0, _, lo => lo
  | fuel + 1, bits, lo =>
    let mid := lo + 2 ^ fuel
    if bits >>> mid = 0 then highestPresent fuel bits lo
    else highestPresent fuel bits mid

def effectiveLow (bits total : ℕ) : ℕ :=
  let mask := 2 ^ (total / 2 + 1) - 1
  let missing := mask ^^^ (mask &&& bits)
  if missing = 0 then 0 else highestPresent 10 missing 0 + 1

def bitWitness : List ℕ → ℕ → List ℕ
  | [], _ => []
  | w :: ws, x =>
    if (subsetBits ws).testBit x then bitWitness ws x
    else w :: bitWitness ws (x - w)

def peelGrowth (a : ℕ) : List ℕ → ℕ → ℕ → List ℕ × ℕ
  | [], _, x => ([], x)
  | w :: ws, b, x =>
    if b - w < x then
      let (ds, y) := peelGrowth a ws (b - w) (x - w)
      (w :: ds, y)
    else peelGrowth a ws (b - w) x

/-- Recover an actual subset from the bitset and translated central interval.
Every proposed subset is checked independently by `witnessOk`. -/
def intervalWitness (ds : List ℕ) (x : ℕ) : Option (List ℕ) :=
  let short := smallPrefix 1024 ds
  let bits := subsetBits short
  if bits.testBit x then some (bitWitness short x)
  else
    let a := effectiveLow bits short.sum
    let b := short.sum - a
    if b < a then none
    else
      let extra := growPrefix a b (ds.drop short.length)
      let high := b + extra.sum
      if a ≤ x && x ≤ high then
        let (ws, y) := peelGrowth a extra.reverse high x
        if bits.testBit y then some (ws ++ bitWitness short y) else none
      else none

def cofactorWitness (fs : Coordinates) (p i target : ℕ) : Option (List ℕ) :=
  let rest := fs.eraseIdx i
  let ds := sortedDivisors rest
  let shifts := [0, p] ++ rest.map (fun t => p * t.1)
  shifts.findSome? (fun w =>
    if w ≤ target then
      (intervalWitness ds (target - w)).map (fun chosen =>
        if w = 0 then chosen else w :: chosen)
    else none)

def hintedWitness (fs : Coordinates) (i h target : ℕ) : Option (List ℕ) := do
  let (p, _) ← fs[i]?
  let scaled := p * h
  if target < scaled then none
  else
    let ds := sortedDivisors (fs.eraseIdx i)
    let chosen ← intervalWitness ds (target - scaled)
    pure (if scaled = 0 then chosen else scaled :: chosen)

def hintedWitnessOk (fs : Coordinates) (i h : ℕ) : Bool :=
  let n := number fs
  let s := divisorSum fs
  match hintedWitness fs i h (s - 2 * n) with
  | some ds => witnessOk n s (sortDivisors 30 ds)
  | none => false

theorem hintedWitnessOk_closes {b : Box} {i h : ℕ}
    (hok : hintedWitnessOk b.minimum i h = true) : b.Closed := by
  unfold hintedWitnessOk at hok
  dsimp only at hok
  split at hok
  · exact witnessOk_closes hok
  · contradiction

def suggestedWitness (fs : Coordinates) (target : ℕ) : Option (List ℕ) :=
  fs.zipIdx.reverse.findSome? (fun ((p, _), i) => cofactorWitness fs p i target)

def automaticWitnessOk (fs : Coordinates) : Bool :=
  let n := number fs
  let s := divisorSum fs
  match suggestedWitness fs (s - 2 * n) with
  | none => false
  | some ds => witnessOk n s (sortDivisors 30 ds)

theorem automaticWitnessOk_closes {b : Box} (h : automaticWitnessOk b.minimum = true) :
    b.Closed := by
  change (match suggestedWitness b.minimum (divisorSum b.minimum - 2 * number b.minimum) with
    | none => false
    | some ds => witnessOk (number b.minimum) (divisorSum b.minimum) (sortDivisors 30 ds)) = true at h
  split at h
  · contradiction
  · exact witnessOk_closes h

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

structure IntervalSource where
  kind : ℕ
  low : ℕ
  high : ℕ

structure CoreCoverage where
  proper : List ℕ
  small : List ℕ
  growing : List ℕ
  seedLo : ℕ
  seedHi : ℕ
  central : List IntervalSource

def zeroRun : ℕ → ℕ → ℕ → ℕ
  | 0, _, lo => lo
  | fuel + 1, bits, lo =>
    let mid := lo + 2 ^ fuel
    if bits &&& (2 ^ mid - 1) = 0 then zeroRun fuel bits mid
    else zeroRun fuel bits lo

def bitRunsAux : ℕ → ℕ → ℕ → List (ℕ × ℕ)
  | 0, _, _ => []
  | fuel + 1, bits, offset =>
    if bits = 0 then []
    else
      let first := zeroRun 11 bits 0
      let start := bits >>> first
      let mask := 2 ^ (1025 - (offset + first)) - 1
      let missing := mask ^^^ (start &&& mask)
      let count := if missing = 0 then 1025 - (offset + first) else zeroRun 11 missing 0
      let low := offset + first
      let next := low + count
      if count = 0 then []
      else (low, next - 1) :: bitRunsAux fuel (start >>> count) next

def bitRuns (bits size : ℕ) : List (ℕ × ℕ) :=
  bitRunsAux size (bits &&& (2 ^ size - 1)) 0 |>.map (fun (a, b) => (a, min b (size - 1)))

def makeCoverage (fs : Coordinates) : CoreCoverage :=
  let proper := (sortedDivisors fs).dropLast
  let small := smallPrefix 1024 proper
  let bits := subsetBits small
  let a := effectiveLow bits small.sum
  let b := small.sum - a
  let growing := if a ≤ b then growPrefix a b (proper.drop small.length) else []
  ⟨proper, small, growing, a, b, if a ≤ b then [⟨0, a, b + growing.sum⟩] else []⟩

def IntervalSource.endpoints (c : CoreCoverage) (t : IntervalSource) : ℕ × ℕ :=
  if t.kind = 2 then (c.proper.sum - t.high, c.proper.sum - t.low)
  else (t.low, t.high)

def IntervalSource.ok (n : ℕ) (c : CoreCoverage) (t : IntervalSource) : Bool :=
  if t.kind = 0 then
    divisorListOk n (c.small ++ c.growing) &&
      bitIntervalOk c.small c.seedLo c.seedHi &&
      growIntervalOk c.seedLo c.seedHi c.growing &&
      decide (c.seedLo ≤ t.low ∧ t.high ≤ c.seedHi + c.growing.sum)
  else if t.kind = 1 then
    divisorListOk n c.small && bitIntervalOk c.small t.low t.high
  else if t.kind = 2 then
    divisorListOk n c.proper && tightlySorted c.small &&
      decide (c.small = c.proper.take c.small.length) &&
      bitIntervalOk c.small t.low t.high &&
      decide (t.low ≤ t.high ∧ t.high ≤ c.proper.sum)
  else false

theorem intervalSource_ok_covers {n : ℕ} {c : CoreCoverage} {t : IntervalSource}
    (h : t.ok n c = true) :
    Covered n.properDivisors (t.endpoints c).1 (t.endpoints c).2 := by
  unfold IntervalSource.ok at h
  by_cases h0 : t.kind = 0
  · simp only [if_pos h0, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [IntervalSource.endpoints, show t.kind ≠ 2 by omega, if_false]
    have hcv := cover_of_validated_growth h.1.1.1 h.1.1.2 h.1.2
    intro x hx hy
    exact hcv x (h.2.1.trans hx) (hy.trans h.2.2)
  by_cases h1 : t.kind = 1
  · simp only [if_neg h0, if_pos h1, Bool.and_eq_true] at h
    simpa only [IntervalSource.endpoints, show t.kind ≠ 2 by omega, if_false] using
      (cover_of_validated_bits h.1 h.2)
  by_cases h2 : t.kind = 2
  · simp only [if_neg h0, if_neg h1, if_pos h2, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [IntervalSource.endpoints, if_pos h2]
    apply cover_reflected_bits h.1.1.1.1 _ (tightlySorted_nodup h.1.1.1.2) h.1.2 h.2.1 h.2.2
    intro x hx
    apply List.mem_toFinset.mpr
    have hx' := List.mem_toFinset.mp hx
    rw [h.1.1.2] at hx'
    exact List.mem_of_mem_take hx'
  · simp [h0, h1, h2] at h

structure SweepInterval where
  source : IntervalSource
  multiple : ℕ
  shift : ℕ
  remainUntil : ℕ

def sweepIntervalOk (n s first stop : ℕ) (c : CoreCoverage) (a : SweepInterval) : Bool :=
  let (low, high) := a.source.endpoints c
  let slope := 2 * n - s + a.multiple
  a.source.ok n c &&
  decide (s ≤ 2 * n ∧ (a.multiple = 0 ∨ (a.multiple ∣ n ∧ a.multiple < n)) ∧
    (a.shift = 0 ∨ a.shift = n) ∧
    s ≤ high + a.shift + slope * first ∧ low + a.shift + slope * (stop - 1) ≤ s)

theorem sweepIntervalOk_closes {ss : List Slot} {first stop : ℕ}
    {c : CoreCoverage} {a : SweepInterval}
    (h : sweepIntervalOk (number (ss.map Slot.minimum)) (divisorSum (ss.map Slot.minimum))
      first stop c a = true) : HeadRangeClosed ss 0 first stop := by
  dsimp [sweepIntervalOk] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact headRange_squarefree rfl rfl h.2.1 h.2.2.1 h.2.2.2.1
    (intervalSource_ok_covers h.1) h.2.2.2.2.1 h.2.2.2.2.2

def bestSweepFrom (n s first stop : ℕ) (ss : List Slot)
    (c : CoreCoverage) (sources : List IntervalSource) : Option SweepInterval :=
  ([0, 1] ++ ss.map Slot.prime).foldl (fun best h =>
    sources.foldl (fun best source =>
      let (lo, hi) := IntervalSource.endpoints c source
      let slope := 2 * n - s + h
      [0, n].foldl (fun best shift =>
        let endAt := min stop ((s - (lo + shift)) / slope + 1)
        if first < endAt && lo + shift ≤ s && s ≤ hi + shift + slope * first &&
          (best.map SweepInterval.remainUntil).getD first < endAt
        then some ⟨source, h, shift, endAt⟩
        else best) best) best) none

def bestSweepInterval (n s first stop : ℕ) (ss : List Slot)
    (c : CoreCoverage) : Option SweepInterval :=
  (bestSweepFrom n s first stop ss c c.central).orElse (fun _ =>
    let runs := bitRuns (subsetBits c.small) (c.small.sum + 1)
    let sources := runs.map (fun (l, h) => ⟨1, l, h⟩) ++
      runs.map (fun (l, h) => ⟨2, l, h⟩)
    bestSweepFrom n s first stop ss c sources)

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def minimumAutoOk (fallback : ℕ → List ℕ) (b : Box) : Bool :=
  minimumOk fallback b || automaticWitnessOk b.minimum

theorem minimumAutoOk_closes {fallback : ℕ → List ℕ} {b : Box}
    (hnondef : 2 * number b.minimum ≤ divisorSum b.minimum)
    (h : minimumAutoOk fallback b = true) : b.Closed := by
  rcases Bool.or_eq_true_iff.mp h with hm | hw
  · exact minimumOk_closes hnondef hm
  · exact automaticWitnessOk_closes hw

def bestDeletionBound (ss : List Slot) (stop : ℕ) : Option (ℕ × ℕ) :=
  let fs := ss.map Slot.minimum
  (List.range ss.length).foldl (fun best i =>
    let ds := decrement fs i
    let z := number ds
    let t := divisorSum ds
    let d := 2 * z - t
    let jump := if d = 0 then stop else min stop (t / d + 1)
    if z < number fs && (best.map Prod.snd).getD 0 < jump then some (i, jump) else best) none

def sweepStep (fallback : ℕ → List ℕ) (ss : List Slot)
    (c : CoreCoverage) (first stop : ℕ) : Option ℕ :=
  let fs := ss.map Slot.minimum
  let n := number fs
  let s := divisorSum fs
  match bestSweepInterval n s first stop ss c with
  | some a =>
    if sweepIntervalOk n s first a.remainUntil c a then some a.remainUntil else none
  | none =>
    if first % 2 = 0 || first.minFac ≠ first then some (first + 1)
    else
      let b : Box := ⟨ss ++ [⟨first, 1, false⟩], first + 2, 0⟩
      if 2 * number b.minimum ≤ divisorSum b.minimum && minimumAutoOk fallback b
      then some (first + 1)
      else none

theorem sweepStep_sound {fallback : ℕ → List ℕ} {ss : List Slot}
    {c : CoreCoverage} {first stop next : ℕ}
    (h : sweepStep fallback ss c first stop = some next) :
    HeadRangeClosed ss 0 first next := by
  unfold sweepStep at h
  dsimp only at h
  split at h
  · next a ha =>
    split at h
    · have eq := Option.some.inj h
      rw [← eq]
      exact sweepIntervalOk_closes ‹_›
    · contradiction
  · split at h
    · next hc =>
      have eq := Option.some.inj h
      rw [← eq]
      apply headRange_single
      intro hp ho
      have hc' : first % 2 = 0 ∨ first.minFac ≠ first := by simpa using hc
      rcases hc' with he | hn
      · obtain ⟨k, hk⟩ := ho
        omega
      · exact (hn hp.minFac_eq).elim
    · split at h
      · next hb =>
        have eq := Option.some.inj h
        rw [← eq]
        apply headRange_single
        intro _ _
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
        exact minimumAutoOk_closes hb.1 hb.2
      · contradiction

def sweepReplay (fallback : ℕ → List ℕ) (ss : List Slot) (c : CoreCoverage)
    (stop : ℕ) : ℕ → ℕ → Bool
  | 0, first => decide (stop ≤ first)
  | fuel + 1, first =>
    if stop ≤ first then true
    else match sweepStep fallback ss c first stop with
    | none => false
    | some next => decide (first < next) && sweepReplay fallback ss c stop fuel next

theorem sweepReplay_sound {fallback : ℕ → List ℕ} {ss : List Slot}
    {c : CoreCoverage} {fuel first stop : ℕ}
    (h : sweepReplay fallback ss c stop fuel first = true) :
    HeadRangeClosed ss 0 first stop := by
  induction fuel generalizing first with
  | zero =>
    simp only [sweepReplay, decide_eq_true_eq] at h
    intro q hqlo hqhi
    omega
  | succ fuel ih =>
    rw [sweepReplay] at h
    split at h
    · intro q hqlo hqhi
      omega
    split at h
    · contradiction
    · next next hstep =>
      exact headRange_join (sweepStep_sound hstep) (ih (Bool.and_eq_true_iff.mp h).2)

def closeSweepOk (fallback : ℕ → List ℕ) (ss : List Slot) (fuel first stop : ℕ) : Bool :=
  let fs := ss.map Slot.minimum
  let c := makeCoverage fs
  match bestDeletionBound ss stop with
  | some (i, jump) =>
    if first < jump then
      let ds := decrement fs i
      let z := number ds
      let t := divisorSum ds
      decide (i < ss.length ∧ z < number fs ∧ (2 * z - t) * (jump - 1) ≤ t) &&
        sweepReplay fallback ss c stop fuel jump
    else sweepReplay fallback ss c stop fuel first
  | none => sweepReplay fallback ss c stop fuel first

theorem closeSweepOk_sound {fallback : ℕ → List ℕ} {ss : List Slot}
    {fuel first stop : ℕ} (h : closeSweepOk fallback ss fuel first stop = true) :
    HeadRangeClosed ss 0 first stop := by
  unfold closeSweepOk at h
  dsimp only at h
  split at h
  · next i jump heq =>
    split at h
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact headRange_join (headRange_decrement_nondeficient h.1.1 rfl rfl h.1.2.1 h.1.2.2)
        (sweepReplay_sound h.2)
    · exact sweepReplay_sound h
  · exact sweepReplay_sound h

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def nextThreshold (b : Box) : ℕ :=
  let n := number b.minimum
  let s := divisorSum b.minimum
  let bound := s / (2 * n - s)
  2 * ((bound + 1) / 2) + 1

theorem nextThreshold_odd (b : Box) : Odd (nextThreshold b) :=
  ⟨_, rfl⟩

theorem threshold_odd_product_le {b : Box} {q : ℕ} (hq : Odd q)
    (hlt : q < nextThreshold b)
    (hdef : divisorSum b.minimum < 2 * number b.minimum) :
    (2 * number b.minimum - divisorSum b.minimum) * q ≤ divisorSum b.minimum := by
  let d := 2 * number b.minimum - divisorSum b.minimum
  have hd : 0 < d := Nat.sub_pos_of_lt hdef
  let k := divisorSum b.minimum / d
  have hqk : q ≤ k := by
    obtain ⟨a, ha⟩ := hq
    change q < 2 * ((k + 1) / 2) + 1 at hlt
    omega
  exact (Nat.mul_le_mul_left d hqk).trans (Nat.mul_div_le _ _)

theorem sweep_threshold_closes {ss : List Slot} {p r : ℕ} {fallback : ℕ → List ℕ}
    (hdef : divisorSum (ss.map Slot.minimum) < 2 * number (ss.map Slot.minimum))
    (hcheck : r = 0 →
      let b : Box := ⟨ss, p, 1⟩
      closeSweepOk fallback ss 5000 p (nextThreshold b) = true)
    (hskip : (⟨ss, nextThreshold ⟨ss, p, r + 1⟩, r + 1⟩ : Box).Closed) :
    (⟨ss, p, r + 1⟩ : Box).Closed := by
  apply close_jump_next hskip
  intro q hp hq hprime ho
  cases r with
  | zero => exact closeSweepOk_sound (hcheck rfl) q hp hq hprime ho
  | succ r =>
    apply close_nondeficient_squarefree_prefix (Nat.succ_pos _)
    have hu := threshold_odd_product_le ho hq hdef
    have h := Nat.mul_le_mul_right q
      (show 2 * number (ss.map Slot.minimum) ≤
        2 * number (ss.map Slot.minimum) - divisorSum (ss.map Slot.minimum) +
          divisorSum (ss.map Slot.minimum) by omega)
    rw [Nat.add_mul] at h
    rw [Nat.mul_add, Nat.mul_one]
    exact le_trans h (Nat.add_le_add_right hu _)

def chooseWideSlot (b : Box) : Option ℕ :=
  let num := (b.slots.map Slot.upperNum).prod
  let den := (b.slots.map Slot.upperDen).prod
  let limit := if b.remaining = 1 then
      if num < 2 * den && (2 * den - 1) / (2 * den - num) - b.next < 20
      then b.next else 0
    else if b.remaining = 2 && 100 < b.next then b.next * b.next else b.next
  ((b.slots.zipIdx.filter (fun (s, _) => !s.fixed)).foldl
    (fun best (s, i) =>
      let key := s.prime ^ (s.exponent + 1)
      if (limit = 0 || b.remaining = 0 || key < limit) &&
        key < best.1
      then (key, some i) else best)
    (b.slots.foldl (fun n s => max n (s.prime ^ (s.exponent + 1) + 1)) 1, none)).2

def wideReplay (fallback : ℕ → List ℕ) (cut : Box → Bool) : ℕ → Box → Bool
  | 0, _ => false
  | fuel + 1, b =>
    if cut b then true
    else if 2 * number b.minimum ≤ divisorSum b.minimum then minimumAutoOk fallback b
    else if b.upperNum ≤ 2 * b.upperDen then true
    else if 0 < b.remaining && b.next < nextThreshold b then
      (if b.remaining = 1 then closeSweepOk fallback b.slots 5000 b.next (nextThreshold b) else true) &&
      wideReplay fallback cut fuel {b with next := nextThreshold b}
    else match (chooseWideSlot b).bind (fun i => b.slots[i]?.map (fun s => (i, s))) with
    | some (i, s) =>
      if s.fixed then false else
      wideReplay fallback cut fuel {b with slots := b.slots.set i {s with fixed := true}} &&
      wideReplay fallback cut fuel {b with slots := b.slots.set i {s with exponent := s.exponent + 1}}
    | none =>
      match b.remaining with
      | 0 => false
      | r + 1 =>
        wideReplay fallback cut fuel ⟨b.slots, b.next + 2, r + 1⟩ &&
        if b.next.minFac = b.next then
          wideReplay fallback cut fuel ⟨b.slots ++ [⟨b.next, 1, false⟩], b.next + 2, r⟩
        else true

theorem wideReplay_closes {fallback : ℕ → List ℕ} {cut : Box → Bool} {fuel : ℕ} {b : Box}
    (hcut : ∀ box, cut box = true → box.Closed)
    (hlo : 1 < b.next) (hodd : Odd b.next) (h : wideReplay fallback cut fuel b = true) :
    b.Closed := by
  induction fuel generalizing b with
  | zero => simp [wideReplay] at h
  | succ fuel ih =>
    rw [wideReplay] at h
    split at h
    · exact hcut b ‹_›
    split at h
    · exact minimumAutoOk_closes ‹_› h
    next hnondef =>
      split at h
      · exact close_of_upperNum_le hlo ‹_›
      split at h
      next hguard =>
        obtain ⟨hr, hnext⟩ : 0 < b.remaining ∧ b.next < nextThreshold b := by simpa using hguard
        obtain ⟨h₁, h₂⟩ := Bool.and_eq_true_iff.mp h
        rcases b with ⟨ss, p, r⟩
        cases r with
        | zero => exact (Nat.lt_irrefl 0 hr).elim
        | succ r =>
          have hnd : divisorSum (ss.map Slot.minimum) <
              2 * number (ss.map Slot.minimum) := Nat.lt_of_not_ge hnondef
          apply sweep_threshold_closes (fallback := fallback) hnd _ (ih (hlo.trans hnext) (nextThreshold_odd _) h₂)
          intro heq
          subst r
          simpa using h₁
      next =>
        split at h
        next i s hs =>
          have hi : b.slots[i]? = some s := by
            obtain ⟨j, _, hj⟩ := Option.bind_eq_some_iff.mp hs
            cases hg : b.slots[j]? <;> simp_all
          split at h
          · contradiction
          · have hf : s.fixed = false := by simp_all
            obtain ⟨h₁, h₂⟩ := Bool.and_eq_true_iff.mp h
            exact close_split_slot hi hf (ih hlo hodd h₁) (ih hlo hodd h₂)
        next =>
          rcases b with ⟨ss, p, r⟩
          cases r with
          | zero => contradiction
          | succ r =>
            obtain ⟨hskip, htake⟩ := Bool.and_eq_true_iff.mp h
            have hodd' : Odd (p + 2) := by
              obtain ⟨k, hk⟩ := hodd
              exact ⟨k + 1, by dsimp at hk; omega⟩
            have hlo' : 1 < p + 2 := by dsimp at hlo; omega
            apply close_split_next hodd (ih hlo' hodd' hskip)
            intro hp
            exact ih hlo' hodd' (by simpa only [if_pos hp.minFac_eq] using htake)

end OddWeirdSubproblems

namespace OddWeirdSubproblems

/-- A supplied seed and its adjoining weights certify an interval without
recomputing or sorting every proper divisor of the core. -/
structure LiteralInterval where
  seed : List ℕ
  growth : List ℕ
  low : ℕ
  seedHigh : ℕ
  multiple : ℕ
  shift : ℕ

def literalIntervalOk (n s first stop : ℕ) (a : LiteralInterval) : Bool :=
  let high := a.seedHigh + a.growth.sum
  let slope := 2 * n - s + a.multiple
  divisorListOk n (a.seed ++ a.growth) &&
  bitIntervalOk a.seed a.low a.seedHigh &&
  growIntervalOk a.low a.seedHigh a.growth &&
  decide (s ≤ 2 * n ∧ (a.multiple = 0 ∨ (a.multiple ∣ n ∧ a.multiple < n)) ∧
    (a.shift = 0 ∨ a.shift = n) ∧
    s ≤ high + a.shift + slope * first ∧ a.low + a.shift + slope * (stop - 1) ≤ s)

theorem literalIntervalOk_closes {ss : List Slot} {first stop : ℕ} {a : LiteralInterval}
    (h : literalIntervalOk (number (ss.map Slot.minimum)) (divisorSum (ss.map Slot.minimum))
      first stop a = true) : HeadRangeClosed ss 0 first stop := by
  simp only [literalIntervalOk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact headRange_squarefree rfl rfl h.2.1 h.2.2.1 h.2.2.2.1
    (cover_of_validated_growth h.1.1.1 h.1.1.2 h.1.2) h.2.2.2.2.1 h.2.2.2.2.2

inductive SweepAction where
  | nonprimitive (i stop : ℕ)
  | interval (stop : ℕ) (cert : LiteralInterval)
  | composite (stop : ℕ)
  | point (witness : List ℕ)

def SweepAction.stop (first : ℕ) : SweepAction → ℕ
  | .nonprimitive _ stop | .interval stop _ | .composite stop => stop
  | .point _ => first + 1

def sweepActionOk (ss : List Slot) (first : ℕ) : SweepAction → Bool
  | .nonprimitive i stop =>
    let fs := ss.map Slot.minimum
    let ds := decrement fs i
    let z := number ds
    let t := divisorSum ds
    decide (i < ss.length ∧ z < number fs ∧ (2 * z - t) * (stop - 1) ≤ t)
  | .interval stop cert =>
    let fs := ss.map Slot.minimum
    literalIntervalOk (number fs) (divisorSum fs) first stop cert
  | .composite stop =>
    (List.range (stop - first)).all
      (fun j => decide ((first + j) % 2 = 0) || !mayBeOddPrime (first + j))
  | .point ds =>
    let b : Box := ⟨ss ++ [⟨first, 1, false⟩], first + 2, 0⟩
    decide (2 * number b.minimum ≤ divisorSum b.minimum) &&
      minimumOk (fun _ => ds) b

theorem sweepActionOk_closes {ss : List Slot} {first : ℕ} {a : SweepAction}
    (h : sweepActionOk ss first a = true) : HeadRangeClosed ss 0 first (a.stop first) := by
  cases a with
  | nonprimitive i stop =>
    simp only [sweepActionOk, decide_eq_true_eq] at h
    exact headRange_decrement_nondeficient h.1 rfl rfl h.2.1 h.2.2
  | interval stop cert =>
    exact literalIntervalOk_closes h
  | composite stop =>
    simp only [sweepActionOk, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq,
      Bool.not_eq_true'] at h
    intro q hlo hhi hp ho
    change q < stop at hhi
    have hno := h (q - first) (List.mem_range.mpr (by omega))
    rw [show first + (q - first) = q by omega] at hno
    rcases hno with he | hnp
    · obtain ⟨k, hk⟩ := ho
      omega
    · exact (Bool.false_ne_true (hnp.symm.trans (mayBeOddPrime_of_prime hp))).elim
  | point ds =>
    simp only [sweepActionOk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact headRange_single (fun _ _ => minimumOk_closes h.1 h.2)

def literalSweepOk (ss : List Slot) (stop : ℕ) : ℕ → List SweepAction → Bool
  | first, [] => decide (stop ≤ first)
  | first, a :: acts =>
    sweepActionOk ss first a && literalSweepOk ss stop (a.stop first) acts

theorem literalSweepOk_closes {ss : List Slot} {first stop : ℕ} {acts : List SweepAction}
    (h : literalSweepOk ss stop first acts = true) : HeadRangeClosed ss 0 first stop := by
  induction acts generalizing first with
  | nil =>
    simp only [literalSweepOk, decide_eq_true_eq] at h
    intro q hlo hhi
    omega
  | cons a acts ih =>
    obtain ⟨ha, ht⟩ := Bool.and_eq_true_iff.mp h
    exact headRange_join (sweepActionOk_closes ha) (ih ht)

structure LiteralInputs where
  point : Box → List ℕ
  sweep : Box → List SweepAction

theorem literal_threshold_closes {ss : List Slot} {p r : ℕ} {acts : List SweepAction}
    (hdef : divisorSum (ss.map Slot.minimum) < 2 * number (ss.map Slot.minimum))
    (hcheck : r = 0 →
      let b : Box := ⟨ss, p, 1⟩
      literalSweepOk ss (nextThreshold b) p acts = true)
    (hskip : (⟨ss, nextThreshold ⟨ss, p, r + 1⟩, r + 1⟩ : Box).Closed) :
    (⟨ss, p, r + 1⟩ : Box).Closed := by
  apply close_jump_next hskip
  intro q hp hq hprime ho
  cases r with
  | zero => exact literalSweepOk_closes (hcheck rfl) q hp hq hprime ho
  | succ r =>
    apply close_nondeficient_squarefree_prefix (Nat.succ_pos _)
    have hu := threshold_odd_product_le ho hq hdef
    have h := Nat.mul_le_mul_right q
      (show 2 * number (ss.map Slot.minimum) ≤
        2 * number (ss.map Slot.minimum) - divisorSum (ss.map Slot.minimum) +
          divisorSum (ss.map Slot.minimum) by omega)
    rw [Nat.add_mul] at h
    rw [Nat.mul_add, Nat.mul_one]
    exact le_trans h (Nat.add_le_add_right hu _)

def literalReplay (inputs : LiteralInputs) (cut : Box → Bool) : ℕ → Box → Bool
  | 0, _ => false
  | fuel + 1, b =>
    if cut b then true
    else if 2 * number b.minimum ≤ divisorSum b.minimum then minimumOk (fun _ => inputs.point b) b
    else if b.upperNum ≤ 2 * b.upperDen then true
    else if 0 < b.remaining && b.next < nextThreshold b then
      (if b.remaining = 1 then literalSweepOk b.slots (nextThreshold b) b.next (inputs.sweep b) else true) &&
      literalReplay inputs cut fuel {b with next := nextThreshold b}
    else match (chooseWideSlot b).bind (fun i => b.slots[i]?.map (fun s => (i, s))) with
    | some (i, s) =>
      if s.fixed then false else
      literalReplay inputs cut fuel {b with slots := b.slots.set i {s with fixed := true}} &&
      literalReplay inputs cut fuel {b with slots := b.slots.set i {s with exponent := s.exponent + 1}}
    | none =>
      match b.remaining with
      | 0 => false
      | r + 1 =>
        literalReplay inputs cut fuel ⟨b.slots, b.next + 2, r + 1⟩ &&
        if mayBeOddPrime b.next then
          literalReplay inputs cut fuel ⟨b.slots ++ [⟨b.next, 1, false⟩], b.next + 2, r⟩
        else true

theorem literalReplay_closes {inputs : LiteralInputs} {cut : Box → Bool} {fuel : ℕ} {b : Box}
    (hcut : ∀ box, cut box = true → box.Closed)
    (hlo : 1 < b.next) (hodd : Odd b.next) (h : literalReplay inputs cut fuel b = true) :
    b.Closed := by
  induction fuel generalizing b with
  | zero => simp [literalReplay] at h
  | succ fuel ih =>
    rw [literalReplay] at h
    split at h
    · exact hcut b ‹_›
    split at h
    · exact minimumOk_closes ‹_› h
    next hnondef =>
      split at h
      · exact close_of_upperNum_le hlo ‹_›
      split at h
      next hguard =>
        obtain ⟨hr, hnext⟩ : 0 < b.remaining ∧ b.next < nextThreshold b := by simpa using hguard
        obtain ⟨h₁, h₂⟩ := Bool.and_eq_true_iff.mp h
        rcases b with ⟨ss, p, r⟩
        cases r with
        | zero => exact (Nat.lt_irrefl 0 hr).elim
        | succ r =>
          have hnd : divisorSum (ss.map Slot.minimum) <
              2 * number (ss.map Slot.minimum) := Nat.lt_of_not_ge hnondef
          apply literal_threshold_closes (acts := inputs.sweep ⟨ss, p, r + 1⟩) hnd _ (ih (hlo.trans hnext) (nextThreshold_odd _) h₂)
          intro heq
          subst r
          simpa using h₁
      next =>
        split at h
        next i s hs =>
          have hi : b.slots[i]? = some s := by
            obtain ⟨j, _, hj⟩ := Option.bind_eq_some_iff.mp hs
            cases hg : b.slots[j]? <;> simp_all
          split at h
          · contradiction
          · have hf : s.fixed = false := by simp_all
            obtain ⟨h₁, h₂⟩ := Bool.and_eq_true_iff.mp h
            exact close_split_slot hi hf (ih hlo hodd h₁) (ih hlo hodd h₂)
        next =>
          rcases b with ⟨ss, p, r⟩
          cases r with
          | zero => contradiction
          | succ r =>
            obtain ⟨hskip, htake⟩ := Bool.and_eq_true_iff.mp h
            have hodd' : Odd (p + 2) := by
              obtain ⟨k, hk⟩ := hodd
              exact ⟨k + 1, by dsimp at hk; omega⟩
            have hlo' : 1 < p + 2 := by dsimp at hlo; omega
            apply close_split_next hodd (ih hlo' hodd' hskip)
            intro hp
            exact ih hlo' hodd' (by simpa only [if_pos (mayBeOddPrime_of_prime hp)] using htake)

end OddWeirdSubproblems

namespace OddWeirdSubproblems

/-- Compute only divisors that could take part in a small subset sum. -/
def divisorsAtMost : Coordinates → ℕ → List ℕ
  | [], B => if 1 ≤ B then [1] else []
  | (p, e) :: fs, B =>
    (List.range (e + 1)).flatMap (fun i =>
      let w := p ^ i
      if w ≤ B then (divisorsAtMost fs (B / w)).map (fun d => d * w)
      else [])

def cappedExponent (p cap : ℕ) : ℕ → ℕ
  | 0 => 0
  | e + 1 => if p ^ (e + 1) ≤ cap then e + 1 else cappedExponent p cap e

def largestDivisorSearch : Coordinates → ℕ → ℕ
  | [], B => if B = 0 then 0 else 1
  | (p, e) :: fs, B =>
    if B = 0 then 0
    else if p ^ e * number fs ≤ B then p ^ e * number fs
    else if fs.isEmpty then p ^ cappedExponent p B e
    else
      let lo := cappedExponent p (B / number fs) e
      let hi := cappedExponent p B e
      (List.range (hi + 1 - lo)).foldl (fun best j =>
        let w := p ^ (lo + j)
        max best (w * largestDivisorSearch fs (B / w))) 0

/-- Select a large divisor without forming and sorting the divisor list.
Higher primes lead the exponent search, and a whole feasible tail returns
its product immediately. The returned weights are verified by the caller. -/
def largestDivisorUpTo (fs : Coordinates) (B : ℕ) : ℕ :=
  largestDivisorSearch fs.reverse B

/-- Suggest a small witness by subtracting descending divisors until the
remainder can be represented in the short, computed bitset. -/
def greedyWitness (fs : Coordinates) (seed : List ℕ) (bits : ℕ) :
    ℕ → ℕ → ℕ → Option (List ℕ)
  | 0, _, _ => none
  | fuel + 1, cap, target =>
    if target ≤ seed.sum && bits.testBit target then some (bitWitness seed target)
    else
      let d := largestDivisorUpTo fs (min cap target)
      if d ≤ seed.sum then none
      else
        (greedyWitness fs seed bits fuel (d - 1) (target - d)).map (d :: ·)

def sparseHintedWitness (fs : Coordinates) (slot h target : ℕ) : Option (List ℕ) := do
  let (p, _) ← fs[slot]?
  let rest := fs.eraseIdx slot
  let shift := h * p
  if target < shift then none else
    let ds := sortDivisors 20 (divisorsAtMost rest 1024)
    let seed := smallPrefix 1024 ds
    let target := target - shift
    let chosen ← greedyWitness rest seed (subsetBits seed) 64 (number rest) target
    pure (if shift = 0 then chosen else shift :: chosen)

def sparseHintedWitnessOk (fs : Coordinates) (slot h : ℕ) : Bool :=
  let n := number fs
  let s := divisorSum fs
  match sparseHintedWitness fs slot h (s - 2 * n) with
  | some ds => witnessOk n s (sortDivisors 30 ds)
  | none => false

theorem sparseHintedWitnessOk_closes {b : Box} {slot h : ℕ}
    (hok : sparseHintedWitnessOk b.minimum slot h = true) : b.Closed := by
  unfold sparseHintedWitnessOk at hok
  dsimp only at hok
  split at hok
  · exact witnessOk_closes hok
  · contradiction

/-- Suggest only those adjoining weights needed by a specified interval
endpoint. The additional strict lower bound keeps them above the seed. -/
def sparseGrowth (fs : Coordinates) (low seedMax target : ℕ) :
    ℕ → ℕ → ℕ → Option (List ℕ)
  | 0, _, _ => none
  | fuel + 1, hi, previous =>
    if target ≤ hi then some [] else
      let bound := hi + 1 - low
      let value := largestDivisorUpTo fs (min (number fs - 1) bound)
      if value ≤ seedMax || value ≤ previous then none
      else (sparseGrowth fs low seedMax target fuel (hi + value) value).map (value :: ·)

def sparseIntervalWitness (fs : Coordinates) (target : ℕ) : Option (List ℕ) :=
  let ds := sortDivisors 20 (divisorsAtMost fs 1024)
  let seed := smallPrefix 1024 ds
  let bits := subsetBits seed
  if target ≤ seed.sum && bits.testBit target then some (bitWitness seed target)
  else
    let low := effectiveLow bits seed.sum
    let high := seed.sum - low
    if target < low || high < low then none else do
      let growth ← sparseGrowth fs low (seed.getLast?.getD 0) target 64 high 0
      let (large, rest) := peelGrowth low growth.reverse (high + growth.sum) target
      if bits.testBit rest then some (large ++ bitWitness seed rest) else none

def sparseWitnessHint (fs : Coordinates) (slot h target : ℕ) : Option (List ℕ) := do
  let (p, _) ← fs[slot]?
  let shift := p * h
  if target < shift then none else
    let ds ← sparseIntervalWitness (fs.eraseIdx slot) (target - shift)
    pure (if shift = 0 then ds else shift :: ds)

end OddWeirdSubproblems

namespace OddWeirdSubproblems

/-- Recover a short interval proof using a selected shift and endpoint. The
arithmetic checker subsequently verifies every generated divisor and sum. -/
def recoverInterval (fs : Coordinates) (first h shift : ℕ) : Option LiteralInterval :=
  let n := number fs
  let s := divisorSum fs
  let d := 2 * n - s
  let candidates := sortDivisors 20 (divisorsAtMost fs (min 1024 (n - 1)))
  let seed := smallPrefix 1024 candidates
  let lo := effectiveLow (subsetBits seed) seed.sum
  let hi := seed.sum - lo
  let goal := s - (shift + (d + h) * first)
  (sparseGrowth fs lo (seed.getLast?.getD 0) goal 96 hi 0).map (fun ds =>
    ⟨seed, ds, lo, hi, h, shift⟩)

theorem recoverInterval_closes {ss : List Slot} {first stop h shift : ℕ}
    (hcheck : match recoverInterval (ss.map Slot.minimum) first h shift with
      | none => false
      | some cert => sweepActionOk ss first (.interval stop cert)) :
    HeadRangeClosed ss 0 first stop := by
  split at hcheck
  · contradiction
  · exact sweepActionOk_closes (by simpa using hcheck)

def packedIndexWitness (fs : Coordinates) (slot h : ℕ) : List ℕ :=
  let n := number fs
  let s := divisorSum fs
  (sparseHintedWitness fs slot h (s - 2 * n)).getD [] |> sortDivisors 30

end OddWeirdSubproblems

namespace OddWeirdSubproblems

/-- Read a bounded base-128 natural number from a byte list. -/
def readVarNat : ℕ → List ℕ → Option (ℕ × List ℕ)
  | 0, _ | _, [] => none
  | fuel + 1, b :: bs =>
    if b < 128 then some (b, bs)
    else (readVarNat fuel bs).map (fun (n, rest) => (b % 128 + 128 * n, rest))

def readNatList : ℕ → List ℕ → Option (List ℕ × List ℕ)
  | 0, rest => some ([], rest)
  | n + 1, bs => do
    let (value, tail) ← readVarNat 64 bs
    let (values, rest) ← readNatList n tail
    pure (value :: values, rest)

def readLengthPrefixed (bs : List ℕ) : Option (List ℕ × List ℕ) := do
  let (n, rest) ← readVarNat 64 bs
  readNatList n rest

def bytesFromNat : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n + 1, v => v % 256 :: bytesFromNat n (v / 256)

/-- Read a backward copy with the overlap semantics used by LZ compressors. -/
def copyFromBuffer : ℕ → ℕ → Array ℕ → Option (Array ℕ)
  | 0, _, buf => some buf
  | n + 1, distance, buf => do
    if distance = 0 || buf.size < distance then none else
      let byte ← buf[buf.size - distance]?
      copyFromBuffer n distance (buf.push byte)

/-- Token 0 is followed by a run of literal bytes, token 1 by a backward
distance and copy length. The checker validates the resulting mathematical
certificates regardless of how this byte stream was produced. -/
def expandTokens : ℕ → List ℕ → Array ℕ → Option (Array ℕ)
  | 0, [], buf => some buf
  | 0, _, _ => none
  | _ + 1, [], buf => some buf
  | fuel + 1, token :: rest, buf =>
    if token = 0 then do
      let (n, bytes) ← readVarNat 64 rest
      if bytes.length < n then none else
        expandTokens fuel (bytes.drop n) (buf ++ (bytes.take n).toArray)
    else if token = 1 then do
      let (distance, rest) ← readVarNat 64 rest
      let (n, tail) ← readVarNat 64 rest
      let buf ← copyFromBuffer n distance buf
      expandTokens fuel tail buf
    else none

private def readLittleBytes : ℕ → List ℕ → Option (ℕ × List ℕ)
  | 0, data => some (0, data)
  | _ + 1, [] => none
  | n + 1, byte :: data => do
    let (value, rest) ← readLittleBytes n data
    pure (byte + (value <<< 8), rest)

private def copyPacked (value size distance count : ℕ) : ℕ :=
  let chunk := value >>> (8 * (size - distance))
  let wholeBytes := count - count % distance
  let whole := chunk * (((1 <<< (8 * wholeBytes)) - 1) / ((1 <<< (8 * distance)) - 1))
  let remainder := chunk % (1 <<< (8 * (count % distance)))
  whole + (remainder <<< (8 * wholeBytes))

/-- Use one packed natural for the backward-copy window. The replay checks
the values obtained from the decoder before using them as certificates. -/
def expandPackedTokens : ℕ → List ℕ → ℕ → ℕ → Option (List ℕ)
  | _, [], size, value => some (bytesFromNat size value)
  | 0, _ :: _, _, _ => none
  | fuel + 1, token :: data, size, value => do
    let (arg, rest) ← readVarNat 64 data
    if token = 0 then
      let (chunk, rest) ← readLittleBytes arg rest
      expandPackedTokens fuel rest (size + arg) (value + (chunk <<< (8 * size)))
    else if token = 1 && 0 < arg && arg ≤ size then
      let (count, rest) ← readVarNat 64 rest
      let chunk := copyPacked value size arg count
      expandPackedTokens fuel rest (size + count) (value + (chunk <<< (8 * size)))
    else none

def decodeInterval (bs : List ℕ) : Option (LiteralInterval × List ℕ) := do
  let (seed, rest) ← readLengthPrefixed bs
  let (growth, rest) ← readLengthPrefixed rest
  let (lo, rest) ← readVarNat 64 rest
  let (hi, rest) ← readVarNat 64 rest
  let (h, rest) ← readVarNat 64 rest
  let (c, rest) ← readVarNat 64 rest
  pure (⟨seed, growth, lo, hi, h, c⟩, rest)

def decodeSweepAction : List ℕ → Option (SweepAction × List ℕ)
  | [] => none
  | 0 :: rest => do
    let (i, rest) ← readVarNat 64 rest
    let (stop, rest) ← readVarNat 64 rest
    pure (.nonprimitive i stop, rest)
  | 1 :: rest => do
    let (stop, rest) ← readVarNat 64 rest
    let (cert, rest) ← decodeInterval rest
    pure (.interval stop cert, rest)
  | 2 :: rest => do
    let (stop, rest) ← readVarNat 64 rest
    pure (.composite stop, rest)
  | 3 :: rest => do
    let (ds, rest) ← readLengthPrefixed rest
    pure (.point ds, rest)
  | _ => none

def decodeSweep : ℕ → List ℕ → Option (List SweepAction × List ℕ)
  | 0, rest => some ([], rest)
  | n + 1, bs => do
    let (action, rest) ← decodeSweepAction bs
    let (actions, rest) ← decodeSweep n rest
    pure (action :: actions, rest)

def decodeWitnessRows : ℕ → ℕ → List ℕ → Option (List (ℕ × List ℕ) × List ℕ)
  | 0, _, rest => some ([], rest)
  | count + 1, previous, bs => do
    let (delta, rest) ← readVarNat 64 bs
    let value := previous + delta
    let (ds, rest) ← readLengthPrefixed rest
    let (rows, rest) ← decodeWitnessRows count value rest
    pure ((value, ds) :: rows, rest)

def decodeSweepRows :
    ℕ → ℕ → List ℕ → Option (List ((ℕ × ℕ) × List SweepAction) × List ℕ)
  | 0, _, rest => some ([], rest)
  | count + 1, previous, bs => do
    let (delta, rest) ← readVarNat 64 bs
    let value := previous + delta
    let (first, rest) ← readVarNat 64 rest
    let (size, rest) ← readVarNat 64 rest
    let (acts, rest) ← decodeSweep size rest
    let (rows, rest) ← decodeSweepRows count value rest
    pure (((value, first), acts) :: rows, rest)

/-- The typed checker receives the decoded data and verifies every rule. A
missing row gives an empty payload and can pass only when that payload itself
justifies the requested closure. -/
def unpackedInputs (raw : List ℕ) : Option LiteralInputs := do
  let (pointCount, rest) ← readVarNat 64 raw
  let (points, rest) ← decodeWitnessRows pointCount 0 rest
  let (sweepCount, rest) ← readVarNat 64 rest
  let (sweeps, []) ← decodeSweepRows sweepCount 0 rest | none
  pure ⟨fun b => (points.lookup (number b.minimum)).getD [],
    fun b => (sweeps.lookup (number b.minimum, b.next)).getD []⟩

def packedInputs (count value : ℕ) : Option LiteralInputs := do
  let data ← expandTokens count (bytesFromNat count value) #[]
  unpackedInputs data.toList

end OddWeirdSubproblems

namespace OddWeirdSubproblems

/-- Return the largest weight at most the cap and the unexamined tail. -/
def takeLargestWeight (cap : ℕ) : List ℕ → ℕ → ℕ × List ℕ
  | [], best => (best, [])
  | d :: ds, best =>
    if d ≤ cap then takeLargestWeight cap ds d else (best, d :: ds)

def scanGrowth (low target : ℕ) : ℕ → ℕ → List ℕ → Option (List ℕ)
  | 0, _, _ => none
  | fuel + 1, high, ds =>
    if target ≤ high then some []
    else
      let (d, rest) := takeLargestWeight (high + 1 - low) ds 0
      if d = 0 then none
      else (scanGrowth low target fuel (high + d) rest).map (d :: ·)

/-- Reuse the sorted divisor list across all growth steps of one interval.
The caller checks the resulting weights and overlap inequalities. -/
def sortedGrowth (fs : Coordinates) (low seedMax target high : ℕ) : Option (List ℕ) :=
  if target ≤ high then some [] else
    let ds := (sortedDivisors fs).dropWhile (· ≤ seedMax)
    scanGrowth low target 96 high (ds.takeWhile (· < number fs))

end OddWeirdSubproblems

namespace OddWeirdSubproblems

/-- Decode the factor and shift hint for a sparse point witness. -/
def decodePoint (b : Box) (data : List ℕ) : Option (List ℕ × List ℕ) := do
  let (tag, rest) ← readVarNat 64 data
  let i := tag / 8
  let j := tag % 8
  let fs := b.minimum
  let h := if j < 2 then j else ((fs.eraseIdx i)[j - 2]?.map Prod.fst).getD 0
  pure (packedIndexWitness fs i h, rest)

/-- The old rules close a minimum without using a payload when the number
is perfect, an extension is required, or a deletion is nondeficient. -/
def minimumNeedsWitness (b : Box) : Bool := !minimumOk (fun _ => []) b

structure PointReplay where
  verify : Box → List ℕ → Option (List ℕ)
  sound : ∀ {b data tail}, verify b data = some tail → b.Closed

def PointReplay.ofDivisors (read : Box → List ℕ → Option (List ℕ × List ℕ)) : PointReplay where
  verify b data := do
    let (ds, tail) ← read b data
    if witnessOk (number b.minimum) (divisorSum b.minimum) ds then some tail else none
  sound := by
    intro b data tail h
    obtain ⟨⟨ds, tail'⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
    dsimp only at h
    split at h
    · exact witnessOk_closes ‹_›
    · contradiction

def consumeMinimum (checkPoint : PointReplay) (b : Box) (data : List ℕ) : Option (List ℕ) :=
  if minimumNeedsWitness b then checkPoint.verify b data else some data

theorem consumeMinimum_closes
    {readPoint : PointReplay} {b : Box} {data tail : List ℕ}
    (hnd : 2 * number b.minimum ≤ divisorSum b.minimum)
    (h : consumeMinimum readPoint b data = some tail) : b.Closed := by
  unfold consumeMinimum minimumNeedsWitness at h
  split at h
  · exact readPoint.sound h
  · next hn =>
    have hm : minimumOk (fun _ => []) b = true := by simpa using hn
    exact minimumOk_closes hnd hm

def divisorOfRank (rank : ℕ) (xs : Coordinates) : ℕ :=
  let result := xs.reverse.foldl (fun (r, value) (p, e) =>
    (r / (e + 1), value * p ^ (r % (e + 1)))) (rank, 1)
  result.2

def rankDivisorList (fs : Coordinates) (gaps : List ℕ) : List ℕ :=
  let result := gaps.foldl (fun (previous, ds) gap =>
    let rank := previous + gap
    (rank, divisorOfRank (rank - 1) fs :: ds)) (0, [])
  sortDivisors 20 result.2

def decodeRankDivisors (fs : Coordinates) (bs : List ℕ) :
    Option (List ℕ × List ℕ) := do
  let (ds, rest) ← readLengthPrefixed bs
  pure (rankDivisorList fs ds, rest)

def decodeStreamAction (b : Box) (first top : ℕ) (bs : List ℕ) :
    Option (SweepAction × List ℕ) := do
  let (tag, rest) ← readVarNat 64 bs
  if tag = 0 then
    let (gap, rest) ← readVarNat 64 rest
    pure (.composite (first + gap), rest)
  else if tag = 1 then
    let (ds, rest) ← decodeRankDivisors (b.minimum ++ [(first, 1)]) rest
    pure (.point ds, rest)
  else
    let selector := (tag - 2) / 2
    let useCore := selector % 2
    let j := selector / 2
    let h := if j < 2 then j else (b.slots[j - 2]?.map Slot.prime).getD 0
    let n := number b.minimum
    let s := divisorSum b.minimum
    let shift := if useCore = 0 then 0 else n
    let candidates := sortDivisors 20 (divisorsAtMost b.minimum (min 1024 (n - 1)))
    let seed := smallPrefix 1024 candidates
    let lo := effectiveLow (subsetBits seed) seed.sum
    let hi := seed.sum - lo
    let slope := 2 * n - s + h
    let stop := min top ((s - shift - lo) / slope + 1)
    if (tag - 2) % 2 = 0 then
      let goal := s - (shift + slope * first)
      let ds ← sortedGrowth b.minimum lo (seed.getLast?.getD 0) goal hi
      pure (.interval stop ⟨seed, ds, lo, hi, h, shift⟩, rest)
    else
      let (ds, rest) ← decodeRankDivisors b.minimum rest
      pure (.interval stop ⟨seed, ds, lo, hi, h, shift⟩, rest)

abbrev SweepReader := Box → ℕ → ℕ → List ℕ → Option (SweepAction × List ℕ)

structure SweepVerifier where
  run : Box → ℕ → ℕ → List ℕ → Option (ℕ × List ℕ)
  sound : ∀ {b first top data stop tail}, run b first top data = some (stop, tail) →
    HeadRangeClosed b.slots 0 first stop

def SweepVerifier.ofActions (reader : SweepReader) : SweepVerifier where
  run b first top data := do
    let (a, rest) ← reader b first top data
    if sweepActionOk b.slots first a then some (a.stop first, rest) else none
  sound := by
    intro b first top data stop tail h
    obtain ⟨⟨a, rest⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
    dsimp only at h
    split at h
    · have he : a.stop first = stop := by simpa using congrArg (Option.map Prod.fst) h
      exact he ▸ sweepActionOk_closes ‹_›
    · contradiction

def consumeSweep (readSweep : SweepVerifier) (b : Box) (stop : ℕ) : ℕ → ℕ → List ℕ → Option (List ℕ)
  | 0, first, data => if stop ≤ first then some data else none
  | fuel + 1, first, data =>
    if stop ≤ first then none else do
      let (next, rest) ← readSweep.run b first stop data
      if first < next then
        consumeSweep readSweep b stop fuel next rest
      else none

theorem consumeSweep_closes {readSweep : SweepVerifier} {b : Box} {stop fuel first : ℕ}
    {data tail : List ℕ} (h : consumeSweep readSweep b stop fuel first data = some tail) :
    HeadRangeClosed b.slots 0 first stop := by
  induction fuel generalizing first data with
  | zero =>
    simp only [consumeSweep] at h
    split at h
    · intro q hlo hhi
      omega
    · contradiction
  | succ fuel ih =>
    simp only [consumeSweep] at h
    split at h
    · contradiction
    · next hl =>
      obtain ⟨⟨next, rest⟩, ha, h⟩ := Option.bind_eq_some_iff.mp h
      dsimp only at h
      split at h
      · exact headRange_join (readSweep.sound ha) (ih h)
      · contradiction

def consumeWholeSweep (readSweep : SweepVerifier) (b : Box) (stop : ℕ) (data : List ℕ) : Option (List ℕ) := do
  let (count, rest) ← readVarNat 64 data
  match bestDeletionBound b.slots stop with
  | some (i, jump) =>
    if b.next < jump then
      if sweepActionOk b.slots b.next (.nonprimitive i jump) then
        consumeSweep readSweep b stop count jump rest
      else none
    else consumeSweep readSweep b stop count b.next rest
  | none => consumeSweep readSweep b stop count b.next rest

theorem consumeWholeSweep_closes {readSweep : SweepVerifier} {b : Box} {stop : ℕ} {data tail : List ℕ}
    (h : consumeWholeSweep readSweep b stop data = some tail) : HeadRangeClosed b.slots 0 b.next stop := by
  unfold consumeWholeSweep at h
  cases hd : readVarNat 64 data with
  | none => simp [hd] at h
  | some row =>
    obtain ⟨count, rest⟩ := row
    rw [hd] at h
    dsimp only at h
    split at h
    · next i jump heq =>
      split at h
      · split at h
        · exact headRange_join (sweepActionOk_closes (a := .nonprimitive i jump) ‹_›) (consumeSweep_closes h)
        · contradiction
      · exact consumeSweep_closes h
    · exact consumeSweep_closes h

structure BranchPruning where
  verify : Box → List ℕ → Option (Bool × List ℕ)
  sound : ∀ {b data tail}, verify b data = some (true, tail) → b.Closed

def BranchPruning.none : BranchPruning where
  verify _ data := some (false, data)
  sound := by
    intro _ _ _ h
    simp at h

def streamReplay (readPoint : PointReplay) (readSweep : SweepVerifier)
    (prune : BranchPruning) (cut : Box → Bool) : ℕ → Box → List ℕ → Option (List ℕ)
  | 0, _, _ => none
  | fuel + 1, b, data =>
    if cut b then some data
    else do
      let (closed, data) ← prune.verify b data
      if closed then some data
      else if 2 * number b.minimum ≤ divisorSum b.minimum then consumeMinimum readPoint b data
      else if b.upperNum ≤ 2 * b.upperDen then some data
      else if 0 < b.remaining && b.next < nextThreshold b then
        (if b.remaining = 1 then consumeWholeSweep readSweep b (nextThreshold b) data else some data).bind
          (streamReplay readPoint readSweep prune cut fuel {b with next := nextThreshold b})
      else match (chooseWideSlot b).bind (fun i => b.slots[i]?.map (fun s => (i, s))) with
      | some (i, s) => do
        if s.fixed then none else
          let data ← streamReplay readPoint readSweep prune cut fuel {b with slots := b.slots.set i {s with fixed := true}} data
          streamReplay readPoint readSweep prune cut fuel {b with slots := b.slots.set i {s with exponent := s.exponent + 1}} data
      | none =>
        match b.remaining with
        | 0 => none
        | r + 1 => do
          let data ← streamReplay readPoint readSweep prune cut fuel ⟨b.slots, b.next + 2, r + 1⟩ data
          if mayBeOddPrime b.next then
            streamReplay readPoint readSweep prune cut fuel ⟨b.slots ++ [⟨b.next, 1, false⟩], b.next + 2, r⟩ data
          else some data

theorem stream_threshold_closes {readSweep : SweepVerifier} {ss : List Slot} {p r : ℕ} {data : List ℕ}
    (hdef : divisorSum (ss.map Slot.minimum) < 2 * number (ss.map Slot.minimum))
    (hcheck : r = 0 → ∃ tail,
      let b : Box := ⟨ss, p, 1⟩
      consumeWholeSweep readSweep b (nextThreshold b) data = some tail)
    (hskip : (⟨ss, nextThreshold ⟨ss, p, r + 1⟩, r + 1⟩ : Box).Closed) :
    (⟨ss, p, r + 1⟩ : Box).Closed := by
  apply close_jump_next hskip
  intro q hp hq hprime ho
  cases r with
  | zero =>
    obtain ⟨tail, h⟩ := hcheck rfl
    exact consumeWholeSweep_closes h q hp hq hprime ho
  | succ r =>
    apply close_nondeficient_squarefree_prefix (Nat.succ_pos _)
    have hu := threshold_odd_product_le ho hq hdef
    have h := Nat.mul_le_mul_right q
      (show 2 * number (ss.map Slot.minimum) ≤
        2 * number (ss.map Slot.minimum) - divisorSum (ss.map Slot.minimum) +
          divisorSum (ss.map Slot.minimum) by omega)
    rw [Nat.add_mul] at h
    rw [Nat.mul_add, Nat.mul_one]
    exact le_trans h (Nat.add_le_add_right hu _)

theorem streamReplay_closes
    {readPoint : PointReplay} {readSweep : SweepVerifier} {prune : BranchPruning} {cut : Box → Bool} {fuel : ℕ} {b : Box} {data tail : List ℕ}
    (hcut : ∀ box, cut box = true → box.Closed)
    (hlo : 1 < b.next) (hodd : Odd b.next) (h : streamReplay readPoint readSweep prune cut fuel b data = some tail) :
    b.Closed := by
  induction fuel generalizing b data tail with
  | zero => simp [streamReplay] at h
  | succ fuel ih =>
    rw [streamReplay] at h
    split at h
    · exact hcut b ‹_›
    obtain ⟨⟨closed, input⟩, hprune, h⟩ := Option.bind_eq_some_iff.mp h
    cases closed
    · simp only [Bool.false_eq_true, if_false] at h
      split at h
      · exact consumeMinimum_closes ‹_› h
      next hnondef =>
        split at h
        · exact close_of_upperNum_le hlo ‹_›
        split at h
        next hguard =>
          obtain ⟨hr, hnext⟩ : 0 < b.remaining ∧ b.next < nextThreshold b := by simpa using hguard
          rcases b with ⟨ss, p, r⟩
          cases r with
          | zero => exact (Nat.lt_irrefl 0 hr).elim
          | succ r =>
            have hnd : divisorSum (ss.map Slot.minimum) <
                2 * number (ss.map Slot.minimum) := Nat.lt_of_not_ge hnondef
            have hs : ∃ mid,
                (if r + 1 = 1 then consumeWholeSweep readSweep ⟨ss, p, r + 1⟩
                  (nextThreshold ⟨ss, p, r + 1⟩) input else some input) = some mid ∧
                streamReplay readPoint readSweep prune cut fuel ⟨ss, nextThreshold ⟨ss, p, r + 1⟩, r + 1⟩ mid = some tail :=
              Option.bind_eq_some_iff.mp h
            obtain ⟨mid, hmid, hend⟩ := hs
            apply stream_threshold_closes (readSweep := readSweep) (data := input) hnd _
              (ih (hlo.trans hnext) (nextThreshold_odd _) hend)
            intro heq
            subst r
            exact ⟨mid, by simpa using hmid⟩
        next =>
          split at h
          next i s hs =>
            have hi : b.slots[i]? = some s := by
              obtain ⟨j, _, hj⟩ := Option.bind_eq_some_iff.mp hs
              cases hg : b.slots[j]? <;> simp_all
            split at h
            · contradiction
            · have hf : s.fixed = false := by simp_all
              obtain ⟨mid, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
              exact close_split_slot hi hf (ih hlo hodd h₁) (ih hlo hodd h₂)
          next =>
            rcases b with ⟨ss, p, r⟩
            cases r with
            | zero => contradiction
            | succ r =>
              obtain ⟨mid, hskip, htake⟩ := Option.bind_eq_some_iff.mp h
              have hodd' : Odd (p + 2) := by
                obtain ⟨k, hk⟩ := hodd
                exact ⟨k + 1, by dsimp at hk; omega⟩
              have hlo' : 1 < p + 2 := by dsimp at hlo; omega
              apply close_split_next hodd (ih hlo' hodd' hskip)
              intro hp
              exact ih hlo' hodd' (by simpa only [if_pos (mayBeOddPrime_of_prime hp)] using htake)
    · exact prune.sound hprune

theorem checkUnpackedBlock
    {readPoint : PointReplay} {b : Box} {cut : Box → Bool} {fuel count value : ℕ}
    (readSweep : SweepVerifier := .ofActions decodeStreamAction)
    (prune : BranchPruning := .none)
    (hcut : ∀ box, cut box = true → box.Closed) (hlo : 1 < b.next) (hodd : Odd b.next)
    (h : streamReplay readPoint readSweep prune cut fuel b (bytesFromNat count value) = some []) : b.Closed :=
  streamReplay_closes hcut hlo hodd h

def checkPacked (readPoint : PointReplay) (readSweep : SweepVerifier)
    (cut : Box → Bool) (fuel : ℕ) (b : Box) (count value : ℕ) (prune : BranchPruning := .none) : Bool :=
  match expandPackedTokens count (bytesFromNat count value) 0 0 with
  | none => false
  | some raw => match streamReplay readPoint readSweep prune cut fuel b raw with
    | some [] => true
    | _ => false

theorem checkPackedBlock
    {readPoint : PointReplay} {b : Box} {cut : Box → Bool} {fuel count value : ℕ}
    (readSweep : SweepVerifier := .ofActions decodeStreamAction)
    (prune : BranchPruning := .none)
    (hcut : ∀ box, cut box = true → box.Closed) (hlo : 1 < b.next) (hodd : Odd b.next)
    (h : checkPacked readPoint readSweep cut fuel b count value prune = true) : b.Closed := by
  unfold checkPacked at h
  split at h
  · contradiction
  · split at h
    · exact streamReplay_closes hcut hlo hodd ‹_›
    · contradiction

inductive ClosedCuts : List Box → Prop
  | nil : ClosedCuts []
  | cons {b : Box} {bs : List Box} : b.Closed → ClosedCuts bs → ClosedCuts (b :: bs)

theorem ClosedCuts.closedOfMem {cuts : List Box} (hcuts : ClosedCuts cuts)
    {b : Box} (hb : b ∈ cuts) : b.Closed := by
  induction hcuts with
  | nil => simp at hb
  | cons hd _ ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hd
    · exact ih hb

theorem checkPackedCuts {readPoint : PointReplay} {readSweep : SweepVerifier}
    {b : Box} {cuts : List Box} (prune : BranchPruning) (hcuts : ClosedCuts cuts)
    (fuel count value : ℕ) (hlo : 1 < b.next) (hodd : Odd b.next)
    (h : checkPacked readPoint readSweep (fun q => cuts.any (boxEqual q)) fuel b count value prune = true) :
    b.Closed := by
  apply checkPackedBlock (readSweep := readSweep) (prune := prune) _ hlo hodd h
  intro q hq
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp hq
  have hqc := (boxEqual_iff_eq q c).mp he
  subst c
  exact hcuts.closedOfMem hc

end OddWeirdSubproblems

/-! Replay a compressed bounded search with certified range and size pruning. -/

namespace OddWeirdSubproblems

/-- An odd endpoint past every fresh prime that can fit under the cutoff. -/
def boundedSweepEnd (B : ℕ) (b : Box) : ℕ :=
  min (nextThreshold b) (2 * (((B - 1) / number b.minimum + 1) / 2) + 1)

private theorem boundedSweep_closes {B : ℕ} {b : Box} {data tail : List ℕ}
    {readSweep : SweepVerifier}
    (h : consumeWholeSweep readSweep b (boundedSweepEnd B b) data = some tail)
    (hrest : ({b with next := nextThreshold b} : Box).ClosedBelow B)
    (hr : b.remaining = 1) : b.ClosedBelow B := by
  rcases b with ⟨ss, p, r⟩
  change r = 1 at hr
  subst r
  apply closeBelow_jump_next (stop := nextThreshold ⟨ss, p, 1⟩) hrest
  intro q hq hqhi hp hodd
  by_cases hcut : q < boundedSweepEnd B ⟨ss, p, 1⟩
  · exact closedBelow_of_closed (consumeWholeSweep_closes h q hq hcut hp hodd) B
  · intro xs ys hm hv hlt _ _
    have hy : ys = [] := List.length_eq_zero_iff.mp hm.2.2
    have hx := Nat.le_of_dvd (number_pos (primeCoordinates_left hv).1) (minimum_dvd hm.1)
    have hmpos : 0 < number (ss.map Slot.minimum) := by
      have hvalid := minimum_valid hm.1 (primeCoordinates_left hv)
      simp only [List.map_append, List.map_cons, List.map_nil] at hvalid
      exact number_pos (primeCoordinates_left hvalid).1
    have hu : (B - 1) / number (ss.map Slot.minimum) < q := by
      unfold boundedSweepEnd at hcut
      change ¬ q < min (nextThreshold ⟨ss, p, 1⟩)
        (2 * (((B - 1) / number (ss.map Slot.minimum) + 1) / 2) + 1) at hcut
      omega
    have hsize := Nat.lt_mul_of_div_lt hu hmpos
    rw [Nat.mul_comm] at hsize
    dsimp only at hx
    rw [List.map_append] at hx
    change number (ss.map Slot.minimum ++ [(q, 1)]) ≤ number xs at hx
    rw [number_append, number_cons] at hx
    simp only [pow_one, show number [] = 1 from rfl, mul_one] at hx
    simp only [hy, List.append_nil] at hlt
    omega

private theorem thresholdSweep_closes {B : ℕ} {b : Box} {data tail : List ℕ}
    {readSweep : SweepVerifier} {limited : Bool}
    (h : consumeWholeSweep readSweep b
      (if limited then boundedSweepEnd B b else nextThreshold b) data = some tail)
    (hrest : ({b with next := nextThreshold b} : Box).ClosedBelow B)
    (hr : b.remaining = 1) : b.ClosedBelow B := by
  cases limited
  · rcases b with ⟨ss, p, r⟩
    change r = 1 at hr
    subst r
    apply closeBelow_jump_next (stop := nextThreshold ⟨ss, p, 1⟩) hrest
    intro q hq hqhi hp hodd
    exact closedBelow_of_closed (consumeWholeSweep_closes h q hq hqhi hp hodd) B
  · exact boundedSweep_closes h hrest hr

/-- The ranked floor proves the search always moves past skipped composite
heads, even when the scan exhausts its rotation budget. -/
private theorem closeBelow_skip_composites {ss : List Slot} {B p r fuel : ℕ}
    (hodd : Odd p) (h : (⟨ss, firstAllowedOdd p fuel, r + 1⟩ : Box).ClosedBelow B) :
    (⟨ss, p, r + 1⟩ : Box).ClosedBelow B :=
  closeBelow_jump_next h fun _ hlo hhi hp hq =>
    (hhi.not_ge (firstAllowedOdd_le_prime hodd hq hp hlo fuel)).elim

private def normalizeSlots (fast : Bool) (B : ℕ) (b : Box) : Box :=
  if fast then freezeSizeSlots B b else b

private theorem normalizeSlots_closedBelow {B : ℕ} {b : Box} (fast : Bool)
    (hlo : 1 < b.next) (hodd : Odd b.next)
    (h : (normalizeSlots fast B b).ClosedBelow B) : b.ClosedBelow B := by
  cases fast
  · exact h
  · exact freezeSizeSlots_closes hlo hodd h

private def raiseAfterOddExclusion (b : Box) (i : ℕ) (s : Slot) : Box :=
  let step := if Even s.exponent then 2 else 1
  {b with slots := b.slots.set i {s with exponent := s.exponent + step}}

/-- A verified split may skip the odd exponents at one existing slot. -/
structure OddSplitReplay where
  verify : Box → List ℕ → Option (Option (ℕ × Slot) × List ℕ)
  sound : ∀ {b data i s rest B}, verify b data = some (some (i, s), rest) →
    (Even s.exponent → ({b with slots := b.slots.set i {s with fixed := true}} : Box).ClosedBelow B) →
    (raiseAfterOddExclusion b i s).ClosedBelow B → b.ClosedBelow B

def OddSplitReplay.none : OddSplitReplay where
  verify _ data := some (Option.none, data)
  sound := by
    intro _ _ _ _ _ _ h
    simp at h

/-- Verify a complete subtree. A certificate may close a box by an
unbounded rule. Size checks and the end of each last-prime sweep use `B`. -/
def replayWithSizeLimit (limited fast : Bool) (B : ℕ) (readPoint : PointReplay) (readSweep : SweepVerifier)
    (prune : BranchPruning) (oddSplit : OddSplitReplay)
    (cut : Box → Bool) : ℕ → Box → List ℕ → Option (List ℕ)
  | 0, _, _ => none
  | fuel + 1, b, data =>
    if cut b then some data
    else if limited && decide (B ≤ number b.minimum * (tailPrimeFloor b.next b.remaining).prod) then some data
    else if (limited && fast) && exponentCapOk B b then some data
    else
      let b := normalizeSlots (limited && fast) B b
      match (if !limited || fast then none else sizeFixedSlot B b) with
      | some (i, s) =>
        replayWithSizeLimit limited fast B readPoint readSweep prune oddSplit cut fuel
          {b with slots := b.slots.set i {s with fixed := true}} data
      | none =>
        if rankedUpperNum b ≤ 2 * rankedUpperDen b then some data
        else do
          let (closed, data) ← prune.verify b data
          if closed then some data
          else do
            let (split, data) ← oddSplit.verify b data
            match split with
            | some (i, s) => do
              let data ← (if Even s.exponent then
                  replayWithSizeLimit limited fast B readPoint readSweep prune oddSplit cut fuel
                    {b with slots := b.slots.set i {s with fixed := true}} data
                else some data)
              replayWithSizeLimit limited fast B readPoint readSweep prune oddSplit cut fuel
                (raiseAfterOddExclusion b i s) data
            | none =>
              if 2 * number b.minimum ≤ divisorSum b.minimum then consumeMinimum readPoint b data
              else if 0 < b.remaining && b.next < nextThreshold b then
                (if b.remaining = 1 then consumeWholeSweep readSweep b
                    (if limited then boundedSweepEnd B b else nextThreshold b) data
                  else some data).bind
                  (replayWithSizeLimit limited fast B readPoint readSweep prune oddSplit cut fuel {b with next := nextThreshold b})
              else match (chooseWideSlot b).bind (fun i => b.slots[i]?.map (fun s => (i, s))) with
              | some (i, s) => do
                if s.fixed then none else
                  let data ← replayWithSizeLimit limited fast B readPoint readSweep prune oddSplit cut fuel
                    {b with slots := b.slots.set i {s with fixed := true}} data
                  replayWithSizeLimit limited fast B readPoint readSweep prune oddSplit cut fuel
                    {b with slots := b.slots.set i {s with exponent := s.exponent + 1}} data
              | none =>
                match b.remaining with
                | 0 => none
                | r + 1 =>
                  let q := firstAllowedOdd b.next 32
                  if b.next < q then
                    replayWithSizeLimit limited fast B readPoint readSweep prune oddSplit cut fuel ⟨b.slots, q, r + 1⟩ data
                  else do
                    let data ← replayWithSizeLimit limited fast B readPoint readSweep prune oddSplit cut fuel
                      ⟨b.slots, b.next + 2, r + 1⟩ data
                    if mayBeOddPrime b.next then
                      replayWithSizeLimit limited fast B readPoint readSweep prune oddSplit cut fuel
                        ⟨b.slots ++ [⟨b.next, 1, false⟩], b.next + 2, r⟩ data
                    else some data

theorem replayWithSizeLimit_closes
    {limited fast : Bool} {B : ℕ} {readPoint : PointReplay} {readSweep : SweepVerifier} {prune : BranchPruning}
    {oddSplit : OddSplitReplay} {cut : Box → Bool} {fuel : ℕ} {b : Box} {data tail : List ℕ}
    (hcut : ∀ box, cut box = true → box.ClosedBelow B)
    (hlo : 1 < b.next) (hodd : Odd b.next)
    (h : replayWithSizeLimit limited fast B readPoint readSweep prune oddSplit cut fuel b data = some tail) :
    b.ClosedBelow B := by
  induction fuel generalizing b data tail with
  | zero => contradiction
  | succ fuel ih =>
    rw [replayWithSizeLimit] at h
    split at h
    · exact hcut b ‹_›
    split at h
    · exact closeBelow_of_ranked_minimum_ge hodd (of_decide_eq_true (Bool.and_eq_true_iff.mp ‹_›).2)
    split at h
    · exact exponentCapOk_closes hlo hodd ((Bool.and_eq_true_iff.mp ‹_›).2)
    apply normalizeSlots_closedBelow (limited && fast) hlo hodd
    have hlo' : 1 < (normalizeSlots (limited && fast) B b).next := by
      cases limited <;> cases fast <;> simpa [normalizeSlots, freezeSizeSlots] using hlo
    have hodd' : Odd (normalizeSlots (limited && fast) B b).next := by
      cases limited <;> cases fast <;> simpa [normalizeSlots, freezeSizeSlots] using hodd
    dsimp only at h
    generalize hbox : normalizeSlots (limited && fast) B b = normalized at h ⊢
    rw [hbox] at hlo' hodd'
    clear hlo hodd
    rename_i h_cut h_min h_cap
    clear h_cut h_min h_cap hbox b
    have hlo := hlo'
    have hodd := hodd'
    clear hlo' hodd'
    split at h
    · next i s hsize =>
      have hsize' : sizeFixedSlot B normalized = some (i, s) := by cases limited <;> cases fast <;> simp_all
      exact sizeFixedSlot_closes hsize' hodd (ih hlo hodd h)
    · split at h
      · exact closedBelow_of_closed (close_of_ranked_upper hlo hodd ‹_›) B
      obtain ⟨⟨closed, input⟩, hprune, h⟩ := Option.bind_eq_some_iff.mp h
      cases closed
      · simp only [Bool.false_eq_true, if_false] at h
        obtain ⟨⟨split, rest⟩, hsplit, h⟩ := Option.bind_eq_some_iff.mp h
        cases split with
        | some row =>
          obtain ⟨i, s⟩ := row
          dsimp only at h
          obtain ⟨mid, hfixed, hraise⟩ := Option.bind_eq_some_iff.mp h
          apply oddSplit.sound hsplit _ (ih hlo hodd hraise)
          intro heven
          rw [if_pos heven] at hfixed
          exact ih hlo hodd hfixed
        | none =>
          dsimp only at h
          split at h
          · exact closedBelow_of_closed (consumeMinimum_closes ‹_› h) B
          next hnondef =>
            split at h
            next hguard =>
              obtain ⟨hr, hnext⟩ : 0 < normalized.remaining ∧ normalized.next < nextThreshold normalized := by simpa using hguard
              obtain ⟨mid, hmid, hend⟩ := Option.bind_eq_some_iff.mp h
              have hskip := ih (hlo.trans hnext) (nextThreshold_odd _) hend
              rcases normalized with ⟨ss, p, r⟩
              cases r with
              | zero => exact (Nat.lt_irrefl 0 hr).elim
              | succ r =>
                cases r with
                | zero => exact thresholdSweep_closes (limited := limited) (by simpa using hmid) hskip rfl
                | succ r =>
                  apply closeBelow_jump_next hskip
                  intro q _ hq _ ho
                  apply closedBelow_of_closed _ B
                  apply close_nondeficient_squarefree_prefix (by omega)
                  have hnd : divisorSum (ss.map Slot.minimum) <
                      2 * number (ss.map Slot.minimum) := Nat.lt_of_not_ge hnondef
                  have hu := threshold_odd_product_le ho hq hnd
                  have hbase := Nat.mul_le_mul_right q
                    (show 2 * number (ss.map Slot.minimum) ≤
                      2 * number (ss.map Slot.minimum) - divisorSum (ss.map Slot.minimum) +
                        divisorSum (ss.map Slot.minimum) by omega)
                  rw [Nat.add_mul] at hbase
                  rw [Nat.mul_add, Nat.mul_one]
                  exact le_trans hbase (Nat.add_le_add_right hu _)
            next =>
              split at h
              next i s hs =>
                have hi : normalized.slots[i]? = some s := by
                  obtain ⟨j, _, hj⟩ := Option.bind_eq_some_iff.mp hs
                  cases hg : normalized.slots[j]? <;> simp_all
                split at h
                · contradiction
                · have hf : s.fixed = false := by simp_all
                  obtain ⟨mid, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
                  exact closeBelow_split_slot hi hf (ih hlo hodd h₁) (ih hlo hodd h₂)
              next =>
                rcases normalized with ⟨ss, p, r⟩
                cases r with
                | zero => contradiction
                | succ r =>
                  dsimp only at h
                  split at h
                  · exact closeBelow_skip_composites hodd
                      (ih (hlo.trans_le (firstAllowedOdd_ge _ _)) (firstAllowedOdd_odd hodd _) h)
                  · obtain ⟨mid, hskip, htake⟩ := Option.bind_eq_some_iff.mp h
                    have hodd' : Odd (p + 2) := by
                      obtain ⟨k, hk⟩ := hodd
                      exact ⟨k + 1, by dsimp at hk; omega⟩
                    have hlo' : 1 < p + 2 := by dsimp at hlo; omega
                    apply closeBelow_split_next hodd (ih hlo' hodd' hskip)
                    intro hp
                    exact ih hlo' hodd' (by simpa only [if_pos (mayBeOddPrime_of_prime hp)] using htake)
      · exact closedBelow_of_closed (prune.sound hprune) B

def boundedStreamWith (fast : Bool) (B : ℕ) (readPoint : PointReplay) (readSweep : SweepVerifier)
    (prune : BranchPruning) (cut : Box → Bool) : ℕ → Box → List ℕ → Option (List ℕ) :=
  replayWithSizeLimit true fast B readPoint readSweep prune .none cut

theorem boundedStreamWith_closes
    {fast : Bool} {B : ℕ} {readPoint : PointReplay} {readSweep : SweepVerifier} {prune : BranchPruning}
    {cut : Box → Bool} {fuel : ℕ} {b : Box} {data tail : List ℕ}
    (hcut : ∀ box, cut box = true → box.ClosedBelow B)
    (hlo : 1 < b.next) (hodd : Odd b.next)
    (h : boundedStreamWith fast B readPoint readSweep prune cut fuel b data = some tail) :
    b.ClosedBelow B :=
  replayWithSizeLimit_closes hcut hlo hodd h

private theorem unboundedReplay_independent_of_bound
    (B : ℕ) (readPoint : PointReplay) (readSweep : SweepVerifier) (prune : BranchPruning)
    (cut : Box → Bool) (fuel : ℕ) (b : Box) (data : List ℕ) :
    replayWithSizeLimit false true 0 readPoint readSweep prune .none cut fuel b data =
      replayWithSizeLimit false true B readPoint readSweep prune .none cut fuel b data := by
  induction fuel generalizing b data with
  | zero => rfl
  | succ fuel ih =>
    simp only [replayWithSizeLimit, Bool.false_and, Bool.false_eq_true, if_false,
      normalizeSlots, Bool.not_false, Bool.true_or, if_true, ih]

def unboundedRankedStream (readPoint : PointReplay) (readSweep : SweepVerifier)
    (prune : BranchPruning) (cut : Box → Bool) : ℕ → Box → List ℕ → Option (List ℕ) :=
  replayWithSizeLimit false true 0 readPoint readSweep prune .none cut

theorem unboundedRankedStream_closes
    {readPoint : PointReplay} {readSweep : SweepVerifier} {prune : BranchPruning}
    {cut : Box → Bool} {fuel : ℕ} {b : Box} {data tail : List ℕ}
    (hcut : ∀ box, cut box = true → box.Closed)
    (hlo : 1 < b.next) (hodd : Odd b.next)
    (h : unboundedRankedStream readPoint readSweep prune cut fuel b data = some tail) :
    b.Closed := by
  intro xs ys hm hv hw hp
  let B := number (xs ++ ys) + 1
  change replayWithSizeLimit false true 0 readPoint readSweep prune .none cut fuel b data = some tail at h
  rw [unboundedReplay_independent_of_bound B] at h
  exact replayWithSizeLimit_closes (fun box hc => closedBelow_of_closed (hcut box hc) B)
    hlo hodd h xs ys hm hv (Nat.lt_succ_self _) hw hp

def boundedStream (B : ℕ) (readPoint : PointReplay) (readSweep : SweepVerifier)
    (prune : BranchPruning) (cut : Box → Bool) : ℕ → Box → List ℕ → Option (List ℕ) :=
  boundedStreamWith false B readPoint readSweep prune cut

theorem boundedStream_closes
    {B : ℕ} {readPoint : PointReplay} {readSweep : SweepVerifier} {prune : BranchPruning}
    {cut : Box → Bool} {fuel : ℕ} {b : Box} {data tail : List ℕ}
    (hcut : ∀ box, cut box = true → box.ClosedBelow B)
    (hlo : 1 < b.next) (hodd : Odd b.next)
    (h : boundedStream B readPoint readSweep prune cut fuel b data = some tail) :
    b.ClosedBelow B :=
  boundedStreamWith_closes hcut hlo hodd h

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

/-- Each weight is at most `G` plus the sum of the preceding weights. -/
def PrefixGapBound : ℕ → List ℕ → Prop
  | _, [] => True
  | G, d :: ds => d ≤ G ∧ PrefixGapBound (G + d) ds

theorem PrefixGapBound.scale {G : ℕ} {ds : List ℕ} (h : PrefixGapBound G ds) (v : ℕ) :
    PrefixGapBound (v * G) (ds.map (v * ·)) := by
  induction ds generalizing G with
  | nil => trivial
  | cons d ds ih =>
    obtain ⟨hd, hs⟩ := h
    exact ⟨Nat.mul_le_mul_left v hd, by simpa only [Nat.mul_add] using ih hs⟩

private theorem growIntervalOk_of_prefixGapBound {C T G : ℕ} {ws : List ℕ}
    (hgap : PrefixGapBound G ws) (hwidth : G + 2 * C ≤ T + 1) :
    growIntervalOk C (T - C) ws = true := by
  induction ws generalizing T G with
  | nil => rfl
  | cons w ws ih =>
    obtain ⟨hw, htail⟩ := hgap
    simp only [growIntervalOk, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨by omega, ?_⟩
    rw [show T - C + w = T + w - C by omega]
    exact ih htail (by omega)

/-- Append fresh weights in order to a covered central interval. The budget
allows each weight to exceed its preceding weights' sum by at most `G`. -/
theorem cover_of_fresh_prefixGapBound {D : Finset ℕ} {ws : List ℕ} {C T G : ℕ}
    (hcover : Covered D C (T - C)) (hnd : ws.Nodup) (hfresh : Disjoint D ws.toFinset)
    (hgap : PrefixGapBound G ws) (hwidth : G + 2 * C ≤ T + 1) :
    Covered (D ∪ ws.toFinset) C (T + ws.sum - C) := by
  have hnodup : (D.toList ++ ws).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨Finset.nodup_toList _, hnd, ?_⟩
    intro d hd d' hd' h
    subst d'
    exact (Finset.disjoint_left.mp hfresh) (Finset.mem_toList.mp hd) (List.mem_toFinset.mpr hd')
  have hg := cover_of_growIntervalOk hnodup (by simpa using hcover)
    (growIntervalOk_of_prefixGapBound hgap hwidth)
  simpa only [List.toFinset_append, Finset.toList_toFinset, show T - C + ws.sum = T + ws.sum - C by omega]
    using hg

private theorem sumDivisors_coprime_prime_power {u p : ℕ} (hp : p.Prime) (hpu : ¬ p ∣ u)
    (b : ℕ) : (∑ d ∈ (u * p ^ b).divisors, d) =
      (∑ d ∈ u.divisors, d) * ∑ j ∈ range (b + 1), p ^ j := by
  rw [((hp.coprime_iff_not_dvd.mpr hpu).symm.pow_right b).sum_divisors_mul,
    Nat.sum_divisors_prime_pow hp]

private theorem sumProperDivisors_raise_coprime_prime_power {u p a : ℕ}
    (hp : p.Prime) (hpu : ¬ p ∣ u) :
    (∑ d ∈ (u * p ^ (a + 1)).properDivisors, d) =
      (∑ d ∈ (u * p ^ a).properDivisors, d) + p ^ (a + 1) * (∑ d ∈ u.properDivisors, d) + u * p ^ a := by
  let hsum := sumDivisors_coprime_prime_power hp hpu
  have h : (∑ d ∈ (u * p ^ (a + 1)).divisors, d) =
      (∑ d ∈ (u * p ^ a).divisors, d) + (∑ d ∈ u.divisors, d) * p ^ (a + 1) := by
    rw [hsum, hsum, sum_range_succ, Nat.mul_add]
  rw [Nat.sum_divisors_eq_sum_properDivisors_add_self (n := u),
    Nat.sum_divisors_eq_sum_properDivisors_add_self (n := u * p ^ a),
    Nat.sum_divisors_eq_sum_properDivisors_add_self (n := u * p ^ (a + 1)), Nat.add_mul,
    mul_comm (∑ d ∈ u.properDivisors, d)] at h
  omega

/-- Raise the exponent of `p` by appending the scaled proper divisors of `u`,
then the old full number `m`. The two budget tests express the first interval
lift with additive inequalities over naturals. -/
theorem cover_raise_coprime_prime_power {u p a C G : ℕ} {ds : List ℕ}
    (hu : 0 < u) (hp : p.Prime) (hpu : ¬ p ∣ u) (hnd : ds.Nodup)
    (hds : ds.toFinset = u.properDivisors) (hgap : PrefixGapBound G ds) :
    let m := u * p ^ a
    let n := u * p ^ (a + 1)
    let v := p ^ (a + 1)
    let T := ∑ d ∈ m.properDivisors, d
    let U := ∑ d ∈ u.properDivisors, d
    Covered m.properDivisors C (T - C) →
    v * G + 2 * C ≤ T + 1 →
    m + 2 * C ≤ T + v * U + 1 →
    Covered n.properDivisors C ((∑ d ∈ n.properDivisors, d) - C) := by
  intro m n v T U hcover hscaled hlast
  let ws := ds.map (v * ·)
  have hv : 0 < v := pow_pos hp.pos _
  have hm : 0 < m := Nat.mul_pos hu (pow_pos hp.pos _)
  have hn : n = m * p := by simp only [n, m, pow_succ, mul_assoc]
  have hvnot : ¬ v ∣ m := by
    intro hvm
    apply hpu
    apply (Nat.mul_dvd_mul_iff_left (pow_pos hp.pos a)).mp
    simpa only [v, m, pow_succ, mul_comm p, mul_comm u] using hvm
  have hval {d : ℕ} (hd : d ∈ ws.toFinset) : ∃ e ∈ u.properDivisors, d = v * e := by
    obtain ⟨e, he, heq⟩ := List.mem_map.mp (List.mem_toFinset.mp hd)
    exact ⟨e, hds ▸ List.mem_toFinset.mpr he, heq.symm⟩
  have hfresh : Disjoint m.properDivisors ws.toFinset := by
    apply Finset.disjoint_left.mpr
    intro d hd hd'
    obtain ⟨e, _, rfl⟩ := hval hd'
    exact hvnot ((dvd_mul_right v e).trans (Nat.mem_properDivisors.mp hd).1)
  have hws : ws.Nodup := hnd.map (mul_right_injective₀ hv.ne')
  have hsum : ws.sum = v * U := by
    unfold U
    rw [← hds, sum_toFinset_of_nodup hnd]
    simpa only [List.map_id, ws, id_eq] using List.sum_map_mul_left ds id v
  have hc := cover_of_fresh_prefixGapBound hcover hws hfresh (hgap.scale v) hscaled
  rw [hsum] at hc
  have hnot : m ∉ m.properDivisors ∪ ws.toFinset := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact Nat.self_notMem_properDivisors h
    · obtain ⟨e, _, he⟩ := hval h
      exact hvnot ⟨e, he⟩
  have hmore := subsetSumIntervalInsert hnot hc (by omega : C + m ≤ T + v * U - C + 1)
  have hsub : insert m (m.properDivisors ∪ ws.toFinset) ⊆ n.properDivisors := by
    have hmlt : m < n := by
      rw [hn]
      simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left hp.one_lt hm
    have hmdvd : m ∣ n := hn ▸ dvd_mul_right m p
    intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact Nat.mem_properDivisors.mpr ⟨hmdvd, hmlt⟩
    rcases Finset.mem_union.mp hd with hd | hd
    · exact Nat.mem_properDivisors.mpr
        ⟨(Nat.mem_properDivisors.mp hd).1.trans hmdvd, (Nat.mem_properDivisors.mp hd).2.trans hmlt⟩
    · obtain ⟨e, he, rfl⟩ := hval hd
      obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.mp he
      change v * e ∈ (u * v).properDivisors
      rw [mul_comm u v]
      exact Nat.mem_properDivisors.mpr ⟨mul_dvd_mul_left v hdvd, Nat.mul_lt_mul_of_pos_left hlt hv⟩
  have htotal : (∑ d ∈ n.properDivisors, d) = T + v * U + m :=
    sumProperDivisors_raise_coprime_prime_power (a := a) hp hpu
  rw [htotal, show T + v * U + m - C = T + v * U - C + m by omega]
  exact cover_mono hsub hmore

private theorem mul_sumProperDivisors_le_raise_coprime_prime_power {u p a : ℕ}
    (hp : p.Prime) (hpu : ¬ p ∣ u) :
    p * (∑ d ∈ (u * p ^ a).properDivisors, d) ≤ (∑ d ∈ (u * p ^ (a + 1)).properDivisors, d) := by
  have h : (∑ d ∈ (u * p ^ (a + 1)).divisors, d) =
      p * (∑ d ∈ (u * p ^ a).divisors, d) + ∑ d ∈ u.divisors, d := by
    rw [sumDivisors_coprime_prime_power hp hpu (a + 1), sumDivisors_coprime_prime_power hp hpu a,
      geom_sum_succ, Nat.mul_add, Nat.mul_one, mul_left_comm]
  have hm : u * p ^ (a + 1) = p * (u * p ^ a) := by
    rw [pow_succ]
    ac_rfl
  rw [Nat.sum_divisors_eq_sum_properDivisors_add_self (n := u * p ^ (a + 1)),
    Nat.sum_divisors_eq_sum_properDivisors_add_self (n := u * p ^ a), Nat.mul_add] at h
  conv at h =>
    lhs
    arg 2
    rw [hm]
  omega

/-- If the first interval lift succeeds with a positive lower endpoint, the
same ordered cofactor divisors and budget tests certify all higher exponents. -/
theorem cover_raise_coprime_prime_power_add {u p a C G : ℕ} {ds : List ℕ}
    (hu : 0 < u) (hp : p.Prime) (hpu : ¬ p ∣ u) (hC : 0 < C) (hnd : ds.Nodup)
    (hds : ds.toFinset = u.properDivisors) (hgap : PrefixGapBound G ds) :
    let m := u * p ^ a
    let v := p ^ (a + 1)
    let T := ∑ d ∈ m.properDivisors, d
    let U := ∑ d ∈ u.properDivisors, d
    Covered m.properDivisors C (T - C) →
    v * G + 2 * C ≤ T + 1 →
    m + 2 * C ≤ T + v * U + 1 →
    ∀ j : ℕ, let n := u * p ^ (a + j)
      Covered n.properDivisors C ((∑ d ∈ n.properDivisors, d) - C) := by
  intro m v T U hcover hscaled hlast j
  let M (b : ℕ) := u * p ^ b
  let V (b : ℕ) := p ^ (b + 1)
  let S (b : ℕ) := ∑ d ∈ (M b).properDivisors, d
  have hpush {x y : ℕ} (h : x + 2 * C ≤ y + 1) :
      p * x + 2 * C ≤ p * y + 1 := by
    have hm := Nat.mul_le_mul_left p (show x + (2 * C - 1) ≤ y by omega)
    rw [Nat.mul_add] at hm
    have hl := Nat.le_mul_of_pos_left (2 * C - 1) hp.pos
    omega
  have hstep (b : ℕ) (hc : Covered (M b).properDivisors C (S b - C))
      (hs : V b * G + 2 * C ≤ S b + 1) (hl : M b + 2 * C ≤ S b + V b * U + 1) :
      Covered (M (b + 1)).properDivisors C (S (b + 1) - C) ∧
      V (b + 1) * G + 2 * C ≤ S (b + 1) + 1 ∧
      M (b + 1) + 2 * C ≤ S (b + 1) + V (b + 1) * U + 1 := by
    have hM : M (b + 1) = p * M b := by
      unfold M
      rw [pow_succ]
      ac_rfl
    have hV : V (b + 1) = p * V b := by simp only [V, pow_succ']
    have hS : p * S b ≤ S (b + 1) := mul_sumProperDivisors_le_raise_coprime_prime_power hp hpu
    refine ⟨cover_raise_coprime_prime_power (a := b) hu hp hpu hnd hds hgap hc hs hl, ?_, ?_⟩
    · rw [hV, mul_assoc]
      exact (hpush hs).trans (Nat.add_le_add_right hS 1)
    · rw [hM, hV, mul_assoc p (V b) U]
      have hh := hpush hl
      rw [Nat.mul_add] at hh
      exact hh.trans (Nat.add_le_add_right (Nat.add_le_add_right hS _) 1)
  have hall (i : ℕ) : Covered (M (a + i)).properDivisors C (S (a + i) - C) ∧
      V (a + i) * G + 2 * C ≤ S (a + i) + 1 ∧
      M (a + i) + 2 * C ≤ S (a + i) + V (a + i) * U + 1 := by
    induction i with
    | zero => exact ⟨hcover, hscaled, hlast⟩
    | succ i ih => exact hstep (a + i) ih.1 ih.2.1 ih.2.2
  exact (hall j).1

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

/-- Each proper divisor is at most `g` plus the sum of the smaller proper divisors. -/
def GapUpTo (n g : ℕ) : Prop :=
  ∀ d ∈ n.properDivisors, d ≤ g + ∑ x ∈ n.properDivisors.filter (· < d), x

instance (n g : ℕ) : Decidable (GapUpTo n g) := by
  unfold GapUpTo
  infer_instance

/-- Multiplying by any prime propagates the proper-divisor gap bound,
including when the prime already divides the core. -/
theorem GapUpTo.mul_prime {u q g : ℕ} (hg : GapUpTo u g) (hu : 0 < u) (hq : q.Prime) :
    GapUpTo (u * q) (max (q * g) (2 * u - ∑ d ∈ u.divisors, d)) := by
  let G := max (q * g) (2 * u - ∑ d ∈ u.divisors, d)
  have hle : q * g ≤ G := le_max_left _ _
  have hult : u < u * q := by
    simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left hq.one_lt hu
  have hsub : u.properDivisors ⊆ (u * q).properDivisors := by
    intro d hd
    obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.mp hd
    exact Nat.mem_properDivisors.mpr ⟨hdvd.trans (dvd_mul_right u q), hlt.trans hult⟩
  have hsum (d : ℕ) : (∑ x ∈ u.properDivisors.filter (· < d), x) ≤
      ∑ x ∈ (u * q).properDivisors.filter (· < d), x := by
    apply Finset.sum_le_sum_of_subset
    intro x hx
    obtain ⟨hx, hlt⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hsub hx, hlt⟩
  intro d hd
  obtain ⟨hdvd, hdlt⟩ := Nat.mem_properDivisors.mp hd
  obtain ⟨a, b, ha, hb, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hdvd
  rcases (Nat.dvd_prime hq).mp hb with hb | hb
  · subst b
    simp only [mul_one]
    have hal := Nat.le_of_dvd hu ha
    by_cases h : a = u
    · subst a
      have hB : 2 * u - ∑ d ∈ u.divisors, d ≤ G := le_max_right _ _
      rw [Nat.sum_divisors_eq_sum_properDivisors_add_self] at hB
      have hsumu : u.properDivisors.filter (· < u) = u.properDivisors :=
        Finset.filter_true_of_mem fun d hd => (Nat.mem_properDivisors.mp hd).2
      have hs := hsum u
      rw [hsumu] at hs
      omega
    · have hap : a ∈ u.properDivisors := Nat.mem_properDivisors.mpr ⟨ha, lt_of_le_of_ne hal h⟩
      exact (hg a hap).trans (Nat.add_le_add ((Nat.le_mul_of_pos_left g hq.pos).trans hle) (hsum a))
  · subst b
    have hap : a ∈ u.properDivisors := Nat.mem_properDivisors.mpr
      ⟨ha, (Nat.mul_lt_mul_right hq.pos).mp hdlt⟩
    rw [mul_comm a q]
    have hscaled : (u.properDivisors.filter (· < a)).image (q * ·) ⊆
        (u * q).properDivisors.filter (· < q * a) := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hy, hylt⟩ := Finset.mem_filter.mp hy
      obtain ⟨hyd, hyu⟩ := Nat.mem_properDivisors.mp hy
      refine Finset.mem_filter.mpr ⟨?_, Nat.mul_lt_mul_of_pos_left hylt hq.pos⟩
      rw [mul_comm u q]
      exact Nat.mem_properDivisors.mpr ⟨mul_dvd_mul_left q hyd, Nat.mul_lt_mul_of_pos_left hyu hq.pos⟩
    have hsumScaled := Finset.sum_le_sum_of_subset (f := fun x : ℕ => x) hscaled
    rw [Finset.sum_image (fun _ _ _ _ h => mul_left_cancel₀ hq.ne_zero h), ← Finset.mul_sum] at hsumScaled
    exact (Nat.mul_le_mul_left q (hg a hap)).trans (by
      rw [Nat.mul_add]
      exact Nat.add_le_add hle hsumScaled)

private theorem sum_filtered_toFinset_eq_listSum {ds : List ℕ} (hnd : ds.Nodup) (d : ℕ) :
    (∑ x ∈ ds.toFinset.filter (· < d), x) = (ds.filter (fun x => decide (x < d))).sum := by
  rw [← sum_toFinset_of_nodup (hnd.filter (fun x => decide (x < d))), List.toFinset_filter]
  simp

private theorem prefixGapBound_of_sortedLT {ds : List ℕ} {g : ℕ} (hs : ds.SortedLT)
    (hg : ∀ d ∈ ds, d ≤ g + (ds.filter (fun x => decide (x < d))).sum) :
    PrefixGapBound g ds := by
  induction ds generalizing g with
  | nil => trivial
  | cons w ds ih =>
    obtain ⟨hsmall, htail⟩ := List.pairwise_cons.mp hs.pairwise
    refine ⟨?_, ih htail.sortedLT ?_⟩
    · have hnil : ds.filter (fun d => decide (d < w)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro d hd
        simpa only [decide_eq_true_eq] using not_lt_of_gt (hsmall d hd)
      have hw := hg w List.mem_cons_self
      simpa [List.filter_cons, hnil] using hw
    · intro d hd
      have hh := hg d (List.mem_cons_of_mem _ hd)
      simpa [List.filter_cons, hsmall d hd, Nat.add_assoc] using hh

/-- Sorting the proper divisors gives a duplicate-free increasing list
whose prefix gap is bounded by `g`. -/
theorem GapUpTo.prefixGapBound_sort {n g : ℕ} (hg : GapUpTo n g) :
    PrefixGapBound g n.properDivisors.sort := by
  let ds := n.properDivisors.sort
  have hd : ds.toFinset = n.properDivisors := Finset.sort_toFinset _ _
  apply prefixGapBound_of_sortedLT (Finset.sortedLT_sort n.properDivisors)
  intro d hmem
  rw [← sum_filtered_toFinset_eq_listSum (Finset.sort_nodup _ _) d, hd]
  exact hg d (hd ▸ List.mem_toFinset.mpr hmem)

private theorem le_gap_add_sum_smaller_of_prefixGapBound {ds : List ℕ} {g d : ℕ}
    (hg : PrefixGapBound g ds) (hd : d ∈ ds) :
    d ≤ g + (ds.filter (fun x => decide (x < d))).sum := by
  induction ds generalizing g with
  | nil => simp at hd
  | cons w ds ih =>
    rcases hg with ⟨hw, htail⟩
    by_cases h : w < d
    · have hmem : d ∈ ds := (List.mem_cons.mp hd).resolve_left (by omega)
      simpa [List.filter_cons, h, Nat.add_assoc] using ih htail hmem
    · exact ((Nat.le_of_not_gt h).trans hw).trans (Nat.le_add_right _ _)

/-- A gap certificate in any order, including prime-power layers, bounds
the gap after sorting the same proper divisors. -/
theorem PrefixGapBound.gapUpTo {ds : List ℕ} {n g : ℕ} (hg : PrefixGapBound g ds)
    (hnd : ds.Nodup) (hds : ds.toFinset = n.properDivisors) : GapUpTo n g := by
  intro d hd
  rw [← hds, sum_filtered_toFinset_eq_listSum hnd]
  exact le_gap_add_sum_smaller_of_prefixGapBound hg (List.mem_toFinset.mp (hds.symm ▸ hd))

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

def HasSubsetSum (D : Finset ℕ) (x : ℕ) : Prop := ∃ t ⊆ D, ∑ d ∈ t, d = x

def DenseLowSums (D : Finset ℕ) (C G : ℕ) : Prop :=
  ∀ j, j + G ≤ C → ∃ x, j ≤ x ∧ x < j + G ∧ HasSubsetSum D x

theorem DenseLowSums.mono {D E : Finset ℕ} {C G : ℕ} (h : DenseLowSums D C G)
    (hsub : D ⊆ E) : DenseLowSums E C G := by
  intro j hj
  obtain ⟨x, hx, hy, t, ht, hs⟩ := h j hj
  exact ⟨x, hx, hy, t, ht.trans hsub, hs⟩

theorem gapUpTo_of_central_and_low {n C G : ℕ}
    (hG : 0 < G) (hC : 2 * C ≤ ∑ d ∈ n.properDivisors, d)
    (hcovered : Covered n.properDivisors C ((∑ d ∈ n.properDivisors, d) - C))
    (hlow : DenseLowSums n.properDivisors C G) : GapUpTo n G := by
  intro d hd
  let D := n.properDivisors
  let T := ∑ v ∈ D, v
  let S := ∑ v ∈ D.filter (· < d), v
  change d ≤ G + S
  by_contra! hgap
  have hdT : d ≤ T := single_le_sum (f := fun x : ℕ => x) (fun _ _ => Nat.zero_le _) hd
  have hC' : 2 * C ≤ T := hC
  have hgap' : S + G < d := by omega
  obtain ⟨x, hx, hx', t, hsub, hsum⟩ : ∃ x, S < x ∧ x ≤ S + G ∧ HasSubsetSum D x := by
    by_cases hS : S < C
    · by_cases hspace : S + 1 + G ≤ C
      · obtain ⟨x, hx, hx', hp⟩ := hlow (S + 1) hspace
        exact ⟨x, by omega, by omega, hp⟩
      · have hc := hcovered C le_rfl (by omega : C ≤ T - C)
        exact ⟨C, hS, by omega, hc⟩
    · by_cases hS' : S < T - C
      · have hc := hcovered (S + 1) (by omega) (by omega : S + 1 ≤ T - C)
        exact ⟨S + 1, by omega, by omega, hc⟩
      · let j := T - (S + G)
        have hj : j + G ≤ C := by dsimp [j]; omega
        obtain ⟨z, hz, hz', t, ht, hs⟩ := hlow j hj
        have ht' := sum_sdiff (f := fun v : ℕ => v) ht
        change (∑ v ∈ D \ t, v) + (∑ v ∈ t, v) = T at ht'
        refine ⟨T - z, ?_, ?_, D \ t, sdiff_subset, ?_⟩
        · dsimp [j] at hz'
          omega
        · dsimp [j] at hz
          omega
        · omega
  have hsmall : t ⊆ D.filter (· < d) := by
    intro v hv
    refine Finset.mem_filter.mpr ⟨hsub hv, ?_⟩
    have hle : v ≤ ∑ k ∈ t, k := single_le_sum (f := fun k : ℕ => k) (fun _ _ => Nat.zero_le _) hv
    omega
  have hle : (∑ v ∈ t, v) ≤ S := sum_le_sum_of_subset hsmall
  omega

def lowDensityOk (ds : List ℕ) (C G : ℕ) : Bool :=
  let bits := subsetBits ds
  (List.range (C + 1 - G)).all (fun j =>
    (List.range G).any (fun i => bits.testBit (j + i)))

theorem lowDensityOk_sound {ds : List ℕ} {C G : ℕ} (hn : ds.Nodup)
    (h : lowDensityOk ds C G = true) : DenseLowSums ds.toFinset C G := by
  intro j hj
  simp only [lowDensityOk, List.all_eq_true, List.any_eq_true, List.mem_range] at h
  obtain ⟨i, hi, hbit⟩ := h j (by omega)
  exact ⟨j + i, by omega, by omega, testBit_subsetBits hn hbit⟩

def lowModulusOk (ds : List ℕ) (C M : ℕ) : Bool :=
  let bits := subsetBits ds
  (List.range C).all (fun i => !(decide (M ∣ i)) || bits.testBit i)

theorem lowModulusOk_sound {ds : List ℕ} {C M : ℕ} (hn : ds.Nodup)
    (h : lowModulusOk ds C M = true) : ∀ i < C, M ∣ i → HasSubsetSum ds.toFinset i := by
  intro i hi hd
  simp only [lowModulusOk, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not] at h
  exact testBit_subsetBits hn ((h i hi).resolve_left fun hno => hno hd)

theorem pseudoperfect_of_central_and_modulus {n C M : ℕ}
    (hA : n.Abundant) (hc : C ≤ n)
    (hcover : Covered n.properDivisors C ((∑ d ∈ n.properDivisors, d) - C))
    (hsmall : ∀ x < C, M ∣ x → HasSubsetSum n.properDivisors x)
    (hm : M ∣ 2 * n) (hs : M ∣ ∑ d ∈ n.divisors, d) : n.Pseudoperfect := by
  let T := ∑ d ∈ n.properDivisors, d
  let excess := T - n
  have ha : n < T := hA
  have heq := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := n)
  change (∑ d ∈ n.divisors, d) = T + n at heq
  have hdvd : M ∣ excess := by
    have hd := Nat.dvd_sub hs hm
    rwa [heq, show T + n - 2 * n = excess by dsimp [excess]; omega] at hd
  have hwitness : HasSubsetSum n.properDivisors excess := by
    by_cases h : excess < C
    · exact hsmall excess h hdvd
    · exact hcover excess (by omega) (by dsimp [excess]; omega : excess ≤ T - C)
  obtain ⟨t, ht, hsum⟩ := hwitness
  refine ⟨hA.pos, n.properDivisors \ t, sdiff_subset, ?_⟩
  have hdiff := sum_sdiff (f := fun v : ℕ => v) ht
  change (∑ v ∈ n.properDivisors \ t, v) + (∑ v ∈ t, v) = T at hdiff
  dsimp [excess] at hsum
  omega

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

/-- Append fresh weights in increasing order. The sum of the fresh weights
smaller than `d` is the extra budget available when inserting `d`. -/
theorem cover_of_fresh_finset_steps {D E : Finset ℕ} {C T : ℕ}
    (hcover : Covered D C (T - C)) (hdis : Disjoint D E)
    (hstep : ∀ d ∈ E, d + 2 * C ≤ T + (∑ x ∈ E.filter (· < d), x) + 1) :
    Covered (D ∪ E) C (T + (∑ x ∈ E, x) - C) := by
  induction E using Finset.induction_on_max with
  | empty => simpa using hcover
  | insert d E hlt ih =>
    have hnd : d ∉ E := fun hd => (lt_irrefl d) (hlt d hd)
    have hfilter (x : ℕ) (hx : x ≤ d) : (insert d E).filter (· < x) = E.filter (· < x) := by
      rw [Finset.filter_insert, if_neg (not_lt_of_ge hx)]
    have hc := ih (hdis.mono_right (Finset.subset_insert _ _)) (fun x hx => by
      have h := hstep x (Finset.mem_insert_of_mem hx)
      rwa [hfilter x (hlt x hx).le] at h)
    have hb := hstep d (Finset.mem_insert_self _ _)
    rw [hfilter d le_rfl, Finset.filter_true_of_mem hlt] at hb
    have hnot : d ∉ D ∪ E := by
      have hdD : d ∉ D := fun hd =>
        (Finset.disjoint_left.mp hdis) hd (Finset.mem_insert_self _ _)
      simp [hdD, hnd]
    have hc' := subsetSumIntervalInsert hnot hc (by omega : C + d ≤ T + (∑ x ∈ E, x) - C + 1)
    rw [Finset.sum_insert hnd, Finset.union_insert]
    rw [show T + (d + ∑ x ∈ E, x) - C = T + (∑ x ∈ E, x) - C + d by omega]
    exact hc'

/-- A gap bound for the old proper divisors gives a central interval lift
for a prime already present. The divisors of the prime-free cofactor supply
a disjoint budget for the new weights. -/
theorem cover_raise_existing_prime {u q a C G : ℕ}
    (hu : 0 < u) (hq : q.Prime) (hqu : ¬ q ∣ u) (ha : 0 < a) :
    let n := u * q ^ a
    let T := ∑ d ∈ n.properDivisors, d
    GapUpTo n G → Covered n.properDivisors C (T - C) →
    q * G + 2 * C ≤ (∑ d ∈ u.divisors, d) + 1 →
    Covered (n * q).properDivisors C ((∑ d ∈ (n * q).properDivisors, d) - C) := by
  intro n T hgap hcover hbound
  let D := n.properDivisors
  let E := (n * q).properDivisors \ D
  have hn : 0 < n := Nat.mul_pos hu (pow_pos hq.pos a)
  have hnlt : n < n * q := by
    simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left hq.one_lt hn
  have hDn : D ⊆ (n * q).properDivisors := by
    intro d hd
    obtain ⟨hdiv, hlt⟩ := Nat.mem_properDivisors.mp hd
    exact Nat.mem_properDivisors.mpr ⟨hdiv.trans (dvd_mul_right n q), hlt.trans hnlt⟩
  have hDis : Disjoint D E := Finset.sdiff_disjoint.symm
  have hUnion : D ∪ E = (n * q).properDivisors := by
    exact (Finset.union_comm D E).trans (Finset.sdiff_union_of_subset hDn)
  have hqn : q ∣ n := by
    have hqa : q ∣ q ^ a := by
      simpa only [pow_one] using pow_dvd_pow q ha
    exact dvd_mul_of_dvd_right hqa u
  have hU : u.divisors ⊆ D := by
    have hpow : 1 < q ^ a := by
      simpa only [pow_zero] using pow_lt_pow_right₀ hq.one_lt ha
    have hult : u < n := by
      simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left hpow hu
    intro d hd
    have hdu := Nat.dvd_of_mem_divisors hd
    exact Nat.mem_properDivisors.mpr
      ⟨hdu.trans (dvd_mul_right u (q ^ a)), (Nat.le_of_dvd hu hdu).trans_lt hult⟩
  have hstep (d : ℕ) (hd : d ∈ E) :
      d + 2 * C ≤ T + (∑ x ∈ E.filter (· < d), x) + 1 := by
    obtain ⟨hdnq, hdn⟩ := Finset.mem_sdiff.mp hd
    obtain ⟨hdiv, hlt⟩ := Nat.mem_properDivisors.mp hdnq
    have hqd : q ∣ d := by
      by_contra hnot
      have hcop := (hq.coprime_iff_not_dvd.mpr hnot).symm
      have hdiv' := hcop.dvd_of_dvd_mul_right hdiv
      have hdlt : d < n := lt_of_le_of_ne (Nat.le_of_dvd hn hdiv')
        (fun heq => hnot (heq.symm ▸ hqn))
      exact hdn (Nat.mem_properDivisors.mpr ⟨hdiv', hdlt⟩)
    obtain ⟨w, rfl⟩ := hqd
    have hw : w ∈ D := Nat.mem_properDivisors.mpr
      ⟨(Nat.mul_dvd_mul_iff_left hq.pos).mp (by simpa only [mul_comm n q] using hdiv),
        (Nat.mul_lt_mul_left hq.pos).mp (by simpa only [mul_comm n q] using hlt)⟩
    let I := (D.filter (· < w)).image (q * ·)
    have hscale : I ⊆ D ∪ E.filter (· < q * w) := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hyD, hyw⟩ := Finset.mem_filter.mp hy
      obtain ⟨hyd, hyn⟩ := Nat.mem_properDivisors.mp hyD
      by_cases hmem : q * y ∈ D
      · exact Finset.mem_union_left _ hmem
      · have hnew : q * y ∈ (n * q).properDivisors := by
          rw [mul_comm n q]
          exact Nat.mem_properDivisors.mpr ⟨mul_dvd_mul_left q hyd, Nat.mul_lt_mul_of_pos_left hyn hq.pos⟩
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨Finset.mem_sdiff.mpr ⟨hnew, hmem⟩, Nat.mul_lt_mul_of_pos_left hyw hq.pos⟩)
    have hIU : Disjoint u.divisors I := by
      apply Finset.disjoint_left.mpr
      intro x hx hxI
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hxI
      exact hqu ((dvd_mul_right q y).trans (Nat.dvd_of_mem_divisors hx))
    have htot := Finset.sum_le_sum_of_subset (f := fun x : ℕ => x)
      (Finset.union_subset (hU.trans Finset.subset_union_left) hscale)
    rw [Finset.sum_union hIU, Finset.sum_union (hDis.mono_right (Finset.filter_subset _ _))] at htot
    have hgw := Nat.mul_le_mul_left q (hgap w hw)
    rw [Nat.mul_add] at hgw
    have hIsum : (∑ x ∈ I, x) = q * (∑ x ∈ D.filter (· < w), x) := by
      unfold I
      rw [Finset.sum_image (fun _ _ _ _ h => mul_left_cancel₀ hq.ne_zero h), ← Finset.mul_sum]
    change _ ≤ q * G + q * (∑ x ∈ D.filter (· < w), x) at hgw
    rw [← hIsum] at hgw
    change _ ≤ T + (∑ x ∈ E.filter (· < q * w), x) at htot
    omega
  have hf := cover_of_fresh_finset_steps hcover hDis hstep
  change Covered (D ∪ E) C (((∑ x ∈ D, x) + ∑ x ∈ E, x) - C) at hf
  rw [← Finset.sum_union hDis, hUnion] at hf
  exact hf

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

private theorem properDivisorSubsetOfDvd {n m : ℕ} (hm : 0 < m) (h : n ∣ m) :
    n.properDivisors ⊆ m.properDivisors := by
  intro d hd
  obtain ⟨hdvd, hdlt⟩ := Nat.mem_properDivisors.mp hd
  exact Nat.mem_properDivisors.mpr ⟨hdvd.trans h, hdlt.trans_le (Nat.le_of_dvd hm h)⟩

/-- Increasing the exponents of primes already present preserves the
central interval if each prime passes the lift budget at the original core. -/
theorem cover_mul_existing_prime_factors {u k C G : ℕ} (hu : 0 < u) (hk : 0 < k)
    (hG : 0 < G) (hC : 2 * C ≤ ∑ d ∈ u.properDivisors, d)
    (hcovered : Covered u.properDivisors C ((∑ d ∈ u.properDivisors, d) - C))
    (hlow : DenseLowSums u.properDivisors C G)
    (hprimes : ∀ q : ℕ, q.Prime → q ∣ k →
      q ∣ u ∧ q * G + 2 * C ≤ (∑ d ∈ (ordCompl[q] u).divisors, d) + 1) :
    Covered (u * k).properDivisors C ((∑ d ∈ (u * k).properDivisors, d) - C) := by
  revert hk hprimes
  induction k using induction_on_primes with
  | zero => omega
  | one =>
    intro _ _
    simpa using hcovered
  | prime_mul q k hq ih =>
    intro hkq hprimes
    have hk : 0 < k := Nat.pos_of_mul_pos_left hkq
    have hcov := ih hk (fun p hp hpk => hprimes p hp (dvd_mul_of_dvd_right hpk q))
    let n := u * k
    have hn : 0 < n := Nat.mul_pos hu hk
    have hun : u ∣ n := dvd_mul_right u k
    have hsub := properDivisorSubsetOfDvd hn hun
    have hgap : GapUpTo n G :=
      gapUpTo_of_central_and_low hG (hC.trans (Finset.sum_le_sum_of_subset hsub))
        hcov (hlow.mono hsub)
    obtain ⟨hqu, hbound⟩ := hprimes q hq (dvd_mul_right q k)
    let v := ordCompl[q] n
    have hv : 0 < v := Nat.ordCompl_pos q hn.ne'
    have hqv : ¬ q ∣ v := hq.coprime_iff_not_dvd.mp (Nat.coprime_ordCompl hq hn.ne')
    have hqn : q ∣ n := dvd_mul_of_dvd_left hqu k
    have ha : 0 < n.factorization q := hq.factorization_pos_of_dvd hn.ne' hqn
    have hvn : v * q ^ n.factorization q = n :=
      (mul_comm _ _).trans (Nat.ordProj_mul_ordCompl_eq_self n q)
    have hsubv : (ordCompl[q] u).divisors ⊆ v.divisors :=
      Nat.divisors_subset_of_dvd hv.ne' (Nat.ordCompl_dvd_ordCompl_of_dvd hun q)
    have hbudget : q * G + 2 * C ≤ (∑ d ∈ v.divisors, d) + 1 :=
      hbound.trans (Nat.add_le_add_right (Finset.sum_le_sum_of_subset hsubv) 1)
    have hlift := cover_raise_existing_prime (C := C) (G := G) hv hq hqv ha
      (by simpa only [hvn] using hgap) (by simpa only [hvn] using hcov) hbudget
    simpa only [hvn, n, Nat.mul_assoc, mul_comm k q] using hlift

end OddWeirdSubproblems

namespace OddWeirdSubproblems

/-- Saturating at most \(r\) fresh prime factors above \(t\) bounds the
deficiency of the current prefix. -/
theorem freshPrime_deficiency_lt {u s t r : ℕ} (hu : 0 < u) (ht : 1 < t)
    (hs : s ≤ 2 * u)
    (hratio : 2 < ((s : ℚ) / u) * ((t : ℚ) / ((t : ℚ) - 1)) ^ r) :
    (2 * u - s) * t < 2 * r * u := by
  have huq : (0 : ℚ) < u := by exact_mod_cast hu
  have htq : (1 : ℚ) < t := by exact_mod_cast ht
  have htq0 : (0 : ℚ) < t := zero_lt_one.trans htq
  have hz : (0 : ℚ) < ((t : ℚ) - 1) / t := div_pos (sub_pos.mpr htq) htq0
  have hrecip : ((t : ℚ) / ((t : ℚ) - 1)) ^ r =
      ((((t : ℚ) - 1) / t) ^ r)⁻¹ := by
    rw [← inv_pow, inv_div]
  rw [hrecip, ← div_eq_mul_inv, lt_div_iff₀ (pow_pos hz r)] at hratio
  have hzsub : ((t : ℚ) - 1) / t - 1 = -(1 / (t : ℚ)) := by
    rw [sub_div, div_self htq0.ne', sub_sub_cancel_left]
  have hbern := one_add_mul_sub_le_pow ((by norm_num : (-1 : ℚ) ≤ 0).trans hz.le) r
  rw [hzsub, mul_neg, ← sub_eq_add_neg, mul_one_div] at hbern
  have hmul := mul_lt_mul_of_pos_right
    ((lt_div_iff₀ huq).mp ((mul_le_mul_of_nonneg_left hbern (by norm_num : (0 : ℚ) ≤ 2)).trans_lt
      hratio)) htq0
  have hclear : 2 * (1 - (r : ℚ) / t) * (u : ℚ) * (t : ℚ) =
      2 * (u : ℚ) * (t : ℚ) - 2 * (r : ℚ) * (u : ℚ) := by
    calc
      _ = 2 * (u : ℚ) * ((1 - (r : ℚ) / t) * (t : ℚ)) := by ring
      _ = _ := by rw [sub_mul, one_mul, div_mul_cancel₀ _ htq0.ne']; ring
  rw [hclear] at hmul
  have hq : (2 * (u : ℚ) - s) * (t : ℚ) < 2 * (r : ℚ) * (u : ℚ) := by
    nlinarith only [hmul]
  exact_mod_cast (show (((2 * u - s : ℕ) : ℚ) * (t : ℚ)) < 2 * (r : ℚ) * (u : ℚ) by
    simpa only [Nat.cast_sub hs, Nat.cast_mul, Nat.cast_ofNat] using hq)

/-- The bound on the next prime and the accompanying lower bound on the sum
of the proper divisors, written without rational denominators. -/
theorem freshPrimeBudget_of_ratio {u s t P r : ℕ} (hu : 0 < u) (ht : 1 < t)
    (hus : u ≤ s) (hs : s ≤ 2 * u) (hP : 2 * r ≤ P) (hPt : P ≤ t)
    (hratio : 2 < ((s : ℚ) / u) * ((t : ℚ) / ((t : ℚ) - 1)) ^ r) :
    (2 * u - s) * t < 2 * r * u ∧ (P - 2 * r) * u < P * (s - u) := by
  have htbudget := freshPrime_deficiency_lt hu ht hs hratio
  have hPbudget := (Nat.mul_le_mul_left (2 * u - s) hPt).trans_lt htbudget
  have hsum : 2 * u - s + (s - u) = u := by omega
  have h₁ := congrArg (fun n : ℕ => P * n) hsum
  have h₂ := congrArg (fun n : ℕ => n * u) (Nat.sub_add_cancel hP)
  simp only [Nat.mul_add, Nat.add_mul] at h₁ h₂
  rw [Nat.mul_comm (2 * u - s) P] at hPbudget
  exact ⟨htbudget, by omega⟩

/-- The fresh-prime budget for a deficient prefix, given a saturated upper
bound from its smallest possible new prime. -/
theorem freshPrimeBudget {u t P r : ℕ} (hu : 0 < u) (hdef : u.Deficient)
    (ht : 1 < t) (hP : 2 * r ≤ P) (hPt : P ≤ t)
    (hratio : 2 < u.abundancyIndex * ((t : ℚ) / ((t : ℚ) - 1)) ^ r) :
    (2 * u - ∑ d ∈ u.divisors, d) * t < 2 * r * u ∧
      (P - 2 * r) * u < P * (∑ d ∈ u.properDivisors, d) := by
  have hsum : (∑ d ∈ u.divisors, d) = (∑ d ∈ u.properDivisors, d) + u :=
    Nat.sum_divisors_eq_sum_properDivisors_add_self
  have hus : u ≤ ∑ d ∈ u.divisors, d := by omega
  have hs : (∑ d ∈ u.divisors, d) ≤ 2 * u := by
    unfold Nat.Deficient at hdef
    omega
  have h := freshPrimeBudget_of_ratio hu ht hus hs hP hPt hratio
  simpa only [hsum, Nat.add_sub_cancel_right] using h

/-- The divisor-sum ratio of a fresh cofactor with at most (r) prime
factors is at most the product obtained by saturating each at (t). -/
theorem abundancyIndex_le_pow_of_fresh_primes {v t r : ℕ} (hv : 0 < v) (ht : 1 < t)
    (hcard : v.primeFactors.card ≤ r) (hmin : ∀ p ∈ v.primeFactors, t ≤ p) :
    v.abundancyIndex ≤ ((t : ℚ) / ((t : ℚ) - 1)) ^ r := by
  let localIndex (p : ℕ) : ℚ :=
    (∑ i ∈ Finset.range (v.factorization p + 1), (p : ℚ) ^ i) /
      (p : ℚ) ^ v.factorization p
  have hindex : v.abundancyIndex = ∏ p ∈ v.primeFactors, localIndex p := by
    have hsigma := ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
      (k := 1) hv.ne'
    rw [ArithmeticFunction.sigma_one_apply] at hsigma
    simp only [mul_one] at hsigma
    rw [Nat.abundancyIndex, hsigma]
    conv_lhs => arg 2; rw [Nat.prod_primeFactors_pow_factorization hv.ne']
    simp only [localIndex, Nat.cast_prod, Nat.cast_sum, Nat.cast_pow, ← Finset.prod_div_distrib]
  have htq : (1 : ℚ) < t := by exact_mod_cast ht
  have hone : (1 : ℚ) ≤ (t : ℚ) / ((t : ℚ) - 1) := by
    exact (one_le_div (sub_pos.mpr htq)).mpr (by linarith)
  rw [hindex]
  refine (Finset.prod_le_prod (g := fun _ => (t : ℚ) / ((t : ℚ) - 1))
    (fun p _ => ?_) (fun p hp => ?_)).trans ?_
  · unfold localIndex
    exact div_nonneg (Finset.sum_nonneg fun _ _ => pow_nonneg (Nat.cast_nonneg p) _)
      (pow_nonneg (Nat.cast_nonneg p) _)
  · have hpq : (t : ℚ) ≤ p := by exact_mod_cast hmin p hp
    have hpq1 := htq.trans_le hpq
    calc
      localIndex p ≤ (p : ℚ) / ((p : ℚ) - 1) := by
        unfold localIndex
        rw [div_le_div_iff₀ (pow_pos (show (0 : ℚ) < p by linarith) _) (sub_pos.mpr hpq1),
          geom_sum_mul, pow_succ]
        linarith
      _ ≤ (t : ℚ) / ((t : ℚ) - 1) := by
        rw [div_le_div_iff₀ (sub_pos.mpr hpq1) (sub_pos.mpr htq)]
        nlinarith
  · rw [Finset.prod_const]
    exact pow_le_pow_right₀ hone hcard

/-- Apply the budget to an actual abundant coprime extension whose fresh
primes are at least (t). -/
theorem freshPrimeBudget_of_coprime_completion {u v t P r : ℕ}
    (hdef : u.Deficient) (hcop : u.Coprime v) (habund : (u * v).Abundant)
    (ht : 1 < t) (hP : 2 * r ≤ P) (hPt : P ≤ t)
    (hcard : v.primeFactors.card ≤ r) (hmin : ∀ p ∈ v.primeFactors, t ≤ p) :
    (2 * u - ∑ d ∈ u.divisors, d) * t < 2 * r * u ∧
      (P - 2 * r) * u < P * (∑ d ∈ u.properDivisors, d) := by
  have hu := Nat.pos_of_mul_pos_right habund.pos
  have hv := Nat.pos_of_mul_pos_left habund.pos
  have hidx := Nat.abundant_iff_two_lt_abundancyIndex.mp habund
  have hmul : (u * v).abundancyIndex = u.abundancyIndex * v.abundancyIndex := by
    simp only [Nat.abundancyIndex, hcop.sum_divisors_mul, Nat.cast_mul, div_mul_div_comm]
  rw [hmul] at hidx
  have huindex : 0 ≤ u.abundancyIndex := by unfold Nat.abundancyIndex; positivity
  exact freshPrimeBudget hu hdef ht hP hPt
    (hidx.trans_le (mul_le_mul_of_nonneg_left
      (abundancyIndex_le_pow_of_fresh_primes hv ht hcard hmin) huindex))

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

private def primeLayers (p : ℕ) (full : List ℕ) : ℕ → List ℕ
  | 0 => []
  | e + 1 => primeLayers p full e ++ full.map (p ^ e * ·)

/-- Read the full layers in exponent order, then the final proper-divisor layer. -/
def primePowerProperDivisorList (u p e : ℕ) (ds : List ℕ) : List ℕ :=
  primeLayers p (ds ++ [u]) e ++ ds.map (p ^ e * ·)

/-- The maximum of the first and last full layer bounds and the final proper
layer bound. Here `s` is the sum of all divisors of the cofactor `u`. -/
def layeredGapBound (u p s g : ℕ) : ℕ → ℕ
  | 0 => g
  | e + 1 =>
    let f := max g (2 * u - s)
    max (max f (p ^ e * f - s * ((p ^ e - 1) / (p - 1))))
      (p ^ (e + 1) * g - s * ((p ^ (e + 1) - 1) / (p - 1)))

private theorem mem_primeLayers {p e d : ℕ} {full : List ℕ} :
    d ∈ primeLayers p full e ↔ ∃ j < e, ∃ b ∈ full, d = p ^ j * b := by
  induction e with
  | zero => simp [primeLayers]
  | succ e ih =>
    simp only [primeLayers, List.mem_append, ih, List.mem_map]
    constructor
    · rintro (⟨j, hj, b, hb, rfl⟩ | ⟨b, hb, rfl⟩)
      · exact ⟨j, hj.trans (Nat.lt_succ_self _), b, hb, rfl⟩
      · exact ⟨e, Nat.lt_succ_self _, b, hb, rfl⟩
    · rintro ⟨j, hj, b, hb, rfl⟩
      by_cases h : j = e
      · subst j
        exact Or.inr ⟨b, hb, rfl⟩
      · exact Or.inl ⟨j, by omega, b, hb, rfl⟩

private theorem nodup_append_primeLayer {p e : ℕ} {full tail : List ℕ} (hp : 0 < p)
    (hfull : ∀ b ∈ full, ¬ p ∣ b) (hprev : (primeLayers p full e).Nodup) (htail : tail.Nodup) :
    (primeLayers p full e ++ tail.map (p ^ e * ·)).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨hprev, htail.map (mul_right_injective₀ (pow_ne_zero e hp.ne')), ?_⟩
  intro d hd d' hd' heq
  obtain ⟨j, hj, b, hb, rfl⟩ := mem_primeLayers.mp hd
  obtain ⟨b', _, rfl⟩ := List.mem_map.mp hd'
  have hpow : p ^ (j + 1) ∣ p ^ e * b' :=
    (pow_dvd_pow p (Nat.succ_le_of_lt hj)).trans (dvd_mul_right _ _)
  rw [← heq, pow_succ] at hpow
  exact hfull b hb ((Nat.mul_dvd_mul_iff_left (pow_pos hp j)).mp hpow)

/-- The layered list enumerates the proper divisors exactly once. -/
theorem primePowerProperDivisorList_spec {u p e : ℕ} {ds : List ℕ} (hu : 0 < u)
    (hp : p.Prime) (hpu : ¬ p ∣ u) (hnd : ds.Nodup) (hds : ds.toFinset = u.properDivisors) :
    (primePowerProperDivisorList u p e ds).Nodup ∧
      (primePowerProperDivisorList u p e ds).toFinset = (u * p ^ e).properDivisors := by
  let full := ds ++ [u]
  have hu' : u ∉ ds := fun h => Nat.self_notMem_properDivisors (hds ▸ List.mem_toFinset.mpr h)
  have hfull : full.toFinset = u.divisors := by
    rw [← Nat.insert_self_properDivisors hu.ne', ← hds]
    ext d
    simp [full]
  have hfullNd : full.Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hnd, by simp, ?_⟩
    intro b hb c hc hbc
    rw [List.mem_singleton.mp hc] at hbc
    exact hu' (hbc ▸ hb)
  have hfullDvd (b : ℕ) (hb : b ∈ full) : b ∣ u :=
    Nat.dvd_of_mem_divisors (hfull ▸ List.mem_toFinset.mpr hb)
  have hfresh (b : ℕ) (hb : b ∈ full) : ¬ p ∣ b := fun hd => hpu (hd.trans (hfullDvd b hb))
  have hprev (j : ℕ) : (primeLayers p full j).Nodup := by
    induction j with
    | zero => simp [primeLayers]
    | succ j ih => exact nodup_append_primeLayer hp.pos hfresh ih hfullNd
  refine ⟨nodup_append_primeLayer hp.pos hfresh (hprev e) hnd, ?_⟩
  ext d
  change d ∈ (primeLayers p full e ++ ds.map (p ^ e * ·)).toFinset ↔ _
  rw [List.mem_toFinset, List.mem_append, mem_primeLayers, List.mem_map, Nat.mem_properDivisors]
  constructor
  · rintro (⟨j, hj, b, hb, rfl⟩ | ⟨b, hb, rfl⟩)
    · have hbu := hfullDvd b hb
      refine ⟨?_, ?_⟩
      · simpa only [mul_comm u (p ^ e)] using mul_dvd_mul (pow_dvd_pow p hj.le) hbu
      · calc
          _ ≤ p ^ j * u := Nat.mul_le_mul_left _ (Nat.le_of_dvd hu hbu)
          _ < p ^ e * u := Nat.mul_lt_mul_of_pos_right (pow_lt_pow_right₀ hp.one_lt hj) hu
          _ = _ := mul_comm _ _
    · obtain ⟨hbu, hlt⟩ := Nat.mem_properDivisors.mp (hds ▸ List.mem_toFinset.mpr hb)
      rw [mul_comm u (p ^ e)]
      exact ⟨mul_dvd_mul_left _ hbu, Nat.mul_lt_mul_of_pos_left hlt (pow_pos hp.pos e)⟩
  · rintro ⟨hdiv, hlt⟩
    obtain ⟨b, q, hbu, hq, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hdiv
    obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hp).mp hq
    by_cases hje : j = e
    · subst j
      have hbu' : b ∈ u.properDivisors := Nat.mem_properDivisors.mpr
        ⟨hbu, (Nat.mul_lt_mul_right (pow_pos hp.pos e)).mp hlt⟩
      exact Or.inr ⟨b, List.mem_toFinset.mp (hds.symm ▸ hbu'), mul_comm _ _⟩
    · have hbu' : b ∈ u.divisors := Nat.mem_divisors.mpr ⟨hbu, hu.ne'⟩
      exact Or.inl ⟨j, by omega, b, List.mem_toFinset.mp (hfull.symm ▸ hbu'), mul_comm _ _⟩

private theorem prefixGapBound_mono {G H : ℕ} {ds : List ℕ}
    (h : PrefixGapBound G ds) (hGH : G ≤ H) : PrefixGapBound H ds := by
  induction ds generalizing G H with
  | nil => trivial
  | cons d ds ih =>
    obtain ⟨hd, htail⟩ := h
    exact ⟨hd.trans hGH, ih htail (Nat.add_le_add_right hGH d)⟩

private theorem prefixGapBound_append {G : ℕ} {xs ys : List ℕ}
    (hx : PrefixGapBound G xs) (hy : PrefixGapBound (G + xs.sum) ys) :
    PrefixGapBound G (xs ++ ys) := by
  induction xs generalizing G with
  | nil => simpa using hy
  | cons d ds ih =>
    obtain ⟨hd, htail⟩ := hx
    refine ⟨hd, ih htail ?_⟩
    simpa only [List.sum_cons, add_assoc] using hy

private theorem sum_scaledList (v : ℕ) (ds : List ℕ) : (ds.map (v * ·)).sum = v * ds.sum := by
  simpa only [List.map_id, id_eq] using List.sum_map_mul_left ds id v

private theorem sum_primeLayers (p : ℕ) (full : List ℕ) (e : ℕ) :
    (primeLayers p full e).sum = full.sum * ∑ j ∈ range e, p ^ j := by
  induction e with
  | zero => simp [primeLayers]
  | succ e ih =>
    rw [primeLayers, List.sum_append, ih, sum_scaledList, sum_range_succ, Nat.mul_add,
      mul_comm (p ^ e) full.sum]

private theorem prefixGapBound_primeLayers {p H f : ℕ} {full : List ℕ} {e : ℕ}
    (hfull : PrefixGapBound f full)
    (hbound : ∀ j < e, p ^ j * f - full.sum * (∑ i ∈ range j, p ^ i) ≤ H) :
    PrefixGapBound H (primeLayers p full e) := by
  induction e with
  | zero => trivial
  | succ e ih =>
    rw [primeLayers]
    refine prefixGapBound_append (ih (fun j hj => hbound j (hj.trans (Nat.lt_succ_self _)))) ?_
    have hb := hbound e (Nat.lt_succ_self _)
    exact prefixGapBound_mono (hfull.scale (p ^ e)) (by rw [sum_primeLayers]; omega)

/-- Within the full layers the difference is monotone in one direction,
according to which of `s` and `(p - 1) * f` is greater. -/
private theorem layerGap_le_endpoints {p s f e j : ℕ} (hp : 1 ≤ p) (hj : j ≤ e) :
    p ^ j * f - s * (∑ i ∈ range j, p ^ i) ≤
      max f (p ^ e * f - s * (∑ i ∈ range e, p ^ i)) := by
  let F (i : ℕ) := p ^ i * f - s * (∑ k ∈ range i, p ^ k)
  change F j ≤ max f (F e)
  have hF0 : F 0 = f := by simp [F]
  have hF (i : ℕ) : F (i + 1) =
      (p ^ i * f + p ^ i * ((p - 1) * f)) -
        (s * (∑ k ∈ range i, p ^ k) + p ^ i * s) := by
    have hpf : f + (p - 1) * f = p * f := by
      calc
        _ = (1 + (p - 1)) * f := by rw [Nat.add_mul, one_mul]
        _ = _ := by rw [show 1 + (p - 1) = p by omega]
    dsimp only [F]
    rw [sum_range_succ, Nat.mul_add, mul_comm s (p ^ i), ← Nat.mul_add, hpf,
      pow_succ, mul_assoc]
  by_cases h : s ≤ (p - 1) * f
  · have hm : Monotone F := monotone_nat_of_le_succ fun i => by
      have hi := Nat.mul_le_mul_left (p ^ i) h
      rw [hF i]
      unfold F
      omega
    exact (hm hj).trans (le_max_right _ _)
  · have hm : Antitone F := antitone_nat_of_succ_le fun i => by
      have hi := Nat.mul_le_mul_left (p ^ i) (Nat.le_of_not_ge h)
      rw [hF i]
      unfold F
      omega
    have hh := hm (Nat.zero_le j)
    rw [hF0] at hh
    exact hh.trans (le_max_left _ _)

/-- The layered enumeration is duplicate-free, contains exactly the proper
divisors of `u * p ^ e`, and has the endpoint bound computed by `layeredGapBound`. -/
theorem layeredGapBound_sound {u p e g : ℕ} {ds : List ℕ} (hu : 0 < u)
    (hp : p.Prime) (hpu : ¬ p ∣ u) (hnd : ds.Nodup) (hds : ds.toFinset = u.properDivisors)
    (hgap : PrefixGapBound g ds) :
    let ws := primePowerProperDivisorList u p e ds
    ws.Nodup ∧ ws.toFinset = (u * p ^ e).properDivisors ∧
      PrefixGapBound (layeredGapBound u p (∑ d ∈ u.divisors, d) g e) ws := by
  obtain ⟨hn, hd⟩ := primePowerProperDivisorList_spec (e := e) hu hp hpu hnd hds
  refine ⟨hn, hd, ?_⟩
  cases e with
  | zero => simpa [layeredGapBound, primePowerProperDivisorList, primeLayers] using hgap
  | succ e =>
    let full := ds ++ [u]
    let s := ∑ d ∈ u.divisors, d
    let f := max g (2 * u - s)
    let H := layeredGapBound u p s g (e + 1)
    have hT : ds.sum = ∑ d ∈ u.properDivisors, d := by
      rw [← hds, sum_toFinset_of_nodup hnd]
    have hs : s = ds.sum + u := by
      rw [hT]
      exact Nat.sum_divisors_eq_sum_properDivisors_add_self
    have hfullsum : full.sum = s := by simp [full, hs]
    have hfull : PrefixGapBound f full := by
      apply prefixGapBound_append (prefixGapBound_mono hgap (le_max_left g (2 * u - s)))
      refine ⟨?_, trivial⟩
      have hf : 2 * u - s ≤ f := le_max_right _ _
      omega
    have hends : max f (p ^ e * f - s * (∑ i ∈ range e, p ^ i)) ≤ H := by
      rw [Nat.geomSum_eq hp.two_le]
      exact le_max_left _ _
    have hproperEnd : p ^ (e + 1) * g - s * (∑ i ∈ range (e + 1), p ^ i) ≤ H := by
      rw [Nat.geomSum_eq hp.two_le]
      exact le_max_right _ _
    have hb (j : ℕ) (hj : j < e + 1) : p ^ j * f - full.sum * (∑ i ∈ range j, p ^ i) ≤ H := by
      rw [hfullsum]
      exact (layerGap_le_endpoints hp.one_lt.le (Nat.le_of_lt_succ hj)).trans hends
    change PrefixGapBound H (primeLayers p full (e + 1) ++ ds.map (p ^ (e + 1) * ·))
    apply prefixGapBound_append (prefixGapBound_primeLayers hfull hb)
    exact prefixGapBound_mono (hgap.scale (p ^ (e + 1))) (by rw [sum_primeLayers, hfullsum]; omega)

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

def coordinateGap : Coordinates → ℕ
  | [] => 0
  | (p, e) :: xs => layeredGapBound (number xs) p (divisorSum xs) (coordinateGap xs) e

theorem coprime_coordinateProduct {p : ℕ} {xs : Coordinates} (hp : p.Prime)
    (hv : ∀ x ∈ xs, x.1.Prime) (hf : ∀ x ∈ xs, p ≠ x.1) : p.Coprime (number xs) := by
  apply Nat.coprime_list_prod_right_iff.mpr
  intro w hw
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hw
  rw [← pow_one p]
  exact Nat.coprime_pow_primes _ _ hp (hv x hx) (hf x hx)

theorem coordinateGap_sound {fs : Coordinates} (hv : PrimeCoordinates fs) :
    ∃ ds : List ℕ, ds.Nodup ∧ ds.toFinset = (number fs).properDivisors ∧
      PrefixGapBound (coordinateGap fs) ds := by
  induction fs with
  | nil => exact ⟨[], by simp [number, PrefixGapBound]⟩
  | cons x xs ih =>
    obtain ⟨p, e⟩ := x
    have htail : PrimeCoordinates xs :=
      ⟨fun x hx => hv.1 x (List.mem_cons_of_mem _ hx), (List.pairwise_cons.mp hv.2).2⟩
    have hp := hv.1 (p, e) (by simp)
    have hf := hp.coprime_iff_not_dvd.mp (coprime_coordinateProduct hp htail.1
      (fun x hx => Nat.ne_of_lt ((List.pairwise_cons.mp hv.2).1 x hx)))
    obtain ⟨ds, hn, hd, hg⟩ := ih htail
    refine ⟨primePowerProperDivisorList (number xs) p e ds, ?_⟩
    simpa only [coordinateGap, number_cons, mul_comm (p ^ e), ← divisorSum_eq htail] using
      layeredGapBound_sound (e := e) (number_pos htail.1) hp hf hn hd hg

theorem erase_coordinate {fs : Coordinates} {p e : ℕ}
    (hv : PrimeCoordinates fs) (hm : (p, e) ∈ fs) :
    let rest := fs.erase (p, e)
    PrimeCoordinates rest ∧ p.Prime ∧ ¬p ∣ number rest ∧ number fs = number rest * p ^ e := by
  intro rest
  have hrest : PrimeCoordinates rest :=
    ⟨fun x hx => hv.1 x (List.erase_subset hx), hv.2.erase (p, e)⟩
  have hp := hv.1 (p, e) hm
  have hpw : (fs.map Prod.fst).Pairwise (· ≠ ·) :=
    List.pairwise_map.mpr (hv.2.imp fun h => Nat.ne_of_lt h)
  have hperm := List.perm_cons_erase hm
  have hn : p ∉ rest.map Prod.fst := by
    have hd := (hperm.map Prod.fst).nodup_iff.mp hpw
    exact (List.nodup_cons.mp hd).1
  have hfresh (x : ℕ × ℕ) (hx : x ∈ rest) : p ≠ x.1 := by
    intro he
    apply hn
    rw [he]
    exact List.mem_map_of_mem hx
  refine ⟨hrest, hp, hp.coprime_iff_not_dvd.mp (coprime_coordinateProduct hp hrest.1 hfresh), ?_⟩
  have hnum := (hperm.map (fun x => x.1 ^ x.2)).prod_nat
  simpa [number, Nat.mul_comm] using hnum

/-- A covered interval reaching the midpoint of the full divisor total
extends to its reflection by taking complements. -/
theorem cover_proper_central {n lo hi : ℕ}
    (h : Covered n.properDivisors lo hi) (hlo : lo ≤ hi)
    (hhi : hi ≤ ∑ d ∈ n.properDivisors, d)
    (hmid : (∑ d ∈ n.properDivisors, d) / 2 ≤ hi) :
    Covered n.properDivisors lo ((∑ d ∈ n.properDivisors, d) - lo) := by
  intro x hx hy
  by_cases hx' : x ≤ hi
  · exact h x hx hx'
  · exact subsetSumIntervalReflect h hlo hhi x (by omega) hy

structure CentralCoverData where
  seed : List ℕ
  growth : List ℕ
  low : ℕ
  seedHigh : ℕ

def CentralCoverData.ok (data : CentralCoverData) (n total : ℕ) : Bool :=
  let high := data.seedHigh + data.growth.sum
  divisorListOk n (data.seed ++ data.growth) &&
    bitIntervalOk data.seed data.low data.seedHigh &&
    growIntervalOk data.low data.seedHigh data.growth &&
    decide (data.low ≤ high ∧ high ≤ total ∧ total / 2 ≤ high)

theorem CentralCoverData.sound {data : CentralCoverData} {n total : ℕ}
    (hsum : ∑ d ∈ n.properDivisors, d = total) (h : data.ok n total = true) :
    Covered n.properDivisors data.low (total - data.low) := by
  simp only [CentralCoverData.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [← hsum]
  exact cover_proper_central (cover_of_validated_growth h.1.1.1 h.1.1.2 h.1.2)
    h.2.1 (hsum.symm ▸ h.2.2.1) (hsum.symm ▸ h.2.2.2)

private theorem properSum_coordinatePower {rest : Coordinates} {p : ℕ}
    (hv : PrimeCoordinates rest) (hp : p.Prime) (hf : ¬ p ∣ number rest) (e : ℕ) :
    ∑ d ∈ (number rest * p ^ e).properDivisors, d =
      divisorSum rest * powerSum p e - number rest * p ^ e := by
  have hs := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := number rest * p ^ e)
  rw [((hp.coprime_iff_not_dvd.mpr hf).symm.pow_right e).sum_divisors_mul,
    Nat.sum_divisors_prime_pow hp, ← powerSum_eq_sum, ← divisorSum_eq hv] at hs
  omega

def liftCoverOk (fs : Coordinates) (p e a : ℕ) (data : CentralCoverData) : Bool :=
  let rest := fs.erase (p, e)
  let u := number rest
  let s := divisorSum rest
  let m := u * p ^ a
  let T := s * powerSum p a - m
  let v := p ^ (a + 1)
  data.ok m T &&
    decide (a ≤ e ∧ 0 < data.low ∧
      v * coordinateGap rest + 2 * data.low ≤ T + 1 ∧
      m + 2 * data.low ≤ T + v * (s - u) + 1)

/-- A small central certificate at one exponent verifies the interval for
the original core. The cofactor gap bound is evaluated arithmetically. -/
theorem liftCoverOk_sound {fs : Coordinates} {p e a : ℕ} {data : CentralCoverData}
    (hv : PrimeCoordinates fs) (hm : (p, e) ∈ fs) (h : liftCoverOk fs p e a data = true) :
    Covered (number fs).properDivisors data.low (divisorSum fs - number fs - data.low) := by
  obtain ⟨hrest, hp, hf, hnum⟩ := erase_coordinate hv hm
  let rest := fs.erase (p, e)
  obtain ⟨ds, hd, hds, hgap⟩ := coordinateGap_sound hrest
  simp only [liftCoverOk, Bool.and_eq_true, decide_eq_true_eq] at h
  have hsum := properSum_coordinatePower hrest hp hf a
  have hcover := CentralCoverData.sound hsum h.1
  have hcofactor : ∑ d ∈ (number rest).properDivisors, d = divisorSum rest - number rest := by
    have ht := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := number rest)
    rw [← divisorSum_eq hrest] at ht
    dsimp [rest] at ht ⊢
    omega
  have hraised := cover_raise_coprime_prime_power_add (a := a)
    (number_pos hrest.1) hp hf h.2.2.1 hd hds hgap
    (by rw [hsum]; exact hcover) (by rw [hsum]; exact h.2.2.2.1)
    (by rw [hsum, hcofactor]; exact h.2.2.2.2) (e - a)
  rw [Nat.add_sub_of_le h.2.1, ← hnum] at hraised
  have hT := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := number fs)
  rw [← divisorSum_eq hv] at hT
  rw [show divisorSum fs - number fs = ∑ d ∈ (number fs).properDivisors, d by omega]
  exact hraised

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

private theorem affine_mul_bound_of_le {base u a b c : ℕ}
    (hbase : 0 < base) (hu : base ≤ u) (h : a * base + c ≤ b * base) :
    a * u + c ≤ b * u := by
  have hab : a ≤ b := (Nat.mul_le_mul_right_iff hbase).mp (le_trans (Nat.le_add_right _ _) h)
  have hd := Nat.mul_le_mul_left (b - a) hu
  have hb := Nat.sub_add_cancel hab
  have hb₁ := congrArg (· * base) hb
  have hb₂ := congrArg (· * u) hb
  rw [Nat.add_mul] at hb₁ hb₂
  omega

/-- The two initial rational budget tests, cleared of denominators. -/
def FreshIntervalBudget (base P r C G M : ℕ) : Prop :=
  let R := base * (P - 2 * r)
  let Z := base * P
  let K := (2 * C - 1) * P
  2 * r * G * Z + M * K ≤ M * R ∧ Z + K ≤ (P + 1) * R

instance (base P r C G M : ℕ) : Decidable (FreshIntervalBudget base P r C G M) := by
  unfold FreshIntervalBudget
  infer_instance

theorem FreshIntervalBudget.lift {base P r C G M u v p a : ℕ}
    (hbudget : FreshIntervalBudget base P r C G M) (hbase : 0 < base) (hle : base ≤ u)
    (hC : 0 < C) (hP : 2 * r < P) (hPt : P ≤ p)
    (hp : p.Prime) (hpu : ¬ p ∣ u) (hdef : u.Deficient)
    (hcop : u.Coprime v) (hA : (u * v).Abundant)
    (hcard : v.primeFactors.card ≤ r) (hmin : ∀ q ∈ v.primeFactors, p ≤ q)
    (hM : M ∣ 2 * u - ∑ d ∈ u.divisors, d) (hgap : GapUpTo u G)
    (hcover : Covered u.properDivisors C ((∑ d ∈ u.properDivisors, d) - C)) :
    Covered (u * p ^ a).properDivisors C ((∑ d ∈ (u * p ^ a).properDivisors, d) - C) := by
  let T := ∑ d ∈ u.properDivisors, d
  let delta := 2 * u - ∑ d ∈ u.divisors, d
  let k := 2 * C - 1
  have hu := hbase.trans_le hle
  have hp0 : 0 < P := Nat.zero_le _ |>.trans_lt hP
  have hT : T < u := hdef
  have hs := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := u)
  have hdelta : 0 < delta := by dsimp [delta, T] at *; omega
  have hM0 : 0 < M := Nat.pos_of_dvd_of_pos hM hdelta
  have hMle := Nat.le_of_dvd hdelta hM
  have ⟨hpbound, hTbound⟩ :=
    freshPrimeBudget_of_coprime_completion hdef hcop hA hp.one_lt hP.le hPt hcard hmin
  change delta * p < 2 * r * u at hpbound
  change (P - 2 * r) * u < P * T at hTbound
  have ha₁ : (2 * r * G * P) * u + M * (k * P) ≤ (M * (P - 2 * r)) * u := by
    apply affine_mul_bound_of_le hbase hle
    simpa only [FreshIntervalBudget, k, Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using hbudget.1
  have hb₁ : p * G + k ≤ T := by
    apply (Nat.mul_le_mul_right_iff (Nat.mul_pos hM0 hp0)).mp
    calc
      (p * G + k) * (M * P) ≤ (2 * r * G * P) * u + M * (k * P) := by
        have hm := Nat.mul_le_mul_right (G * P)
          ((Nat.mul_le_mul_right p hMle).trans hpbound.le)
        rw [Nat.add_mul]
        apply Nat.add_le_add
        · simpa only [Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using hm
        · exact le_of_eq (by ac_rfl)
      _ ≤ (M * (P - 2 * r)) * u := ha₁
      _ ≤ T * (M * P) := by
        simpa only [Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using
          Nat.mul_le_mul_left M hTbound.le
  have ha₂ : P * u + k * P ≤ ((P + 1) * (P - 2 * r)) * u := by
    apply affine_mul_bound_of_le hbase hle
    simpa only [FreshIntervalBudget, k, Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using hbudget.2
  have hb₂ : u + k ≤ (p + 1) * T := by
    apply (Nat.mul_le_mul_right_iff hp0).mp
    calc
      (u + k) * P = P * u + k * P := by rw [Nat.add_mul, mul_comm u P]
      _ ≤ ((P + 1) * (P - 2 * r)) * u := ha₂
      _ ≤ ((P + 1) * T) * P := by
        simpa only [Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using
          Nat.mul_le_mul_left (P + 1) hTbound.le
      _ ≤ ((p + 1) * T) * P := by
        exact Nat.mul_le_mul_right P (Nat.mul_le_mul_right T (Nat.succ_le_succ hPt))
  have ha := cover_raise_coprime_prime_power_add (a := 0) hu hp hpu hC
    (Finset.sort_nodup _ _) (Finset.sort_toFinset _ _) hgap.prefixGapBound_sort
  simp only [pow_zero, mul_one, zero_add, pow_one] at ha
  refine ha hcover (by dsimp [k] at hb₁; omega) ?_ a
  change u + 2 * C ≤ T + p * T + 1
  rw [Nat.add_mul, Nat.one_mul] at hb₂
  dsimp [k] at hb₂
  omega

theorem coordinatePrime_dvd_exists {p : ℕ} {ys : Coordinates} (hp : p.Prime)
    (hvalid : ∀ x ∈ ys, x.1.Prime) (hd : p ∣ number ys) : ∃ x ∈ ys, x.1 = p := by
  induction ys with
  | nil =>
    have h := Nat.dvd_one.mp (show p ∣ 1 by simpa [number] using hd)
    exact (hp.ne_one h).elim
  | cons y ys ih =>
    rw [number_cons] at hd
    rcases hp.dvd_mul.mp hd with h | h
    · rcases (Nat.dvd_prime (hvalid y (by simp))).mp (hp.dvd_of_dvd_pow h) with h | h
      · exact (hp.ne_one h).elim
      · exact ⟨y, by simp, h.symm⟩
    · obtain ⟨q, hq, he⟩ := ih (fun x hx => hvalid x (List.mem_cons_of_mem _ hx)) h
      exact ⟨q, List.mem_cons_of_mem _ hq, he⟩

theorem primeFactors_card_number_le {ys : Coordinates} (hv : ∀ x ∈ ys, x.1.Prime) :
    (number ys).primeFactors.card ≤ ys.length := by
  have hsub : (number ys).primeFactors ⊆ (ys.map Prod.fst).toFinset := by
    intro p hp
    obtain ⟨x, hx, he⟩ := coordinatePrime_dvd_exists
      (Nat.prime_of_mem_primeFactors hp) hv (Nat.dvd_of_mem_primeFactors hp)
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨x, hx, he⟩)
  exact (card_le_card hsub).trans (by simpa using List.toFinset_card_le (ys.map Prod.fst))

theorem properDivisors_subset_of_dvd {u v : ℕ} (hv : 0 < v) (huv : u ∣ v) :
    u.properDivisors ⊆ v.properDivisors := by
  intro d h
  obtain ⟨hd, hlt⟩ := Nat.mem_properDivisors.mp h
  exact Nat.mem_properDivisors.mpr ⟨hd.trans huv, hlt.trans_le (Nat.le_of_dvd hv huv)⟩

private theorem tailFits_mono_start {xs : Coordinates} {p q : ℕ} (hle : p ≤ q)
    (h : TailFits q xs) : TailFits p xs := by
  cases xs with
  | nil => trivial
  | cons x xs =>
    obtain ⟨u, e⟩ := x
    exact ⟨hle.trans h.1, h.2⟩

/-- Follow the actual prime-power tail of a primitive abundant completion.
Every unfinished prefix is deficient, which supplies the fresh-prime bound
at each step. The two division-free budget inequalities remain valid as the
prefix grows. -/
theorem cover_fresh_tail_with_lift {base P r C G M u : ℕ} {ys : Coordinates}
    (hbase : 0 < base) (hbu : base ≤ u) (hG : 0 < G)
    (lift : ∀ {x v p a}, base ≤ x → P ≤ p → p.Prime → ¬ p ∣ x → x.Deficient →
      x.Coprime v → (x * v).Abundant → v.primeFactors.card ≤ r →
      (∀ q ∈ v.primeFactors, p ≤ q) → M ∣ (2 * x - ∑ d ∈ x.divisors, d) →
      GapUpTo x G →
      Covered x.properDivisors C ((∑ d ∈ x.properDivisors, d) - C) →
      Covered (x * p ^ a).properDivisors C ((∑ d ∈ (x * p ^ a).properDivisors, d) - C))
    (hv : PrimeCoordinates ys) (htail : TailFits P ys) (hr : ys.length ≤ r)
    (hcop : u.Coprime (number ys))
    (hA : (u * number ys).Abundant)
    (hprim : ∀ d ∈ (u * number ys).properDivisors, d.Deficient)
    (hsigma : M ∣ ∑ d ∈ u.divisors, d) (h2u : M ∣ 2 * u)
    (hCT : 2 * C ≤ ∑ d ∈ u.properDivisors, d)
    (hlow : DenseLowSums u.properDivisors C G)
    (hcover : Covered u.properDivisors C ((∑ d ∈ u.properDivisors, d) - C)) :
    Covered (u * number ys).properDivisors C ((∑ d ∈ (u * number ys).properDivisors, d) - C) := by
  induction ys generalizing u with
  | nil => simpa [number] using hcover
  | cons y ys ih =>
    obtain ⟨p, e⟩ := y
    obtain ⟨hPt, _, hp, _, he, htail'⟩ := htail
    have hu : 0 < u := hbase.trans_le hbu
    have hv' : PrimeCoordinates ys :=
      ⟨fun x hx => hv.1 x (List.mem_cons_of_mem _ hx), (List.pairwise_cons.mp hv.2).2⟩
    have he' : 1 ≤ e := by omega
    have hnum : 1 < number ((p, e) :: ys) := by
      rw [number_cons]
      have hw : p ≤ p ^ e := by simpa using Nat.pow_le_pow_right hp.pos he'
      exact (hp.one_lt.trans_le hw).trans_le (Nat.le_mul_of_pos_right _ (number_pos hv'.1))
    have hdef : u.Deficient := hprim u (Nat.mem_properDivisors.mpr
      ⟨dvd_mul_right _ _, by simpa using Nat.mul_lt_mul_of_pos_left hnum hu⟩)
    have hM := Nat.dvd_sub h2u hsigma
    have hpmin (q : ℕ) (hq : q ∈ (number ((p, e) :: ys)).primeFactors) : p ≤ q := by
      obtain ⟨x, hx, hxe⟩ := coordinatePrime_dvd_exists (Nat.prime_of_mem_primeFactors hq)
        hv.1 (Nat.dvd_of_mem_primeFactors hq)
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hxe.symm ▸ le_rfl
      · exact hxe ▸ ((List.pairwise_cons.mp hv.2).1 x hx).le
    have hpu : u.Coprime p := by
      apply hcop.of_dvd_right
      rw [number_cons]
      exact (dvd_pow_self p (by omega : e ≠ 0)).trans (dvd_mul_right _ _)
    have hc : Covered (u * p ^ e).properDivisors C
        ((∑ d ∈ (u * p ^ e).properDivisors, d) - C) :=
      lift hbu hPt hp (hp.coprime_iff_not_dvd.mp hpu.symm) hdef
        hcop hA ((primeFactors_card_number_le hv.1).trans hr) hpmin hM
        (gapUpTo_of_central_and_low hG hCT hcover hlow) hcover
    let u' := u * p ^ e
    have hu' : 0 < u' := Nat.mul_pos hu (pow_pos hp.pos _)
    have hdiv : u ∣ u' := dvd_mul_right _ _
    have hsub := properDivisors_subset_of_dvd hu' hdiv
    have heq : u * number ((p, e) :: ys) = u' * number ys := by
      rw [number_cons, Nat.mul_assoc]
    rw [heq] at hA hprim ⊢
    apply ih (hbu.trans (Nat.le_of_dvd hu' hdiv)) hv' _ _ _ hA hprim _ _
      (hCT.trans (sum_le_sum_of_subset hsub)) (hlow.mono hsub) hc
    · exact tailFits_mono_start (show P ≤ p + 2 by omega) htail'
    · exact (Nat.le_succ _).trans hr
    · apply Nat.Coprime.mul_left
      · apply hcop.of_dvd_right
        rw [number_cons]
        exact dvd_mul_left _ _
      · apply Nat.Coprime.pow_left
        exact coprime_coordinateProduct hp hv'.1
          (fun x hx => ((List.pairwise_cons.mp hv.2).1 x hx).ne)
    · change M ∣ ∑ d ∈ (u * p ^ e).divisors, d
      rw [(hpu.pow_right e).sum_divisors_mul]
      exact hsigma.trans (dvd_mul_right _ _)
    · exact h2u.trans (by dsimp [u']; rw [← Nat.mul_assoc]; exact dvd_mul_right _ _)

theorem cover_fresh_tail {base P r C G M u : ℕ} {ys : Coordinates}
    (hbase : 0 < base) (hbu : base ≤ u) (hC : 0 < C) (hG : 0 < G)
    (hP : 2 * r < P) (hbudget : FreshIntervalBudget base P r C G M)
    (hv : PrimeCoordinates ys) (htail : TailFits P ys) (hr : ys.length ≤ r)
    (hcop : u.Coprime (number ys))
    (hA : (u * number ys).Abundant)
    (hprim : ∀ d ∈ (u * number ys).properDivisors, d.Deficient)
    (hsigma : M ∣ ∑ d ∈ u.divisors, d) (h2u : M ∣ 2 * u)
    (hCT : 2 * C ≤ ∑ d ∈ u.properDivisors, d)
    (hlow : DenseLowSums u.properDivisors C G)
    (hcover : Covered u.properDivisors C ((∑ d ∈ u.properDivisors, d) - C)) :
    Covered (u * number ys).properDivisors C ((∑ d ∈ (u * number ys).properDivisors, d) - C) :=
  cover_fresh_tail_with_lift hbase hbu hG (fun hx => hbudget.lift hbase hx hC hP)
    hv htail hr hcop hA hprim hsigma h2u hCT hlow hcover


end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

private def properSum (n : ℕ) : ℕ := ∑ d ∈ n.properDivisors, d

private theorem sumDivisors_fresh_pow {u q : ℕ} (hq : q.Prime) (hqu : ¬ q ∣ u)
    (a : ℕ) :
    (∑ d ∈ (u * q ^ a).divisors, d) =
      (∑ d ∈ u.divisors, d) * ∑ j ∈ range (a + 1), q ^ j := by
  rw [((hq.coprime_iff_not_dvd.mpr hqu).symm.pow_right a).sum_divisors_mul,
    Nat.sum_divisors_prime_pow hq]

private theorem properSum_fresh_pow_step {u q : ℕ} (hq : q.Prime) (hqu : ¬ q ∣ u)
    (a : ℕ) :
    properSum (u * q ^ (a + 1)) = properSum (u * q ^ a) + q ^ (a + 1) * properSum u +
      u * q ^ a := by
  have h := calc
    (∑ d ∈ (u * q ^ (a + 1)).divisors, d) =
        (∑ d ∈ u.divisors, d) * ∑ j ∈ range (a + 1 + 1), q ^ j :=
      sumDivisors_fresh_pow hq hqu (a + 1)
    _ = (∑ d ∈ (u * q ^ a).divisors, d) + (∑ d ∈ u.divisors, d) * q ^ (a + 1) := by
      rw [sum_range_succ, Nat.mul_add, sumDivisors_fresh_pow hq hqu a]
  rw [Nat.sum_divisors_eq_sum_properDivisors_add_self (n := u * q ^ (a + 1)),
    Nat.sum_divisors_eq_sum_properDivisors_add_self (n := u * q ^ a),
    Nat.sum_divisors_eq_sum_properDivisors_add_self (n := u), Nat.add_mul,
    mul_comm (∑ d ∈ u.properDivisors, d)] at h
  unfold properSum
  omega

private theorem properSum_scale_le_fresh_pow {u q : ℕ} (hq : q.Prime) (hqu : ¬ q ∣ u)
    (a : ℕ) : q * properSum (u * q ^ a) ≤ properSum (u * q ^ (a + 1)) := by
  have h : (∑ d ∈ (u * q ^ (a + 1)).divisors, d) =
      q * (∑ d ∈ (u * q ^ a).divisors, d) + ∑ d ∈ u.divisors, d := by
    rw [sumDivisors_fresh_pow hq hqu (a + 1), sumDivisors_fresh_pow hq hqu a,
      geom_sum_succ, Nat.mul_add, Nat.mul_one, mul_left_comm]
  have hscale : u * q ^ (a + 1) = q * (u * q ^ a) := by
    rw [pow_succ]
    ac_rfl
  rw [Nat.sum_divisors_eq_sum_properDivisors_add_self (n := u * q ^ (a + 1)),
    Nat.sum_divisors_eq_sum_properDivisors_add_self (n := u * q ^ a), Nat.mul_add] at h
  conv at h =>
    lhs
    arg 2
    rw [hscale]
  unfold properSum
  omega

private theorem cover_raise_fresh_pow_alternate {u q a C G : ℕ} {ds : List ℕ}
    (hu : 1 < u) (hq : q.Prime) (hqu : ¬ q ∣ u) (hnd : ds.Nodup)
    (hds : ds.toFinset = u.properDivisors.erase 1) (hgap : PrefixGapBound (G + 1) ds) :
    let m := u * q ^ a
    let v := q ^ (a + 1)
    let T := properSum m
    Covered m.properDivisors C (T - C) →
      v + 2 * C ≤ T + 1 →
      m + 2 * C ≤ T + v + 1 →
      v * G + 2 * C ≤ T + m + 1 →
      Covered (u * q ^ (a + 1)).properDivisors C (properSum (u * q ^ (a + 1)) - C) := by
  intro m v T hcover hfirst hsecond hthird
  let n := u * q ^ (a + 1)
  let ws := ds.map (v * ·)
  have hv : 0 < v := pow_pos hq.pos _
  have hm : 0 < m := Nat.mul_pos (Nat.zero_lt_one.trans hu) (pow_pos hq.pos _)
  have hn : n = m * q := by simp only [n, m, pow_succ, mul_assoc]
  have hvnot : ¬ v ∣ m := by
    intro h
    apply hqu
    apply (Nat.mul_dvd_mul_iff_left (pow_pos hq.pos a)).mp
    simpa only [v, m, pow_succ, mul_comm q, mul_comm u] using h
  have hvm : v ≠ m := fun he => hvnot (he ▸ dvd_rfl)
  have hvfresh : v ∉ m.properDivisors := fun h => hvnot (Nat.mem_properDivisors.mp h).1
  have hmfresh : m ∉ insert v m.properDivisors := by
    intro h
    rcases Finset.mem_insert.mp h with he | hm'
    · exact hvm he.symm
    · exact Nat.self_notMem_properDivisors hm'
  have hcover₁ := subsetSumIntervalInsert hvfresh hcover (by omega : C + v ≤ T - C + 1)
  have hcover₂ := subsetSumIntervalInsert hmfresh hcover₁ (by omega : C + m ≤ T - C + v + 1)
  have hinterval : Covered (insert m (insert v m.properDivisors)) C (T + v + m - C) := by
    rwa [show T + v + m - C = T - C + v + m by omega]
  have hval {d : ℕ} (hd : d ∈ ws.toFinset) : ∃ e ∈ u.properDivisors, e ≠ 1 ∧ d = v * e := by
    obtain ⟨e, he, heq⟩ := List.mem_map.mp (List.mem_toFinset.mp hd)
    have hei := Finset.mem_erase.mp (hds ▸ List.mem_toFinset.mpr he)
    exact ⟨e, hei.2, hei.1, heq.symm⟩
  have hdisjoint : Disjoint (insert m (insert v m.properDivisors)) ws.toFinset := by
    apply Finset.disjoint_left.mpr
    intro d hd hd'
    obtain ⟨e, _, he, rfl⟩ := hval hd'
    rcases Finset.mem_insert.mp hd with hm' | hd
    · exact hvnot ⟨e, hm'.symm⟩
    rcases Finset.mem_insert.mp hd with hv' | hd
    · apply he
      apply mul_left_cancel₀ hv.ne'
      simpa only [mul_one] using hv'
    · exact hvnot ((dvd_mul_right v e).trans (Nat.mem_properDivisors.mp hd).1)
  have hws : ws.Nodup := hnd.map (mul_right_injective₀ hv.ne')
  have hwidth : v * (G + 1) + 2 * C ≤ T + v + m + 1 := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hfinal := cover_of_fresh_prefixGapBound hinterval hws hdisjoint (hgap.scale v) hwidth
  have hsub : insert m (insert v m.properDivisors) ∪ ws.toFinset ⊆ n.properDivisors := by
    have hmlt : m < n := by
      rw [hn]
      simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left hq.one_lt hm
    have hmdvd : m ∣ n := hn ▸ dvd_mul_right m q
    intro d hd
    rcases Finset.mem_union.mp hd with hd | hd
    · rcases Finset.mem_insert.mp hd with rfl | hd
      · exact Nat.mem_properDivisors.mpr ⟨hmdvd, hmlt⟩
      rcases Finset.mem_insert.mp hd with rfl | hd
      · refine Nat.mem_properDivisors.mpr ⟨dvd_mul_left v u, ?_⟩
        simpa only [one_mul] using Nat.mul_lt_mul_of_pos_right hu hv
      · obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.mp hd
        exact Nat.mem_properDivisors.mpr ⟨hdvd.trans hmdvd, hlt.trans hmlt⟩
    · obtain ⟨e, he, _, rfl⟩ := hval hd
      obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.mp he
      change v * e ∈ (u * v).properDivisors
      rw [mul_comm u v]
      exact Nat.mem_properDivisors.mpr ⟨mul_dvd_mul_left v hdvd, Nat.mul_lt_mul_of_pos_left hlt hv⟩
  have hone : 1 ∈ u.properDivisors := Nat.mem_properDivisors.mpr ⟨one_dvd _, hu⟩
  have hsum : ds.sum + 1 = properSum u := by
    rw [← sum_toFinset_of_nodup hnd, hds]
    exact Finset.sum_erase_add _ (fun d => d) hone
  have hscaled : ws.sum = v * ds.sum := by
    simpa only [List.map_id, ws, id_eq] using List.sum_map_mul_left ds id v
  have htotal : properSum n = T + v + m + ws.sum := by
    rw [show properSum n = T + v * properSum u + m from properSum_fresh_pow_step hq hqu a,
      ← hsum, hscaled, Nat.mul_add, Nat.mul_one]
    ac_rfl
  change Covered n.properDivisors C (properSum n - C)
  rw [htotal]
  exact cover_mono hsub hfinal

/-- Append the fresh prime first, then the old full number, then the
remaining scaled proper divisors. The three budgets persist at all powers. -/
theorem cover_coprime_prime_power_alternate {u q C G : ℕ}
    (hu : 0 < u) (hq : q.Prime) (hqu : ¬ q ∣ u) (hC : 0 < C)
    (hgap : GapUpTo u G) :
    let T := ∑ d ∈ u.properDivisors, d
    Covered u.properDivisors C (T - C) →
    q + 2 * C ≤ T + 1 →
    u + 2 * C ≤ T + q + 1 →
    q * G + 2 * C ≤ T + u + 1 →
    ∀ a : ℕ, Covered (u * q ^ a).properDivisors C ((∑ d ∈ (u * q ^ a).properDivisors, d) - C) := by
  intro T hcover hfirst hsecond hthird
  have hu' : 1 < u := by
    by_contra! h
    have he : u = 1 := by omega
    have hT : T = 0 := by simp [T, he]
    have hp := hq.one_lt
    omega
  let ds := (u.properDivisors.erase 1).sort
  have hone : 1 ∈ u.properDivisors := Nat.mem_properDivisors.mpr ⟨one_dvd _, hu'⟩
  have hs : u.properDivisors.sort = 1 :: ds := by
    calc
      _ = (insert 1 (u.properDivisors.erase 1)).sort := by rw [Finset.insert_erase hone]
      _ = _ := by
        apply Finset.sort_insert (· ≤ ·)
        · intro d hd
          have hdiv := (Nat.mem_properDivisors.mp ((Finset.mem_erase.mp hd).2)).1
          exact Nat.pos_of_dvd_of_pos hdiv hu
        · simp
  have hds : ds.toFinset = u.properDivisors.erase 1 := Finset.sort_toFinset _ _
  have hrest : PrefixGapBound (G + 1) ds := by
    have hg := hgap.prefixGapBound_sort
    rw [hs] at hg
    exact hg.2
  let M (a : ℕ) := u * q ^ a
  let V (a : ℕ) := q ^ (a + 1)
  let S (a : ℕ) := properSum (M a)
  have hpush {x y : ℕ} (h : x + 2 * C ≤ y + 1) : q * x + 2 * C ≤ q * y + 1 := by
    have hm := Nat.mul_le_mul_left q (show x + (2 * C - 1) ≤ y by omega)
    rw [Nat.mul_add] at hm
    have hl := Nat.le_mul_of_pos_left (2 * C - 1) hq.pos
    omega
  have hall (a : ℕ) : Covered (M a).properDivisors C (S a - C) ∧
      V a + 2 * C ≤ S a + 1 ∧ M a + 2 * C ≤ S a + V a + 1 ∧
      V a * G + 2 * C ≤ S a + M a + 1 := by
    induction a with
    | zero => simpa [M, V, S, properSum, T] using ⟨hcover, hfirst, hsecond, hthird⟩
    | succ a ih =>
      obtain ⟨hc, h₁, h₂, h₃⟩ := ih
      have hm : M (a + 1) = q * M a := by unfold M; rw [pow_succ]; ac_rfl
      have hv : V (a + 1) = q * V a := by simp only [V, pow_succ']
      have hs : q * S a ≤ S (a + 1) := properSum_scale_le_fresh_pow hq hqu a
      refine ⟨cover_raise_fresh_pow_alternate (a := a) hu' hq hqu
          (Finset.sort_nodup _ _) hds hrest hc h₁ h₂ h₃, ?_, ?_, ?_⟩
      · rw [hv]
        exact (hpush h₁).trans (Nat.add_le_add_right hs 1)
      · rw [hm, hv]
        have hh := hpush h₂
        rw [Nat.mul_add] at hh
        exact hh.trans (Nat.add_le_add_right (Nat.add_le_add_right hs _) 1)
      · rw [hv, mul_assoc, hm]
        have hh := hpush h₃
        rw [Nat.mul_add] at hh
        exact hh.trans (Nat.add_le_add_right (Nat.add_le_add_right hs _) 1)
  intro a
  exact (hall a).1

end OddWeirdSubproblems

/-! Integer budgets for switching between two orders of adjacent divisor layers. -/

namespace OddWeirdSubproblems

/-- Sufficient conditions at the box minimum for either of the two central
interval lifts to apply at every later deficient prefix. -/
def FreshTwoCaseBudget (base P r C G M : ℕ) : Prop :=
  let R := base * (P - 2 * r)
  let Z := base * P
  let K := (2 * C - 1) * P
  2 * r * Z + M * K ≤ M * R ∧
    Z + K ≤ (P + 1) * R ∧
    2 * r * G * Z + M * K ≤ M * (R + Z) ∧
    2 * r * G * base + (G + 1) * K ≤ R

instance (base P r C G M : ℕ) : Decidable (FreshTwoCaseBudget base P r C G M) := by
  unfold FreshTwoCaseBudget
  infer_instance

private theorem affine_mul_mono {base u a b c : ℕ}
    (hb : 0 < base) (hu : base ≤ u) (h : a * base + c ≤ b * base) :
    a * u + c ≤ b * u := by
  have hab : a ≤ b := (Nat.mul_le_mul_right_iff hb).mp (le_trans (Nat.le_add_right _ _) h)
  have hbase : c ≤ (b - a) * base := by
    have he := congrArg (· * base) (Nat.sub_add_cancel hab)
    rw [Nat.add_mul] at he
    omega
  have hnew := hbase.trans (Nat.mul_le_mul_left _ hu)
  have he := congrArg (· * u) (Nat.sub_add_cancel hab)
  rw [Nat.add_mul] at he
  omega

theorem FreshTwoCaseBudget.alternatives {base u T P r C G M p : ℕ}
    (h : FreshTwoCaseBudget base P r C G M) (hbase : 0 < base) (hle : base ≤ u)
    (hC : 0 < C) (hP : 2 * r < P) (hPp : P ≤ p) (hT : T < u)
    (hM : M ∣ u - T) (hprime : (u - T) * p < 2 * r * u)
    (hratio : (P - 2 * r) * u < P * T) :
    (p * G + 2 * C ≤ T + 1 ∧ u + 2 * C ≤ (p + 1) * T + 1) ∨
    (p + 2 * C ≤ T + 1 ∧ u + 2 * C ≤ T + p + 1 ∧
      p * G + 2 * C ≤ T + u + 1) := by
  let k := 2 * C - 1
  let R := (P - 2 * r) * u
  have hPpos : 0 < P := by omega
  have hdelta : 0 < u - T := by omega
  have hMpos : 0 < M := Nat.pos_of_dvd_of_pos hM hdelta
  have hMle : M ≤ u - T := Nat.le_of_dvd hdelta hM
  have hMp : M * p ≤ 2 * r * u := ((Nat.mul_le_mul_right p hMle).trans_lt hprime).le
  have hk₂ : k + 1 = 2 * C := by dsimp [k]; omega
  change 2 * r * (base * P) + M * (k * P) ≤ M * (base * (P - 2 * r)) ∧
    base * P + k * P ≤ (P + 1) * (base * (P - 2 * r)) ∧
    2 * r * G * (base * P) + M * (k * P) ≤ M * (base * (P - 2 * r) + base * P) ∧
    2 * r * G * base + (G + 1) * (k * P) ≤ base * (P - 2 * r) at h
  have ha : 2 * r * (u * P) + M * (k * P) ≤ M * R := by
    have hx : (2 * r * P) * base + M * (k * P) ≤ (M * (P - 2 * r)) * base :=
      by simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h.1
    simpa only [R, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using affine_mul_mono hbase hle hx
  have hb : u * P + k * P ≤ (P + 1) * R := by
    have hx : P * base + k * P ≤ ((P + 1) * (P - 2 * r)) * base :=
      by simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h.2.1
    simpa only [R, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using affine_mul_mono hbase hle hx
  have hc : 2 * r * G * (u * P) + M * (k * P) ≤ M * (R + P * u) := by
    have hx : (2 * r * G * P) * base + M * (k * P) ≤
        (M * (P - 2 * r + P)) * base := by
      simp only [Nat.mul_add, Nat.add_mul]
      simpa only [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h.2.2.1
    have hv := affine_mul_mono hbase hle hx
    simpa only [R, Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hv
  have hd : 2 * r * G * u + (G + 1) * (k * P) ≤ R := by
    apply affine_mul_mono hbase hle
    simpa only [Nat.mul_comm (P - 2 * r) base] using h.2.2.2
  have hR : R ≤ P * T := hratio.le
  have hqk : p + k ≤ T := by
    apply (Nat.mul_le_mul_right_iff (Nat.mul_pos hMpos hPpos)).mp
    calc
      (p + k) * (M * P) = (M * p) * P + M * (k * P) := by rw [Nat.add_mul]; ac_rfl
      _ ≤ 2 * r * (u * P) + M * (k * P) := by
        simpa only [Nat.mul_assoc] using Nat.add_le_add_right (Nat.mul_le_mul_right P hMp) _
      _ ≤ M * R := ha
      _ ≤ T * (M * P) := by
        simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using Nat.mul_le_mul_left M hR
  have hlast : u + k ≤ (p + 1) * T := by
    apply (Nat.mul_le_mul_right_iff hPpos).mp
    rw [Nat.add_mul]
    calc
      _ ≤ (P + 1) * R := hb
      _ ≤ (P + 1) * (P * T) := Nat.mul_le_mul_left _ hR
      _ ≤ (p + 1) * T * P := by
        have hm := Nat.mul_le_mul_right (P * T) (Nat.succ_le_succ hPp)
        simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hm
  by_cases hsmall : p * G + k ≤ T
  · left
    omega
  · right
    have hscaled : p * G + k ≤ T + u := by
      apply (Nat.mul_le_mul_right_iff (Nat.mul_pos hMpos hPpos)).mp
      calc
        (p * G + k) * (M * P) = (M * p) * (G * P) + M * (k * P) := by rw [Nat.add_mul]; ac_rfl
        _ ≤ 2 * r * G * (u * P) + M * (k * P) := by
          simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
            Nat.add_le_add_right (Nat.mul_le_mul_right (G * P) hMp) _
        _ ≤ M * (R + P * u) := hc
        _ ≤ (T + u) * (M * P) := by
          simpa only [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
            Nat.mul_le_mul_left M (Nat.add_le_add_right hR (P * u))
    have hmiss : G * (u - T + k) + k ≤ T := by
      apply (Nat.mul_le_mul_right_iff hPpos).mp
      have huT : (u - T) * P + T * P = u * P := by rw [← Nat.add_mul, Nat.sub_add_cancel hT.le]
      have hd₀ : P * u - T * P ≤ 2 * r * u := by
        have hsum : R + 2 * r * u = P * u := by
          unfold R
          rw [← Nat.add_mul, Nat.sub_add_cancel hP.le]
        have hRT : R ≤ T * P := by simpa only [Nat.mul_comm T P] using hR
        exact Nat.sub_le_iff_le_add.mpr (by
          rw [← hsum, Nat.add_comm]
          exact Nat.add_le_add_left hRT _)
      have he := Nat.mul_le_mul_left G hd₀
      have hd₁ : (u - T) * P = P * u - T * P := by
        rw [Nat.mul_comm P u]
        omega
      rw [← hd₁] at he
      calc
        _ = G * ((u - T) * P) + (G + 1) * (k * P) := by
          simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]
          ac_rfl
        _ ≤ 2 * r * G * u + (G + 1) * (k * P) := by
          simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
            Nat.add_le_add_right he ((G + 1) * (k * P))
        _ ≤ R := hd
        _ ≤ T * P := by simpa only [Nat.mul_comm T P] using hR
    have hwide : u - T + k < p := by
      by_contra! hm
      have hx := Nat.mul_le_mul_right G hm
      rw [Nat.mul_comm (u - T + k) G] at hx
      omega
    exact ⟨by omega, by omega, by omega⟩

open Finset

theorem FreshTwoCaseBudget.lift {base P r C G M u v p a : ℕ}
    (hbudget : FreshTwoCaseBudget base P r C G M) (hbase : 0 < base) (hle : base ≤ u)
    (hC : 0 < C) (hP : 2 * r < P) (hPt : P ≤ p)
    (hp : p.Prime) (hpu : ¬ p ∣ u) (hdef : u.Deficient)
    (hcop : u.Coprime v) (hA : (u * v).Abundant)
    (hcard : v.primeFactors.card ≤ r) (hmin : ∀ q ∈ v.primeFactors, p ≤ q)
    (hM : M ∣ 2 * u - ∑ d ∈ u.divisors, d) (hgap : GapUpTo u G)
    (hcover : Covered u.properDivisors C ((∑ d ∈ u.properDivisors, d) - C)) :
    Covered (u * p ^ a).properDivisors C ((∑ d ∈ (u * p ^ a).properDivisors, d) - C) := by
  let T := ∑ d ∈ u.properDivisors, d
  have hsum : (∑ d ∈ u.divisors, d) = T + u := Nat.sum_divisors_eq_sum_properDivisors_add_self
  have hdeficiency : 2 * u - (∑ d ∈ u.divisors, d) = u - T := by rw [hsum]; omega
  obtain ⟨hprime, hratio⟩ :=
    freshPrimeBudget_of_coprime_completion hdef hcop hA hp.one_lt hP.le hPt hcard hmin
  rw [hdeficiency] at hprime hM
  obtain ⟨hw, hlast⟩ | ⟨hfirst, hsecond, hthird⟩ :=
    hbudget.alternatives hbase hle hC hP hPt hdef hM hprime hratio
  · have hstep := cover_raise_coprime_prime_power_add (a := 0) (hbase.trans_le hle) hp hpu hC
      (Finset.sort_nodup _ _) (Finset.sort_toFinset _ _) hgap.prefixGapBound_sort
    simp only [pow_zero, mul_one, zero_add, pow_one] at hstep
    apply hstep hcover hw _ a
    change u + 2 * C ≤ T + p * T + 1
    calc
      _ ≤ (p + 1) * T + 1 := hlast
      _ = _ := by rw [Nat.add_mul, Nat.one_mul]; ac_rfl
  · exact cover_coprime_prime_power_alternate (hbase.trans_le hle) hp hpu hC hgap
      hcover hfirst hsecond hthird a

theorem cover_fresh_tail_of_twoCaseBudget {base P r C G M u : ℕ} {ys : Coordinates}
    (hbase : 0 < base) (hbu : base ≤ u) (hC : 0 < C) (hG : 0 < G)
    (hP : 2 * r < P) (hbudget : FreshTwoCaseBudget base P r C G M)
    (hv : PrimeCoordinates ys) (htail : TailFits P ys) (hr : ys.length ≤ r)
    (hcop : u.Coprime (number ys))
    (hA : (u * number ys).Abundant)
    (hprim : ∀ d ∈ (u * number ys).properDivisors, d.Deficient)
    (hsigma : M ∣ ∑ d ∈ u.divisors, d) (h2u : M ∣ 2 * u)
    (hCT : 2 * C ≤ ∑ d ∈ u.properDivisors, d)
    (hlow : DenseLowSums u.properDivisors C G)
    (hcover : Covered u.properDivisors C ((∑ d ∈ u.properDivisors, d) - C)) :
    Covered (u * number ys).properDivisors C ((∑ d ∈ (u * number ys).properDivisors, d) - C) :=
  cover_fresh_tail_with_lift hbase hbu hG (fun hx => hbudget.lift hbase hx hC hP)
    hv htail hr hcop hA hprim hsigma h2u hCT hlow hcover

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def CentralCoverData.growUntil (low target : ℕ) : ℕ → List ℕ → List ℕ
  | _, [] => []
  | high, d :: ds =>
    if high < target && low + d ≤ high + 1 then
      d :: CentralCoverData.growUntil low target (high + d) ds
    else []

def buildCentralCover (fs : Coordinates) : CentralCoverData :=
  let n := number fs
  let total := divisorSum fs - n
  let ds := (sortedDivisors fs).takeWhile (· < n)
  let seed := smallPrefix 1024 ds
  let low := effectiveLow (subsetBits seed) seed.sum
  let high := seed.sum - low
  let growth := CentralCoverData.growUntil low (total / 2) high (ds.drop seed.length)
  ⟨seed, growth, low, high⟩

def centralCoverFromGrowth (fs : Coordinates) (growth : List ℕ) : CentralCoverData :=
  let ds := divisorsAtMost fs (min 1024 (number fs - 1))
  let seed := smallPrefix 1024 (sortDivisors 20 ds)
  let low := effectiveLow (subsetBits seed) seed.sum
  ⟨seed, growth, low, seed.sum - low⟩

theorem headRange_of_valid_core {ss : List Slot} {first stop : ℕ}
    (h : PrimeCoordinates (ss.map Slot.minimum) → HeadRangeClosed ss 0 first stop) :
    HeadRangeClosed ss 0 first stop := by
  intro q hlo hhi hp ho xs ys hmatch hvalid hw hproper
  have hc := minimum_valid hmatch.1 (primeCoordinates_left hvalid)
  have hpref : PrimeCoordinates (ss.map Slot.minimum) := by
    change PrimeCoordinates ((ss ++ [(⟨q, 1, false⟩ : Slot)]).map Slot.minimum) at hc
    rw [List.map_append] at hc
    exact primeCoordinates_left hc
  exact h hpref q hlo hhi hp ho xs ys hmatch hvalid hw hproper

def liftedSweepStep (b : Box) (first stop h shift p e a : ℕ) (data : CentralCoverData) : Bool :=
  let fs := b.minimum
  let n := number fs
  let s := divisorSum fs
  let slope := 2 * n - s + h
  liftCoverOk fs p e a data &&
    decide (s ≤ 2 * n ∧ (h = 0 ∨ (h ∣ n ∧ h < n)) ∧
      (shift = 0 ∨ shift = n) ∧
      s ≤ s - n - data.low + shift + slope * first ∧
      data.low + shift + slope * (stop - 1) ≤ s)

theorem liftedSweepStep_closes {b : Box} {first stop h shift p e a : ℕ} {data : CentralCoverData}
    (hmem : (p, e) ∈ b.minimum) (hok : liftedSweepStep b first stop h shift p e a data = true) :
    HeadRangeClosed b.slots 0 first stop := by
  simp only [liftedSweepStep, Bool.and_eq_true, decide_eq_true_eq] at hok
  apply headRange_of_valid_core
  intro hv
  exact headRange_squarefree rfl rfl hok.2.1 hok.2.2.1 hok.2.2.2.1
    (liftCoverOk_sound hv hmem hok.1) hok.2.2.2.2.1 hok.2.2.2.2.2

def readCentralCover (guided : Bool) (fs : Coordinates) (input : List ℕ) :
    Option (CentralCoverData × List ℕ) :=
  if guided then do
    let (growth, tail) ← decodeRankDivisors fs input
    pure (centralCoverFromGrowth fs growth, tail)
  else some (buildCentralCover fs, input)

private def certifiedLiftedAction (b : Box) (first top selector : ℕ) (data : List ℕ) :
    Option (ℕ × List ℕ) := do
  let (slot, rest) ← readVarNat 64 data
  let (gap, rest) ← readVarNat 64 rest
  let (p, e) ← b.minimum[slot / 8]?
  let base := (p, slot % 8) :: b.minimum.erase (p, e)
  let (cert, rest) ← readCentralCover (decide (32 ≤ selector)) base rest
  let j := (selector % 32) / 2
  let h := if j < 2 then j else (b.slots[j - 2]?.map Slot.prime).getD 0
  let shift := (selector % 2) * number b.minimum
  let stop := min top (first + gap)
  if liftedSweepStep b first stop h shift p e (slot % 8) cert then some (stop, rest) else none

private theorem certifiedLiftedAction_sound {b : Box} {first top selector stop : ℕ} {data tail : List ℕ}
    (hc : certifiedLiftedAction b first top selector data = some (stop, tail)) :
    HeadRangeClosed b.slots 0 first stop := by
  unfold certifiedLiftedAction at hc
  obtain ⟨⟨slot, rest⟩, _, hc⟩ := Option.bind_eq_some_iff.mp hc
  dsimp only at hc
  obtain ⟨⟨gap, rest'⟩, _, hc⟩ := Option.bind_eq_some_iff.mp hc
  dsimp only at hc
  obtain ⟨⟨p, e⟩, hslot, hc⟩ := Option.bind_eq_some_iff.mp hc
  dsimp only at hc
  obtain ⟨⟨cert, rest''⟩, _, hc⟩ := Option.bind_eq_some_iff.mp hc
  dsimp only at hc
  have hm := List.mem_of_getElem? hslot
  generalize hok : liftedSweepStep b first (min top (first + gap)) _ _ p e (slot % 8) cert = ok at hc
  cases ok
  · contradiction
  · have he : min top (first + gap) = stop := by simpa using congrArg (Option.map Prod.fst) hc
    exact he ▸ liftedSweepStep_closes hm hok

def liftedSweep : SweepVerifier where
  run b first top data := do
    let (tag, rest) ← readVarNat 64 data
    if tag < 32 then (SweepVerifier.ofActions decodeStreamAction).run b first top data
    else certifiedLiftedAction b first top (tag - 32) rest
  sound := by
    intro b first top data stop tail h
    obtain ⟨⟨tag, rest⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
    dsimp only at h
    split at h
    · exact (SweepVerifier.ofActions decodeStreamAction).sound h
    · exact certifiedLiftedAction_sound h

end OddWeirdSubproblems

namespace OddWeirdSubproblems

/-- The modulus carried by the minimum prefix and the divisor sums at its
fixed exponents. -/
def paletteModulus (b : Box) : ℕ :=
  Nat.gcd (2 * number b.minimum)
    ((b.slots.filter Slot.fixed).map fun s => powerSum s.prime s.exponent).prod

theorem fixedPowerSum_prod_dvd {ss : List Slot} {xs : Coordinates}
    (hfit : List.Forall₂ Slot.Fits ss xs) :
    ((ss.filter Slot.fixed).map fun s => powerSum s.prime s.exponent).prod ∣ divisorSum xs := by
  induction hfit with
  | nil => simp [divisorSum]
  | @cons s x ss xs hs _ ih =>
    cases hf : s.fixed
    · simpa [List.filter_cons, hf, divisorSum] using
        dvd_mul_of_dvd_right ih (powerSum x.1 x.2)
    · have hsum : powerSum s.prime s.exponent = powerSum x.1 x.2 := by
        rw [hs.2.1, hs.2.2.2 hf]
      simpa [List.filter_cons, hf, hsum, divisorSum] using
        Nat.mul_dvd_mul (dvd_rfl : powerSum x.1 x.2 ∣ powerSum x.1 x.2) ih

/-- The modulus survives all admissible exponent increases, and adjoining
any tail preserves both divisibilities. -/
theorem paletteModulus_dvd_append {b : Box} {xs : Coordinates}
    (hfit : List.Forall₂ Slot.Fits b.slots xs) (tail : Coordinates) :
    paletteModulus b ∣ 2 * number (xs ++ tail) ∧
      paletteModulus b ∣ divisorSum (xs ++ tail) := by
  constructor
  · have hmin : number b.minimum ∣ number xs := minimum_dvd hfit
    have hg : paletteModulus b ∣ 2 * number b.minimum := Nat.gcd_dvd_left _ _
    rw [number_append]
    exact hg.trans (Nat.mul_dvd_mul_left 2 (dvd_mul_of_dvd_left hmin _))
  · have hg : paletteModulus b ∣
        ((b.slots.filter Slot.fixed).map fun s => powerSum s.prime s.exponent).prod :=
      Nat.gcd_dvd_right _ _
    rw [divisorSum_append]
    exact dvd_mul_of_dvd_left (hg.trans (fixedPowerSum_prod_dvd hfit)) _

theorem paletteModulus_dvd_of_matches {b : Box} {xs ys : Coordinates}
    (hmatch : b.Matches xs ys) :
    paletteModulus b ∣ 2 * number (xs ++ ys) ∧
      paletteModulus b ∣ divisorSum (xs ++ ys) :=
  paletteModulus_dvd_append hmatch.1 ys

/-- In particular, the fixed modulus persists at each intermediate prefix
formed by adjoining the first \(j\) coordinates of the fresh tail. -/
theorem paletteModulus_dvd_take {b : Box} {xs ys : Coordinates}
    (hmatch : b.Matches xs ys) (j : ℕ) :
    paletteModulus b ∣ 2 * number (xs ++ ys.take j) ∧
      paletteModulus b ∣ divisorSum (xs ++ ys.take j) :=
  paletteModulus_dvd_append hmatch.1 (ys.take j)

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

private theorem number_of_fits_mul {ss : List Slot} {xs : Coordinates}
    (h : List.Forall₂ Slot.Fits ss xs) :
    ∃ k : ℕ, 0 < k ∧ number xs = number (ss.map Slot.minimum) * k ∧
      ∀ q, q.Prime → q ∣ k → ∃ s ∈ ss, s.fixed = false ∧ s.prime = q := by
  induction h with
  | nil =>
    refine ⟨1, Nat.one_pos, by simp [number], ?_⟩
    exact fun q hq hd => (hq.ne_one (Nat.dvd_one.mp hd)).elim
  | @cons s x ss xs hx htail ih =>
    obtain ⟨hq, he, hle, hfix⟩ := hx
    obtain ⟨k, hk, hnumber, hprimes⟩ := ih
    let extra := x.2 - s.exponent
    refine ⟨s.prime ^ extra * k, Nat.mul_pos (pow_pos (he ▸ hq.pos) _) hk, ?_, ?_⟩
    · simp only [number_cons, List.map_cons, Slot.minimum, hnumber]
      rw [← he, ← Nat.add_sub_of_le hle, pow_add]
      dsimp [extra]
      ac_rfl
    · intro p hp hd
      rcases hp.dvd_mul.mp hd with h | h
      · have hf : s.fixed = false := by
          cases hf : s.fixed
          · rfl
          · have hzero : extra = 0 := by dsimp [extra]; rw [hfix hf]; simp
            rw [hzero, pow_zero] at h
            exact (hp.ne_one (Nat.dvd_one.mp h)).elim
        have hs : s.prime.Prime := he ▸ hq
        rcases (Nat.dvd_prime hs).mp (hp.dvd_of_dvd_pow h) with h | hp'
        · exact (hp.ne_one h).elim
        · exact ⟨s, by simp, hf, hp'.symm⟩
      · obtain ⟨t, ht, hfix', heq⟩ := hprimes p hp h
        exact ⟨t, List.mem_cons_of_mem _ ht, hfix', heq⟩

private theorem coprime_coordinate_concat {xs ys : Coordinates} (hv : PrimeCoordinates (xs ++ ys)) :
    (number xs).Coprime (number ys) := by
  apply Nat.coprime_list_prod_right_iff.mpr
  intro z hz
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
  have hy' := hv.1 y (List.mem_append_right _ hy)
  apply Nat.Coprime.pow_right
  apply Nat.Coprime.symm
  exact coprime_coordinateProduct hy'
    (primeCoordinates_left hv).1 (fun x hx =>
      ((List.pairwise_append.mp hv.2).2.2 x hx y hy).ne.symm)

theorem properSum_of_validCoordinates {fs : Coordinates} (hv : PrimeCoordinates fs) :
    ∑ d ∈ (number fs).properDivisors, d = divisorSum fs - number fs := by
  have hs := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := number fs)
  rw [← divisorSum_eq hv] at hs
  omega

def paletteBudgetsOkAt (useAlternate : Bool) (b : Box) (M G : ℕ) (data : CentralCoverData) : Bool :=
  let fs := b.minimum
  let n := number fs
  let T := divisorSum fs - n
  let C := data.low
  lowDensityOk data.seed C G && lowModulusOk data.seed C M &&
    decide (0 < C ∧ 0 < G ∧ C ≤ n ∧ 2 * C ≤ T) &&
    b.slots.all (fun s => s.fixed || decide (0 < s.exponent ∧
      s.prime * G + 2 * C ≤ divisorSum (fs.erase s.minimum) + 1)) &&
    decide (b.remaining = 0 ∨ (2 * b.remaining < b.next ∧
      (FreshIntervalBudget n b.next b.remaining C G M ∨
        (useAlternate = true ∧ FreshTwoCaseBudget n b.next b.remaining C G M))))

def paletteBudgetsOkWith (useAlternate : Bool) (b : Box) (G : ℕ)
    (data : CentralCoverData) : Bool :=
  paletteBudgetsOkAt useAlternate b (paletteModulus b) G data

/-- Central coverage, low subset sums, and the arithmetic budgets exclude
every weird completion of the box. -/
theorem paletteBudgetsOkAt_excludes {useAlternate : Bool} {b : Box} {M G : ℕ}
    {data : CentralCoverData} {Q : Coordinates → Prop}
    (hM : ∀ {xs}, List.Forall₂ Slot.Fits b.slots xs → Q xs → ∀ ys,
      M ∣ 2 * number (xs ++ ys) ∧ M ∣ divisorSum (xs ++ ys))
    (hdata : PrimeCoordinates b.minimum →
      Covered (number b.minimum).properDivisors data.low
        (divisorSum b.minimum - number b.minimum - data.low) ∧
      data.seed.Nodup ∧ data.seed.toFinset ⊆ (number b.minimum).properDivisors)
    (hok : paletteBudgetsOkAt useAlternate b M G data = true) :
    ∀ xs ys, b.Matches xs ys → Q xs → PrimeCoordinates (xs ++ ys) →
      (number (xs ++ ys)).Weird → (∀ d ∈ (number (xs ++ ys)).properDivisors, d.Deficient) →
      False := by
  intro xs ys hmatch hQ hv hw hprim
  have hxs := primeCoordinates_left hv
  have hys : PrimeCoordinates ys :=
    ⟨fun y hy => hv.1 y (List.mem_append_right _ hy), (List.pairwise_append.mp hv.2).2.1⟩
  have hbase := minimum_valid hmatch.1 hxs
  let n := number b.minimum
  let C := data.low
  let u := number xs
  simp only [paletteBudgetsOkAt, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    List.all_eq_true] at hok
  obtain ⟨⟨⟨⟨hlow, hmod⟩, hc, hg, hcn, hcT⟩, hslots⟩, htail⟩ := hok
  obtain ⟨hcert, hsnd, hseedsub⟩ := hdata hbase
  have hbaseT := properSum_of_validCoordinates hbase
  have hfixedLow : DenseLowSums n.properDivisors C G := (lowDensityOk_sound hsnd hlow).mono hseedsub
  have hfixedMod : ∀ x < C, M ∣ x → HasSubsetSum n.properDivisors x := by
    intro x hx hdx
    obtain ⟨t, ht, hs⟩ := lowModulusOk_sound hsnd hmod x hx hdx
    exact ⟨t, ht.trans hseedsub, hs⟩
  have hn : 0 < n := number_pos hbase.1
  have hu : 0 < u := number_pos hxs.1
  obtain ⟨k, hk, heq, hprimes⟩ := number_of_fits_mul hmatch.1
  have heq' : u = n * k := heq
  have hnU : n ∣ u := ⟨k, heq'⟩
  have hNle : n ≤ u := Nat.le_of_dvd hu hnU
  have hsub := properDivisors_subset_of_dvd hu hnU
  have hcofactor (q : ℕ) (hp : q.Prime) (hd : q ∣ k) :
      q ∣ n ∧ q * G + 2 * C ≤ (∑ d ∈ (ordCompl[q] n).divisors, d) + 1 := by
    obtain ⟨s, hs, hfix, hp'⟩ := hprimes q hp hd
    obtain ⟨he, hbudget⟩ := (hslots s hs).resolve_left (by simp [hfix])
    have hsm : (q, s.exponent) ∈ b.minimum := by
      exact List.mem_map.mpr ⟨s, hs, by simp [Slot.minimum, hp']⟩
    let rest := b.minimum.erase (q, s.exponent)
    obtain ⟨hrest, hq, hnot, hnumber⟩ := erase_coordinate hbase hsm
    have hrest' : PrimeCoordinates rest := hrest
    have hnot' : ¬ q ∣ number rest := hnot
    have hnumber' : n = number rest * q ^ s.exponent := hnumber
    have hc : ordCompl[q] n = number rest := by
      rw [hnumber', Nat.mul_comm, Nat.ordCompl_pow_mul_of_not_dvd _ hq hnot']
    constructor
    · have hdvd : q ^ s.exponent ∣ n := by
        rw [hnumber']
        exact dvd_mul_left _ _
      exact (dvd_pow_self q he.ne').trans hdvd
    · rw [hc, ← divisorSum_eq hrest']
      simpa only [Slot.minimum, hp'] using hbudget
  have hpreCover : Covered u.properDivisors C ((∑ d ∈ u.properDivisors, d) - C) := by
    rw [heq']
    exact cover_mul_existing_prime_factors hn hk hg (hbaseT.symm ▸ hcT)
      (hbaseT.symm ▸ hcert) hfixedLow hcofactor
  rw [number_append] at hw hprim
  have hfull : Covered (u * number ys).properDivisors C
      ((∑ d ∈ (u * number ys).properDivisors, d) - C) := by
    rcases htail with hzero | ⟨hf, hb⟩
    · have he : ys = [] := List.length_eq_zero_iff.mp (hmatch.2.2.trans hzero)
      simpa [he, number] using hpreCover
    · have hmd := hM hmatch.1 hQ []
      simp only [List.append_nil] at hmd
      have hsigma : M ∣ ∑ d ∈ u.divisors, d := by rw [← divisorSum_eq hxs]; exact hmd.2
      have hct := (hbaseT.symm ▸ hcT).trans (sum_le_sum_of_subset hsub)
      rcases hb with hb | ⟨_, hb⟩
      · exact cover_fresh_tail hn hNle hc hg hf hb hys hmatch.2.1 hmatch.2.2.le
          (coprime_coordinate_concat hv) hw.1 hprim hsigma hmd.1 hct (hfixedLow.mono hsub) hpreCover
      · exact cover_fresh_tail_of_twoCaseBudget hn hNle hc hg hf hb hys hmatch.2.1
          hmatch.2.2.le (coprime_coordinate_concat hv) hw.1 hprim hsigma hmd.1
          hct (hfixedLow.mono hsub) hpreCover
  have hmul : n ∣ u * number ys := hnU.trans (dvd_mul_right _ _)
  have hfullSub := properDivisors_subset_of_dvd hw.1.pos hmul
  have hs : divisorSum (xs ++ ys) = ∑ d ∈ (u * number ys).divisors, d := by
    rw [divisorSum_eq hv, number_append]
  have hm := hM hmatch.1 hQ ys
  rw [number_append, hs] at hm
  apply hw.2
  apply pseudoperfect_of_central_and_modulus hw.1
    (hcn.trans (Nat.le_of_dvd hw.1.pos hmul)) hfull _ hm.1 hm.2
  intro x hx hdx
  obtain ⟨t, ht, hs⟩ := hfixedMod x hx hdx
  exact ⟨t, ht.trans hfullSub, hs⟩

theorem paletteBudgetsOkWith_closes {useAlternate : Bool} {b : Box} {G : ℕ} {data : CentralCoverData}
    (hdata : PrimeCoordinates b.minimum →
      Covered (number b.minimum).properDivisors data.low
        (divisorSum b.minimum - number b.minimum - data.low) ∧
      data.seed.Nodup ∧ data.seed.toFinset ⊆ (number b.minimum).properDivisors)
    (hok : paletteBudgetsOkWith useAlternate b G data = true) : b.Closed := by
  intro xs ys hm hv hw hp
  exact paletteBudgetsOkAt_excludes (Q := fun _ => True)
    (fun hfit _ ys => paletteModulus_dvd_append hfit ys) hdata hok xs ys hm trivial hv hw hp

def paletteBudgetsOk : Box → ℕ → CentralCoverData → Bool :=
  paletteBudgetsOkWith false

theorem paletteBudgetsOk_closes {b : Box} {G : ℕ} {data : CentralCoverData}
    (hdata : PrimeCoordinates b.minimum →
      Covered (number b.minimum).properDivisors data.low
        (divisorSum b.minimum - number b.minimum - data.low) ∧
      data.seed.Nodup ∧ data.seed.toFinset ⊆ (number b.minimum).properDivisors)
    (hok : paletteBudgetsOk b G data = true) : b.Closed :=
  paletteBudgetsOkWith_closes hdata hok

theorem CentralCoverData.seed_sound {data : CentralCoverData} {n T : ℕ}
    (hok : data.ok n T = true) : data.seed.Nodup ∧ data.seed.toFinset ⊆ n.properDivisors := by
  simp only [CentralCoverData.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hnodup, hseed⟩ := divisorListOk_sound hok.1.1.1
  refine ⟨(List.nodup_append.mp hnodup).1, ?_⟩
  intro x hx
  exact hseed (List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp hx)))

def paletteWithOk (b : Box) (G : ℕ) (data : CentralCoverData) : Bool :=
  data.ok (number b.minimum) (divisorSum b.minimum - number b.minimum) && paletteBudgetsOk b G data

theorem paletteWithOk_closes {b : Box} {G : ℕ} {data : CentralCoverData}
    (hok : paletteWithOk b G data = true) : b.Closed := by
  obtain ⟨hdata, hcheck⟩ := Bool.and_eq_true_iff.mp hok
  apply paletteBudgetsOk_closes _ hcheck
  intro hv
  exact ⟨CentralCoverData.sound (properSum_of_validCoordinates hv) hdata, CentralCoverData.seed_sound hdata⟩

def paletteLiftOk (b : Box) (G p e a : ℕ) (data : CentralCoverData) : Bool :=
  liftCoverOk b.minimum p e a data && paletteBudgetsOk b G data

theorem paletteLiftOk_closes {b : Box} {G p e a : ℕ} {data : CentralCoverData}
    (hmem : (p, e) ∈ b.minimum) (hok : paletteLiftOk b G p e a data = true) : b.Closed := by
  obtain ⟨hdata, hcheck⟩ := Bool.and_eq_true_iff.mp hok
  apply paletteBudgetsOk_closes _ hcheck
  intro hv
  have hc := liftCoverOk_sound hv hmem hdata
  simp only [liftCoverOk, Bool.and_eq_true, decide_eq_true_eq] at hdata
  obtain ⟨_, _, _, heq⟩ := erase_coordinate hv hmem
  obtain ⟨hsnd, hsub⟩ := CentralCoverData.seed_sound hdata.1
  have hdiv : number (b.minimum.erase (p, e)) * p ^ a ∣ number b.minimum := by
    rw [heq]
    exact Nat.mul_dvd_mul_left _ (pow_dvd_pow p hdata.2.1)
  exact ⟨hc, hsnd, hsub.trans (properDivisors_subset_of_dvd (number_pos hv.1) hdiv)⟩

def paletteOk (b : Box) (G : ℕ) : Bool := paletteWithOk b G (buildCentralCover b.minimum)

theorem paletteOk_closes {b : Box} {G : ℕ} (h : paletteOk b G = true) : b.Closed :=
  paletteWithOk_closes h

end OddWeirdSubproblems

/-! Build a central interval from a short prefix of a box's known factors. -/

namespace OddWeirdSubproblems

open Finset

/-- At each known prime, check the two inequalities for lifting the cover
to all powers of that prime. -/
def knownTailLiftOk (C G : ℕ) (pre : Coordinates) : Coordinates → Bool
  | [] => true
  | (p, e) :: ys =>
    let m := number pre
    let T := divisorSum pre - m
    decide (p * G + 2 * C ≤ T + 1 ∧ m + 2 * C ≤ (p + 1) * T + 1) &&
      knownTailLiftOk C G (pre ++ [(p, e)]) ys

theorem knownTailLiftOk_sound {pre ys : Coordinates} {C G : ℕ}
    (hv : PrimeCoordinates (pre ++ ys)) (hC : 0 < C) (hG : 0 < G)
    (hCT : 2 * C ≤ ∑ d ∈ (number pre).properDivisors, d)
    (hlow : DenseLowSums (number pre).properDivisors C G)
    (hcovered : Covered (number pre).properDivisors C
      ((∑ d ∈ (number pre).properDivisors, d) - C))
    (hok : knownTailLiftOk C G pre ys = true) :
    Covered (number (pre ++ ys)).properDivisors C
      ((∑ d ∈ (number (pre ++ ys)).properDivisors, d) - C) := by
  induction ys generalizing pre with
  | nil => simpa only [List.append_nil] using hcovered
  | cons y ys ih =>
    obtain ⟨p, e⟩ := y
    let m := number pre
    let T := ∑ d ∈ m.properDivisors, d
    let new := pre ++ [(p, e)]
    have hpre := primeCoordinates_left hv
    have hm : 0 < m := number_pos hpre.1
    have hp : p.Prime := hv.1 (p, e) (List.mem_append_right _ (by simp))
    have hnot : ¬ p ∣ m := by
      apply hp.coprime_iff_not_dvd.mp
      exact coprime_coordinateProduct hp hpre.1 fun x hx =>
        ((List.pairwise_append.mp hv.2).2.2 x hx (p, e) (by simp)).ne.symm
    have hT : T = divisorSum pre - m := properSum_of_validCoordinates hpre
    simp only [knownTailLiftOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    have hlift := cover_raise_coprime_prime_power_add (a := 0) hm hp hnot hC
      (Finset.sort_nodup _ _) (Finset.sort_toFinset _ _)
      (gapUpTo_of_central_and_low hG hCT hcovered hlow).prefixGapBound_sort
    simp only [pow_zero, mul_one, zero_add, pow_one] at hlift
    have hs : p * G + 2 * C ≤ T + 1 := by rw [hT]; exact hok.1.1
    have hl : m + 2 * C ≤ T + p * T + 1 := by
      rw [hT]
      simpa only [Nat.add_mul, Nat.one_mul, Nat.add_comm (p * _)] using hok.1.2
    have heq : number new = m * p ^ e := by
      rw [number_append, number_cons, show number [] = 1 from rfl, Nat.mul_one]
    have hv' : PrimeCoordinates (new ++ ys) := by
      simpa only [new, List.append_assoc, List.singleton_append] using hv
    have hm' : 0 < number new := number_pos (primeCoordinates_left hv').1
    have hsub := properDivisors_subset_of_dvd hm' (heq.symm ▸ dvd_mul_right m (p ^ e))
    have hnew := ih hv' (hCT.trans (sum_le_sum_of_subset hsub)) (hlow.mono hsub)
      (heq.symm ▸ hlift hcovered hs hl e) hok.2
    simpa only [new, List.append_assoc, List.singleton_append] using hnew

def prefixPaletteOkWith (useAlternate : Bool) (b : Box) (G k : ℕ) : Bool :=
  let pre := b.minimum.take k
  let data := buildCentralCover pre
  data.ok (number pre) (divisorSum pre - number pre) &&
  decide (2 * data.low ≤ divisorSum pre - number pre) &&
  knownTailLiftOk data.low G pre (b.minimum.drop k) &&
  paletteBudgetsOkWith useAlternate b G data


theorem prefixCoverFromData {b : Box} {G k : ℕ}
    (hv : PrimeCoordinates b.minimum) :
    let pre := b.minimum.take k
    let data := buildCentralCover pre
    data.ok (number pre) (divisorSum pre - number pre) = true →
    2 * data.low ≤ divisorSum pre - number pre →
    0 < data.low → 0 < G → lowDensityOk data.seed data.low G = true →
    knownTailLiftOk data.low G pre (b.minimum.drop k) = true →
    Covered (number b.minimum).properDivisors data.low
      (divisorSum b.minimum - number b.minimum - data.low) ∧
    data.seed.Nodup ∧ data.seed.toFinset ⊆ (number b.minimum).properDivisors := by
  intro pre data hdata hCT hC hG hlow htail
  let ys := b.minimum.drop k
  have heq : pre ++ ys = b.minimum := List.take_append_drop k _
  have hv' : PrimeCoordinates (pre ++ ys) := heq.symm ▸ hv
  have hpre := primeCoordinates_left hv'
  have hsum := properSum_of_validCoordinates hpre
  have hcovered := CentralCoverData.sound hsum hdata
  have ⟨hnd, hsub⟩ := CentralCoverData.seed_sound hdata
  have hdense := (lowDensityOk_sound hnd hlow).mono hsub
  have hc := knownTailLiftOk_sound hv' hC hG
    (hsum.symm ▸ hCT) hdense (hsum.symm ▸ hcovered) htail
  have hdvd : number pre ∣ number b.minimum := by
    rw [← heq, number_append]
    exact dvd_mul_right _ _
  rw [heq, properSum_of_validCoordinates hv] at hc
  exact ⟨hc, hnd, hsub.trans (properDivisors_subset_of_dvd (number_pos hv.1) hdvd)⟩

theorem prefixPaletteOkWith_closes {useAlternate : Bool} {b : Box} {G k : ℕ}
    (hok : prefixPaletteOkWith useAlternate b G k = true) : b.Closed := by
  simp only [prefixPaletteOkWith, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hdata, hCT⟩, htail⟩, hbudget⟩ := hok
  apply paletteBudgetsOkWith_closes _ hbudget
  intro hv
  have hstats := hbudget
  simp only [paletteBudgetsOkWith, paletteBudgetsOkAt, Bool.and_eq_true, decide_eq_true_eq] at hstats
  exact prefixCoverFromData hv hdata hCT hstats.1.1.2.1 hstats.1.1.2.2.1 hstats.1.1.1.1 htail

def prefixPaletteOk : Box → ℕ → ℕ → Bool := prefixPaletteOkWith false

theorem prefixPaletteOk_closes {b : Box} {G k : ℕ} (hok : prefixPaletteOk b G k = true) :
    b.Closed := prefixPaletteOkWith_closes hok

end OddWeirdSubproblems

/-! Check a squarefree prime interval using a central cover rebuilt from a short factor prefix. -/

namespace OddWeirdSubproblems

def prefixSweepOk (b : Box) (first stop G k h shift : ℕ) : Bool :=
  let fs := b.minimum
  let pre := fs.take k
  let data := buildCentralCover pre
  let n := number fs
  let s := divisorSum fs
  let slope := 2 * n - s + h
  data.ok (number pre) (divisorSum pre - number pre) &&
    lowDensityOk data.seed data.low G &&
    knownTailLiftOk data.low G pre (fs.drop k) &&
    decide (2 * data.low ≤ divisorSum pre - number pre ∧ 0 < data.low ∧ 0 < G ∧
      s ≤ 2 * n ∧ (h = 0 ∨ (h ∣ n ∧ h < n)) ∧ (shift = 0 ∨ shift = n) ∧
      s ≤ s - n - data.low + shift + slope * first ∧
      data.low + shift + slope * (stop - 1) ≤ s)

theorem prefixSweepOk_closes {b : Box} {first stop G k h shift : ℕ}
    (hok : prefixSweepOk b first stop G k h shift = true) : HeadRangeClosed b.slots 0 first stop := by
  simp only [prefixSweepOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hdata, hdense⟩, htail⟩, hwidth, hC, hG, hs, hh, hshift, hfirst, hstop⟩ := hok
  apply headRange_of_valid_core
  intro hv
  have hcover := (prefixCoverFromData hv hdata hwidth hC hG hdense htail).1
  exact headRange_squarefree rfl rfl hs hh hshift hcover hfirst hstop

end OddWeirdSubproblems

namespace OddWeirdSubproblems

open Finset

/-- The large picked divisors and the small bitset seed are listed in
increasing order. The optional shift may lie on either side of the seed. -/
def pointBitsOk (n s : ℕ) (seed picks : List ℕ) (shift : ℕ) : Bool :=
  let used := 2 * n + picks.sum + shift
  divisorListOk n (seed ++ picks) &&
    (decide (shift = 0) ||
      (decide (shift ∣ n ∧ shift < n) && !(seed ++ picks).contains shift)) &&
    decide (used ≤ s) && (subsetBits seed).testBit (s - used)

theorem pointBitsOk_closes {b : Box} {seed picks : List ℕ} {shift : ℕ}
    (h : pointBitsOk (number b.minimum) (divisorSum b.minimum) seed picks shift = true) :
    b.Closed := by
  simp only [pointBitsOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hdiv, hshift⟩, hbudget⟩, hbits⟩ := h
  obtain ⟨hnd, hsub⟩ := divisorListOk_sound hdiv
  obtain ⟨hseed, hpicks, hd⟩ := List.nodup_append.mp hnd
  obtain ⟨t, ht, hsum⟩ := testBit_subsetBits hseed hbits
  have htdiv : t ⊆ (number b.minimum).properDivisors := by
    intro d hdmem
    exact hsub (List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp (ht hdmem))))
  have hpdiv : picks.toFinset ⊆ (number b.minimum).properDivisors := by
    intro d hdmem
    exact hsub (List.mem_toFinset.mpr (List.mem_append_right _ (List.mem_toFinset.mp hdmem)))
  have hdisj : Disjoint t picks.toFinset := by
    refine Finset.disjoint_left.mpr (fun d hdt hdp => ?_)
    exact hd d (List.mem_toFinset.mp (ht hdt)) d (List.mem_toFinset.mp hdp) rfl
  let u := t ∪ picks.toFinset
  have hudiv : u ⊆ (number b.minimum).properDivisors := union_subset htdiv hpdiv
  have husum : ∑ d ∈ u, d = (∑ d ∈ t, d) + picks.sum := by
    dsimp [u]
    rw [sum_union hdisj, sum_toFinset_of_nodup hpicks]
  have close (v : Finset ℕ) (hv : v ⊆ (number b.minimum).properDivisors)
      (hs : divisorSum b.minimum = 2 * number b.minimum + ∑ d ∈ v, d) : b.Closed := by
    apply close_minimum_witness (ds := v.toList) (Finset.nodup_toList v)
    · intro d hm
      exact Nat.mem_properDivisors.mp (hv (Finset.mem_toList.mp hm))
    · simpa only [Finset.sum_toList] using hs
  rcases hshift with rfl | ⟨hproper, hnot⟩
  · apply close u hudiv
    omega
  · have hnot' : shift ∉ u := by
      intro hm
      have havoid : shift ∉ seed ++ picks := by simpa using hnot
      rcases Finset.mem_union.mp hm with htm | hpm
      · exact havoid (List.mem_append_left _ (List.mem_toFinset.mp (ht htm)))
      · exact havoid (List.mem_append_right _ (List.mem_toFinset.mp hpm))
    apply close (insert shift u) (insert_subset (Nat.mem_properDivisors.mpr hproper) hudiv)
    rw [sum_insert hnot']
    omega

end OddWeirdSubproblems

namespace OddWeirdSubproblems

def pivotPosition (xs : Coordinates) : ℕ :=
  ((xs.zipIdx).foldl (fun (largest, best) ((_, e), i) =>
    if largest < e then (e, i) else (largest, best)) (0, 0)).2

def reconstructLargePicks (fs : Coordinates) (p e : ℕ) :
    List ℕ → ℕ → ℕ → List ℕ × ℕ
  | [], _, target => ([], target)
  | rank :: ranks, cap, target =>
    let base := divisorOfRank rank fs
    let exponent := cappedExponent p (min cap target / base) e
    let d := base * p ^ exponent
    let (ds, remainder) := reconstructLargePicks fs p e ranks (d - 1) (target - d)
    (d :: ds, remainder)

def guidedPointWitness (b : Box) (slot h : ℕ) (ranks : List ℕ) : List ℕ :=
  let fs := b.minimum
  let rest := fs.eraseIdx slot
  let k := pivotPosition rest
  let (p, e) := rest[k]?.getD (1, 0)
  let shift := (fs[slot]?.map Prod.fst).getD 0 * h
  let target := divisorSum fs - 2 * number fs - shift
  let (ds, small) := reconstructLargePicks (rest.eraseIdx k) p e ranks (number rest) target
  let short := smallPrefix 1024 (sortDivisors 20 (divisorsAtMost rest 1024))
  let seed := bitWitness short small
  sortDivisors 20 (if shift = 0 then ds ++ seed else shift :: (ds ++ seed))

theorem guidedPointWitness_closes {b : Box} {slot h : ℕ} {ranks : List ℕ}
    (hok : witnessOk (number b.minimum) (divisorSum b.minimum)
      (guidedPointWitness b slot h ranks) = true) : b.Closed :=
  witnessOk_closes hok

def decodeGuidedPoint (b : Box) (data : List ℕ) : Option (List ℕ × List ℕ) := do
  let (tag, rest) ← readVarNat 64 data
  let i := tag / 8
  let j := tag % 8
  let fs := b.minimum
  let h := if j < 2 then j else ((fs.eraseIdx i)[j - 2]?.map Prod.fst).getD 0
  let (ranks, rest) ← readLengthPrefixed rest
  pure (guidedPointWitness b i h ranks, rest)

def guidedBitPointOk (b : Box) (slot h : ℕ) (ranks : List ℕ) : Bool :=
  let fs := b.minimum
  let rest := fs.eraseIdx slot
  let k := pivotPosition rest
  let (p, e) := rest[k]?.getD (1, 0)
  let shift := (fs[slot]?.map Prod.fst).getD 0 * h
  let target := divisorSum fs - 2 * number fs - shift
  let (ds, _) := reconstructLargePicks (rest.eraseIdx k) p e ranks (number rest) target
  let seed := smallPrefix 1024 (sortDivisors 20 (divisorsAtMost rest 1024))
  pointBitsOk (number fs) (divisorSum fs) seed ds.reverse shift

def verifyGuidedBitPoint (b : Box) (data : List ℕ) : Option (List ℕ) := do
  let (tag, rest) ← readVarNat 64 data
  let i := tag / 8
  let j := tag % 8
  let fs := b.minimum
  let h := if j < 2 then j else ((fs.eraseIdx i)[j - 2]?.map Prod.fst).getD 0
  let (ranks, rest) ← readLengthPrefixed rest
  if guidedBitPointOk b i h ranks then some rest else none

def guidedBitPoint : PointReplay where
  verify := verifyGuidedBitPoint
  sound := by
    intro b data tail h
    unfold verifyGuidedBitPoint at h
    obtain ⟨⟨tag, rest⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
    dsimp only at h
    obtain ⟨⟨ranks, rest'⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
    dsimp only at h
    generalize hok : guidedBitPointOk b (tag / 8) _ ranks = ok at h
    cases ok
    · contradiction
    · exact pointBitsOk_closes (by simpa only [guidedBitPointOk] using hok)

/-- Use a direct rank hint for the larger cofactors and the single-byte
cofactor hint for the smaller ones. Both cases use the same witness checks. -/
def hybridPoint : PointReplay where
  verify b data := match data with
    | [] => none
    | tag :: rest =>
      if 64 ≤ tag then guidedBitPoint.verify b ((tag - 64) :: rest)
      else (PointReplay.ofDivisors decodePoint).verify b data
  sound := by
    intro b data tail h
    cases data with
    | nil => contradiction
    | cons tag rest =>
      dsimp only at h
      split at h
      · exact guidedBitPoint.sound h
      · exact (PointReplay.ofDivisors decodePoint).sound h

end OddWeirdSubproblems

/-! Input codecs for the bounded stream replay. -/

namespace OddWeirdSubproblems

private def rankedBoundedPoint : PointReplay :=
  PointReplay.ofDivisors fun b data => do
    let (count, tail) ← readVarNat 64 data
    if count = 0 then decodeRankDivisors b.minimum tail else readNatList count tail

private def verifyBoundedPoint (b : Box) (data : List ℕ) : Option (List ℕ) :=
  match data with
  | 0 :: 0 :: rest => guidedBitPoint.verify b rest
  | _ => rankedBoundedPoint.verify b data

def boundedPoint : PointReplay where
  verify := verifyBoundedPoint
  sound := by
    intro b data tail h
    unfold verifyBoundedPoint at h
    split at h
    · exact guidedBitPoint.sound h
    · exact rankedBoundedPoint.sound h

private def decodeBoundedSweepAction : SweepReader := fun b first _ data =>
  match data with
  | 5 :: tail => do
    let (ds, rest) ← decodeRankDivisors (b.minimum ++ [(first, 1)]) tail
    pure (.point ds, rest)
  | _ => decodeSweepAction data

private def literalBoundedSweep : SweepVerifier :=
  SweepVerifier.ofActions decodeBoundedSweepAction

private def sweepCoreShift (b : Box) (tag : ℕ) : ℕ :=
  if tag = 1 then number b.minimum else 0

private def verifyPrefixSweep (b : Box) (first : ℕ) (data : List ℕ) :
    Option (ℕ × List ℕ) := do
  let (params, rest) ← readNatList 5 data
  let [stop, G, k, h, j] := params | none
  if prefixSweepOk b first stop G k h (sweepCoreShift b j) then some (stop, rest) else none

private theorem verifyPrefixSweep_sound {b : Box} {first stop : ℕ} {data tail : List ℕ}
    (h : verifyPrefixSweep b first data = some (stop, tail)) : HeadRangeClosed b.slots 0 first stop := by
  unfold verifyPrefixSweep at h
  obtain ⟨⟨params, rest⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  split at h
  · split at h
    · have he := congrArg Prod.fst (Option.some.inj h)
      dsimp only at he
      subst stop
      exact prefixSweepOk_closes ‹_›
    · contradiction
  · contradiction

def boundedSweep : SweepVerifier where
  run b first top data :=
    if data.head? = some 4 then verifyPrefixSweep b first (data.drop 1)
    else literalBoundedSweep.run b first top data
  sound := by
    intro b first top data stop tail h
    change (if data.head? = some 4 then verifyPrefixSweep b first (data.drop 1)
      else literalBoundedSweep.run b first top data) = some (stop, tail) at h
    split at h
    · exact verifyPrefixSweep_sound h
    · exact literalBoundedSweep.sound h

def boundedPalettePruningWith (useAlternate : Bool) : BranchPruning where
  verify b data := do
    let (G, rest) ← readVarNat 64 data
    if G = 0 then some (false, rest)
    else do
      let (k, rest) ← readVarNat 64 rest
      if prefixPaletteOkWith useAlternate b G k then some (true, rest) else none
  sound := by
    intro b data tail h
    obtain ⟨⟨G, rest⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
    dsimp only at h
    split at h
    · simp at h
    · obtain ⟨⟨k, input⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
      dsimp only at h
      split at h
      · exact prefixPaletteOkWith_closes ‹_›
      · contradiction

inductive ClosedBelowCuts (B : ℕ) : List Box → Prop
  | nil : ClosedBelowCuts B []
  | cons {b : Box} {bs : List Box} :
      b.ClosedBelow B → ClosedBelowCuts B bs → ClosedBelowCuts B (b :: bs)

theorem ClosedBelowCuts.closedOfMem {B : ℕ} {cuts : List Box} (hcuts : ClosedBelowCuts B cuts)
    {b : Box} (hb : b ∈ cuts) : b.ClosedBelow B := by
  induction hcuts with
  | nil => simp at hb
  | cons hd _ ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hd
    · exact ih hb

def checkBoundedBlockUsing (oddSplit : OddSplitReplay) (fast : Bool) (B fuel : ℕ) (b : Box) (cuts : List Box) (count value : ℕ) : Bool :=
  match expandPackedTokens count (bytesFromNat count value) 0 0 with
  | none => false
  | some data =>
    match replayWithSizeLimit true fast B boundedPoint boundedSweep (boundedPalettePruningWith fast) oddSplit
        (fun q => cuts.any (boxEqual q)) fuel b data with
    | some [] => true
    | _ => false

theorem checkBoundedBlockUsing_closes {oddSplit : OddSplitReplay} {fast : Bool} {B : ℕ} {b : Box} {cuts : List Box}
    (hcuts : ClosedBelowCuts B cuts) (fuel count value : ℕ)
    (hlo : 1 < b.next) (hodd : Odd b.next)
    (h : checkBoundedBlockUsing oddSplit fast B fuel b cuts count value = true) :
    b.ClosedBelow B := by
  unfold checkBoundedBlockUsing at h
  split at h
  · contradiction
  · split at h
    · apply replayWithSizeLimit_closes _ hlo hodd ‹_›
      intro q hq
      obtain ⟨c, hc, he⟩ := List.any_eq_true.mp hq
      exact (boxEqual_iff_eq q c).mp he ▸ hcuts.closedOfMem hc
    · contradiction

def checkBoundedBlockWith : Bool → ℕ → ℕ → Box → List Box → ℕ → ℕ → Bool :=
  checkBoundedBlockUsing .none

theorem checkBoundedBlockWith_closes {fast : Bool} {B : ℕ} {b : Box} {cuts : List Box}
    (hcuts : ClosedBelowCuts B cuts) (fuel count value : ℕ)
    (hlo : 1 < b.next) (hodd : Odd b.next)
    (h : checkBoundedBlockWith fast B fuel b cuts count value = true) :
    b.ClosedBelow B :=
  checkBoundedBlockUsing_closes hcuts fuel count value hlo hodd h

def checkBoundedBlock : ℕ → ℕ → Box → List Box → ℕ → ℕ → Bool :=
  checkBoundedBlockWith false

theorem checkBoundedBlock_closes {B : ℕ} {b : Box} {cuts : List Box}
    (hcuts : ClosedBelowCuts B cuts) (fuel count value : ℕ)
    (hlo : 1 < b.next) (hodd : Odd b.next)
    (h : checkBoundedBlock B fuel b cuts count value = true) :
    b.ClosedBelow B :=
  checkBoundedBlockWith_closes hcuts fuel count value hlo hodd h

end OddWeirdSubproblems

namespace OddWeirdSubproblems


set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock0 : (⟨[⟨5,1,false⟩,⟨11,1,false⟩,⟨13,1,false⟩,⟨17,1,false⟩],19,10⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    22 29 0x4050405040506000a110105050503000a0b01040502000b0101000100
    (by decide) ⟨9, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock1 : (⟨[⟨5,1,false⟩,⟨7,1,false⟩,⟨13,1,false⟩,⟨17,1,false⟩,⟨19,1,false⟩,⟨23,1,false⟩],25,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    17 32 0x50101090e010608010b0c01070b010504020007070105040200050101000100
    (by decide) ⟨12, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock2 : (⟨[⟨5,1,false⟩,⟨7,1,false⟩,⟨13,1,false⟩,⟨17,1,false⟩],19,10⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveFourteenBlock1 (.nil))
    18 32 0x4040200061b0105040003000605010c0e010404000005040600080101000100
    (by decide) ⟨9, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock3 : (⟨[⟨5,1,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨17,1,true⟩,⟨23,1,true⟩],29,9⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    26 25 0x701010401000a15010709010e070104040200060101000100
    (by decide) ⟨14, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock4 : (⟨[⟨5,1,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨17,1,false⟩,⟨19,1,false⟩,⟨23,1,true⟩,⟨31,1,false⟩],33,7⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    33 145 0x404040400000600070101045d02048aa8d0d5d6fda89567a7f890a8fa91df058e8183e2f3e2cd02aed1f1d792f75bace4fdb110b0ebab0ca5bf2f07010a0359020aaa9299b9d3aaf5f303e78db8c4b2f4eee72ad395bbd5a2b5ad45c0c2b9c6949314c3edbdc8e50399e4baaf02d081f501bd9301fd01d147230c0353020574000601010c070104040200100101000100
    (by decide) ⟨16, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock5 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨47,1,true⟩,⟨53,1,true⟩,⟨59,1,true⟩,⟨61,1,false⟩],63,3⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    22 4329 0x40401c9020180db8de698f682e5018c8db3ac92e6fd08f2fd8d9f8502cdc7d1b348a2c75dc9018517080301c70202848fac90dc8bdae705a0a2f9fa9d99e50880f2e3c588ff04fb97e0abf521cbdf9b13a68353000501b90185010a0301c50204988580c7d2e5b6db52ecd18489da9f49aeafc3c9b305b0e7938b02a0d8971db30701080301c102059cefc6c4e883e3f703b494b5e990edef058c9abfabfa8b218a8f8f8901f1ca4f00050cbf01170100050bcf01bf020aada9edc68ff6b7b11980e58afdf1aa8d0fffd0b7e5aff3099e9bf683b107a7eeade702b0d6c558cb1d2c000514db01b5020ad9a1abf086c6ddff73e3a8dba3f6b0e90185f29fbcddabcb45c494a9adbf2100051a9a011ea6c303000903e401b32f110b0e0301b3020df588dcd785d1b5f76ff2cab1cdd08bb777e59397ec8731b784a70d9d9d01fd3b11080301ad020f81c8cddac7cac3af02e0ab8c8a8cab86d119eaf2ab95ee81e30ee19fe4a2eb9103fbb181f9d141f58f951498b34d131161000501a501a7020ed3c5aaf1d7bfc5cb05b2feccb7addae3df04ca92f3a4c78cbf08dfebd797bf02f1dcfaff09a38f1ca34d17110b050c0301a3021780ecc487e481aacb1ecf98e59d80e68f02bee4cfa3b797cf04e394f09bb5b56b94e5e5a506f5ede302ccbf11d56400050dea01019d0216e08bb5d3a1e293cf03a3b1d6d3f4c0e1ed32d4f993ea84cff902ddcce5e4c0ace565cfcea7f79909a5e0db9356beab1487493600050fb2010197021b81fba0d9f296b7913d91e0a8ef88f9d301b1d7fdfdc3caa3028f8a86f4ff8d58d0e18883069482856ad34913070a030195021fd1c1f6eee58ab19b0191b38896f9aeaab903daac93e39eaceb03aff8d9a2f2fd01e1f4bee9bd1cb1beb30582f149070167000507c8011f979fea8db6c0c8b902d4b9e2dc9adbf6b102c7f895c1f1aafd01c7fff7f9e5915ee99dfcb91acbc7b904e8c101fd01a11132000507c1011de8b9c3e9aae38e9306f3cea1fec4c5cdd728a482d292a6d2b968b1c0b4ba919106a0acede399558a849508d2ab2e000c08b1010183774d4947350b14030183021cf3f5aaa6cdcfbccf0a9bbed1adb3beddcd04fbf4a1ddcccbf30591e9d7fae1cb0fc4c192cf0380cbd50deb01d13b010a037f0229d7b2bccf8ca5a39b04e3c8c8dc84f9d2fb0eb0e49be89d8ab93be3dc9adfead90ab086b3af9d18efc6e307baa9018513010a037102289ac3f8e2f9dddcef079f81f3c8d78fa5b30194e6e48cc7d5b3f90aadbbbd9eb0acdf2df7d5ea99dc8135d783e2d1f904d3f4d5c96fddc101af000b0cd101070110036d0227bc8cd6ecf0b9f9d909cf97c3b5b6a5e4d352e9908eb080f9cd02caca87a4bd88dd75d0c8be9c990894a7a08304d5d78701aedb01bb173d00060bda012ff3f3f6c9a2f4b5cf03ba8eb0a2fcf390a73f94abbbeda2dde102e0d2e1a8fb9fef02a6bc918acff31ed8ce84e10388fcdd3dfb771d0a0367022efcebbb8db8ccf09d05e3c683ecb7c7dfa116e8cddad8cca8e72fc98be5fc9eeb26dbdeadb2f111f8da969f09bce50deb770b0a03650236ceb7d9a18d9f81c535a8eed98cb7bced02f0f9a68ed3cae1199ac9aea8d8cb02b5b7c389b1019700051289016ee89f31a301fd01d1610b0c0361023880bdcf8eb1aec6b702fe82bdcc99f3d19925d8e7ef9ff2acc70192e4deb5e986e547dda5afd491438cd5a4eb0593f3a101fd01d1130a035902349d9ba1c198bb9ddd07bb83f2c095e3f1fb02dfed9cdb81a4e6cf048c81998fd8c3fd0580f596f4c18d019b9b8fdbcf1089cdd91db3171307010c03530231db84ade387eeada10ea9b5a9b29ebc808346b0b7bc9cd3b5b153f1d4ccacba8515adabbf87ef068bf4ef8b59c7fd16b311010a034f0233000001a7020295f8f39d8fc294ff16b9c485b7bdb6cd1bca93b9ea97ff4da3b4c69be7338986aeb507d387ff01b39577080301a30205d9a4f4aeef84df9b65c5f9c2bce9fd8771c094c1f098ad029d8bb2a8f5a711bf94aab146f9ed029b000802f101130b07010e03019d0209acc4c8af94cdd49d01a5eedfcf8ff9d7e33ad5b1d4c6d78949d0f0d0908f3888eaab8706f2abaf56c517080301970239000902ce01399f979283dbaa8d6dfea3e3e3a3890ccd9ed8d908fc9911f32f0b1b00050ad1010dc2ec92bba199c1950585d6bea1abd7adfd2ff1e598b4829ccf59f4c884a68389159dd3f4cef10ad3d8cccb05e8f901fd01bb0b0a03018b021489dad0cba38be1bf209880fc81b7c6db2195fec9859e9f01d0f298b6ab559e9cb734debb2be901cb0b016400050ace0115ae83e9b1d6cda9ad0389dfa8cfcbe9b18705beeea5eea1bfbd01e4dca7f6af872a8feaeaa306d1d5d101c7ad1107010a0301830218f5d29fd7b3a0bf9502a1fbebcde1e085df07c8c396c2f5ccd117b58385d1ffd934ccacdce4d306d4f8bbb77fa6cd13bb01d11107010c037f021bead0e995aee496b7089082f693e0abc6f97bb29faff3c8b5fd4dabc8abe19ab32fc488848ccb0ae5cdf4830a98cf019e000d0699014f3d0b01120371021aecc2d187828ac59b1100093f0101a184a2d79e9bc69f01afbad999c3e0f1019fe5dce09ae1038eb5d885bf13e680fb44d501d14d0b010c036d021aadbbc4ffebdddccd0bc9e6dba8cd9d9aa902fff3efaf8bd1f9bf12cab1b1c3fcf7970393bbfeb2a0ff01c19fa5bbbb0fcaa7890291bb4d0b0a036b02298efa86c596dabecb02b5caf8edbdc98b9b25b38ac6eff584ef01f690d3aebfa1bb0e9ca9a1fbab01aad6ffb32d959919a14f130a03670228a8e1a7fbe0ea90d104cfc6acc6abfdfff123dfa59ab584f6976ccc848fe8e4db0cb69482a78b05e9bef6af2f97bd01d1000a03e3011d010e03650226dcafeae8f589b4dd08b8dba2ebc8d7dab569ba9ae4a395feb338ebad8fbdcea11197c5f3ee8503aaa6988b07dffd01fd01851d13010c0361022ce5f79981a5a38ce708d49ec8cccfa2e08708f6d6828bc4f5dd078fe0f6ac9bb303988bd7a6b367c2c90197d31d0b010a03590238c2d7aee4ade1b59b018dc3ec92e0d1cbef05febd85d4c9d6b109e68ace9ff29b08d28cf4ded505dcb486a5028991b968e101a1070a0353022100040401870203bbcafd93ffc68ee109db93adcde2eef917baa9f5b295b50ddbd5e5b3b304dc8ebdf96cb5b911d535080301830206c5fe8ff0dcbff3a567c98ef485d6ffef0485b196aab59afb01c1899dd98ab301c7a1c8e3f90d85fdef079ccd028f000801ca017f0b010e037f0214e0f1dc8cdbd2ad890b9493ddbc928cdd01eda59ef7febb3bab87abbd13aef3c707a8993b1108037102188c8c908eeb97db9949868bffa9b7fa990383e6ead1fc9af90294ab83fc928b26bfa8ed8f2ee28dbb06d4c7771d070a036d021aaa9f82d3f0e1f8f123c2b08de1d3c9c13ef9c087c5cbbd08a2b583a08906b9e296dd01d7d1e9018b000607dd01bb1d0200060aab011ccab4db89caa093a701eebdd5a5c6c3b6d901bcf5ae94e7d2c501c8e5ee9ea4f3079a80ebe70ed98b29000a3e01470c0367021c83affaee86f980a50490c68888ff8296f51ca5d89ca8f4bcdd1d8fe8d285e4d720cd8dfee9c50190a5e6933ee5af34000d06a2013b11100365021af5a6bab780aadaa107ede2d782c5a1f7af01b5aab8fc949d98fb0494f5fedcd19aeb0183f8c8fbf9af019d8186dab702dabaab378913070a036102114300050aab01710203ab9393a7a18dacd12be7b5a1faaf929b3b84a89fb088852d8f8dc8d2d109b2bef5f77ae69d01fd2f110b0a036d02058883c580b5a8dfe5019df68dcbb2d1ffd70882a2a58af28efd12f58da8cbf1db1bd7ede7e8ed078e9cb78902ffcfc9108b771d0a036b0205000000006e000c09e601019d0203d2d2a8c4908794c538afd2c39183abf102a4aff1f1b4bdc502e5d4d3fa908915e486cbef01d9a7ed01f3c377110b0a0301970205c7cfeadebec6efed079ef1d8d9f5ada701aac0c3cfee912ed292eef317b8fdbf3fb101fd3d08030195020cb8a393dea2e7eae95dd4f28d89c9efd958fb8be389beb301d6ecf3b0bdc71190d2a8b311cd87d101819d01a10803018b020dd9ffb2fefd828bb97ca8aeb0f99ddd9101f185f7daf9d3a365becbbdedbd01d1eaeff6871781bfaf6ad301fd4f0b0a030189020d8d96e492d295cf9304f1d3f7cee3d5c0eb0198bca0b09edf879905c5ecdeef858bc101c890ad8cccff7f82d8fcd9019791dad73bc7cd01ff000702d401853b010e0301830214dac6938ef88eb0f101c0f4d2a6bda8feeb04b8fc9e978ed1b108ba85fcc1fbb303adaaa8cbb10ab89ced149ef716e977110a037f021ccefeaeead9c8acd9049bd884bf88e491e916988e98c396ab11a2c09eb6f50194c193cf5ccccb65000602b1012f0a0371021bcda9bbf3b181e9b50887bbe7ace892e8db18fcf8e1bce5dbd318aca399d6c19501bcb59bf6df1eb29ea907f283018517130a036d021b8cbf82b7dcdec7e309c9daccf28181d4895097efbfd7b2acfd08efbbcb8dfea3c520c2f3be9feab102fbe5d6e4c355a3f4f738e6f522e52f110b0c036b021a8aea8fc0b49884bf0bf3c5c6b9fcbcd6c702b38c81f6d2b9e8ef0193bba3fbd1e58d1a899199c0a70c97e0ffd90881e9f102e7e901af000633014f11010e03670229ba918fed9bb8eb9f389caaeee9c7fbf301e8e697f2b79afd02f8d590fee95cc48d970feaa92d000d04c201654d071003650227e7fed9ffd9dccdd304c89085a0ecf8b3b345e7b7cbb2a9ccbb01acd1bed7d9b3fb01a8c68db4e4d302bcf6d2bf0193aab101a1f33c00053c01a11107010e0361022e87b9d3b3e79cf0a90497f9cdb3a0d48a9b5cd7b7ddc78bd3c901b4b3ab84ced6ff5f8ee0deffdb4dd7c7e50ca48d37000603bd011d1307010e03590233ffbda6a5d5d39587038cb499fa9bfcc3bb34c4cdbbb0b787b301dd88a1b9f58ed701b7a0d4bb99eb01a8cac892d501f387b2f73fdea3339d0b0a0353021d000404018102018de9b0fabda09fdf4bd3d5bdff86c71ef195c19cbb03ece4a68517bdd713bb3b1708037f020db4b2e7d6aff08da101f599c5d5bdd9949729c598bbfba5aee50181b7a686ba83af05f5f5f3bbf3028ebfbafd4ed69f598f59130a03710212fdda9b899dc4f6c169e18fdcb8ace0854cd0d5accf8ddb01a1ddc0fe94a70191f8e480832380b7eb0bdabf01fd0b010a036d0213d3e8a49e958a81f3029afdc3e3eb8cc8b3039aa7b59feae2f70496a0b583e6ed06a5a1eebc971df6a7b3079ccd01cb130b07010c036b0217b4b5fee0c6c885e502c0ecf6abe596ace110b7a1a8c58192c120a0ceef94b6c7109dfa80b8eb25fcbac104b4af02c500057201bb0702000502e90119c6efa8cb9eede49102bacfbc8fccebd4f30eb69ad7ed859fa7559c92a2ed8b25c6a6debd048cd7d902b5a54913010a0365021bd6acf9afc4ece7cf0489f4fbe88de0d7bf42eb8eaee4a8d8f35ea9cf8c8d9db942ebebe9eced17d28ae6fd1fa0b3d122fb9f01fd01d101cb01bb01a101857761592f0701140361020f00040404046d021b9afec6bb93daa760c0c6bff59ab303d0d583c6c3028cd2d4d323d8ad13bb01851108036b020301ab0006010108029d0173020ca1b2b7a0c8c79913c0b8cacef0dd46e386acd323aebcfb11c7f9710b010803710204fad7cc97939a8dd51ceb90e2c6c8f6b719d4a1ddf5a98f01afafe194d10bf4dd97019c933b0108036d0207d387e5dfccf7a4d70a9ecbf1dca5b7ef09e0ac96e6dce917a499e4910fe5aee915a7eb2fc33b0b010a036b020cc7dd82c7bedbf0a71fc8b3e7f7cfd5c501b1c7acacc7eee152f2a98aabcd5ae3dfa4d1068cbcaf31a301fd59170b010c0367020ec1bc9fc4f6b8b8b76a86c6c590c3f4bb02e4bab1b68d9195048eeff89fbdd701c7b9fad5b507aaddd304ac8b01fd771d0a03650212a3f78ee5e4ffcfb30295cf9be583a780df0cc0c79dbdf8d504f4dac980f717f4e2f30281fb4d01080361020d02920009080104040200080101000100
    (by decide) ⟨31, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock6 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨47,1,true⟩,⟨53,1,false⟩],55,5⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveFourteenBlock5 (.nil))
    21 829 0x404750202b4e0f5e6d988b1cd13899293f0b0a4bf65e88aed81e49750929fc1e8fd16acbcf98d0a92e1c510e88f1e9d01a12f0a037102079cead7e5f6d0dfd10eb58eda8ddbbac107e6edffd6dcdb0d9fdacea89b019ef3e89d01b6bf01d10108036d02099ac485efc4c9f8b73e83cab583cdffcd0487b4dbff858d9104a2c5ecc0adf31981b38a8569c5cf0197d301d113070a036b0196000a380151e5f0f9caaf8a9b1dc6ced5d2d5f90caca7ffb5bd038287bec3268d9b1d000704f301bb01a101851d170e0367020b000901b00102eba5caf2feb690bd17d5d1ec9cd1c0f733f1a5d8a2c88f0383898097cf06b8c0d5548701cb07270005038c0112f6d7c1ef898ab9f302da8cc0a293cad1b502c099df9d8ac9ad0981fcd8fbb78f0bc4b3cdfaff09d989fb5a974d231d0b010c0361021a9dfaec8096bfe8d304efe7e2bde0e1eec10ad7baefceede0e921cedbcec2b89b05e9e99b919b33e0e6a307f28364000603c801131107010e03590218bbcaa5b8a0beb2910deda6fe88dcb5eb8503e3dcd1b894efd509bed5ae9bf3bd06bc85eff8b171d99b9305dda701fd01d14f13070c0353021100040463020389898c93c3e0e1bf02ffb0dfb1df87c902dcdbd1b39e954fbb858de5099be69d01889d0501080361020300000075000e02dc010c02db016d0201c2e7f684b9b1bbcf12d5f0d8eca2cce354a4edd1d8ebc903c49bde9df513ac8d9d44d501fd018511010a036b0205eab4c9819d8ce599018ac69ea2a8cf8cd725c5b68de1f9c90dcca8a4f69304eda4d8bf108ffb1db3350803670208fe93f7e3f1dcbfcf43d3ffc28e9c83df02f7c0fb89d7b7bf08969d9db18dab01b9c191b8d561e5e7ed4ecbe173e30b010a0365020ea9b5a9b29ebc80833a91c6adb3d1e4912e8caa90f3b4877de49bf0ca8701a5fdd2fce710dc80e30786f901fd350b0a0361021886e0e4f3e186c8bf0196f9a19fcdd9aee304a9b4cccfc4c6d70f94e1c1f7f38902899bf88be93697a0c13bdfa92d8701851d13010c03590219a5de95ad92b3bed707b196dc8cb18cd2d937ccd0db8ab5b9c902a5dbaeebd8d59d74bce4efb1d33493f4a5b304c1e7b70488d901fd01d101cb010c0353020d00040402c2000607010b0b01050701040400000000000700
    (by decide) ⟨27, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock7 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨59,1,true⟩,⟨71,1,true⟩],73,4⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    21 1818 0x40401b50202dec2cfd0b6f7ee910489accad8a781e701f9c48bee9fdb01a68881c7fb01f7ecf3816cb52a000a06c701b3070c0301b30207e4b8efc3baa2dfb10184bc9ab0ddb4c55fb4f586d6d53ad4f4ae9519ab8dc708cca12a00080aed010b010c0301ad020ccfe3cddce692eded189b9585d9beb48d2fb9bba5a1e0cf03f5f9dfc6f722a2a7bd77b34f1f2d000501c901a7020fc4bebff2cda0daab4dd388aeb5b7cdd102e2c7b8ccb885a304f2c886e6bde776c7f6caed04e2a6a701d9018513070a0301a302149fa3c9d9f8b389b377bcd3feac8af1a10187f6e3a1b4d38d01839afcbfbecf0886c7e9c90c9a84dd02d4897717010a03019d021a84aabdafcaacaaf716ab9cdfb6afbaeb03d0efa1f9ba9f01a6ce9a85ff16e2ad9f0bc19d2bf51101920005058d01970219d898fba4e3d1f2b50b000962011af6cc838985d507e492e8ffa104b692829d47e9d701d901bb0b010a030195022493a1c5afe28bfbe90c99c1c8f9b483d97cbfe5e8ee83fd028e8cc9afb6a746cc92c4c912fb8bdb17f3050803018b0223d0d7b1facbc0a4b30298cae48de8acd4ff0dbb9df8a2ffd6db01d2eed79fabcb04c899e0fd07b0c49f01f99d01d90185070a030189022288f8f7db87dd9e9107f8fdabccf1ceb48774f390fef9e7d8a302e2ae88d6e4aba103b7bfe8ab9fd301cab0a9da9f4daf8d8323b0a75901be000606de012183e4d0f0dac5efa50c8da887b0bacfd5a70194c89ce1ca80d08944ffeaabd3ba9709ccf58da0b504d1d1bf9930a3f32fc301a11d0b010c037f0237f7b69bb38bdf80f701ffb390debcaf91b50b8dad9ff7bfa29328fbfa9bddecf303e0e09ec2f1018c9a90cd0feaa94d0803710239d6a2a6c89692db8903b2a091a9f29f9bf92695c4e397e3e0bd12b786fbb6a7af08b59bd795f33285dfb924afbf31af3b0b0a036d0238cee890dbfea0baef0592e6c7aba2e085ad01a0c695d7fee4ecef02fae1dfa8e8edff1e8acad8fdf90ae6f1b98521feb50508036b0236bff3e583cebbfabb0bf187f6a2bcb5bfa35ec7be9fae9bc92deac2b985df09aef3b1a9488fd5298301851d010a03670243b0f595f6cab0b4cb56cba1b492c1df8f3ee6b3e99588bb649dc993eba31e98f7c8dd04ed8fa301e0cb771d070a03650240dbaae9fc82ffcd8f05f183f2ae97c5e48d689585cd809fd9a50780c0dcb1a5b102e6b6b9e2a12189f5a301a4b902eb000d02df01614f13071203610223090005058801018f0204bdb5c9a08bafb2ab118ddd8294f2cac90bb3bddefbbac3019693d4a69932fc8bd901aeeb4f132a000503a7018b02069cb89384b395adc968a0c683b99c9ffd0693b29c80ee91c106f5a5bcf2d5bd02f386c5eca950d1b2cd2898ff0fa51332000501a5010189020eb9bfe4d4c7eba0b5068ee4948ea1f4d711b0c3b0aac4cb03e4a9edfaad04d493db3da71d0b080301830212f9ede18addd399cf3df7d083fdceb4f542ee92cbcd869d2ecc89f8c7ef2fe08984ed1bc4bccb0b828158000c0186017f774f170b12037f022281bbb1f7cd8ce99502c8f0bef7fee3bbf313aca1e8f8b383c34dd8b9c4c59ff37ed5c8c796d922f5f984d707c9e18b5be91f1107010c03710220e7adfaf6e294a68107d3a684f1da96f9970197dcb6ebe0f3aa9b04b9afeee6e485b905d1c6edf6c1c9038db6d990831de2f9b303c0e37a000d47016d674f4d1f070116036d02209aa79fb6acd884b70be6d4ac8eacffd58d11fa8696ab90c1c71dfbe492f18783169cc38cba9f02a78ff28f25edf73a000c02ba01776b674f4d49471d170b0118036b020f0001890206979186c0fccbd0d717a699a299d0ddd564a7d5e9dadaeb08b98ca1f7c505c48acd32cf1f1707010a030183020bc5a3e8a4eabdd6ff1cc5abbae4bbd8bf1ee4b5ebd68ff523d3daee83af068bf4ef8b33f3bf67000a01c7014f170b0e037f021dae94b090cbc0968d01a3b2fcc3c0c080fb02b7d9f1d68c989f05969a88a38bdb0983e685f6cf01c9cafce304ffa9360007018701851307010e037102228ab8b8eef9eda8dd01e5cd89ddb5c98fcf16d9bcbfd491a1ed11d8fbd68a99a319d9a6a3e59501a9c7d19f50d1e526ff4f070a0308003f000a02b3010e029f01770208f7dfb4d993f4bda551b8dcf5a7bb82b15efdc7d68ebf930195eecdc4e7ad05dc91cba9488fd501d901d101cb01bb01a1018559130e0371020dc5d8d1aadf88f4ed02dbcd88e8afb7d58f12e481fecedfcf0a92d1a2dc9902baebb88754a7ed36ed1f13070a036d0211fec5ecc0c9acedcd01cb8ee5f2c3e28acf03b9ef8ad3b2ddb70a92ca81c2c1af05f19aada4b1018cc0c3890b85c901d91d170a036b020700730201b88ab884e0fbfacd08ad92c8aeeb9eb90fb8ccfa85bbb103efe7e4b0db0886cfc70186cb77170b010a037102078cfda6bda9bbcd8701d187c084d8b8b7eb0193aa85b8babc8302e48fe0a79ac52ca799a0a10adaa9cf04adc9470b010a030285000c19010a0f0104040200060b01050701040400000000000700
    (by decide) ⟨36, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock8 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨53,1,true⟩,⟨71,1,true⟩,⟨73,1,true⟩],79,3⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    21 3721 0x40401cb0226d193e8b1a2d8bdd743defab5a3c5cc9f02a194fdd0818bf34ea6dbcf85cd06d693fbb50196e6c971bf1f30000502f901c702269fba9ae5c2c0b7f501edca85bffdf1fda508b2e8c6efb6e3e301e396d698ec81088688ec8f02bec7d132e101bb3000050abf01c50225bc86ffce8290acb104c88ac1ccd7d290b10dd8c0cda1bcd89117b38bc9c1e0bb03899983a3bb01bbbbb1c32e000511fd0101a11d030005038601c102258aadb282a1f8a6cf068392e6938ecc89e502e39fa8a5ba82c702a5fdac8aff8d3cd1dec3e10af1b4d93a85018513070a0301bf022f89b6dd8cbcc1a7d77bddbbd884cedab702c58aef82bf9eef01f7e6fcf9ed931cf1d6d4bf07a9aafb4bed1f6300053601b5022ec6ecc9d7a5f5d0a102b9cfe8f78fbc8afb05bb97e4bb8ef6dd07f4e0fbc7eaa902bc99c986ab79a6b6d101dde71d3100050dd601b3022cff8e8fb7e292c9ff06ff8e9ab68b90839f02cfae8ea9a8d0df5bb597dcec8f0c9ed297fd028db7e901f3f101d94f0732000507d1012bb7afd5989eafc3dd0babbb8db4febcaaa318ece6e5f08c82f101db9984d2da8921000510e00112a1cec307dcaf11f31d070b00050ceb012ab29baeadf19894f10dfaa2b9b2f0e4fcc54ac887c0eca8ba95019aaee7d19ac8e101d2dea2eea3b135e181a5f506c899c501cc914f1737000507bf0128eabcf48eadb58ecf1297e185bb8cd9a2bd6ba9bca19ce0c7af05c3f9feccdaf9e903aeefedbc9b9f04afdca8a3b3018cc0c3891ab88b10c5170b013c000507bb0127a2deb9eee9d288ad0900090cd10119adcb9cefbbc99335f882e295c5b511f4c0e9f909c0adc903b88701d901d13520000507be0126e094a6b9d386b0f70900090cd50101fc86b79bccb0e6b106998fb3aebdbcb905b39f9ff5cbb501c0fcc6e7bf24c7d7e50996a325000b02e80195018577591d110114030195024288dc99a2aab997a102d7fb9180d6e981d502f1fcf59ff690930c89fce496de8707b9cae2da83019a918f8316b2e301d901d159170b4300050cc001418f859dc192e89f9b04a99094ffd1c0cfb329d997f3fde8f8a30b91b6ba8b859702dddc9aa29937a6d8cd0bbbf301d91f31000607a8013ea280aa9dcbf5b78909d3fed7a8ef8393bf669ce1d88997adf14addd1d2bba8b30fc2b0e5e7fb03b790f1ff01b785871db32333000607a7013caed2b2db9cd3c6fd090009430140f781c09da499ab05b4f3bdf7a281f903f0f280ccbd8f019cb5dfbc910cb694f507d6ad2400066f011f17010e037f0243dcab8ca9fac0b0b10de4ad82c196d5ccd70ccafdeb84cdc6c70a95b888dfdbc703ebf6b5a6cb01db9fa6b91197d901d901d149133c000510fb014f89e7a9abe78ce0a904b3fcafdcc3d785df0c91fac1eef5eceb1ea0fdc8928703e39aef834ca39728000e118901594f110b12036d024dd08b80d48d919bcf06e5fdb6a9c9d9fea511fbeda0a9d7feb715d4b4b8aadcb71f93a4cba28f02e199a7c701e6bc37000810c301851d0b010e036b0253c1f2d2fbeb9d9bf102f0cefeb99e9789e512938cfb9b90c8b50df2c2bd97edd512e18fd1e4b507d5eae3e903fdf08f01e4fd01d977110b0c03670251f2a9cb92a4e5fca305c0aca3f4caa89f8f108b9788a0db95b725fa9aa1cb9fd509aad6b8a6ed0188d3e6870893d573000a0de50159110e0365024ed397bbbf97f7bd870a86e499f1f8bcc0cb659ac9f9928db1d5399d9588f9b68b18e78687d99121e8e8d4a57cc9cd0196f101a1130a0361022d4000060ab301af0211928aab97cfcde8d501a0bf9bc3a9f0cabd02eec8c29bbdb2a101c0e7b99ad0c533fcd9d8c30ca5bde503f5b701853100050aac01ad0216b1c19ff2e1c995b97294bc82ddaeb9fd4bb1e5bb9586e5048de9fbbcdf0ddaa99113916707080301a702199fabcfb0f2eedfed01a1d2d08082e1c5f102bbfceadc99da9101a0b3bcf6c98f64adeebbf91c9980c7528b01a15b000505dc01a30218a8b2d3c3c1f095d306e08ba6dbc5acf8c728eff3dfce83c1d77585e4d2f9bbb10afada819bb305f187ab810f8d300009118e01670c03019d0221f6cea39f9aa6cb9902a3d9b5eadcdaff8f06d8f1c7e797ef9709ef92fbd992df06a9be8190f105f4fce1f3018a9f8b14870185113b00050a830121bd8bfbe4a6d5c5fb04a894e9b1d0bdd59b0ba5ccb0b786928711a2cdf5baa6ad01e590fb98c70ceecaf93fc977132f0006059e0129eb92d7bd849c9dd704838db4e4b5cda4c50fe6b9f28a81a289528df7c29bfef76ea1b2ecf6d547fc97a2cb0dea88cf1888b11f0735000507e601299e8bfbfccedffc8d05f281daed9dc4c8cb3bf580d8f2ce978502a2dce9bdc2aca301a4a891b3e4d905c6d1eda90292f3db02c3b17711370005059d0127b6f7e9bbaeab97af0cfdb4fafbd8b2e4db08d4b7c4fdccfec30cf0d19ab2c0a50db595a3bef507dcc2a08b56839501d947320006059c01269ceab2bac3b2d49b118394bfacad89d3e13ca5bffdd7e1b3f30490b5a6949ae103baf6bacab913b196bf01cfaf01851d010a037f023e94aaaadacad9d1ed04edf699b5d4948f83079de69bc1b7c8ed06ac84a28ce7ff07eadad388d503ed8eb9029d937711660005059e013bfad8b4c2feb6dff909a698d4e7bdae91cf0187bba4ffd9f091df32cbe4d5d9fcf90fd698c5c9d543ec88db19f5dd2f0009088901850b010e036d023aedefb9b798a5a6ff0ceadcd0ed9ea8edc71effaacac1e3e58b60c28cfac6e2d528cecebebea739e6858120b28101d967130a036b021b0001a9020dd1828397b7d8ad894befb29cec94c4df56c1c792c0ec9702fdceb0ad8501dfe795db1fe5df139d01bb6c000501da01a70210e3c4def2b1a7b5af7ea9d8b3f3ebddbf099ee58af9cafef710f78ae09c968108e4f4bfda8506f0e4c5f301fb9fad77b313113500056d01a30215eec59ad9dfe7819701a3e7dbfce8c2c4c10db1f895a0a789e760f8e9dda4f106d5d6b3952682bd59ed1f2d00050991019d0217b1b9d7d690f1cbb90589d8ed8fca83aebf188ff5d0c7b5dbef7defbd9fbba48759afd8ff8bc90bcda184b902b58ec910c51f1d07010c030197021789e6d98780c7b2db079eed96a88e8891e512b7efc680df87ff35cbcfa3f9c304cba7dae3019bd7cb12d3170b010a0301950220b8dfc1a68b99eab106e0d2f9a9dba5d4bb23e4d683a1edc8990cd294acbfeecd07cdbac098cf7ef796a137baa314d14d1105010c03018b021ffcffa4dddb93f7cb08fcd09f86c8d0fd91299cf88296efcda501a1daf8e1d7b58b64c8fb92bb8b23eaedb5fd2d84909306dcbf01851301e0000502c20128faf7c0e994e6839305c6d6f4beda9cf1d916f6b5a797c790870bc1f5c9f6e2bf02caf3dff0db2d9c86830a9acb01d96b0b0a0301830227daec8598e1ad95cf0aaf8691e0809984b11bdfc6ccecf3a9e7549bb2a2c9e68b58bb94dbf2bb09ecf6fd952682bd21cd7f1f6a000607e5013cb488dff8d9eac78b02c082b4ecb1c2a3890287819bd3c487c902b2faf5c2bad15dfba5c0f36899b8c305c4f34f072f000507e4013ea4deaa91b2c7e4f504918ad3d1da878ddd0e80b6f983edd0bf01b789dc9dd3b121bfe7b2d70cebb8ab2da50705010a03160033000501ad018f0206a0e8aa9eefe0e7ef54f0c1e9a8dfe5a13eb1ddb6eb838d1296b4f7949744b2ab9110e28b01d977112b000605a10108b9a0ebe2d599f8e70196c780b69fa7a18301afa097ccb9aee3019dbed59ba38f19b2c4f79b02dc90a934cb01892e0007059c011080c583de8da7819301e1b7fdacd3c3fea51e8196c7f798a9168af1809ecf399eefc72a89bb17c50b290005029301070002001007cd0105010104019b0202c8cfd6c99fc4be990dfbd6ce98b7b39f07f1ee85a3a5bb03c884d6d8e530c984b5098c9901d901bb07050a0301970204ee87a0edb0c5bcad12c7bb97b2debdff1a9ab68bdaaeb70df9c5d485c57ce289b107ceb9590708030195020fc282f4f7f0d5c5e50191a39587a8abf8cd2fc7b5dabab18b1c81e785f5ed0491acdaa711d7d71f070803018b0212c1c59fb1ea8fc0bb3a8ec1f285e580890296d9efbcd58ded0193f7b7a3df9517c59bc8b501eb9cff01b7000a01e4011d11010e0301890216edd99e8aeec095eb0381ecbbc3bdce8f810ce3f0c1dcb7f8f703a8ed88d8939901dbc99bddf70d95e6cb2fad1308030183021dd28ca1d9a6a2ab957ba8fcf7d4ff819103a19f94b5e2b8d701faabb7d4b59716fca3e2a33cae8301851708037f0226a8c4c3ccb4eae6a30883b7aaffe8d58deb4ba9afaed2e48a8d4b99c997df80c32d9adff78dd11db5bcdcb92ce7d170cd01d91f0b010c03710224faf69ad8b7bfafd70c95b19febe8f6d3a302b8a0ace6b7d0b0a103d394f3a7ebdadf01abb3d6acfbeb79a8be8bbd1cc0cbed2eda8301da000c01eb01776d67594d4947351f1d07011a036d0224a48f869eb8e9d4b11094b1dd90e4cd96c301bc84c2d2fdc199a901eca5ffb0b998a73e9ae4e29bf516a8e8d8f301c49ff71afb4d230a036b02130001930207ce8cb7d5f0c99b8d2da2f6f0e6c3bfe9268e84e38f9c9339d4d4d99ced01f1d8b3937e90bb26ff018b07010a03018b020a8e82f3ffa68a9bc734838b8982fa9abf38b3e08788a5dd19f0e7b783d902d289e7e73dd5e111992311010a030189020f98b49399c0d8e19902dc9c918dd786899321d496c9969a80d55382e9b6fde9ef0192aeda83c09964c9ab8305f19701df000a01f10101850183490110030183021694aeb9c0a2e99a87018fadf8c0ee8e83896afa9684c2b88502d08999989c875cc5c2d5c533a5eb2ca71f131107010c037f0227e780adaf88f3f5b701a5aea0fde1fa99c307f4d291b8a0f0d703b9acfa8ec39526adccb5b90598f5a773f7590b010a03710226b2d3848ee8efe89b06b0c595c6a38a93a901bbe698fddaa5d78502f7eba3feaf98f101e8f2cac6bb831beebfa2fd03adc68f2fad01851f0a030c00040401af000c770104040404770209d39d9196e5b18de10183f5b8c1e884809d7a9b9391f2de8d0ca5d4c4958557af8fa912f0a101d901d101cb01bb01a11f13010e03710211dac5bdaa94e2bfd517e4db83f2e4b8a913c39f80abbfdf04b4b19ba4d95f9a9b911ec5ff01851307010a03040004046d000f0101000100
    (by decide) ⟨39, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock9 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨53,1,true⟩],73,5⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    20 275 0x50101047f0213ffc6dbfd99d6a8f72fdc90baa8f5ef831cf2ae8ff78a851198bda5ddc5039aa59c8901ebffe73a85010803710218bedde6ca9e80dda3029586d1d2d9cc9a8502a68d98cccee5e501e5ffabe8988930b5e083a70992a6e90196f101d901d101850b010c036d021da7d68fcae6c193d541b4bf97eee2ebc727f1b1dbb89acf09c2dcb8fbbd23949fcb0ca5bf12d31107010a036b02070079020cc6dfcadfaae3d9f114fc80bdfc98aaa306cbc8e485eda302bbdf8899c519aa9a8149b94913080371021383c1b7aef786f99943b1af88b0e9f79b5ca19ebc98ae830bacc39bb3ad01edc9e2bb46baf331a3771d010a03040001f5000c0c01040400000400090801050701040400000000000700
    (by decide) ⟨36, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock10 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨53,1,true⟩,⟨59,1,true⟩,⟨79,1,false⟩],81,3⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    21 1825 0x4040200050a8b01ad021ea9d6faa7ce888dfb03df93ce8fc5a4d7d30298c6bbc9f4b8b13feef4c8928539b3a1e29516c2e2d90181c71d0b010a0301a702229b93c2e6dec692eb02d8b6dfee98d8f7b51be8ebaf82efbfc724faa6bfe094cb168ab2e4b0fb0ea5eaba990baee2f916ab87590b6b000505920120f9fabaecb0d4ebd507fa90a8d7fa8bd3af5e8eb59edbfacfe304b689f9a6d7bc8f07efd1b7eca9810391b9d6fee302da88e92da501d11d0a03019d022e85e4b983ebf19b8717a5eafcfdb283d34babebc18da3f33cc1fb91b6990cfbfba9e703e091a147cf01a11d070a030197022db7dcaadb8d9af8e502a7c3a3f5d48fdd9360dfadbd8dbb95068fbee4f1e101c984d5bd15f3f120db670701019b0005059f012ab1b3e38fb3ebcdbb0c81d79dbb9087f4b578bbaab5cbcaad8d0dc5dceab8b7ed09d5bbeec7bf76c2bbb111e4e7139107310006059f0129e3abd4e6d595ab990de0a782bce9f9c18d01a7cccdfcdad09cd702dee690ef9f91df16d4a2e19cff028187edab6be2e131000b02b9018901857701100301890227f993a9ecb992c4b314c784fcd6efb6a39972b2a6e7f9dbb3cf02b0dacab9b1bca101f0d4e8f4b6e538d8eccced13e0acab09d4e73f000a01ef01671101100301830226dd838d9afbe5ffef1787f7e3f4ddedd1f302aea9efeef88ae4df26ab8ecca98edcbf01f8cb90cefddd159bd1bff90cc1d38505a2ad1f0b0a037f023efcdbd89283e1f9f90babf789c28784f6955fb9e5dad7ed84e501ecc1c5e8cdf5db74dcada793dd26b7d0d39b0bef9dcb6b8301d97900050995014ccbdef5bf939ab98701bc87f3f9b5c498af06e3c59ccaddfbfd049de2e195c4ab67c483edcb05e091a707a8992d00053a01851d010c036d024b97edcef7c496b88104b68dfd8ec7e399f102f3b08dc5b3d6dd09eccba39ee9830c9491aedd9339c683b316b2e335000b77018535130110036b02190001a70219c9de90b1bbbfcff90385d2b2ae84f986b10bd1a0fd91b3e3e9268cf98beafca563d7c5b0acad0fadd7fae901b1ccb92fc33f000501e401a30221aeeaa28cf3abd9c337d5aab9c3afd5814ac8b9f8c4e4a90fc0bfaff2bd01a194cdc940dcfd28000b05bf019d0185776b591f011203019d0220f6a785d2b4cc87e305e6c8bee68ce48d8b15fbd0bc988cfd8b5fbac2eec2cb18ade1b5dd04aa8ee50281fb01d901bb3d000605bf01970220bebea1c5b9eab5b907ebe2f283c2f6b09b21dae3908492f0bf10beb68eb584d704e4b5f4ccfb489ba8fd31b88f35c54d0b0a030195022c848ce39ef59de1ef04ddf4b2918ae4c887289ae1d2a2b398ff139afd82a1aec902d392bab2d913c8c6ef06dcbf19f577016b000502d8012bb380cfb2ddb8fb95079af7a3a1a799c1e714d88d96bfb0e48f7fd3dcf8e6d9dd06b7b182bcd31ca3d88b01f2f51f131131000704990129bfdc93ee968ac7870dd4ca8890b299de935adcee9dbd9cadad2e9088fdef83fd0fdc9eeceacb03a59583cd72c8eb01d5f301a11f07360006049301289dc3ec95e6c0f9d311f5bebe94bbd1d18901869fd6b7ac8cf39f08bf9ff6ebdce2e51193c281edfbbd43858ac5e70692f3cd4eb101d94f0a037f0241b5e0befdcd9dd6f505c891cbc6aedddebd14c1f9d2c098f4d52285d3c48ef1f710a4a8c3cbb906d8c9e6d301affedd3da74f1107010c0371023f8dab9e95bcf3ece10baef6a683ef92bddd08d8ffeea1c6a6a71cdf98b897c49301cdc7cc94e1348bf6d907a98b01d977110a031401ab000601b3018d02119a94a8838e9ff7ef49e0ead78986cab90283e6ca9383b301adbca9b88344b58cb50e96db2700066c01070a03018b0213f6d9ea9bc5f58dcd37c3e0ddc6f0eda101c6efa48bebf1a102b6e396b9b7af559feceab309d493b314ab1f080301890215f7f596a2d098ca9105fcd09eb08bf0b7ab1ea4c8cfd4a5abff4bf4c0f8e89c810da498c4beb302f9e2b3ed01a4e366000649013b0b02000501c2010701000801010902ea01018f020eb8d696bd8286d0ff01bd81bb98f6a2eaa17df1aa81a2c9f11499ebe6ca99029dceede90b96a52a000501b401cb01bb01a1018b0185776b674f1d1203018b0210c4a9949dfdf8998701e8f2e2b0cfb1fcd10fc8bc84bd91f4e70796a5e2b3cce90d8186c8ff089dd39977b301d901891d07010c0301890218db94aeac84c2d8ab01b3a7cf87e3e5f4d57187faaec2dadf1990bceadbd504f9e984ad01edc8ab42d501d901a1170b010c0301830217fac9bdc589a2aec7079ea29abca3bab6cd02e28dfdc4fa90a50b8da0c1a094d10ef798daa1e569ddb5ab0ecad301d901d101a11d010c037f0229b6cdec9eb5f6cce306f0ffd8cda3ebfdc15e8b93b3dfe580fd0198b8fa96a3a6f3018de2edcbe8dd1dacacd512f0a115b171010a03710227faf3ef99f98edc970d93e4f9d6ba93f9e30182f2fac89699a4b501cf8fb68de1ffef038f9af7d4f3ad46e7c8cb930acac9e525c74d0b0a030c02ad00070901050701050501040402000b0101000100
    (by decide) ⟨40, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock11 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨53,1,true⟩,⟨59,1,true⟩,⟨73,1,true⟩],81,3⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    23 2329 0x4040200050cef01bb022de8a5a290a2c2c3ed03aef08ba392fa9ad524f7ffa9e996e8b910d6ccfea09ebf0be0a6e9c1f703eab9c087039485d331a30185170a0301b50232b884f9a2e595d2d510c69882cca9f7c51084e29dfbeefb5eaeedf5a10dfbe0f10ac789600007038601057601b30230dfd1a5eac884bccb058794fab3f0f6d8f907a5aba48b86ceaf06dbf08fd3bfeb06b7ca9882c102ffc889fb07dcaf31000501ac01bb0b010c0301ad022f879dd2b2aaf3a6c109ede4a883bb89bdd91e9292b7a8a0cdab35b3a6e8d796a704deb690838f028197a9bf2ead8d24ed1f1307010c0301a7022df6fb9ae297bd97e50d829db8efaaf7aaab33a2f68fe2b5fc9d0887fbb0f1b8cf02c6d4ae89db3aa7b0e5228be901d9670174000505f6012c9ec7c7a9faac81db11d0c18b8cefa7d6ab628dfaf5b6f6cc8d649bc69ed681b502b885bdd7ad30fefe9f03f5a901d901d13200070d9e019d022ac693f3f1dd9aebd115f2b2819cd8fcb4f301bee3c1a7d7d98bfd08c9a198eddffd02dac8fcdaeb1790cac702f8a935080301970229fe82d889d3bfe4a31980a19ef096b2f6d705c5ed9dafc386e105a49bc6e4affd01d6efddcaa111fae38526ff018566000709e20147caa9e582a9e585d576fef0d89195a1a977d793d6f8d69103d1c3d48bbb53ababf916db2400077f015913010c03018b0246c6bfa4f98ae6ad9702efa6a6a784b1e1c318e9d59ad6bae28f0e92c5a3f9a7a1059795a4d9fb64eba8f331adad36000c06bb01670b0103000506bc0143baffe4ddadeaa3dd09ae949794f59affb90aedb8fff7caefdd1391aab0bcfdbd0981c99085f70180e1c9b31c9f912f000a480159110e0301830241b3aae4caefecf2e10be3f0d3a7dcbfabdd01f285b9b3a689b3b703e9d8cbd6c3b79d0490e7998ee2f903f4fecef8c16ac7fcbd0596ef3e000a0397014d070110037f0249afccdfca86d289a50cd88e9e80a5dc92f75b978eccc395f69301c6ab9cddf2bfd901dca9ddffe88b56d0f080b94bfbd8a92193d7591d0a03710255d6ac80fa87e0cdfd03a6d1d4f7fdd9f68335eeeb9ddb9ad75eb9ca86c19f4d85aeb3b70bfc91ff05b9b301bb1f010a036d02548d9098b687ceb2db058197b7cfedffb9ff79e98adc9fd2f5af01dd9be090c1c6c503b4ecd4a2e1bf0cdbaceaf1049ed29b15c711050a036b021f0001b3022dbee2c0f38192f2f163c6a1f2f493a3b1028bb184c9feafe10287a481f0e5a91ab7bed695029dfcaf3d831f080301ad0230f192af88e5ddd79d0192d699aad593b3fd018799a8f29ddedd02af94b09bbacf6cf8d5f4910c84cfd507fb81029200087b011107010e0301a7022fdba2e5909feca6b104e69a8b92939deb8b03d385aab3e5bbf30a92bfbf89af89039ed3f0a9f357d592ab0aa1b12da501d1110a0301a3022dfabbb69bb7829d8f09d0a5dfabd8b6ccf75aabe586cee2f0e1489ae3dcd1d8876c9393b7d4931be69ab0b9049fe9a50488e573000b01d4019d01000501d4014d493b1d11011803019d022c99d487a6ce9893ed0fc1e6b3dd9dfea7972ac4fb9f8b96a8c912b3bcf6f2f7d50eaff8ab94f105b5a1d2d3048fa7f501f99d01d901850a030197022bcedca2aaab9fbbb711b0d8dec2f5a9b4c725f0d9a88ff6d0a17f90b6abd1dafb018aabb6d1af8304ffc1bb9305b5e7bf0286f101d94d110b01800005069a0128d885a9bcfcc481a9189db5c0fc859086c502b384dd928f83eeff1dbbf2dfd4a2878b018c9fc8f8ceb5af028ad88189f38532ca93eaf745c080ed0ca5bf3e000b45018b0185776b59060006018e018b0244c7fa9eb4e7cf9cd11d85cff8feaae389029adeccc7f7dedd0394a5ebb8f4f145befac7990ddedbbb0cd3b12e000e03ad014d111003018902468aaba386a1f8acc902a1aee8adcfc5f9971be2e7c4fcc4f7831ca5e9c5d7bcc33fa0d8aca4d317a99dc1df17f8f3910dc2d13a000b02e501850183776b594d1f1301160301830243f8b7d0f0c9f8cabd0696caf08a9dffa9d77790c5bef4decad501ebfe92c3f4b89102cd8597c1fed31782d09d91028981c1018d991d110a037f024c9ca999fc93a9e1f106f6f88dffd39b88f351fe98facbbab7d703e796f4c7c8bbc306e2fd9fe1d0a150d3c5a8c5168b87912fad01d1070a03710249c2fbc8d08e8e9ded0cdbbaf3c4dafdd38f0ae8d5f1d69280d3169c8dcae39a8b06f2d98ae8990fa786e103b39301b3000504db011801000602870197021ee9f9e1dcaac3e1ef01e88ed8c9998bc1ff2ef8fbd3dfcfd9588e8fa38bff08fdcef1bf48cde901d901cb07010a030195022387f8e581bdb8fe8107c0e1c6e685a2dca5168deb87c9b983e330c3f5babe889510d1d2a880f101afbfede145c68b0193851f0768000502cf012ae0fdd7c2a9f9efc901f6d79be6f6b9ceaf0a86ade4cccda3f1048fb4fdfb95a901a7c4fef5ab2091ceff1394f501d901d101cb01bb01a1018901857f775949130714030189022dc1deace2b88a93cd04f2a5f6a2febff69535a1d0d0a6c4bfdd0d89fbd2c9d9f707b0b39687f70282a8e3db639efd3cb159077a000502b6010900040404000d03df010903c601019b021aa995a5b6d18a88f902898dcdbabcadd6bb06c5b9af85c6c3df02d6dea59185bb06bff99fdd970594c698ed038481c702dfd301d94d17010c0301970219fcc5aa8299e0b39b048fcfeaee80f79eb529c7f4e1efd5b8b301cbb996b9f8828d588387c6c5bb2693e1bebb02d5be9f01a3ad01d901a111010c030195022297fccbf1d2d0c1ab0685bd89b19c9efbdf11d6b8b8c288afbb4fe3d2acbd8af701eaaeb5b2f754f8b7a108cca101d9771d0a03018b0229d8b7e3ded1caccc355acc9e6c6ebb3c938ada3e7a395fb01a9f4c9dc8e9309afced9e3018f92d712c10108030189022cb0b1f6bcbef3b5ef03cff192ad96a5e9e32984a091b6f88383318b88c4d9d2c905cde7ccfabd0dcfb9c903d0956711010a030183022b82f8dab6de99f4db0981d0b7afb1cadee321ccc9d8f3db87993f80c39af3abdd6bbee1d0a31bc4f7f30190a51f0b010a037f0241b99b89bfa2c69ec75ef0fbe785accee903fafadbb59894f957abc28db7c963c580c5ff45c080ed18c0d13dfb49130a03710243bdfafecf97c1fdb902ceb99cffe8e89ea90cc2be80d6dfcfed0d99f5fbe4bdf907e7d091faed39aebac112e0a925c707010a031003b800070901050701050501040402000b0101000100
    (by decide) ⟨40, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock12 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨53,1,true⟩,⟨59,1,true⟩,⟨71,1,true⟩],81,3⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    23 2729 0x4040200050ecb01c10234ac8e8dde8ee5e6a70180dad2d4abe6cad54fd5eeb8be968759a08cb7bcbd25c7fc9db916fce7d903a88901cb2f00050ca301bf0231cda8ec96ebebeead089ef3c3a9f583bcef24dae4deede8abdf0192a3abebba999d1ed3d2dcb3cf04abd8afc102e791e1039fa73600067a011f11010e0301b502318794cbeefeb9effb08939fc195d39a88c901e3bce1f89ae6f1c10ed8e489a8eaddef03aa85f2f388c57099cbbc8712c9f3a932cf01d9351341000607ae012fb4d7eaf7b6a3f4e50ec398d8a092ecd5ad04a0c8ebeebc809905e7f88284d2c7018be49fb7b501b4e1b378af2d000901f701ad01000507b1012de29b89ffee8df9cf129ebceafb90f78fdf67f9838bd98ee391038eabd6efb996b301c8ade5f383d306dbe6839177e6f7459377133500053d01a7022cd5f2c9b093a9fceb13f2d089828ae19bd1028eab9b8dbbdbfb8709f8cd91a4b0bfb70180f08dc09ec502efdcf98d63fc8b25c7351f38000707b6012b83b5e8b8cb9481d519cfd9c9d9e4eca3c17b9badba86e1a9d9028291b3c1fefed304bea5aeae98bd03a996ea92d928f8f6991edd974181591d3a000607b80146e088e3c5f0bacd9501d6bbedd0a383eac709a9c7c6a2f584d10d88c7f48de28308aee8d0d8ed06becae0d92ca89f2f000b4d019701857767594d473b351f1d1107011a0301970245e88fb8d8b9c89eaf03bcd3e2fce6a791df15d1c6979385e0bb09eaf287e9918504d3e8e0e5bb27c594fb029441000c01fd0195771d01100301950245cfa6f2848288ecfb07fdba8b8683a2f4db50f7e390d690a3a701b5e6b9a9e2add150c3dd8db3a957c4b2dd8b0199aa9301a3ad67013f00050df10144cf8adaa58e81add909e6dcfaceb8edf49f62d7ecf0ccb0f5810192ecc9cfadc4d51193809c8b9507bb97b49902f598d531000c7d01070e0301890241ceb69388b1eaeff30ffed6abaf9ca3dcf13bfcd5b6dbb997b31384a4e98bc5f51ebcc585ebf303b48f8dad0693e53500073c01a113020005079e015099fd99b1c18fd7a503def8abc0cfd0d9bf05aba2b7ff9f9bbb029d8ac3a4a7c701cfcd8fa4e15daddf950892972e000c420167110110037f0256b1a7869084a7fbcf0499a7efcd878ae3fb0cd5cfd78489a7bb55acced7e5c5b929e7e7a48aa308fdcef1bf41ebf136000b088e0185777167594707011403710253a9f2d8ccd197e9d308bbd9d7dbfda681eb62fff898dcc698d704b2f7cefbb080d701cb87b998b89d0dde8286f50182bbfd15c701851f0a036d025bb5fda3f7c1f7a0df0289ccd5e082d8d5ab07dbcdef80dfe6a91ec5d2f685f4b105e3dae0f6a501a0c3ab9571cf8f02ff8f01851d0b010c036b02210001b9022ea5908ae6c9f782f7049ad2f5ac9dff97c507f4c99490ecaaf304f18bcecfcce704a49bec88df01ba86acf30bf7bd01b600060a8301b50232fb81c192aeedeaaf59d198f683fb9a8b1987d8a79fc5cb41b2cbbdaf8b14d6f1bb8b64cfa501c2a701d901cb1f30000501bd01b30231a0aec18dbaefefb105a5e090eee0b68b99358c9fff9ec7bdd101809dcaeda0dfad41c88eb488cf08e3d7ae9303c9dfd933000502c20101d11d110c0301ad022fc5dbc188c6f1f4b309faefe0cd96b89efb619ed1abfcd481f301dcc4abb6ecb0f904c68b80e5cde301cdf0eda4fb39c683b328adbd1afb070a0301a7022eb3f9c185a49df7df0d93c1f6afadeebcd17382f580ecefd99b03a8f8a5cfb5edf7039fde87cab9c903ecbbdcded12aaacfa102b3b901d93b0180000502f301a3022cd9a6c180b09ffce111e7f5ae8ecb8680d1019593d1fc95d490e50ed58ff98ccfd291159ea3a796eff706eb9399f28b02c3c2e5a10ffe9f108b1f13070c03019d022afed3c0fbbca281e315a5ceb9a6b6fcc1bd02c4b3f4a7defb83d523b2f1e49ed1b4b140aad1d3a18bd318fdfd999da706f7e9efa70282e9c702d6e5170181000506d5012ab5e2c0f9eaf883b919a1bad4d9e7f9e8953fac99dca4d4fbf3038ce8f1bddab8b702eff9b8f0f5cb39a0adfaa70cc0969f01b5b301d94d38000703dc0148a9afede1b090d3af01b1b889e6daed8edb3fda81e4e6bd972e90b6c9c59508d0ce94db03a599eb01f3f12b000a02e5016b1107011003018b0247a496a78ef897e3d503c19eb7e98691a0a502fde588afe9ca97059c99d485d28d0498b0f78c8f26fce3bb0488e54d110b0a030189024494c9d397d0ad94c709deaf8bf18bbda7c11b99f9d8f9b2e9df01d285a394f5aec102b49cc48fac814bb194d1049f8501d901a173000808a401428a96c5f2e0bbb5930bf3c2ef96a1a3acc70293f4f6f3f3f19e9f1794bcdeeb8d87b901a3b2dbf3e1bcf13fdee293cdb32b81acb9e301b2e8e315c7018511010c037f024a9183a0a2eabbf49f0ce8fae4edfba898f50185d2fcecd4b6f6e906a3f0ece0d9c2f72985bbdbcea101dcb78b42d57723170a03710256c88dc1f8cfaf8fa703ab82ede2d1bbfcd92cd0d9f2cfa4bfd933b6f2acd4fcdf24c8d3d7fae506a6de8eab6cb5b91ce91d070a031c01b0000602c7019b02268bb29795eef9e1a501ff8b8ed9dbd28ecf01918c87bce5feb955dce5cbb7e306dbb689911af5ef2a00063f0101bb01a1010c0301970225cae8cee7e6d9d0df04a4a1d9dcfe92b7b706caceca9d96eaf708a2abd4d5c2bd03c0c8d4948b018b82cca53af5fb390006058701110b0c030195022efc93a990bcc9f68b03ffbbe4f1b08c85a90cae84b5cfadff8b26be80c9c6dbaf36d5b383b9e117dcc9aeed5cff8746b901d9590b010c03018b022ea5d2cacdf7c7f88906a39c9be59fa1fcfb2885c4c9ded392ff01bd9ceaa2f6f9a754c6f283abc318ec9dcd9d01bbd5ed18cf01d91d170b7a000502e8012ca290af86a8c1fe830cc5f49b8394b0e8ed01c6bde9b9f5c9d0c702998095b0a2c5b701a89ccc98aeb336d5d3fca31a8d90cf0bdd9701d94739000502e1010b01000514010f01010603f4019f021acf88c6ace7c2c09d05c7e98fbd83dba1f710a6cffa8bc2bb8d2380de82cea58502e8fbf78be709c5d4c103f3e3110b050a03019d022591e0d68fdbcdaab748a4fcbac2f8c8d50198a9f9dbf387b501b5e4f79dd911d2989b049ec301d901d14d070a0301970224d2e5a9e084e398f502cc86b48ba1f3af9921d6ebdfb1ab8d9301a6f4a3d3a0e2e306f9f6caf3db019fe1cb8314f0871107010a030195022de693cb8c95aad2d902d9cce18efaa3fccf0381fbddd3d6a7b17f8bf2ac9da712fdbcdfdf02a6e9b56b8301d901bb130a03018b022d91e78d9eb4aafa8304ed92ada6ca95e0bb01e8000839011eee9eb2d8b19b26acedc6b19d16ecbaa706dcbf1f851f1718000502980189022b94e1d3d591abf0810c9debe1d1d09ae7cf2a969ef6f0bfecab2dbbb780c2cd8b3380de9fe7c1679bd8a125aab7209b1d170a0301830229ec88d7f9cfacbed511bb9ae79ccab7ede703838eb7ae81c5bf0282c7aae7a6fb20c2d5d5f104baf6b506dcbf01d9470b0a037f024485cdfc92d781b0a303dfa3b0cde3e0df99138385c4bdbe97e3458be0bdb798cf02bd9986fcfd208cc9f105c4bb01d901d101cb4d010c03710241d1a6fb9393aed1d709b097ed82de98f9b14285d7cdefe7d0a3028bab8eb7e8d2a76396ce9889cf1995fb91f512fe979b01d7b977110a031201e1000541010187021aae9b80d8cee3d9b70bf9b2f7d5aa91bf1bd1f3f5cba6df03b189d1cba566a7ffa10bbfe312ed1f131107010c03018302033500050101050701050501040402000b0101000100
    (by decide) ⟨40, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock13 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨53,1,true⟩,⟨59,1,true⟩,⟨71,1,true⟩,⟨73,1,false⟩],75,2⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    24 3418 0x514c101e9025e89f2b1b0efe2aca5019ed4dd8f88c19ad9058ad1dbd4969fe503f1869fc38c8901aef4eea79302abfd913adf01e53b070a0301e5025da0dcdaa887f8fba3029ee68ffab1cdfec108cdcb8bf7c1fda9019adcabd882f7279fc7cfc103cfcd8343ef176500053601e3025bceb1ac96b8a6999f048bfdeeebf390f2ab22b1d8dbd3efcca328cdcd9ac5a9bb0ac99cd893f702f686fb4a9b01a10b3200060ab40156d7afa1e1c9adf39309f7e6c794a59fc8f34ae7f590a0a7c0c301f3aff6cb92818330a5ce80ce9919bb8fa48b02e7dac102c3b10185133700050ab00151e0ad97acdab5cd870edcf18ac8b9d0b4eb01fbb680ba9dfac08d0284d5a195de868339a39eb6b1dd0fa98e8cf303a489df25c73400050cd801c70250f797c0a3f2cc9c8511d2e2bd96a1d3839d0b8beab38bd2cb930fb5e0e699cbfd118d968d8d89098b86d9e908828eb3078fad01d1010a0301c5024fa4ec9292a2f9ba8113a99fddd9b6e2b88b3afc8bb1f1aa82e30184eaaa8f9dacc144d6d18dcca908bcef94a34abae76d000701bd01c101bb01a105000503c3011f1307140301c10262f7e1f1b8b9eda79529be8b97affcc68f03a7909d8d8df08d0299d2afbbeffb01c8bdd7a3d321bdc3d5039b9935080301bf025de0dee2e589f6a9e706a9b7c8ad8db7a3bd1dbbe2d9ba82b0e701a2d5e4d7c3a6ad398bcfb0bb85129cf0d4d91c9f911db3110b0a0301b5025cdc91acd4b3c4f79106d7d99087d8b0dab9018bbde09385d296bb03fcc9f7dbc0f3b30ca99da1d1b9fd0ac9f49ad8ef01aef9b2d923ce9b01ac000901c301b31d170b100301b30259cea98aa2b0b0df8f0b82e4f0eaf3bc88fb40d2cc9f8fa5f8e90184c5e1b9d3e5c306e39e88aaa901fda9e58f1c9f9115b13b1307013f000511800156c0c0e7f0ad9cc78d0efae5d6a5dbc6b0ef24a2ecfafcaff4f702cee7dae4c0b6bb7a9cc08989f90ea7caaedb0daaa0ff079ccd3400054201bb1f0c0301a70254b7a5fbcf80b9e1e110a8e788ead9aed4c101b39b9accc2f586e503e59ed789d7f2d703ca88f18cbe9572d3d4dfe52cfff99903d9fb3d00094301a301a101854d1d0b120301a30262b8f9ec81b2cf95f304a3ef84d98daab38509d096eef1e1c6cf0bf9f2f69382bb40b1def89314e4b0bb0bf7bd3a000d13c7018577674d491f131403019d025ed7b1c2b0d0bdbc9908cde1cbed92f9f9eb0ffcfdf3c7d4b1c768d7a4dec8f1d317e1a081aa870999a9fcbb01dff6d35be93b1340000512840197025db6eedf95dab7c8fb09bf8999b4ede7c3d31400083f0162e29eabc1cead1bb5d6d2b7cd05899896a554f4b915000801ef01470b010e0301950261b4e0fc98b3a4d58f06c5e99680d0acbaab59da82de8da1b58d3ccbc2b697c0e30daac5c9c9b303e39aef8301b8b6f938000709ac010609e4016081acf6dc98e1eaf508dd9badd9eafda0ff10be9091d1cbeac516a3bfcdcf999913c0f4cad3a176acf1cb16ab87018908030189025be790e6a7c999aca70d8eddea85d3cce1e142f0cad0e4e8f5c505e7b299ec95c7830a97bddcd4baeb179787eabd02e7f1f902b1d14d0b6c000510d2015980a8dbaf9493d7f30ed8a4c5e1a193b3e5028fd091fcffb3d18b0baba6ceededbdbb06d19bb2d0ab01dfe795db0b94f731000c01d7017f77674d0712037f024f98bcb589dabff0bd19b3a98ecdfdd0eef902ddc4a591fedabda103bed5d1a3fac889048fcafcfce3e102d1ea98c1f90598c0ab0181c701d93b231307010e0371024cb1d4aa91a5ba9c8918c09dbbb3b7be92d506b2e8e5f2a8ababab3cddc5b6fbbb98e92c9ef9bab6afeb1caed5e8e3bd048f98c5ff3fd5af3a851f13070c036d024afea0a4d58af7b1ef1886d7d1e694b4e4c307f5bdb991ddb0b0ff7cd3c4d0f2ebf8ab058edab9e2a5cfab08f9fcd5fa9fd101a6989ccd877daa81d308dc8d01cb000c0998013510036b022f0001e1025983ede7cfddfac6895bcbe8d1f58595a723e0e9b1a0fd8f0bb1efe1e99105c4d2ad8f44d2e76483493300050c9e01df025a86a0f8e98bcb82e701bcdef79ae6baeac105f6e0db8ff4b0af078daaf9f3c5b70695def8f199028587c9e11594b11ff11d0b0a0301d30254f6de94c3c8e6f48b07dc9feacbfafddc815f85a1b3e699fde31ae0f5e6f0aff90ac6ceb7eaed01a5a296bd029efbf305828b01d11d0b010c0301c7025489bdd992d380f1d107d2a8c2a4cdaed09301fbbd87b99582d9f501e59fd8bac5f28705cbb2a38fd99104d588a8b2a95c93f2ad3a8de72cd11d170b0c0301c50252aefce2b0e7b4ecdd0be291e9bdea99eafb15d9de9aaff98b8105f5e2d2dbf1ad0585d5cc8b27f1e742d54d01e40005029b01c10251c1dca6fff1ceeaa30cd28893deb8d1adf537e5e699a9d6d5b9029380e8b9dcb0970184e097ded1fd25f0abad10e88f18b74d2311010c0301bf024d9fb9fe8ba4d0de8112e9c68891e7cac48b0788bbaabbfeabdf0684e490e6ecd301a3fde3e0d12a9de8e108efbf6b000a06cb0101a10185776b4d49473b1f0b160301b50260a984ad93aaadc1ad0ddbb4efe591c88f1eec80b394a0ed1caac9bec304f989a306d4c701d94913073a000506d5015d8be2ccc48384d3f30498a9e1b0b39ea2ab07c1b899f3e4d9c37bf396c2efcf20000508920103f6808967dd2317010a0301ad0259eec0ebf4dbdbe6b90895d7acdc88aba0cb1c828acbdfaeed9504d0c087fde8dd02a29dc3ceff2ff2bcb11c8cfb1d0b013f000506ea0157daffd69596eb9dbd0ae4ee94eee0cae5c12df8929d9e81feaf18ddffbddee08927fdd4deb4bb53ababf908c18b01a3130732000506eb0154bdddf5c5efc2b0830ece85d3eca9b5e9c153b0ada8d9f2f4b303bad2ecaff1c9954db2bda3bd9714e7cbb089078ee7ed03acf501a11f0a03019d0262ae85bb8286c7a895028a8af7ece99bc8851ecffde29db0ee853dd6bfadc6f3c501a3daf9ff96e712ebd8a6f301dff6d32aaf1f0b71000506ed016187a4e0b0d2e1bfaf03dee4edd2cfc2ecd117efa0ef8cccc3dd16aa9db98ce5cb18bce6a0acbd01c4f1c3a514add92f000637013b0b0c030195026598fdcbc9e89db1f301a39de1de8ddf94c704a2c881ded3c1d301dcd296cce59f61caec8cbb12f2ddb731000601f3017717010c03018b0263decddedfe385f98102f4a2a997d39face7149684e0bf93ada729c396b8ccfa8909b889ecd1f107828297e518c9d123bf4d0b0a030189025fafbe98a1d3bfceab07fea6d09c858cf2b12dd79081a0b08de543cedec7a6cec525facbdae3a704fed7ee8502eacffb01b89b01d901d14d1f13010e030183025cbadebecdc990dcc70be8daffabccdbd28b06a1bdcaf382c7bd04fa8abea2badb04eea0a5c7ff08a8c9ab05c4bb01d901a1110a037f0252a28fc4e7a4eccea917da8d93e9d8dc859b3ac2c4b0b8de95a3038ce8f1bddab8b704a0dec6f78e970299f384b7a5598ba5f157e801ec000b4801350701100371024fadafeb939abddcc519ba83a2af9be8a9e1028a8893fbc9a2f9ad168dd480c6affe8707bee3fed7acf701e99790e8b50e9dedeb0481ed3e000b05e60185491f11011203280009000505a201bd023295ad8dd0fda5a4e516abf7868996bac79f02d1fbd1c7d0d9c5a76dacd1c2c5dead0bc1d3e3b4c704a0e1cfb309b9bd320009059b01b54d1d0701100301b50231ceb2fcc19ded8183168caa889092d699990486ccdefcecaccce717ad85dcd9b6ae9b2adfe8b593eed5079adea793cb04a8df91cd11a7dd10c51d0a0301b3022ff9c4c991ffc495dd15adc38ea587a98f8707fbdbd2afc3ddfdff76ecd48cdef6d4910e8cf28ec3d5d5f501f7f6f5b381e501a4f195f4ef23e3a7d119ea8d2fad1d110c0301ad024f91a3ebb59df986bd01c0a4fcb2d0a4b2c304ebaaf0c2b3b7e307ef8fcce7aac321b7ddc48507ced6d305f0db01a7170b0a0301a7024d9ed4e6c5cb9bdad104edd6ccc6a9aba4ab13f2a1d7fba182e107908fcaa3b8b30387978d9cc70199d1a9db08938d2bf535010a0301a3024fc3bd82bf8be09ce504d6e5bcb0f1d0fa9534c2aaa0c8ffe88d1ce8b7958ae8bb2f91d29782d30e818ff7dd019bfad302b0000702e201a13b0c03019d024cbeb9efd2d8e0cfef0a9cb3b190f9c9d5cb21cdadcbc29ca69301a4c1928bbdfac30a8f80ebcfab02d391eb910188e1b124bd3a00056f0197024bbce3bed99d8bb69d0bda9981c196a7b5cb4ab9ec8de8d3b293019d8cbdc8d8ef8713df9d9adbf70787d9859302bc84ab1ee177170a0301950258e3bbbbed96a1e5c102eec88ea8d7b6e29f099487afc4a698a901f7f7bb82d7f901ecfbceba8d16d38ebf4cb31107010a03018b0257bffb89a1f7c787fb04efdd81e0dd90adb110a1bd91809cb6ad14a3d5a2dbb2d112b6d3fad39503c89392b702c9f2c160ab01d93b07010c0301890253d5b9f1c09bb6efa90aa59aa4c697f4a29d728bacbec2c9c8c1028b8fc7ff85b5e144f9bbccd1e708a8b6bbdd02b58ec901cfe14d070a03018302170001ea000501010401a3023386e29bf39bf292af10e79996d9cdc6fbdb0bbeb6bd8dbee4ff0bfbdfea83c303a8effb8f01ddf8b52d0008540101a1019d01950185774d49473b351f1d13071803019d02318d83fbed97c8a3cd15ef9bcac2f4fde2d775d4fe94adc2baff02fc81b9bef29fe901d9f0c3f8d4fd27ebbac2e90ea9ed9b04dde301d901d101cb01bb4d1d0b011003040004045e00140101000100
    (by decide) ⟨37, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock14 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨53,1,true⟩,⟨59,1,true⟩],73,4⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveFourteenBlock10 (.cons fangFiveFourteenBlock11 (.nil)))
    27 4618 0x1f302598692c6f7cac8b2c504a0b8c0c3d287b3c3088f83c6dfffaec307e084c6d8d0f37b978dad835a988e9f08a08101f132000603e3010717c5013b1701120301f10258a7c6fdcac0f5bc9b0598f58ef5a9bbceeb04cca6a2f29cdab50cf8a3a6a7e8cf09f6ccb087a90293e4acbd3680e1139159130a0301ef025c83e2acd594e6b39f01feaee9b694f8b2bd069cbaffbaed919702beb6fc84eaa131fccaf2d712e3bb8d64834f17010a0301e9025ab9c598d5f2f7a98303f7afc3edbcd38cf5049eafbaa18fefab0491d3e4f6ae930499a3b69e8d01f4c8b1bf05e2f1018501a5000507f801e50259d4b6ced6a1ffe3f504dc82eff788c3add71afedfdcf1e4d1c312c8a6aaa0ef9f0494cae6b1fb03e9c6abb701ca89b115c701e33b0a0301e302588a99bad78090d9d906c498e6f1ea89e08329d7f98f87c596e727c0ecf4eefbbb2199e6a4afe5038ce489cb3ddded77110b0a0301df0253abc1fed99ac3bb850bf3f7928cdf9bf69359d2a6db8d90d9e305d1a18cd980bfad0ad7f2ee9989d9028b9ce8d281089df0cb01a6000609d201d30100051fad01070e0301d3024ecceac2dbb4f69cb11191dbc7aa88d3c2e901a4dfb4f4ff90f2e701f59fbde1ceb8bb0289f3c9b1a2e90aa3a0ddb30197dce36ff901a11d07050c0301c7024de7dbf8dbe3fed7a312fb94a0d2cd89ae813780d3dbdfd5c9fd01dd87bda0aada8502bca482f08dff46f1ade9cb15d18cc706ecc97a000a139b01590b01030005139c01608ef68fd8e9d0f1ed01b88da1a5fcb5b6cb01b3ff8ce3b29db7139cb4bdbdad0399e4baaf7883d374cf1d07012d00050acc015f8fb79c90f8ba959302c29ff9e996bdf7910ce5c79ac99dffb52eaeaba7e49d9367c3e1f5db03e1889758cb1f130b073000060ad7015a91fcdaa9c2c8c5d10898f4889b8686cc9323dca9bf91d2a0db1fded0bacdefdb0ebfdaa0abcb01c292f4a930a4db2f00094501b501a11f13110701120301b5025992bde6e1d1b1e8f709b9b3fc92cdd1fb9918fd93a3cd9f99b331c0dbc4abf9af0b9d8bf3e1ef01a3d4d4cb2682bd3c000913ff01b301a101851d07100301b3025694818c89fdedd2e90ca7b781dcedb49e8f6aa1aed4dbbb89f502d9f295f2c9d1f907ecf5bfceb8f701bfb5e0e2833ea385f504a3cb4200070ae4011d0102000513b6015395c4b1b2aaa9bcdb1089c5939d8bb48efb46f9c7a4a88f84f705cffedf9defd08502ed9be5908dd70d97ffccd750c3a135c54d0b35000518b70162a284ccb7a7fb989b01f48df9b0a2f39cdb02a8f0eb95caa9d501d2c3e7e390a35dd4edc49139feffeb09cfb32d0006048f01590b0c0301a3025ed3859ba4e4c3cea505d1caf8e68d9af38136fcfbdcaf95c6ed0ad2ebf1c2d99b0295ba9494d90196fccbb30aa1b101d93b0b0a03019d025b8485ea92a18c84af099ff2f3c1c1d3aea779ebf4f68effec85018dea9ed0f0f8a502f5ebb292f341b69db357c5ed01b4f911010a0301970264b2b1b4d1a2b9fff701828e9cc1bca2cba965c0fef2998ea976c2e3f1ebe506e993c9eb01808ae36ff901d913110701a7000613d5015dd3f8ead4b3f38ce908c1e889d990adafdb0f99b29cb898ff992dcd84e6a88cf901f9f1acaf8734fcf8c3068bb9592f00051482018b025ca7baa8d584988fb309dfcc8fb6a5e7c2833489f583d4c1b5b34af2f7b4dce3eb1ebe86bcc7af7ddbb5a345c68b18cf170b3400050abe0158a1fee2d6f58797910ccdffe9c3a38183a7028db0a1cbbfd38e9901c793fdd0c3e3db17d3cfa7f0c303cbe5f099018df7e93da7018511070139000518e60155c981ded895d19ca509000916dd0101a68d9494dfe4c99510b5f6dec6a2bcbf05baadebe3858703dca3a8a0a303bf81b695098fb70ea54913010c037f024c91cc90dcc7d4aeab18b5f982f9bb9b87cf0480f6c49fe8e9bf890ac594c9cdced70d87ad92a2e3088688ec8f01b7858701e39f0803710249b8cf8cdde89eb3bf17c7a5b99bd6c8c5d307e0cea8a6c3ba88cf14b093cc9ed4f3853aa5c4da82a29114defbfae09902d0cb8c9311c5019e00070bde014f07010e036d02488c90cadeb8c3b689178ffbd4ace49fa4d5099bc4c3a6879cea854d959dc38b9ecca906e6b9cc809dbdad14c9fdafbca5fd01d0bad9829f5cd8a4dd10edc70ea54f49000502bc016b0245b393c6dfd98dbb9d16a1a88aceffcce2d90da0e48c89d396dab542e599c6fce980b942c8d5ebaaa0855799e1ebc6c518dac6d28103d4f1a50481ed3e00080d9e014d0e0367026995f7e4b7e2f0f6e5368d9feaab98958702f1d8b2b7a6d4f10582c2e3e29a9d6cbbfcb9fb1de6d49504eb85018505010a0365026580e58ce8a0eefee104b28fc3abbed2dec745bcf1a7f295ddd503b0ddd8dca1f9c952dce5d9f1b30bcbb1bd8301ca89b11be11f6d000506830161023b03000611b101d30231e2f7e9dbe3e3dfc71695bcf2ecd28b8aa52db9e6a79ddd83d706f2a1f9eee49106f7f0a1efb9290005048f010190eca511b906000708db0131a2f4869f84eefbc515f8fad6d6fbdbafbf01cbb9b5f0be8beb9b0bdb80b881f1d5b7048e98ccc9faed32d8acf2bb06fb8e9b0ad1ab01d901d11f113c000504c501c50230a2ecbfa5c785b3c118ebb48cd7d6a1ecc377d386f199d8ef8507a3a2a6a3d1e69713deeea8f4af93199e96c097fd02d0c3f5f9018692b317f31f0a0301c1022fe2e8dbe8e890cfbf18cabaedb0fb969cbd02a18da4d3edd0cceb0c83f18df9a3bdf107f3accbc2aee358bdffb7b517b0d59d09b7eb01d901a17c000708e7014db3829d9bb89dace728ec9d94e894c6a72780fcccd5a4b314a2fda8b2cb01feb4b1e911a7dd1aef05080301b5024cc5c68bf5d3f2cc9101e293d0e7ebaccab101c6ebc8a7c8dbbb06ebe9a7b7a8d1019fd0afccd109e889af04dde35c00060ac201b3024f8a97a991ebe492c50183babe859bffd1d9038a95edf2f4b6c36993ad89be852db28192950da98eaf0283f501d9300005088701ad024cab8feda1c08bcaef05ae8de8fed186d9ef1ea092fbaccac4e5548d9a90da97ef219a8d8a9e8b0d86e6cea503b6a1d3029b8f35000701e90111010e0301a7024ac18af081a2fb9b8b08c597c0f9c8e896eb0bfeccd2bfdbaf8b14d5eeb1a7d5bf0fd3a0e2f0dd07e6c49aad5ec0b14e9d670b3a000509940147e283b490f7a2d3b50cf6d08efaa6fcd9e120dec6e6bbddaff938ded2fda489b72be5dd9ab8f903ae90ed8b72f0af2f0006740107010200050994014582fbf8a0cbca8bdf10e987cee4b992879572ded9d599f5a9db02bea4e8bdfe97bf0284e2eafb5e8beb648301d901d1350b01330005099a0155f0999181a5fceb8f01bca089ac9fb7d9e701f5d0d39c868ed303bbbce6c19ccd04e28ec5c6bf028b83b2b712d3f32f000602a301771307010e03019502508ebbc3b4e0b5dfd109ed9fa3d5f1eccce533f599d2a0f1eff93afdd0def3e8a729b8bfeed9a50cccec8bf752c5d164834f1d07010c03018b024efaf5cdbf85daddab0ba3ec9dadc9fad6bd59a6f9f384b0ad9705908984ace88295049fb9fdeca99531dec4a3d901dad7a7039bd501d9077b0005098d015bb2eee0ddbdbe9ec501a9e7b3afcdf996eb07fad1f9cada86cd01d8cfcda292e510b899fd950280e1b126ff01851d2f0006098d0158cdd2f991abfce9e905a3c2ddf1b19589f50dcd9dfa86aab1ab1393dcb5dab8ff01c7bbd0e7c307f2e3954da11108037f02588ece84fcb0b5869509a6f4aed1c0ded2c563e7e2cbeea6fde501c4e1efcacfd58d03d6aed1938bcb03f389fbe88553feb3812e8f6700070cb801710b010e03710254ffaefaccf7998f810e83cfe9fde4b9cac73291a9a1fd81a5e9068fd88cd4ebc720ecd1d0a506d2b1a30596ef34000601b8011f130c036d0253b7dfb5b59acb93b70de2d6cad789adfac102e3a5defae0e999d904c9b4e8f4bf99b702edb7cddebb9d0299a8e3cc9301e6f5d9c501bedbf11afb110a036b02270001cb0233daacf980f2ebaccb0dbff8e8de97d6d5b502d4e5f789a797cd01f9eff08c9c8916b7d3abab03f8b0a51ff11778000506e601c7023397eaf1adf4f3a3910ec0f7fb959d839ebf20a39ab4c7e9ef9359c3f8b5eef0973ff8bbcbd2f923a5cf83cb09e8af8d0692bb3500074501c501bb01a1773b100301c5023292e6e287f983909d10c182e9b6a5baa2e15ce2efdc94d9ffdb02d899d696d095cf02c8d7f5ded2a922ae8b9eb503b5a0b53e0007028d01c101bb03000502cb016b4f4d493b170b160301c10231d0a4dab4fb8b86e310ab9087c0abd9c09f029497edd5e3faf5953e94dca9fdc9b302f1ef92b9c10187d0c4b55caacb01c9b701d94f1f010c0301bf022f83dab49685b2d7c117a5dcd0efb3dc8c9f01b4938eada9dc939f02b2a4eeefc6d8971de58adab89176caab913ab8f768e14d110a0301b5022ec198acc387bace871784e3b1c8d8d0bc9902eb8acf81f0d8edf70bd3efc084b2f4cd05fc9e90b6b1f506c98cc5ccd3029d8cefc10987b901ba000601fd01110c0301b3022cf9d295ca8dd2b1d916a1f7d3d4c7adcc8707b08ca5cfc3d08c8f07a9c5b8aaccd5cd0ba4f69ebbc3db02a780cdb3ff01deb8d1df0fecd93e00093e01ad130e0301ad024a97dad8c0b6c683b902c7b88bf0c8c09acd0a8fb1e0d1efeeb913bdfef5fdcfbd03c2bab5d69570e0a4ef29f1c135000907b601a701a10185771f130b0701140301a7024db3bac2d3abe3b4ff68fce4c0e288b2d306c09bdbe4b5a3bd05a6caa0b7f8ff78d4bc85e901ccc9b524bd1f13070a0301a3024ac6e1fe9e828eefc105e9f78cd0a8f0a0ef08c1d0bfdef1dee10ce497aabf94cd06f8ffb8cdd702e6ab8ae513cdd172000504c701a11d0b0c03019d0247da89b9e8d8baaa830a9f93d1b3c3bf98a555e3b0b2839c87c950c0f1e7ddbdf301a5de9d9493c330e0b8bdb347a2c7f30aaab719f5110b050c0301970246e0c1a381cac8e8990afcbe92b7d89d8baf01c8d282d18ccda69906df95b084dcf1a7059ac5cd8885bd03fca8a7b7f102dbf5c5e101cd9af101cc9101d93b010186000504f301539cd996e7a2a6b7ed03dfbcefff91c9cfb511d3f2a486e6a313d097b1d506e7fbef01b5f7018b070803018b025283b5e9adce81869f05c49682fd8981f9a510fc8586f982cf9f43a4c8a8fce0bd0ea1d3a791c91de2b0c902f2914f13010a030189024eb7cbe180d190f1b50b9a9d8dede782b4e31dc7fbd2fa87e6c1058e86e4c1e3ef07e1a0d6f1a5649fd9c35ed94d0b010a030183024c8585868da8c68e990ed996bebee7c8daf9499791afa183b58501c9a2b7e6a8c9e1019aa0adb1baab35cbf7bea1019dc18f019d971f010a037f025bc4cecae0f2f59fa104e8d4fd99a7dddffb058ecef685a6d49b03f9bffa81e6f904a0f7cce0e7049d94d2fd01c5d9f701f3f101d9350b010c03710258a5eef5b5e997cddd09a9aed8dcabd9f98d1baee0fdd3a8acc101b0b598f5f29da742dbbee9d7fb2ff9eaf4ab0ff1b8f74bed4f130a032402c7000503f60101ab022ea1ec8cd3f29fdff104fa8cdea3bbcfe9fd03edf1a1f1adb7cd3ae280cf96872c8feeb6db01f9a3bd13911f07010a0301a70232a2ac8492faf7da9b03a8d7b1ecc3ddbffd27fbc0b6978390bb02ddfba8fcf6b8cf039bf7dec8f8e768a5c7bced25c9e4c703b8876b000801f4011f070e0301a30230b5bfceccafde8ca50885d6e7abcaf8ae9701b9bc949a91bcd1bb0281f697b0def5e90180effdcfdfe108f0e6d2cd0188d9d301850803019d022ec8d39985e4c4beaf0faa99e687bc9097db04dc96e99fffadeb01ddcd91eaffd741f59eebf714d6b7dd01b9c54d08030197022df9d9dcc3cbbbf9dd10ac9383da98a29afd7b88d385a789c5ad01d1a8c8d4a0cccb52feb3e9d3bd678db69fb521aabbef0fa2bb01a800064401130c030195022aeefaadf8ce91a2c3138be2ccb2bee285d9078fd08eedc2accce16e8ebce9e6aa9caf79e4b2e9dac4e52ef88efe9db91f8da080b37c87ff3e0007018301bb01a1018b01854f1d011203018b022aa080f1b6b588ddf11cac9484e6f7edc78b53878cc4c3adc49f0595878d9fa2988f018b929fc1a1df16f1d5b5ef018dafe30194f1440005380185130c0301890249eadee4ccafe9fea301b6cbecfbcbdb89e303fc9398f980a7b362eff5e5a5972adcd8f6ef0ae9efb502b3b901d901d101cb01a1170c030183021100040445000f0196010b018b01050101047d0212ccc5faf0d3abf1d501e9a8dc90919cd1cd0389a8eceea4e19d0194ae8bf6998f68e3c1bfbf3fce8bc309f0e301a111010a0371021ae7c2b2a6bc98bacd4aeafee7abb7e29501f18f99dee9b1ab23dbcfe4d3a907a6f7dfdf62b2bd1097590b010a030467000605010a0c010404040404000a0101000100
    (by decide) ⟨36, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock15 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨53,1,true⟩],61,5⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveFourteenBlock9 (.cons fangFiveFourteenBlock8 (.nil)))
    27 413 0x50399010501010401850201f2e9d9e0dca6f9d503ffbcada68be29701d3dbb7b2c0c171b8d3b2852ee18df104feb7280006620101bb01a10185170b0e0301830207df8baeeada9dc3b902d1888abfabdbd34da9ecb38ff33c8f9cb6e10ef5b8cd02f1fd01850b08037f021be8e9eeb99dcbe4c72efc99fca7cdf8b506d5cd85f696e301d8bdc588d325c2a3f70a8bc75c00054001cb6702000601ba011dede68b8bccf4ced30482f288a5e0abf1ab11e0cfddfef4a2e725dbb4b8aebbf93b8e91a999dd09b1fce39709a997af01a89701d901d10185070c036d021da7d68fcae6c193d506c381c1d4eea4fcad01888e96e6ecf29ad705a1c1c68f9cd1ad10da9c92f4b4df02f2c4b0f1b70aa8b6f90a84eb189f170b010c036b020b00007f02149a8db1a294f9faf56ae2c9d18cf194b503a5d3e7e4e0b4f301dbc7c5effed101b4919ebb8b25cea2fb4ec901d901bb2313070c03710218dfa09ba19b8cdeb902c4b0c2b69bfba1fd1189a597889ad9af23fffa9da4b8c53ce6aeede106bde6c503c0e3170b010a03040001ee00160c010404040404000d0101000100
    (by decide) ⟨30, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock16 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨53,1,false⟩],55,5⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveFourteenBlock15 (.cons fangFiveFourteenBlock14 (.cons fangFiveFourteenBlock13 (.cons fangFiveFourteenBlock12 (.nil)))))
    36 4617 0x50ea201fb025ccab4b6a3e7d2bb9908b5a7d6b1e6c1d6eb089bf18cf4fdb08f0395ce86dce6bf52a59afd9327f699e716a0d9108b3100050fe601f1025be888b7fa8af39ec708acafa7ffbb968eb57cc2bfdd92a7b0fb01f7a58dd3f2ecad0287e8bdc2e7ab01c6adb2b6bf0fd5aadd06cfcb351f3a0005039801ef0259c184bcfcf4d5c8d10b00090aea0160a3c4a3bc91f6f736b885a2bbdfe35bb6d0a4e4cd0ab0e3bf837fa6cd01ed8d01e94f230005039e01e90257fcacc0a9bb978fad0cc8cfc085f695cbab0181d1a0d9f4b7da8f02ff839fe8b0809f01cca5f5fda48514ebf6e3b105c3c7db0396a301cb010a0301e502579a80c1ffdeb7f2db0dc380e1ece5c9d8fd76a29ec4d3a1d3ff01a2d0cee49fe6f517f0dbf8d7ad03a8acd18f05c1b4cb04a3cb01e3760005039201a11d010e0301e30255d5a8c5aca4f9b9b70fb78fa0aef7c6afdb5c92d096faf7abc101ea8bbb8a86d99d02dc9bc6ffdea301cba9e6dbef12bed1e908f6b3771d0a0301df026699ebf4e5f6c396d9129cc886bfeef78101bedfffcbb0df28cacfb2ab02d7fb9b2fe71d07080301d30260b1ed8783a899dfb505fcf0d784ac9ec9f13ebba6899db9c2fd43aaf69fb1f4c72999ca9190ed3585d288b35797e132cf01d94f01a300051497015fb5ed9fb2f0bdc0ef06f0cfd9dead839dc751b3bbf6b7e5b49b64c6e1a0cac8a716fbbcff868b01bdb5c3990197dce337891f173400050eab01c5025dbdedd092818583e308bfe787a4c5f4e9890186b9a995e39fd99b0a9bd6c292dee7df1c9680cb9685cb19f4c3c298e502c4ffaf8f2af9c126ff1d0b013f00051496015cc1ede8c1c9a8e59d0abdd88ddde8938ff119f682bde1c2e6b102c8b596bbcaf303f6c3e2ab5bf1df13911d2c0007149e0157d5eee2afb2dbccbf0f94cfe4dee8869bd5648092b7afc8b0c501d8f9e6f3e582ff0190afd6e39db90acb8688cb0fb5a2b706dcbf35000746018513070e0301b50256d9eefadefaffadf910e0fbd0ddd2f7a2d91e9afdc482fca2df0285f8f8c4c2b8d705d0e4c1cee19f0b9899bbe7ff018eb682971dbad73f00073c01a11f010e0301b30265b7f9c4d5cac4bb9b02bbefba86abf7c0c50890bb88dfbfb1c50192b2cfa49c830ffccbb5b10cbfcbfd05bc34000901b3015901000514930161f5d1e7a4809796b105eac2a1eba2f5df9d3aad99e1b38483d3029e838181acac8904d385f6f7c2fb01dfd69ceea738f9a8f501e39f36000517b701a7025fc9b7a982f9a3d39508d890d597c59ac1df109caa81caf1a0c770bcc6adde9fcd0a95b684f4d50ff1ddaf0699ad3000083a0106149d0166f1afc5bce993aca101df9aebbde3b4b2d302f386b181a5a09f65b9a78ddbbf43b3f7d7b703b2cca50294972c000b0286019d4f13011003019d0262fa8ad5c99686b0a305a2ffaed8c8999bed53f0e7fdf8c294d503a4abe1c2d2b7f308abecef89ffc707e9dde0918774fbe7e729b59f2adb3b4200050ba40161d2a985cda58286f906c7e7b883d6bcabfd60c4adf6e2b2b7f104c8bd97c3aac6c302dca7ccc3ed8961fbe8ca9901dad7a721e101d10137000519f6015b8bc0f5e1efecb8a70d81d2b5b2c6eaf5e101a49bfab9a283aaa104c6edb5b897d79f0494bcc0af9ec177e9d5e5a701fdd0acb501b4b5a70185f7018b0b010c03018b0259e3dfa5e5fee88efd0ce9d6e0e9ffeaa6db02f2d9e4a8b9e2a9e362c5b7d4ad94f3328bb8d9f1e30dfda5f8f106f5ede304b48778000b039b0189018577594f4d47140301890255ecbab5f2abdb92ff12fa82f6a4f0dbcdab79c4ed83a1db8eef01d98bb99dcfc1d16c86d294b2bb1fc6ebd8f904938af1049bad4f1f43000513f601539cf795fac9d2c0ab13f6d9ea9bc5f58dcd02d7d2a5efa7c4dcf50ca190e8c9b888cf08ccf1a582ace501bab6bfc38b3c9ccdfd13cdd137000a0291011f070110037f024a86cbe697b2b49f8517e0a6e6e88de0baa107e8ec96dbc1dfadb56e9283dce084fdd3069ffb8f89a8c7d307b69e9caa99ad03a1b7fcdfb104c6c8e0913d8dcf2fc301a10b0c03710247b788c69fd0abccb116f4d7a2cde29cbcdd0b91fde7dd80e4dfa5019afbe79487efb18301ac91e5fb80f48903c4d4e485f78b0291f7fdfa9313e680fb05c4bb01d977130c036d02468fa6f6a3dfa7a38716beefc0c0ccbabdfb01aa00090fb60163a2def4fe9cbff701979cc0efd5d58305fcd89385b577ceb19f57c98b5cbd6b07010c036b0268a8b1a8acd8e9c28902d08cfac997848fb702b0dacab9b1bca103bdd7e6e38ae103c394b3c2e530b5d7cb3ddded5400080cc101050cc301675935011203670266a58ee6f8effa8deb04b9a284bcf49680cd2785a8ddb5ddf4b134b98581aab7f52900060b89012bddfab9f701cfb79569eb01d901cb0b010c036502629ec9e4919e9ba5af089080a9fbd3abd28169d5cc91adb78b8903b9f9df8887d7a90298e5e985fad728ecc283a707f4c19d03d88f3b070a0361023b51000611e401d90233aa85a9c880b2eadd16ee93cab8e7b7fe8702db95ecd0c0abc383239b92d0bbfac3a134b899d797acd901ccc4a4efa8e90ec8a381910585e1ef01e39f0705010c0301d30230b4b1f4ecc6dfa1a918f4b7c18caeac85fb06c7f5df87ebbcb0db1cfb9de1afec81d71dcfd3cb96b8d926c983f7d78304a9f79b8d0efa9d7f000701de010c0301c7022ff68ed6dda7e6d58b2093a5b28ae0afe8894191e395f8e791b901efa9e3d080f9f101f08581e3c0915ac4d893ed01b9a0ab1afb4d0b3b000508bc0150a2b5a0f3d68f84c501a2e0ab8cf1b3ebff049c9fffb2daffcd02d59e88d7969f1fb2e3c38901eed2df03e28301d977070a0301c1024fb7f9828784a88abb02baa1ddbdaca4fcaf15b7acb8e3cae0872192fbe5a6eba502cc8ddda701a9adbd77b34f1164000608d00150bc8eeac7a39f87c30480adc3b7ca9aadb103ef87e1f5d1f29901bcad80a484872496efcbcd19a897dd09e6932d000608d1014d070c0301b5024fcaa6db9e96eab19505a3fda5fdcdfbabfd10b8fc80f6b6a6a30ec8c9b484c8e70a89f9aa96811aaeacbb03be8d01d1080301b3024cf4eeada2f1ccae8b08e8bb98f5eacf89eb5ba6d28feb98f8b901d2cdc7ade6dd9104ffb983eef6ed0381a787ba8330ddfac30ffe9f1391677500050ec2014a9fb5ffa7ccaeab810dafe5f9c1fbbc82fd25d7eae8e2f7b0cd6ffb948692d5f921ea8adce5a314c392f1f11eb98d01d901853300080ec20148bbe5e0d5b3c4fea50fe6c5ac96bca983bd4df9a9d7ebffc0c302bcd9b099a88d812becd9a9acc34f96cf8b04a3cb01cb3100050eff01a30258818793b4b3b6d8c902aa93e3e5a0b8b1e303809bc9eb80f0ab02bfd190d1ac9101e6bba79cc140f3e7ef418135110b3200050eca0154d2c5d3f1fef5819b068d96a3abc3ddf3d3018992da96c0e5f7f568d7a4dec8f1d302c1f88aaabcd10284cbf6de8541b9dfa30390c747010a0301970253c3859486c2df8ee107cbf4eac6b4cebbc30196c9febdb1ceee9702d3f495eed5f2bb58deab81aaa515c6b2fda304eb85176f000508f2015ea99ae6dbddeecfd336e4d5d1bae8bccb52cdb1b585b99d13e7eec0d4ad049280d5db07b8c8c90f8da11db3052d000608f9015cfbbfa096a2bff4a102a1bec0eed6dc82ff028fc6d49b898ef903d1d587d196fb01d9b1b99cd70197aaa58d37bdd518f901bb013400050ed60158f2acccc5f0b3e28b07e4a1b2f8c6ccbfb903fde5d5bfe7a78901adc996f5f98565e6e8decf1ec3c0870aceb72d00060b820105059b01830260a8d6929c9ec9f49501add2abc38d86b9c301a1afe59cb98d9760eca8859be90ec0d2bba90189cde72b000604e3014d0a037f0255d9cdd3ded5d4f4bb0e92c2a0bb8fb0e7dd019ac098ceedb088ed06b1b0a2e494bfc91fe5f4e28da571e388a30deb8f01d901d1770b010c03710252d5a6d4969ca1998f12a090ecace6d3e5fb0193c8aea9d79de1957e9cd7aad6a2bb018bfccadebad52deadfadf301cdbff525c701a10b0a036d0251939394b1ffc7abb913b78898dba5e0b3ef01f7d4bcd097a9f58106c782f789cd8ecb0787afa586ddb301a8d5d9b8e90a858f831c8baf12d3110a036b02290001d10232a583b1a7b9ab84e516b2f4cce8d8ffe79f6fc3c1b0a6ce99b306bcded99e9de5c507fbedbaebbcc701adae8eb3c90bd0dabb04dff11d110a0301c70231e4aacb97ced0c6ff16968cc1e0c8d5adcd029ef8f28c8685af8301ec90cbf7d4bfaf05d3d49693a54cf8fabd2af9c11be10b050a0301c50230e2f8fef7f99bcbb31894a6b2f4ead983ed02a794d6ebfdb2d0ef16fabbf594e49bcb259987fbb3bfc52ba7eaa4f58106aefef88f7edec71e9101cb13050c0301c10230a2a098e88ec18dcd17f4a0d8ecfee8839303eaf6bbf6cf88b7e301b8a3baf3ec90d731e6abc68ab306f3dbe09706f5ede325c707010a0301bf024e99e58ff0ebddb8c565b8a18be2e5fff905d3bba398a2fb8f0af4cecfceafcb03b3c6d99b99018ec7ae8503d09503e0000901bb01b501000501bb016b1f130701140301b5024dab97d0e294a1dba30291e08e9cc2c7bfdd14e2f3c0a1c9bbe93cc8d9d1cfd0b342f6aecbb5b103fcf2f3876ca3f539000673014f110c0301b3024ff397f5eee78c9bff01c5cc8298c8e2ddbf0187a097b3dcf7cd339ef5a8f7a124dcb2e6e17ffea578af3100053c018511010c0301ad024d90bea786aba4f9dd0683da8baacb92e1930d9793da9ee8e7b10ff19fbfa5929d0284baefdba302e6b7eaf736f5c737000901b501a701a101857713100301a7024ba482c7ebae8ae2f108d0c389e0a593fa9144bcdee5c4f2879d02f4c8b2f4e9ff8b33bab1b7b4e172ecda91bd20b5ca810a84eb01d901d11f010c0301a30248c1a8f982f2a3c0cf0db2b192a3cbdde5cf2fbb958bcef184d535e2deedc9ddbf17c781fa8d87098cefad9902a0c08f01c9b74f7f000604e1019d0257f7a6e7a6f199eecf13bfdbc88fd1feed38bae9c8e78ceb0ad7a99c92a758cdd3d906b0a927000a03b00101970185776b4f4d1f13110701160301970256e29cfbfceacef6bd01f4f4de858ae8e9f901a8a0e69db7bcbd0187abeadb9bbd0cb7f0a5af5c85f72adb01080301950250f8ebe3aac9d89de309faaa80caafb2c6df64eca6dcb994c9df02c1d3fca0bef1d90384dfab95d1f922cd8ecbad37dd8725c71f0178000505de014fe3e1f880c38da5d10bb2e9b5dbc0b8e0e7018fe9f8d6c5b9f0a701acf382dfc8d5f14487ddf0eedd02add3b3c30281bbd332000601b101770b0c030189025cac9cf7a4c6e4ffff01dff4e7aac6c19b8703a0b2e68a8d86c104b69d83d094c903bca2f9e0af37faa7ef12a8d919f53b0739000505d80159c3a6e5fbb08df1ab05aac3dbc5928ebc8f3b8ef7e6dfa6c5db1a000703bd0133c9ddef9a9b08a2e88503b8c50185131107010c037f025983ce97cebb958cef09b3a1d993b593dbff018ee1a4ce9e95eedb5fe4ad8688cbb50199f9f0f1c1e126a6dec08509ddc3dd0885a34c0008460135010e03710255f09cfcdcd6c2e5f30dd2b6ecabb7cee6a9019bed98f7ccd9fdcd02a4fda590ecd2ab03ffcfb386c7b308e5ccbcb8e5039fa7f2f161be853e000901bd01a11d110110032407000504960101af0233f1fee7d9ceb2fd9b049eb4e19c9cd8979f278592d789dfa7cf05e087bbc2b2a301a4f5b18d850b93a1ad04a4d73100057701bb0a0301ad02328bd0fda19de79cb108a9a0dbb7a3b9a39b01c6cdd8d1f38ad6eb48b0a9d8bdd3f372d7bdc6d4cf06ffcf93974dcee31be11f1307010c0301a70230f287e0fbd2dfb1950ce1f0afb1a7a18ceb549fc1b5d3afa4f901ccdad6d8c1a08737bfdeace6df0aaaede59d01fadfcd01d901d101cb01bb01a34f130701100301a3022f8bd9f6c3a293d0ab12e28293a99ef7bafb52af95eaa1cf8d42b5e984b8e104b69ebf8f0dc6c114ed1d0b010a03019d022da5ac8c8af1c7efc1149681ad97919dedf303d9b7d5ccb6d1b48d1d9f928a88e7b7ff74d1fdc3d9b2eb1ffaf9bf8f9d04e4cdd5f92f93bd2fc31d0b050c030197022cd8c7bdf88c83f9f313f3e7f3e4e8a8bde905de8ee0a3c7a3c3db1f80c482ccf9e6f528c3d097ccf5e9018af4ccf1c102e8d7bd04feb701d9470a030195024c9992ffafe091e18522bec5e7f383b1c93be0fbc2fcdccb1bd1ab8398d703d4cea9e101fcf48d01ebd3018b13070a03018b024b8ce8aeaca6cacca702c0e5f0959bd3d38f05a8a7a293ccc5d905818bd0a6e69102e0b1c4a8d57292edeb01969a8313914d110a0301890247e7e8bba1f9f58e8d089dcddfaaabe9c0ad0191df81ecdde993c530beb9f6dbcbb90696d4a7d6911688af9b02d2ab01851f130a03018302130003dc000501010401001d0101000100
    (by decide) ⟨27, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock17 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨47,1,true⟩,⟨73,1,false⟩],75,4⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    21 1199 0x40402000507cb019d0219ffc7c4fa8583eca5029496fab0a5abec9b05a0fcded4dab5e70a9dee9df484a30cbe98f0eac5068ce2feb533e9fd63af33000635011f1d010e030197021dd7fec4dbaeaef0e13c95b0f79cb6acb50bbbb89097959305e1ab8b92fd03c5d5c0f102a6eea12f000c03dc011d0b0e0301950221e1f7ac9fe685b9af05d1fc9b828bbdc5ab43c9b5cd8fc9edf304cda8cc94ceeec901a3b3849780eb05dfe2cefb0b9b8cc306a7f33c000b0394018b0185671003018b0221a3dfc3c6f7f4e5d507cee6c1ceea8b8a830183a1d189d299f4fd01b8e09a9c91d8ed62e1c8bed1f30cf4b7ccc502d1fba53fc901d9491341000603ce011fe99889bcadc2eac70eb6ecda949b808bdf01c68cabe3fdb88fcb02ceaaa9de84b0f102d0d9daa780e50cb1d899c16dc48911f305010a030183022ff5a29b98d88b9c8503e9b4dba2c8d4ac9735faf9cbe7bce539e192c4e9a916c6dccef77ebfdf62000a01e0016713070e037f0240d1e0f7ecd5b4959b6bb9e3d19a85d58709fef5c9d497cf03e5cbb5d2a30f8ff1ff01852b000501aa0177170b03000503e30142d3a4d6c6b9d6d6e502daffab98f998ace905a8cab6c499efbb03b1fbd5e391af6fd9d2cfff038ff38565ab01d94f070a036d0241b6dff2a8fcdda7b305eff4e5e792dd97ad0888c6e283ccc3c508acd4afa8a9bb03e987d3a6bf05e49afef306aec9d3428501a12f0a036b02130001970214d1ccf5d1efccc1f166c2b8e483bcb58701d9cda1bfd29ba3029ea8de9ea0e55e9bf9e6e909faa0a90df0f7019e000803b50101a101950185776b591d170b14030195021ce2cfef84e5dac3e303b5cba4b7e2b1c6b70e92c7bfa89a80f930c6b9e7e3da8f4cedc0d9dfc121a9d8b1e72681ffdd06e88101d901d10a03018b0220e3a5d4b994ddbdcd01d79bc1f3b4deecbd0281ba84d5b6dbf715a3cfa0c3bf04b6b19adb018d97ef01b89b01d97b000601ba010189022187afb0aec5d4abcb07c8a7aaaee1e5fadd2d89b7b286998b87018cee9ee2f4d5cd01cacb90f79f951db1f6b3d909bedbdd0afbc538000501f401bb1f11010e03018302208695c0bce0ec92e70cc1b0e3e3d992a1ad60c0e389bcc8abc101af80abcbf2c2a331e7aae6a4b102e9a1a1d15be0c317f313070a037f022ca58b9b85bfff96bf0fd3aea7b28896e79d489d8ee3d7fcf7e90198dd97c1abb29302cbcdcee6e3dd01cea8f8899929dfc79b06d8854f1107010c03710240e2e8dba9e79e84d30ab098bbbea4dccd20ee83ffcaf4e3088cb79e8fd302a0d9a9a51bb6ff18d91f0b010a030e01ad00050e010e01bf010183020ad9e8e0edcdb0b1b561c5a3e9d7f7fa8102c38fb0f8f2bf970184c498a3cfab7fca8db8ef48feeec904bddf01d901d101cb01bb770c037f0221808ea4a9cbc08db74285d3b1d982a1db03d2ac9fc0ccb0bb45d7d289888b34f9a0df9f03fac0ef2bf54f080371021feacaf990aa9fa09b07a4b6ef96ffd1b18d5d93efe2a29ec58b3babd0f1dbf1af21e0a483fd8f14a39798c104d9b59702cff501d901d113070c030600040401aa00094a01083c010501010400710207fac3d7f3cf95afad0cf8a1efcab580cd2bdda5d5fbff9105c1ccd593b958979eb129eef125c7010803022f00080a0104040200070101000100
    (by decide) ⟨37, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock18 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨47,1,true⟩,⟨71,1,true⟩,⟨73,1,true⟩],81,3⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    20 1998 0x4040200050b8f01af0226eac7a2bd8392dfff05cbebd0a198edf6fd2cffcae690d093f35ffea6f3bea0c3018cf3c9b692f929c4ba9ec517fa8ed505f4853600070efe011f010e0301ad0225be95b8fac4f1c5dd0ac2c2ddb2899ba7e75cacbda5ff8dbb936effaad4839fd5028bfaeee3a3a50dd0bf8efd11bce0c51aa7b31afb4907010c0301a70224cb9ef2ce9bb0def10df290c2e4f188f6956fa8ec878b93948502b2a88b94adbddd01f8fc8399968342d2c3cacf0dea88cf10b7f11199070a0301a302359ea285c897c8bee70289ac88889c88b8df019ff2ed80b9dfdd58acd68e828917acfbb4a104d493db0190a51107010a03019d023399ecc89a9bc7acf507c5cecbd28dd8adc541fccff3a9bdd897019881f3feda808301899aabc99d9510eab8a4cd488fd501e700090bd9010c0301970232c385b3e09cf1d1cf09b1b1c9ae9acee4d555c68dc5eeefe8a1019ee4c1f1d386b531e08ed1b38507cfdc82c92db8cf14954938000605d3012f9181cdbea3c5899112cee4d5bb829a9a9901add1dcafbedaf9ff08d0cfe1ffaedfb70cbebbf4d6fad10db28bb3a1ad5af1a6bd01cbe0fb1afb1f13070c03018b022eba9ab984a4efadeb1599a8d398a9d6ed93668df690cac38db5058bca9aad80dbf103fddd9af3da9d02d2bbdaa6a101b1b0a9ed0184bae96e9f01891d110c0301890247fef38ad2c29cc7e3399e90e1c0e7c483318ea09bc79ef33994fd85c0a10cdbb7b3df049cc1cf4fd701bb1f0101b2000505c60145e5c3cce1caf9bedf0596cbb2efabc4a1e50db9d6f2aaac99ff10efcaaae2919766b9ab90d513dce1b70bee97590b010a037f024ea6a7eea7a3cf8e9b05d2cea7d3bdfa88d32cbce3fedefbdad336a8eda68ff8db0286b389f48f668dc9f112d34707010a0371024bc3c584baa3bedbef0ae589eeacf2e4b1d94ab8af90c2ad80eb03f5daa2b7b3cbe1038bd8b483878779d990e0ab0fb2e701d92f110a036d024a9293cfc3e3b6c2d90ce993e0c2c9fcf5b301a1e6f3f0f788daf302bd8baef3f384b10bc3abf7eebd01e6cad6a10192b2e101d300063e011f070c036b021b0001a90226f8c0c3ef929086c901d8dbecd8a7dfa79f04be858685c2faff03c78da4e7dfe33683ef968352e985d90996a3380009058c01a701a10185776b49110701140301a70226818ed99ea6b1b28d05bcd3f3b491bcaba7149cbffb99f78bf32dcf91af88989f0d9ce097da9503a683d4b102fa85a701d3bf01d90185170b0c0301a30224ce83f9a584e3b3b30aa386d692ffa8c5c9019794e2f0d6eec7ed04feeda8aff68ec104e9a3aedb95a901eeedb08dc119c6be8d0ebfe501d9019d11010c03019d02239af999abe395b4d910c794c4daf8b09ba960bc9fc3e2fdcd9305ceb5b79acae4d378c9dbe8f3f97c8feeffbf32a19ddd16c4e901d96b0a0301970234be98a0d1a998ecb301c1adf6b7e692acfd06f8d883a6f1d6db01f3a3f5f4b2a70eadf4fbd504d6a7e705b58701d117010a0301950230fba6f9c0d98ecbad0ca79a9be6c0eb83991bc2e1a7b58ca1cd01f9bdd7dbebcf04bafdb5f702d7fb9b1be1070502b0000604a60130a190a4f0c98cc4df0e8ba1b090fb8d99d14ed9cfe9b698cfc901a1c795d0c088c73a8296ab9ab304eab592ad28cbe11be11d1734000504a5012e92cca7809986b0f514a2be9d8c869bf6b17e90c299c4b3beb30484e3b5aface6b303ddda85fd8df736e688a0eb03bec1ab01f4f501851f0a0301830243e9dcb2a1fdd684c902aedeaeb1c886f1cf1bb2fdc586da858904d3a9babc94f30296dcd3e4f36df9b6e110b7f1139d1d070a037f0240c1b5c58ebefe89ad0fdca7f88d9b9798ef4989c4c9e0ebcbfd019e96c6b28a8395019481ccc78bd96bce8b928d1ed1b88120d713070a0371024ebafd93c59ed3e5d305a5b1adce9efca2a104a69acfd0fee6ad3d9cb7a685bf07afb19de11197d901d901d11f0b0a031601de000601ce018f021ed8aaf9b6f7bea8cf02a1d4dbf188da96c10ba2abffb5d2f1ad178ca3f5bbd5f10cb9a0b58fd54cde84a11fa68330000a3a01018b0185470b1003018b0222fb9b9397bfe0daa13584f7a49bafd28d0cd5c3c3c4ada503d2e495a59539a284bd14f9e9300007028401bb01a14d11010e0301890224a0ebd9f3a6958db905f280c1a3dca8aaf31d93b2d4fed0ed990186f0b29fd0de870181e7fcdeb98133f9d9a48f0fdea3b902afed01d11105010c03018302074b000801010902f10101910219edd9cd8e83f580fb04ead8c489e9c093bb1184e2f7a2c496b5369ea3b99ee9a905b6b2ccc7b303c3eaed8568d5c90283f535000538018b0219be8a858bfeaac9d906dba8f9949790e3f970be91eaac8aa5ed05fad890bba3d98302fa848baaff34b8f6af059fa110c513010a0301890223ad879da5abcce19304c78ad88cf8cdfab30dd08ac28de0999f05e4a184b0a49f7aad9e97db30c984b50ad58b67000601b70101a11107010e0301830222a2f1c1c3bbedcbcf09cf8d91b0a3c295dd5ae3f8e883c1ebaf7fc7bec18a8ec302f89ecbe0cd99298aeee3e703c187f302b1d101d91f0b010c037f022e88bbb098a2e0e1890db9a9fdafd0f3d9c70190a1fc8698b889a705ceadc589b8fa9b05fbb7ee9ca0af35a9cff68103a9ddf715b101850b0a0371022cb7ded3eed18cf4a514a3b094efb098c3fd48bbc49ada91c6930ecacadcbefa81028edde299ad04f39cf501cbcb01d901d101cb67130c030c01bc00070901050701050501040402000b0101000100
    (by decide) ⟨40, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock19 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨47,1,true⟩,⟨71,1,true⟩],75,4⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    20 1441 0x40402000508b101a1021eb6a8b5bfd18d96c701c8d8c0b686aa8e9102d8efd5fda8a5d105cea9adf3b8b711848d8ef703cff2ff0191a91f0b010a03019d0224d786a0b4fae9afcb50ecf5fcb0c7c5b704c580f9cad292d303bbd4f48f96dd019de4e39aef018cc3e58d08e39d01d901d17711010c030197022498eeb7dc8cd8dbf102f0aca9fe80dcbde306daf1b6aa9db5e30fb0989bcce6e306a7e2abc9990196a7828126ff01d977170a0301950221e1f7ac9fe685b9af0ce8f9a5aaeffdfb8b01b5bbc1b8c290a3ab01c5d1bfb5e8a5b902b087e0c79e9505cdb6858701eab69901db000b04d2018b01857767594f4d472f1d0b011803018b0221a3dfc3c6f7f4e5d50ed6c2e2fadb85b2b301e78694b1a8d0dfef048f91e8b09ce0cd05fbe1aeaab69701c691dc9f8f02a5d8cb01d901d14f13010c0301890230898eca9cc4e29e9f06ffac90acc9b4ddfb07dda88c8283e2c901e7bca6d8f7f70a87ebc4bd45bfc31e9101851f070a030183022ecd9de2aba6aabccb0bdba49dc0fac9d2ff2ea0f8e3e6fcf6f949a1cd8ec2d08b3ab08bc9dca733fad4dadd03b396f11ee101851d07010c037f02439a86b399f4e59bc703f5f78d848b98dabb3187d190bfefd302f5b89d9bdb69f3f9e508c8e501e700063c01170b010c03710240e9c6ded9c7f0adeb09a1aed6d5f7fde1fd4c8ff5908b9d9bb73bf589ffabdaf715fe9489efcf03b4ab92b14c869b36000601ad011d070c036d023fd1a6f4b9b1b5f6fd0bbb95a8ecf5e98f8901ada6faa7acd0909301a78daeb9c8eee145fcbf92f6b105b5f5fdf501a6d2cf6b8301d91307010c036b021500019b0219a4b2a5a0e3c9f0ab03ceabe0e08e9cebbd14e7a8fd9d81c4d302e3eac4aba1e316f6dce99502c4b8c502938301cb08030197021dffb4a6a3818fcf930184b2adbacb89aeef49b7aabddcccd51697f2c4ef870a92a0bbd70ad4d7f50480a101a7000a77014f070e030195022389e390928fa4dd9305d9baefa59bb0ddd11191cc9cdcc7adbd0994b58dc6e4af08f58cea83d378a9bbcd2c99a101d901d1130a03018b0222c99698999cf0d0e107d8f4f1dcd7f0f8d94f8aa8f2f1c8ccfb0bc18e85adc0a103b2d49994ff27ab9cd303f2d56d000b03a301890185771f070112030189022187afb0aec5d4abcb0eca81829fd3fe9ead0193e39fa3f89dea9d02c1dcd4a2ecbbab03f3c4a7e3f3bb1ef0ab8ff901aaa5ad3f000602d9014f1107010e0301830230b4f297eeec95e0bf04a8d4fefca4aed0df03e283c5c099f28524c2ea9dddb30ba2dfbbad0ab3cee94da134000534017f0241a7cb90d7f5d5bfa1019ed8e9b6f28b8ddf04dc98e6b293d1a3028eb7bff5f98101fc9fe2d3d309abe8d711f32f13070a03710243abe4e9eadae9c4df03919efefbf6d5b9ed07bae7ddf5c0dfc513efb6d79feb9302feb3dcf71ebeff3bad1307010a03106700050e010e028f010187020ec3a3f88e8ed297a96cf1f4b2b0808acb3cdee98df398b928b591b4e6db07ac91e29d01a2e6ff3bad0185131107010c0301830214de8b9ee0aea792d13a92ceff8b8294c3018293a6a4c28fcd01aec09ba8d4f72e9dac88af3189c3cf03b887231f0b0a037f0221808ea4a9cbc08db707ac94eae5c5e2c3ff0199a08e80edb5abed01ef91b2d7ebaedb01d3b8d097c9c72be7d0f7970c858ad704bddf01d901d101cb01bb01a1018577716b2f0b01140371021feacaf990aa9fa09b0e84eefbb0c5c1badd01b193fa91b3f69d9d0f82c3dcf88fc2c132859ca3d1cd8506e88fc183a10287af9cd32aeda713cb01d10b010c030800040401fa0009018801087a0105010104770208a395ecfc8fb4d6a901aff1a782a4e7b79703ea85f784c986e361d898a79d831a928687e1128db0db73f72f11010a0371020fe8a8e0efb2e2869b01d7b4bcddb4a2d0c304e6a9f9d8de85e90491878d9592cb038cffaefcbf6e92f99f248a8301a11d010a03046a000b0a0104040200070101000100
    (by decide) ⟨37, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock20 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨47,1,true⟩,⟨59,1,true⟩,⟨79,1,false⟩],81,3⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    24 2834 0x4040200050ec901c3023aed8ee5dbb084ead111978dedfeecd0f4ff028ebda0d8ebe98cab09d9e5bfb2dba102c4c0cfe8d745d6a8b908cca115d51d0b0a0301c1023a9f86d7b2d1aec8af1180a8f492e0f2c88103b6c49499c8c6c0bf12eb91e39c8abeb904f28282b2b1fd44ff80a9fb06d890e105a2ad70000601e301130c0301bf023798de8fe6f7ff9d851997dbb598cd8fe6dd01e3f2c2c9c1e799db02b39fefdc9ca8e3059caadca2e3c97fe7a096870c93ead50283f50185130a0301b50252e0d98ed1f4ebc2b30beea9dd8f84ecef1cf9eba3d3a2ab25e3b29796e711a9858df96cf2e72da501d96e00070fb601b3024ffdd18fca94d6e0ad04e5eeaae3a2d4f6970b96eba786d79f950ee683e9b9c7a306b7ca9882c1028396cf9d018798872bd92f3500060efb01ad0252c490b0c6fee182cd04ac80eeac9492ca9f53e6eafc9689e146a0c1ae9f91168cb2d2d70ba7e6dd05d3b52d000901c101a7010005058b010b100301a70250c78c93e69fdfbba107a9afd3a0c8da91832bd18ec7c9edcc9958eafcc89ca8bd129ac4bd9eab06caa2a19b37d2ab018537000910cb010b010e0301a3024dcbc5e8d5919d909f0c8497eacae7a5afd94e89bbd5e49a8a8b7efadbf5f1f6eb239bf1d3d2a501b7b2f48d2c91db670803019d024acfffbdc482dae59d10a2e286d781c6e6f501a6e2e4b49089e0bd07a08fbfbdf5a5cb02ade6d9b687eb7bfeb2fee54490a8a10cc7f572000f0788013b0712030197025ceca6b5f1e8f4a3ad0abecfcab881f4c101f3b5e3cb90e701abba9386a533e9fd248b0b052c000507940156ced98daace8dfcf309c488caacbfdbc8c5120008029e011ea0e2a487b1a50281ec8ece8d15accad911000a02e1011101000507960155af96b8b5fbf9c2810abffdfbfeb6a1b6d5018aa8e595dfc5cbaf01aacc93f1ed8cc308c4dabbaaaf45bfe0930ad0dd30000803b6011d0c0301890262e8a98999de99d1cf14a6d8c8c8d6dfa118a5e1bcf3b6e920d9f29c90a308baf3e5b705839c9901f2f51d3100050eb8015fe68eb4f1eeeeebbb04b48ef5dcf9a9ae950ec4d9e0969198b306c4c2dea5feef068a9ac9878501bfb192df72c1cb31957f010a037f025fa1fad39880eee8bf08d4c5aabcaecff29d018a8dcadab4afa6fb0297e7cebfdba78b04a4bfddceb28b01f0f497f39b77a2ca9f16e09523bf2f0a0371025bf2a89389c899ab830eaabed0bdb0eba59f11e7e0bc9fc5b2891bb69a99bada9702e7f1d0a2b76aaae49b2c99e16ff9771d0a036d025a9abef382abeecca501b4000905e60101f5d5e1e28be9ebeb02eddbeda1d3d5f90a8a87bb8dcb8b03a78e898be3038db5f0b115868726000a03bc01050c8701594f4d2f1f130718036b02230001bb0239ab8c83fee8e2ced110debbfae78195d0ff01c9cce4d3e0cedbd125e2d985ec9dc76c9991de99c54fbaa5da8909a885bb148c9744000609b401130c0301b50238d9fff092d0fde7f710c6e5dd94c5e0adb90388c6b3a4c0e2dbe51188d092a49ac6e307fae3bacb89dd6985f5a0c115e6b5c30293833c00074101a113010e0301b30236e6dbb4ce89cfb3e915d2c29ca7b8c0dab102b0feb4aff5a4ebff059dcdb9bbbbbfe906c4dbc5a2a3bf7e9db4f7a36ffabd3a000901e601ad01a103000601e6010b01140301ad02509aae92b3cbd798ab0185aa9497f8d5f4d704e38dc490d6999108ab93fadf9ba905a285a6ced30185b1e1cb2ff5a320d73800056601a7024ea4baeaefd690f1b704cdb895ac9bd3e8c75385919b90e28311f3c9e3d7fb04d8d2aefd03e1889758cb7713010a0301a30250cd9ea3b4b3b9ccc304c2dcc7e6fb9affeb17cdfddeb7e2c6977a9ff0adb9b319dd97d6ef03c493dd189f019d13076300050786014dc2f99fce8f9ef88908f1b4edaeb2a8bda901a897dfff93e4a98b07c0bac4b3b1bf028b8ef0f5eb12f998ad2ad02e000c07fb01970185776b594f1d1714030197024cbfc29eac839686cb0beebc9edbda94c48d15b4e9f581fbd8fb1b9ebfdbcfffa703b4a0ceefb90cbfcbfd2bd901080301950259fd9fd5f6e9ffcdc702b0ea93e6dbe2e9cd188fe2a0fefce2cd3ae6cc82f990e714fffa90dea91382bef9c131b5c50197d301d9018b77000504fe018b0258d7c486b5ca8ad4dd04d5b9bcfc8ad1b3cf58809beae6cea31dbbccf1f9bb03e3f98ec53ddded24b501080301890254e6b197f1eaabea9f0ab783ffc282e7facb44fdefd19cc5faa32698d392e8c7f90dbfdeecfced02f8bdb6c701b19dfb0193856b010a03018302529af9f8efaac1f8cb0ef1ddd2aeaf80edc323a8caf9c2b4df995b96bdf69ebbff338f8ef398a315a5b8e5a706fc9be10383f9019e000c07d8017f77070112037f0262fbc1a3bbde8d9be303ece4d4ede980e7a719bcf4f6caa488b701a485e4d1f3e71f84eff19b07c4f9b524bd0705010a0371025fbb8d908b96e7af9708d6e9f5e9df9584a53dbce9f0fdb1c9dd31f28cc0aca0db62a4e7fad18f0cbcb9e1c102cbc6b701938501a170000502de011c01000602f5019f023b83ed8f959cb1ebf501cfc6f6b297a68cf506ed8bbfbaf39301b6e297f4d90bc8faad09f7dd28000b04a6019d01857f77594f2f11011403019d0238e38c80dcfca9b59f08a1b8b7caf9f5b0fb0385d89b88aec8850489e886fc93f324a9a4d2bb10ffde9108cca1019708030197023882ebd19fc6fbf8ad0ab490faedc9f2ccbf0cc1b1cdb1f6f19916d3fdfc87f5ed38e8ebf1810d99dbfd0191a92f130773000502ee0134a1c9e3ecbc98c7f314d28d80db9fa6df8b79e8ccadd5adb6e902b58aace9dc88c32cb7f6d8bd8f6cb7da810eef8912ed230b0a03018b0233c1a9b4af86eb8b8114ac8afd82b9c7ab8903b2cfdfaf8aeebbb70bf68fcd94ec87997eb6b4c7ded938d59799c108f2dca306fbfd6d0006018a0189024ad6c4a8feb8dbe2fb04d985cc86f4e299d9309097dedad6deb933e28abcffd3cf56eaa28487f309e9e4a78d6196c135c5131107010c030183020d3d000514010f01010604b701a30239c7abcbcfd2eda3a714fcb1cbc8a2dbd732f3fee5fb81e368e4f2b2bcdb20000501ff0101d9a2e704000501b00185110a03019d0237ade4d088f7d1bab506d3df9fc7bac9d0ad07fff3b1beb7bbdb11d4b7a3d38bab01dfb8eaa3930dd2bb9f1190ef1d0b010a0301970236cff7d1c6d99dc28f088694b7e0a4b5d9ff6bb6dda29cfeb8fb01e5e189d488aeed11a08d97fd8b01b18fa2eb4dd49124bd3b010a0301950232fad6d8fbc199e8d1128180e6d488cdba9301e4a2be9a9f94c4e103cebe82f0a7df913babf1dbb8ef25f4ebc2c50ba7e6dd07b38f01ab000b4e018b01856b07011203018b02329ce9dab9a2e5f0ab13eb8eedf8c0a68b83028dc596a58ebcf48507d6e5b19ce89b8d07bca6c6e2a69516e4dae7b98306edc9ca8330fff743000b01b4018901857704000501b3011f1d01180301890248e887a0b1e8b2aca903bd9783c2bd998aff24eba4c783b9af9d0cac839defc2ef01eebaa98ae914e8e2c302bd837708030183024bbace9a97f6fbe79f03fcacc4dfc9d0cfc506bbeff8f6eae78905e590c7b8d5af01e3ab94b0e111b9d5ed028fbf01d94f110a037f0254d3e1edf0a0a4b8db04dbb8f2f3d3f6efd121c686a4b4b4b68922a1edcbebbc930aefe3d8b2e126a4e98709c6fd01a00006018c0101bb01a1018577716b674f4d3b2f1f1d17110b07051c03710251d499a682f7bfbcaf0a85c89fafcbceff9b6aa9cae39bb6d3d51eb697d2f3ddfd0ce094e6c2e90fdbfee18f01daed8d44d54f010a03125000054d010189022db4a6d5b6be8ac1e10690dd8be9e2f1f2cf13d7abecbaddeef5268ff0fbd0e7a521eff3bd98a520dad5af01f4f501d901d101cb4f1307010e03018302034100050101050701050501040402000b0101000100
    (by decide) ⟨40, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock21 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨47,1,true⟩,⟨59,1,true⟩,⟨73,1,true⟩],91,3⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    17 1107 0x505c801af023acdcadcf8f69fa2810af1c9cab7edbefd9b01b9a2f891e4b188c102d3eeccd4b4c79535adf5d99bb508d5d396f501a8b0fd3dfb3600053b01ad0238c9b4f2f0a59980a310c1f9fcfbb4ffaccd71f8d2f197b6bcc703a6e6e2d6dfadb103c4e4c6d98ac513a4d3c4c302bdfed11ae736000502ac01a702379bfbd6eac4bfbf8f13c1d9f3b09dfdb58d01a3b3abb7e5a090d1039cd6c1d3f3a69505e5eacbd1c4a903d9b8a3f4d91fa2dfe305d3b539000902df01a3070e0301a3023597e5ece1f3b99db118a2bc92c881dd9ca901bec8f4db96a59a911180889796d6d2b306e3f8d9b5e2dd34edcaa9df22d297ed09c1fb01a11f4000056e019d024dc785dae6a7e1f5a304c7f8e79ccdd186f339b5f4a2839bf513c2d987bca701e8a3a4d10ce5db1e91230b010a0301970251e78ef4a28abf849301a6f89bcdf0b3e7e50399f1819dacd8e303ebabf2cd90f902ead3efad9f04bba1d5c30399e8e3018ac301851169000504ae0195024ca8add8da9afc8bcd0beaf0bfdcdab6eb9b0799b49185e385810d92afdbd0aeed02a6d283ecdd49f98ff90aa1b112d3110534000504bd014b9be786b29ea1f3bf0dc699dbe4bd8da1c33a8ad4c3d5f9dac52680a8dee1ba850deaccd5e9bb01da9fa6c1189fd74fd701d93b17010c030189025ad7e0bab8eaa3c1c701c4def692a8ed89e505a0fdb0a3ebeaf317b2d4d2e18eb10f8be787edad05938ac1db289aef6a000b01f401850183776b1d17120301830257f5a8dfdf93fda69306abaf89db8ff1ae8b04f7d0fef6a3b38701fcc8e5ff90c30cd8f5a503ab9501cb0108037f025ed8e09fb3f1a4f6d905d1f6be87c0c3cda50186cca9f8dca6d1d501a7a1fafad7aee346f9e887fda90cf9cd90bd5c90ad6c00067d011d170c037102668b98d5c898f5c8ff01a9da8b8af4d7fbfb01b08abbcde990ed01cbe6cc8dd7ff61b7bbede114eab88b02b3b91f08031837000601e501930237f1f0c5cfbdaee8fb089e82c4ebce87a6ab0280eeaacbda81e3d90dc9c8a2b2f0c5d521f1ac868cc4e91bb8b6d8e7b50780e4bed5189fd73a000b41018b1d171003018b02378af986f5f7b5c1d90ce0be89e6abb4dfa513b3afdae091ae8f1ae995ccd0dfe903aec2a2d0bb2fcb93f906c3e501d901d101cb01bb01a1018901857f772f07120301890234d692cae9a5c9cbf313bf8ff9b68af0f3e30185e1bb9f9b8eb6dd059cca9fb6c2b4c70dc5e094fbcbd905f189e6edf162f4b8ef01888f01d93b07010c018a000a01b6010b01b401018f023a87d9c9c8cff3dfaf7297cc99abf9cf9b03a2d0b9bcc79daf01cab996fdecf955fda2f2972aabf511d74d13010a03018b02399ce2b595ed92a7d503cbd0edd18184f4a70fecdc879ac2b09306f0bf8eb4c1c509b2bca8f3eb01cba8c79d02e2a901d901890b0a0301890236dbfcf7fdc4ee80c70becfedfcbc7c59fb120d19ffeefcca48f0ed5b5f6f3b2c90286c6ffa6cb59fa8c9f1dbfbb11d749110a03018302070001a700090b01040404040400090101000100
    (by decide) ⟨45, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock22 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨47,1,true⟩,⟨59,1,true⟩,⟨73,1,false⟩],75,3⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveFourteenBlock21 (.nil))
    27 4917 0x1e5025fcbc2ceabe3cdffed119bf4f8d2cf94b4b901d3aae39edbe0d29704abe4c8f7d8a6ef068882b0b9c8d301ded1feccb3019efcd0cd01d3dfb936fd01d10a0301e3025df3f5a8a7cfe7d8b114bcf194aba4d39ee91edef4a8d8f5e5875ec1b98088d6f725dc92bbfceb0cb28cf7c70586f8e740af1d010a0301df027084809db2f8aca2bf02fbc58b9e9bf793f5048cfcf0ddc9a38901f1d7a3bd82e502cab4ca955bc1d319f54f01aa00050ab201d30269d4baba87b382a98309cdbfbfbaedaee0e9158797fb80b8dfd10382e9ba8ded9d01f3cbd49c8f039ea5af2d000818ce010719d1016b2f0200050eb701c70268ccc49495bce5ffb909c191eac7e2cf8bcb01adf0a1c18e8ba69d0484d3adf1e3dab501a2b0dfc4efb507e0c494e701afabc143ef1d0b3900050fc10166bcd7c8b1d0adaca50ccda48ca9d9a4b0c94692a1f6d7ae8d9f4e998db886b8f705f9d5d0a3e73fe8b5f303b8c51f080301c10265b4e1a2bfda9182db0cbcc899bb9684eab701e48aa89adec9ead103eee8e8cbaee7e301c78b89d48aed01ba9fc2b38b41dfd5d730a3f319af076e000518d401608d91e5868b83b2e912c9c3fcf8c98fdbc901a8c18fb4d7e9a0a104f39b85f4e892ad0286e1cfd2be8301bd8bf5a48f1bc4bccb34000501e8017701000718d4017386a882accf8a9fb3018495c2db8c91c8b50296b4bec0cb96b71afaa9eeefd30288c2f9c74cb0ef189f01bb23010a0301b3026f98d8dde6bcd9a3ad04eae8848a82d1e5db22cfb79ac098929d1be19ed3a0a99719d7de80e1a942d68199039c8f07056300060796016bab89b9a0aaa8a7a70887e4f189c1b48d890180b3c3c3a5bdb1b50cdaea83d9d6addf07b8a5c1faceaf03a6f2f481a303f7b99d837cefa764bb133b00050fd90168e1ffa0f1c8dcffa30ad2c1d1afe8cb94bb0197e0908088afb3d704f2caebadd89ec945e1ad9a8b9f27e3e9d6930dc5c9e101f434000501a8014f0100061e800170e3f9b0ced3a9d6b703f1e5a4fea697c0e314f0dddf83c0fc8f1cd9d8cec0c3ff05d09980e6fb468cea8f02f2912f0730000618db016cbca0e28fa898cbe508bfdabab58de289bd08c3ae97acea8fc705c393da91aa8d04a4a79dc6df6b87acfd108ffb189f770b320005078f016b84adf2cfc4bdc89f09ddbeadaa91eea9bd2af9a9a4e1dc8aa126b5aac4cc9edf13b4c2c0b8eb01c5cbb4f101bdfa2f0005118b011301000507950163ecefc590d1f6b6c10feecdc4b3d8b0dcb301d8cfff80a48cedb303e4bab29093d8ef02cd80d89af4b9019ba5c8d5873c95a58b1b80d53700060595011f0100050597018b0262b4fcd5d0ee9bb2fb0fd1b1dbaeabea84c103b2b0b7f5c680f8f707d9cf89a5a3d3d903d4b29d9cf08704cd90ec94b31c999faf01fef301d9110a030189025e8da48791c38aa8a915f588b2e181cc85f101cc9491bd85bcf5eb0b92a2ac97b1def140bdb2ecf3fd8d64f69dc69ead37f7e5bd9d10c1b88925c71d0b017f00051e94015b9dbea891fbd4a19d1aa4d9c69298e49af727e39ab6a3bdb09301a2fef4d78ecbb706889af784e7f327c696a0db15eabfab01eea701a11f0a037f0251969a9bd3c1d788b31dae94b090cbc0968d07b0c899e4d7b6baf931dbb0c1f790abc3498d88c5effe836bd1f791a58d15c8ccfbd10182c3f1750005039001851d07010e0371024ea6b4bcd3faa181a71ca990a0eacfd083990b97e2f6b0c8a9a4e150bdddc587b283ab45bafb86a6abdb01a1c7c2a2d6ef58ebf7bdff0286d7f55cf31d0a032a48000618c901c1025fbbb3a1d0c6cedccd01a490ff83d8b2ded701868bf2edd7dfd502bab7bef7cc89419df681a91887e8c503c7d77f080301bf025abbd28b8bfff3bdcf089cd8f5afd1b985cd4885fcf18aa68c8701bea0ae9282c29b2cca83ccc7a743a5a39a8d05e8858701b9c501a1170b6d000608b20159bbd8a097f1e19de90aa0d2bbabdbfbbb8905df9d95edcebeed0696919adb9bc103849de5a7b901adeda19b01bbd14930000511c40156bbeadfbbc7aabeb70ebfa6ce93cd88cd8727bcdea18cc4a2a92392dce9eed1c348b1b7bca9c509eeede7bf4dcee36889170133000508ca0153bbfd9edf9cf3df851387d382fec88eaaef1ff4e1989ecdd0b50eb98ad9b380a11fc49dc3a520c1d1c7678917080301a70266dcb8cba19785a7d30187b6fdcfd6b9c69d24d3d4b5f1c2c92dd38685ec87189dbbd7b705c2c8e7069cdd5d00083c017701000502ae01a30262f8b9d2d9a4aa82ed05e8fbeea3afa88f9d408ef8d9b6fab7f503b1dcc7ec93a68109aae3da89850284ea8f2e00101788014f3b0b0300050397015f94bada91b1cede870ae486d3adbd8dfbc36d91aa9fa2d3aa97059786ceeec2dd05fc8ac8fdad01daf0b34ac53b172f000608c6015df390b1f9b685d1e50bc6a4f6b39b97a48901dee0defef9c9d2cb0ddee091d8c99ae503d2a5d6c9a9bb0285e2f6b7e714f98cb506b0a901d901cb3b000511ca016a84ffc2bec882a69f03d484b2ec8ba7e6eb0e849ef1f3e1a2e5138592ada4cfa105e09bc1e39f01fcbf8bb71a93811d81110533000508d40168c1d9e2d7b995cda5058a88cf8ddf8c97895bd4d0838bdfcdc304e495d7a5e99b1b90a09d9706adcb9302992c00080bfc01a11d0b010e030189026fd8de9e80bba495c50fabefd0c4dbafb513aa90dad29beb03cfbbe5a0eb0bbea3db06892d000510da011d1102000511d4011901000801c801a50259b598a0debadbaab91da2e1d1e0dcc6bf19f7bd819ac6d30d95e5b8cb910ae49b96e340bacd44d7018511010a0301a3025c8894eab1b7e2a4ed3f82958da2c2f5f70483c6a7edc7edb734d7d98aacc709b18cdcfd01a4a2fb5b000d13f2019501854f4d0500050b99019d0258c5e8819ce5dec48706c8cee0ab879bfb9d34caa6c5bebfbea15fc7f999a5c1a31df7ceea80cb03a7ebc7db04afc0cf059fcb4f3600050fe701060002001215ef01040402000511cd01d3025af0a7f19eca97b29b06b0e5fd8da6feed9b1ec9d1aca78dd2e70392fa898c9dcd19c5e8ad930fe0f0bf06ecbd2f000502b001c70a0301c70259fbb3da9dd0c1ce8107d3a8b7ac97dec5a91db9dfe994c0aab720dfcdc8f4badb0699acc6db8f01d8c1928550a3a517f3591d0a0301c5025891cbac9bdd9685cd0a8d92e0d28d9ae7ed25d4d797db958ed701bbc48fee95848b37e1a1e6c9d3049ca0c4a902a4fce71ca31d070a0301c102579cd7959ae3c0a1b30bd486f784e187b49f01eb94ddb09db2af01c2f994c2e99334b5c1e9d509c7bec9038cdb01d901d1770b010c0301bf0252d492a2968393acb10ef1dedc82b0a2beed038081a6f1caa4dfd30bf39dd8c0f6fbdb3191bcd4d6b5c525d6808be6b723cfd2e1810b8d8fcb01e4e1771101ef000609900151df9e8b9589bdc89711e9bac3f0b19ce99f01b4dcc4d3c4e3aab501b9a3deedc9aec104c69594e6b9ab7ba8bfbec31887faf50db235000a02df01b301000507cf016749120301b30263cec7c296fcf8b98302abc6ec8eb386ae870acbfdd69ec5fdf72cb3b4d4fdabb72ca0b985d6ab06e1e68ca1019b86a74ac54d110a0301ad026094abf0dbdd9dd9e906ecb982bd9c84f1e50a9cfa8785898dc518fd91aef2ec972eab8bf0a2ab0a828ec3c101b2bdf164831f017400050ea8015dedc48fdef2e19aad08c491ea94a1daa5a701a4c8e9b5f3c5dbc50eac9eedaacfcfe70897c9bb91a0df07e5f095dbbb07b2c6f324bd231d07013a000508fe015ab3a8bea3d386bb930d9f94cdcde49becf90197ff92a582b487d32acfc1acb9fead40f5c4bfe5d707b7cbcb9f15e9df12d32f0b34000509800169a088e8e3b7b4f68550959c80b79aed975daf97a2db82e107e7a0b2aded01ada9d5b531aab14fd701970b2b00060ec00167edd0e0cde2e192ff029aebf794dbfccfb1158bace08c83ed850fb3fd81afdfef07d3be8c8ec929c2e3d505b9b32e000b01b8019501857767591f0701140301950260f1b8b7e1bbbea3e109ec8586ace7f6cae9019bde8ddda2b5bebb04858bc1b2aea78502fda18ab1faed01b393918e8143c8d39922ade717f3174800050eb1016add80b598be9cd7b101ccfcebf2f699dea502b98a8891cdff1bedd9e2eb03d1c7b14ac52f1108030189026686db839b93a9b8bb06edddd296c8d19a873aba8bc0bceaf28d019ff2ed80b9dfdd0193b6e4a1cdf32a9f80a9a90eb6abd303acf560000c09f60101837767594d49110b160301830262f7ece1f2a1b1f9970ab996cedae2f6fba753b4d8a9d5afc5ab0593c1fea5a1f7b125a6eddfcdb703e6f5978905efd101d92f070a037f025883eaeda392cfdbd914c0828bb5e382e4a103e9f3f9cfb8bb8f8f14b9c9aff5ca9fff35afd9c0cee8dd23a2e9c885ed18d3c488e75da0f314a7130a03710254f4fccbfaa0d89cb518bbdebcf7eb85f2bf03d8c899c88cc6cf9312d7d1b0b1bce8e50da0e281d8dcb302ffe3f8a9d51babcbe90be9f51e915911010c036d0253adc5bba5e7dcbce31e9399908087c7c9dd07eeb4e2e4dcb4ef179bd7e9edd8a91bd786c9df0aa296ef2fbd4d11010a036b02270001cb0258a8b7e0fd9fc88aad0388b6d7c0d8d6adaf03968ff19c8fc8a30fdb8a8de7af03a6f6a0d50281ade903b8c502a900074001c701bb59010e0301c70257b6e9af8fa4b290d704acecb0fdf195cd870bb793b380e995ed04b1e2f99ff7eb06f09e89c9f904c0d1e8d11fa4953900074301c501000643016b0b100301c5025bc7dad9b6f3b79af901989a8ebaf2c4efdd05b2a3f6b299f8db03c6d5fce7d39501eea2acfaf105bea48b0bf8f735000701ef01c101000706bc011f0701120301c1025acea1b1afd9d9908702cfabfcb9d4a2ada102e9e7c7bb86cddb138483df83cb01f79ffdb108c18b01d901851f0b0a0301bf0255ef82e98bd982d9cd07e797c3de93ddab8701eaf1ac9ca1f0bf9d06e8c3fae3aa869f02aee6a79483bd018386f7b4d307e2bfdd08a39119f53b750005049601b50254f5c9c184bfa4cedb09ddf5dab6d392aebb01ada5abd78680d3dd029ebfa3c58d9aef1abd94b6bfa301dcfae3a50fc7a11f080301b30252899dc8eef28aae850ee49fc7fac4a089f146eacbf7cab6cbd501c095879086bb1db2f9928909d493b305a2ad66000802e1012f01000507e201ad024f9cf1d0d9a4f08daf13a7a7c2ff95f2b9851fb2d784d1ad90a50283a08f978ced9d0ec584d887c3019285c68507c4b33200063a0149130c0301a70261c089f085b0b0e4d90289c4a5e4f0d897f7128fb18491c1ffdf0afa83f9e28aa954c5a7b4bf16d4facd01cd8334000601e7011d1102000505aa015df4d88585fbc7aae706e2d980e1f7d3e4ff34d3baf284af91eb0188b8cee2be92d901c49dd38ae2811fc6ac8af90aa9b3d135c53b010a03019d025aa9a69a86c6ddf0f50b8dfd95d7dea1b9d90182e5fec4899eabb304a99dd198b49e9101edebfec2b6ef25a7b5b1a706dcb4a17be101a11773000505b401599095cbdc8abaddcf0de0ff84e8b5949df5089ce7c0ecf3e2ad0fccfdab98d9ad0987fac097dd04c891eccd0e879b20d73b110a0301950264d386b7b8c1c397bd04b090fcec998e86cb1ddaeb99ddf0c1a90e9298e1f69fcb6bbfe7dbdf0483aeab62000b01ee018b01853b17011003018b026399d7b099a7dc808f05f4a4f3cfe0a195a34ddff3fb858e96c330c089dbf2b9992ec1f18ba4f31daa968ff9019893ff3b8f3b1307010c030189026a82808ec2ddb2c0ef0189b2ecedffdcf4b101ffa4e3f8f5e5c562c2b38ce3cf14e7cbb0890a97adc30190a51d73000503cd01830266e3d394f5baa69bdb058fed9fe9a9f8f2df0fdbc9aa9ac594ad30a3c0b5dfa69909b3d5cdbfa503bdd38edd01bab4954da159010a037f025bb9b5eba6ffbb99d511bbeefacdf5ea9dad02aaabb38c8ff584bf01d4ad88c2dce48f31b9d9b3e6af05b9d086b134dee56b000b02990185771311070112037102589b88f1d9dcaef4c114c5b6d68c909ffbc90385acb8f1b893a2f52ec78cddd4d1d4830385ecbfc691a6ff05a3bbcff0f4a302acf6ebe2dd23b0cdd106ecbd01d96d010c0324500005048a0101ab023a82d9feb98bf1cae910f885ccd58587dbe702aacbf1a1f8a282d704a2dedc84a682f104f99fd3e797ff0881dcfaf58f6df9b6e159d28f5f9f01850a0301a70238d0e8d8f6c9d7efad16aefd9ff2ccb792952eb7d8f7b289838b01b3a2d5c9a18ddb01eccccca6e6eb4acba385af0e9aa8af0fc7a121d3591d070c0301a30236c5fee0d2e6b1a69315c5cbf0b1f4e7afab069ac7e1bbf8b7e8e11294f0fc8ec0edaf2ae3afa1d2c18d02cfeee99fe514a7cdb3098fb701b9000b01fa019d01000501fa011f131403019d02558398f4979fbdc2e33c8dbcabb5eceebd02a9ccabfce7accb01b4a796cf9ca114e493a8cb09d9e59d52df7f07010a0301970253f385f6f0e5b5f6b902be8eb6d2a7eff99713b7a1bca4d9aaaf05bfa889b2bc9b05d1b1be94a501aee8f98f10e88f6900080180015907010e030195024ea2a784b0c38ff8e70c91d2848d80929bd1019eecb2b1cf8ca58f6ac0e1fffab6c105b6bb96db972890cad11ffae515d51d0b0a03018b024d9294878a8988acbd0df2c9c9cfdd87eec901ceba80d9e8f7bffb03b0d8c2c8c8fbb507b7c5a3a6959d029ae2918d95019dd8aeb92ae98101d901d101cb01bb01a1018901857f77594d4914030189025d80e298d9ed8486d502d6d8afe7d68fd3fd0891c8afd488bed302fa97d4d69ba73d93a3e2a90bbea3db07c4b301d901d159110b0c03018302110001cb00050101040100160101000100
    (by decide) ⟨37, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock23 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨47,1,true⟩,⟨59,1,true⟩,⟨71,1,true⟩],91,3⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    19 1294 0x5069b01b5023afd8da09fa9a4c091119be3a2eda8d697bf3899f9ce8990a5870f89e6c285b8ab05fd8998b3fd0dc490bd0fc7a14d1f010a0301b302398087e6d686a5b68f1492a7aa87a7e0fa8d0285fbe48d8892dff506cc86a9f5fa83cb02bce9fcfbed9f03a6aff7a0ed19bbf7c108f3b117f31d72000502ab01ad02378382ad8ce3a6ac8d198de6fcfbf1d4cda501cadaccee83aa82c31186e9be828ce6b10ea6fbaa8cc98322d7cae8afeb03dfdba09f0295e7f902a4a94d0a0301a70251b6ae9dba95cbcad10292c0dd9bb58c9ba702a9d1d7ca9df285529bcce9dca106f8e694b133c3e5139d1107010a0301a30253eb85a3a48ef5cce5029ff0eef9b281ddf90df697dcf99fa6bf0cd986ea819e990aacf197d3ad08848dd0f10aedd901d117010a03019d0250d0f883e2aa88dfef07aaa297cee0f594ad68a9c5e2d9d3eaa7039480c5f9b0a4ff019990f6a3e0d901b280e0ffa3038ff3850fa52f23070101e7000503f7014fc89ea3f788b9e69d098faebce494d9ccbd7cd5dedcdbd7ee8901d29a9dd482f4c30497a884f5cd9f05c096cd9b9f0184aff2d925bfb701d94d0b010c030195025dcb97aa93a683d5c136e4d5d1bae8bccb1ccb9db3ce85890ee5efd8e5f101d0b0d3ff70d1ff67000b01c0018b01851d17011003018b025c9ee8f9d4b3a5d7fb02b08c94f4909d9ad1229edafad4c7a29724e197aceffcf509b0ffdfa6c525af9e891ba2d30508030189025899dde897db8bdfa90882abb88293f5b79b019f81a990c7cbf18f048c9beec199bb8d01dca6c194d6cd01b2d0fde8fb1ef6e5b302f1fd01d96711010c0301830255c1818799f5cfe49d0c9bc9a5ccec9dd7bb01c0a7e8c7dee28e9764e8ce82d4d9b301b8bbadade0cf7edc85928d05f287ed08cca101b5000c3a017f1110037f0266f7ca98edc2b5d3c502ab85e4c4e5bdc5c905e88581dfbadcd10cede6f4808103f6b5cceb07baa92e000701f601bb01a101854d170e03710263a597ff878bfb8ef106d5fd87c3a197b9d50184a79ab3f1a7d8a107b6e399a58eb7df04ffc6d7b3b9bf0bf2fae8b945b9fd01e58b40000501af0185010c031a05000602b50199023b86c889a3a182fca905d0cbf7c4e583f5c30c9ba989ec829e9913a08d9fbac89d0ec28484b58b03c8f4bc834def970185b901d901bb1f070c030197023aa2b9c784a390bfab0883ffd6aee197a5d105c3d987839490af77c0b285b6d92cbfbea3a108b585bd02e2a9776c0005028001950236adf0fbe9add48eb5139ae6bd8aa4ac94bf4c84a6b0838ba3a701c9eae5bff6f7e51188e9e59bfb2eaba8fd01d901d101cb01a11d070c03018b0235c9e2b9caafe1d1b71594c3f6bcc8d2d4ef7be9c4bac490facb04cdc8fadaa0c4c103b2c1d2b2dca776d3bfbeb712e390d303ed8f01d93b0a030189024dd5f4a1dfda9ffeed02dad790efbbf0908b07c1d8abd0c6feaf05a798a8c7e9e108a5efb49101b3cdfd69eb67130701a9000501cb010b01000901d4010b01c50101930238bc8bdccbf2c4dec10abee2a6faaf8a9edb3ed2bd81e89de8c104e2cfc8fdfcfa8b0698a0a2c1959777ff9e82e90dfcb6fd07ceb90b010a03018b0237d48bc7809b9feafb0cf1b5dff1c5ff969f56e7f0eb83d7c4c503d9a7b8efbaee9305f0fe8ec9fbb7018891b9c9bd04d6d3d101d3bf1f1107010c03018902359c8b869d95b190a91582beb9a8c7f49af125f2babfd5dfb18769bec29b89d4e310abdf868fcf10ae99dd0babc901d901d1170a03018302070001b800090b01040404040400090101000100
    (by decide) ⟨45, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock24 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨47,1,true⟩,⟨59,1,true⟩,⟨71,1,true⟩],75,3⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveFourteenBlock23 (.nil))
    27 3893 0x506b201c5025de988e5cf8784f1fd08c3ddf1fbc6bad09701cbc5c9a8b282a0a708d190dfe8c0f3990bc0f6c787a1d128cfa6c2ad08c3d4df01d2bb01d11d0b3c000612f4015ceccfd5a7e2bec5830ad2a2b6e79bbda6e370d5ced1d6fbb98d02a189e9fbbabbf703f689acd497e7019ecba19dcd25fba4cd058c8b36000a09f0011d170103000509f30157feb283e3abdee4a10fecd0c89de8efd79d02ae91b9879588bba50cc8bdb2e0f7c79b03a5f9e5a5f0e14282fe89b32ea3c111b9110136000509eb015781f8f3bc8798b7a712fcc9c2c7e6cfb7af57d9d2c68289a1d927b5b3da9398e913f190e2acdb08fbd5f7c30494ffe70185f733000676017f231f0701100301b3026a84e1df8584b0c2d301dfbaeffcc19bea8104cedcb792c5b28f03e0c5c48cb2d37bdaf8cbf719c2a9cd0efa9d1d814f073b000512d60166ae848b8ca18acad90682dacbf998c4b1c9498bb5a6fff3eded01b0b9c480c6ccbd0289ccd0f8e302bfe5a7a73e80b530000903a201a7010006169b014f1f1d01140301a70263f49afde6b49bfadd098ac8a2dae1eba2b7589291cbd48c94c305e7da8381cc82e5058beff6ba8dc101fea180c19d12bf89a508a081108b1f42000709cf01609dbda9edd0f682e30e8cbcacb9d1fc8be944db9b8f99fc9fff3882cf96ff94cb60e8a798eb8b12d0eae6cb05e8f901d901d17f34000509cb015cc6dfd5f4edd08ae911f1dac7bb948eb3c901c8e5b5c388aef5ab19a79cad8a88e315f397cdbed333a5969102b3b901d94f32000608dc0197026ec6edbaf39783858f01dee0defef9c9d2cb0befbeb8c2d5b0c55ea886f68d95d978c0a3dea1a311fbebbbcb44e8bb4fd74f1735000512bf0167919188c7afa085d10abda5a9f898d3abd955ef93c1c4ebf08b01e9edacfc82a5e552d6b1c1acb703b3ebd89928eac91afb1d1734000512b60171cdf5b1c1ba9cdfa10188878b83ed9684d97491eb91a8e0f303a0a3c6a3e1ed34cdd3c5f90994f79701d9a301892e000512b6016cd185de87bbb4db8b05e582dba48e80808501b081d8d7cba4a8850394bfa0c09d9bd958dacbffd7a90ce78ad2af03feacff32000c07eb0101837f774f4d473b14030183021b0e0008028301a9025f9faa88cb8e9aa4d949c69dd4ddbc8cc3019eee9887fba4c731f2faca8f01ecaf931e91018513080301a7025cfba987ced6d6fcdd0493dafdca8fdabc812f849aec89b9c1e10890e7bece94bf14aedaa89b9104c68ffeeb0885a35d00083f014d0b0103000514c60159c5a7c69483b280e30aa1dfccecc598fac314dec5d393ba83952cdae5e89799cf1aafd49ee3e7078fc681d75998fb2f000c14c4011d0b011003019d02568fa684d9b08d84e90fc1c885cef3ff95c568c0b698aec3a9c764ab879abcdee101ea9fe4dcd8b1599cafb7c5149ed2ff0483c34f1f11010c03080044001016ac01040402000511f501d9025ddbecaae0d4a7b3b908c2c483f1c1eca7cb74bbbae9a9ea81df02da93b2849edb8b0791d7d9cbcad706da8acbee8101d6a3c8b905f48501d901d33d000a058b01772f130701140301d30258b1cf8fb9e5fad9950ff5edd3f096abc8c126eac5fff4c697e10185a4f7a5beceed439092d381ef15d3fac3ad0382eba506c3e501d9130a0301c70257bff4f5c8d3c8ca8f0fe1b08bd1bae3ddd301c6f2dba4f094d393068fe7daf0b89ea321fffbfc82fd08e79aaaff03b4fd8303c3a101d959177f000608f70155dcc0c1e6aee4ac8312d8c08eacbaa990ab74a19deacbc1978702fb93e6c581d4c90df0ddbe96b905a8e0c7a764e0dd3a8559010a0301c10254eae6a7f59cb29cfd14d6a1c4f1c5a790df0a85e3cf9aa888e50a8de5ddd7afc90699a2bbc0ad59f49fa711dcc9670007039301bf0100060391011f0b100301bf0265aed984829483afb505aaf0bcebf3caa4970cb2dea088a1afeb6ca6a6c4c2b34bc99db8c702a7c9f31e911d0b0535000508f601649faa8aab938cc3b306e1bab29fb88bddc104939bf18cd898c3089cb4e3fba503cae187b909a5d7108b2f072c000608fd0160f19d9da690a7ffad0ad4dd9fb2def1b59b1af798d2d89588d573efeee490be8f0298fb9ac3b89758da92d2f137fbb2ed59a701d959173700060eca015dc390b0a18dc3bba70dae94d084ddae9ae101cc8da3d2d1f6cf8d01a5879bc3bcf1f131e1cee2bbcf0c88a6c2f101b4dcad44d501a7073700050ecd015ba4b2bcf38bd5e3a311d2aa839595cefbc305ebcbc1f8fae88904f4d5a7d5a2a30697c6f38ceb01fafbf6990bbfe321cd01a31d34000502ab01a3026ab7cf9da6f6c5dbd9039fbeb4bbaab9989502ace8a59b9490a502ca8eabd48f95369a95b0ed02c4dcc34fd701bb070132000508fb0166aefca6e49bcc82cb07d882a0a0e9a488a52df494dbf196fcbf01baa1d4a8a4ba9305a8a0c2b7c701c69fb6a706dcbf30000c0b9001110e030197026581b5ffa3a7f8e4f109ba92a5e1f1b9fbc919818c90d480fcfd5dab98bcdca8bb7b8ca891898d08adbf9b0bbfe311d51f1d13010c0301950269a8d98be9f997e1ad05ceb48ca291a5b0c3758da28ecbc6b9f903ee92d9cd88da9f04add6bdaa87a704ba93b181e512ccfb8f04acad75000502fb01070c03018b0267e6ddaafbe1abd6df0890f2d5add6d5b4e7179cab92cce2c9b11ba3eda681f0f704b6c18babf36ffe88dd0fd7b512d301891307013b00050ecc0163a0ea88b199e7b6f50cf0dbf7a8cad6da9756e393e0b9e9ceed03c7d98ad8c7e6bf06e4e2a4dfdddb4cbe8caf9d02f598d51ca31f073600050ec801609cf2c6d4ea8fa1d90ff0f1ad9bd5eed1af019b9bdd8387f199d56d81b4f19e97b528edb9c694e31590c19af104c8a2ed29830b050a037f0255cf90a0d1c39ad7b718d5dbbba6d6cfa48504c883d6b3d8d2f09915b4dcfd99f3e9f323b4b780d7e69108ccc28ed8c70facdc930480a11f070a03710252cb98def593c2c29b1defcfe0fc89e4a8a502ecc387d7f3b7a19718c9bde89889ef9b47b5b7b7e0d3e13ae2cabfb1c518dda4f2af01a5d98f01b8e501d901cb1f13010e036d0251899cfe86fbd6b7cd1da9bbc0d49cb2a9f304a982acb7dfa2a6a30182e2f9dba2eebef978c2faa99087c101a1ecc081b4cd6ab6cbefe12593eae50fb2e701d901d11d0c036b02290001d1025be8fdd890c5f0c6a106e7da979ddad0859b389dffe7cab8a2d12ade81cfd1a78b0e89fbeaccd720c9b29f02d1af01d901d12f02bc00053901c7025af2eea392a7cbb2f308a1dbbdb09aefcab9218acbe6e4f5a2d107beadceb9a0bb02f2d8b6ba8f58e9dedd0cfbdb01d93200073e01c5025986cfb995eb818c970a9ac7ebdecabfaef76c87eef6bff3f5b901b18b98d69cad9901f2cddaa490d949ffaefa8f2295d79708f3b1471339000507b301c1025890c08497ccdbf8e90c9d9ea9809b9795d50d9ac6a8cedeb8a514a7848192b8cf09ffcbded7851495958935c57711010a0301bf0253c1f2fba0b5a29883129af0d2d8efda9cab3b87dabf8f92c9d701c9c5eb89b8c8ad11e3b3d180d708b5bf98f101ec8f9b01d8f1771d0a0301b50252cbe3c6a296fd84d512818ff7a1b8829eed0184000903b20104a5ed92ffdff4990392cfc3abe309b3ac8d01dde701d91d010a0301b30264d2ea95dea4ea95d902f2ec92f1dde8bba105cb86cce5ca8faf1a84ba8f9c813e0005029f0104f88097038bbf01bb1f010a0301ad02619483abf5d3d2c1ab0780d28cb2ced498e33bc0a99f97d691bb3d96da8d8c85af0888cdeabce501c4dfe99f0b97d31ce977230b010c0301a7025eea9490859dc2deb70ab7e3cbefb6d8e6a107cdc1d1f9fddf9b0485faf9f8d2e501bbaa8afaa307e5fffd07b58901d901bb010a0301a3025babada69cccab8a890db0dfc0a6b79ad8db01cdb6b0f0c891c9db05af9fbff5dee3e508a2d4dfd3a0c102aec4f381a504cdc5e701f8ff01d901a10a03019d026aabe9c2b1b6e1cebf7f9ba6f3a6e5b2fd0994ae9a9bd6b1e112e9bd9fdba8ab11f1fe99c5c902c3afd7f74ad3cd70cd01851701f5000505e20168f7c4c2adb0f9e08d02e5f6948a97dfabbf03ac95dc9ac589fd38f4f9a5c3eb10c1f5f8af0ce9ab952fad1d17012e000505e5016db49bf794caf8afd90ad2d4c792c0cb8b20b3d68f82ab8f01b2b4d7c2c71af4dae1098c9901d901d177112b000505ec016beadbfed3ea8be98301f4d6e4ced183e88d0c9393f1dbf8a0e3049bcee6d9d2e92a8da1d4eb01a2b6cd70cd01a10803018902678e9c9591c7c6958106f6eb908be6facca565f8a7bcfbd5b9b905f4c695fb94b88907b6dcecdf95c739c4c38f832697deaf03b09768000842011d110e0301830263fb9ca49085ed87d50ac78695a787e2fc85018599ecbbdec1d2c502b3bd90b1fe8883028bb0b7ff8fbd24c1c989c705bbe4cd3a000b038701857f776b594d1f17070116037f0258f8dcd8cadff598fb15a5f5df908c9385fd03d4cfb88389eb8ce70dcce4f5999bf58d2190f5c8dd86d109a8b3a5a19703c2c8ad9f52e1eb14a74d0a03710255e5dce7c99e9c8bcf18dc9cf4cfd6e7c6cd03ddbbd7fdcf9d868938a495eabfb3c0e302ac9eb9c7cde4e92affe980a5ff0bb8d7ff9b01ddc6a15ed901850a0324018e000504a10101af023abadfeffbd1ebd4ad178bafc684ddd19f950193aaf4bd85e5d2d10187e5f0d5f1d0894db2faa681dd20a4efe6e314adf9c929f3231f07010c0301ad0238b79dd4b482e5daa716a4efdfdccec6a4df06b681e9d7b796b5fd17d8d4a2fccb9fb153b5c98ecfd7f709a7dec8f2b501ec9e8ce70288ed1f130a0301a70253c185c8cba6c9edf303a8a3bacdb2d9bbe1218bf3f8a7ad819101c6b5f7b2fee309d08bb7e3018180fd01a900094001a301a1170b0e0301a30255fdcfcd88c8838caf03bfd193a5aa9faebb1cf6e4fb939796cb17caeae2e2e68738fcc0c8c1049fcdd501a39137000501ef01cb01bb01a1019d01857f77591d1203019d0252d98397c9bad691cd09bda6e8b2b4e1f3ed13f69fa0f5f6b29707c0f3e797f7cd03b89585abbd26ebc5d334c3af2bd94200053601970251cce9db89e0f1e8d70ba9a48d9ffcf49deb23ecece6afabe5db2ad3b9ecc8a3ef01a8b58eb5dd0fa7a2e5018283110b050a030195025ffdd9c8f59286aec301caa2c6c7dfcb92d1029bf8eea492a7b10180c4ac8894b751eeb1b3fb18a991c101eea701d9018b0b0a03018b025eccf6d5d6f4a9a1f103d8ec89eedfe8b3c313b7efa58fcca59f7ae294de97a8ef019dfbf681feaf6fa89aa8a51dccc5f10efa9d01d901d101a10b0c030189025abacdfbfc9b91fbfb0a9feeacf8d1a1c8872fced4a5d9cf89d504a3e28ff08ee701ea83c7d1f743f4c4cb2c99a1149547010a03018302130001e800050101040100170101000100
    (by decide) ⟨37, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock25 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨47,1,true⟩,⟨59,1,true⟩],73,4⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveFourteenBlock22 (.cons fangFiveFourteenBlock20 (.nil)))
    21 383 0x6038c01018f022385aca3b0c6ae91ed06c4a08fa38af9b59d138eef91fb85c0b349f984ef81c3e701de99aad69709d9e59d05c0e331000877013b0c03018b0222c4e7bfb5b095c49f08ab8bdee0dfbec9ed0183f1d0dfafe0f3c713d8e8b1e682e503adcad8b6a362c2acaf05d3b501d901851d07010c030189022b8cece18abab5a0c306c0bbcfe5e09caac76ab3f291e8d8a88b16b1e1a5c1dadd01f380ccb1d53585baf706c6b96f000c01b00101833b0b100301830234b9f8ee9fd585a58b02a3f4c7c9dcdeebad07a4d5cdf486f48f07a192c2d2cae50793e2b792b913d1d2e903b1cb01d901d10b0a037f022ed5e9c2ece6f0c6a515a5f5df908c9385fd0283ddd0e8f3e3c0a3049bfbd5c3989ae7088abafad9eed33fdea1c5f71bdbb9dd07ddd167070a03710248fafffce8eed786ab01b380aba0c6bd9d870386e3d5edc5a3e94adafcf5afbf02febea1e756aef501d901d101cb01bb01a10185776d590110030c0001b800091c010713010a0e010501010401000e0101000100
    (by decide) ⟨36, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock26 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨47,1,true⟩],61,5⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveFourteenBlock17 (.cons fangFiveFourteenBlock19 (.cons fangFiveFourteenBlock18 (.nil))))
    33 3745 0x4040200050c9301e5023b84e09bd3c48e82b117a8ccdcd5d9a4ddb905d0b5ea9dc1d8a89b14e5c2c2f5a5a8f71beaaed0d89e9d03c9a8a5e8ef02a6cb84d749d8bd01e33c000c3d011d1701120301e30257f78fffc8e0d986f565d8db8398eeab9d02c1bb8ac491ed9b328ad38790d504d79fd485298db701df01d93300114a011d17160301df0258f7f580c4a1e0acbb01ca94fbf7bf898a8f02ef8ff1e6c085f104d49988c58cc105c4af89d58544b5b19d2dc48d01d901d339000b09ae01594f4d49472f1f0b01180301d30253f0beb6bf95c2cd8f07d085d6b4a4eee48d65e4b1e7bf86e9c10487a1bd868f98dd219dc7ecb7a3d106d199aeea9719dc94bf03c7d744000803c20113070e0301c7025384cad4e8fe92fd9d09c2a5f3bb8af5c3bd09fda1acf2f7f4a106b3d98dd8d5e701b7ebb4c5a323ea919d08c18b01d91f010a0301c50251ace391bccfb3ddb90bcfc582bfc299d6bf209eb6ac96b884d371e0f1d883dae702a7eea2b1b4cf3be39882d507919b8902bd8301d91d110577000509b90150c0efafe6b8848dc70cbe8ab6d2a488ecf14483b59da4ffb59360cffaccb8ccbd02a3f2bbb1b746d6caef02acc71d080301bf024ca5acc7b7c395fe8d12cbe59b8bb0d1dd8f11f0a6bfbef693990be68db7c485b302d9f987ad9704ef858b1f1d080301b5025f90e3b7fade97a9c918c089909bbed0d90dc79e90bae78103f0f3cc99f964a4fcbd0996a317f35917018f000610bb015bf8cef8cb809aead704a0cff1befbafede102f4e59d8af6d693078bcf87cbcab537b7dfd7dd09f59f9b02b2df2d00057c01bb130703000509e40158e0bab99ba29eabe50888e2b3dfc8f78fcf2594e8d2f8b2a7c551f59782aca9f35f98b89c9f85439385f3a10c9e95fd08efb901d901d14f38000609dd0156d0ace4a68ea0d7990ad3e7b1fdebecdfcd36cfd5cf80d9d9ab65acefc1e6b7bd01c6a49e8ba2e71bd4d2fbcb01f7b7d53100097401a30100050599011f130b0701140301a30253b898a4f6b0a498a70eb6f9cec8b8bc93cd5f96a4c48db69dbd0c90ca8edd84cb05e882cd97c317b8d4af02eeb701d13a000510bf016192c7faf799c4a29102aec0d7dcc6a3a18f15a7dae4bfa3e7039991f7dae736a2d8bd14858126000b04a70197018577470b10030197025fedeeeccb9ea3ffe303d8f082d0a2d4bc9d1fe38ce9c8d3cbb17f9ae0ecfeae89019382c1fe990db3c5910896bf1afb4f13053e000610c00163f982b0deb4ecb0d701a692a8c3dc8edab307dac6fd81d5d7ff01fb978cfdd0c937c6839bd502b5d9ed01d901bb110130000514cc0162c0f991d2f6b1dd8d0385838598b2ca81db078fa8e2fefde4e708f3ccb2e8afd30383aeacb0a758daa4b911dcc92e000a02f5012f130e030189025e98ddb4b0bb81e2af07f1d6d1f8dad986fd359284a884e380af37dfd98495c3851af0b5c4fe8f16fba8818312dfc321cd4739000609c9015ba8caf699be8cbb9b0bd683e6d7f9c0938f0def83ba9489c4e306d9cbbdc9dbf11cb5f6ebb3049fa7b5039bd510c511010a037f0251a08a9cc988f1f29513ba94bcf6ba8283f304aa9e9eb4ecb4cedb13e7898285f4bebb16f191b58b90f76299dff0f114d08af50699d36b000701c101a11f0b0e0371024eaff7deb28bfccb8112e281d0a59df4aee708a3a2f3daade4cdf12f8ff4e7a6b79dbb54fab7c58697ed15f8a8e3f18b039fbddf8f018d97ef02cbbb110a036d024cf7eebfa6cdc1f7b71be9ff8edcf8d18589019aefa284859facdf0e9fa398d5d3858f289ae7eeadbffb13df90939ecf15e5f3e8c77cefa74bed1f0183000609a6014a87dc818fd0ccd0a31ae4eae7f2cbb9d69d05e6d3a6b6f3b8928b04d0e2e69faeffdd04be8fa596bd01bbf99c9b11b9cd3100080aa501050aa70167594f4d2f1d1403670248cfd2e2849291fcd91aa2a0d4bdb4edfee707d5c3c994a889ecc935f9f0eb8bd7e7f95d90f8e6f1a6b50fcf81eeadcd078fcc9fed0182bbfd31af490a03650245dfc0a3ed959cd5c5199d8cadd387d6cffb0c9ccec8a1d2f2c6b52dbdbc91b2cb91ad03f8fad29de8d3c302f4e7b1eae1fd44f4a6abbf01cba0c132e15911010c03610233018f00060ea501c5023a8bc7fe88a7f7a8a508a69cc8eef3b5cef30e86c9c2c8b6bfbd06bb8f90f5f8df0db0cbc49fe503edaffdd702a492e926ff01a136000603db01c10239bec1a2c7f2bb86db08bc95d3deba98e08b01a7fc92b0f1ca92bf14b8afd4f8e5c11af8c4f999d902a2f4ba9d10dbb71e9101bf0b0a0301bf0236bd9fd985e78ddee90ff3d5c9d992fc87e75fc3889df1d0eca17bbbcea6acd9ad0284ba9b81dff91282d2aefb03e695eb0499997000050ded01b50235f098fdc5b1d1bd9f0fdd96b2fae8aa8991029e89b2dea394c6d508ea9dfecec8dadb08d5b980efcd8917c4ecdb97d765c3e6f101d8f101d901d149010c0301b302348984eb84919cd8c114c8b4bbbdef91e4c901bfea8ec391c0d0cf0bd0b7a4baf9b1dd19fbbefe8f9ca90fbcdfbecae703b4b1a6c501eb9cff16fd7f00050be90101ad024c9acbf1c8bfd7abb329ace68292ca80dd01f491c5ee878ac30396b5ddfbd8ab6fa8de84e31bafb3b90b918d18f96723130135000506f1014ab0f9cbcbae87eadf03bac0afebf2fdbe931fc19bcaa193d1a76094f8e5d7addf5aae9ff4918515f0fd91f121dbc717ab11050a0301a3024ccaf7b2e6e6d1dc8b03e2d48eba8b91dbbb06ea83e9e0f2dbdf08be9693cab7c90caaa7f4e7832ccbd2d30c98f911b913016a00050b880149d4a6999bf8dda2e108b8dbb2fa8ca986814fd8bda999bf99fb45baaae8f8a7f354dfa8f099f50f8ae2d89101c6b391108b32000707ad01970248d7b5e682fee18fd30ab187d7dbedc4ddd53687a898b0e6899901d19dd1e9b6d4f31890b3d8e5d303acd88b910186f9c3108b35000501a801950255bf8ff5c588cff9ef01e8eac6cb8097bec106dd81e497e7edd10ce4a3f1d596e308d9929b9ad1019b92a5db59803000060481018b1d0703000506f50154a1d5d6b0de92839503e5bafbafc48eab9d0ac2d58cf5cb9ad90786f4ffbecb8314d3b7fcc16befeb26ff4f13072e00050b800150c9a6f8f3ded89f870990c0a89799eea0c35fa6cfbeeac795a901ae9faea58a82e326f786e9de8b14dd9087c701a6dbb149130134000506fb014e8eb2bacb89dcb1d30dc185ebaae8d4a7b12febb5c881f190e30184aef5a3cb8eed32d5fda886cb03acf2ebf101f6eab90fa508037f025e84868a86f3a3b9ab039f84cfe5e0d58ae711ca9dc9dcfcfcbd0dd8dcaeb2bc970297f58cdfbf1eb795fb09f9c101850b010a0371025ad9ff88c8adbfd2bf089fba8cb58fe2f09d019588c1cffab1a33ae2cabfb1c511eebba7bf03a3f7bd73e30708036d025984fbc7e98acddf8909b3b480b6e9a2b8f901a4ceac9b89c0df8146d68c8792d6a710efa99fc7dd01c6f0dc910be9f501d901851307010c036b02230001bd0238cc86ea9697ecdca506e6e2b08f8dd5df9d6fa6c7cc84d19bc905c4add384cecda911d1d386fccfa5088bbfb2d39301c0dfa88d7489c715b101d947010c0301b50237fc818cadfe90a5c3089fc1c8b8c3f7fbf37b82d7cf9be5cfdd05bcc3e38bd1a2df03f4f7fcbed5a5428189d699098ec2a91a8902d3000507ed01b302368beff2f5b0fb819d0dcc9ce7bf85bafdc920bfffa9ccccc1af18f0e7b3e3b58f1097f6d8e3d56ed59dbd15bbdd30000801fb0101ad01a10185776b4f4d1d11140301ad02349bded9bce3e5dcf70f9f93d8f6db92c8b903929cbdb7e3a1a9fd08b2d0bb9baabcb1048aded7a49dfb04e3878e9eb701ab8aaed901bba89f428501cb230b0c0301a70232fbd39decb0acefb31490c8d680edb9c2cb01ad90c2bee5bac0d704d6c6a7facfe4bd02cbcdcee6e3dd24ebe7abff02de9ce901f4f501d91f13070c0301a3024ab6cfbcadbbc4e5bd6380ada5f7b2a8e50194a7e5eddcf48301ac92ea83c4b305dca4aca73680e12aaf130803019d024cc2b98a85b5abbabd01adf7f5f4bfb5cd890787f1aadddad3f70ca6ad828cc5ef1b8addd692ab6199edf50d999f01f3000601b40101bb2f110b0e030197024bc0dbf6b4e8abdda703a49aa0fcddca9ff106eeaff1b8a1d0a166b2dec4fe8501b5cc83f5db2490c4b305b58712d339000602a20101950246b88a94a1e7ad8bb90cd881ea9ae1a9c1d51fde8dbfa2ed9e9b019ae49fed99e1eb2ccf8b8ce789098487d1d903f680810480db01d92f13010c03018b0245b6ad80d19aadaea30ed986dcd0dcbc86ff15d685b5a0e290ed1bb2c7e7b6d5830482f2fcb9f1338d88fb11b1c301d901d101cb1d070c0301890253d9e98a83b5d0be8b03a2aef58bd3afbcf105eabeeea8f1b9b102d0a9bfc1f18306def885d5018481fd01888f01d901a11301ae00050489015192d79ba7bbe7b7a707b09f99e0d6f290d527b58dcfa6daa0a519bfda9be68bb504d89a91da9d54ade7eb38fbc51e912f130a037f0257b3a7febeb3b6819507d3c4b1b59f85f4a710e2f1fec7bbc98f53c3ffe3e5d3d302879597c0a98948b894a9e308b7d4ad6987131107010c0371025e9ceef085c9ae9de302dc8dd0e8bcc9d9df07ce9beba796fc8919fcdadac2f4f30cf49da0dcd904a3d593a304df9501d977170b010c031c01a9000502e10101a10226c8fecde687d3d1b108caea82efb2a0d4a9028580a7b0a4b79ca901bfa2badbb5e9e70286b3c9d4fca902fcfcb2a1d945efc3d1329cb1209b110a03019d02258ca89ee69e9897d310adfd89cdd7a090e53e95ac91f49bd38b02c3d3a69feaeec7018d84a7a4978b0494f0f6b318adf343ef1d070a0301970237a5fda9f69bf3c4b11fd4d2aad2aab4dd1ee9ce94c7ecd529f7f781d88d0ec6e9dcf50591d891771d080301950233caf99b8ad181a0ef0bccefe3979bb3dd9123dcdde4c2ae9daf63c4b5be9fe8db36b9c3a1a08b0592e2a6df02aa9ab9428177110a03018b0232ebf8b1dbc28480950ce3d7e0d883cbcee101b696c0d5b787e7f501b4a284bde8bebf3ce891aebfdb05f6bea69f02fa85a7528b110b0a0301890230cef5f5ce958c9e871399e5b7879acf86bf01f2a8d2f9bff5e1ff0ce0baa1abe4c1e50c84a1f7ccd2e704ec9efd89e91389d0915cf31d0b0a030183020d02dc00051b010f01010a0e01040402000a0a0104040200090101000100
    (by decide) ⟨30, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock27 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨47,1,true⟩,⟨53,1,true⟩,⟨79,1,true⟩],91,3⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    19 1267 0x505f001b50259aff9d5aac1f9e6973ec4c4cdeda7e18f5b8dc4f9d2e2ed0386988ffe9961f7fab30685ab1be12f2a000509c301b30256b0bec3baa0a3bdc905b79e93e8f5e9e9d31ca3c1fcc691e2af14debfd893a3a314b1d4f29bd304dffbc9db68ddf76b110b0a0301ad0259918cb9b4cdfa9ae904fffbffa193fc9ae107f99e93e4adffc50f9588c2a4a7ad01f5a4a0ae9f049fe9a506a7f301d92f130a0301a70256ffe9d4b2cac6ffad07f4acc1eda9d7f4a75dca83f7e8fb9bfb039188fb93aab903d2a995b3d709cfc39f0188a101d977170a0301a30253e5f5bcefc5ba96930cffb0aafdb9a8c1857f81bfb8addc86b702b5c0eac1dde2d902a8a5c8c6caef0f96b1e5ab0582f29d0285e71d170a03019d0250cc81a5acc0adacf911c9adc1f1d2aebaf101e4c5d3ade2dcaaf901e5a7f6e0d5a5bb018fd1c8e8aec501fa9c8fa30e9bb301d901d17713010c0301970264a2eebda8f5faa4c934e3f59ca8d689a731b0e5a0c0ad852f9aa1deb4bb17a2d6e1fb02dca98102c8000e03e101351d0110030195025dc5bba0a5a8ba9ed70accccda85becbfad313acfd98c8fdefd71db297cd82a5db0bdbd1b591e902d8ca99ad26eea527a513073b000505b9015c9997b48affadb78d0babbddfb1f9e1a7d101baa5adb9dbdac09b02fc9a928df9cce904fac6f8d286b32f90d4bedf289ea8f507a28d01d9770b010c030189026adbff9b92e39cd88337cba089e0bf8bad03acb8e7bd8bdeb343bfe190c0990cf9b1d3ff0bd39301d94d116b000605be0167baf2c4aad0c7e3ff0583c290b591fef3eb11848dd8bad49cd91195a2fbb68aa701819394a3b309cfc39f04dde32e000701f401851d07010e037f0266f1a580a7a7cfb1b309ad9ad1bde0d8d5f901b48e99ecfcb68f990398ec98dcafa6c904838786b987dd01d2df8af78569ef9df907d4f501d901d113070c037102639f8fa6e7ceffc6a70fe2a0aba081e4b5850d8a93faadaebde903b2d5d5c1c2ed04f7ede2e2f901c8fbeadb19f5dd10974f010a031a7f000602d00199023b82fa939ddeed9baf12afc5b19bf3feb287518b9c9783fff8f307afa7ed87b7f56d90aa8ec906df899101a89701d901bb130a030197023a9ef1e08ef7f080dd14cab7cca7f6b295b74bedcbf4c1d6d4993ace9fd484cdb11ac4f1b1fc8103f58ca3fb21c69d68000b01bc019501857f774f130701140301950252b081b7c3a98db79303ea86cbd98d859db715c3fea8d19a938103f0fed59ad5fd36dcf1929303e0d33700097a01851307010e03018b0256e58194d3a3f8b38b7be1fbeda186d3bd6be9d3c0cddee948fa99d6a9a71aa4df8f9f05999ac9669901d94d0b0a0301890252febdebc98bf8ddd907c5d789e3de96ceab01aff6f7ebbff8c8f303bcbe80de8e92830688a79481c1f372a4a0819337faa7ef09dfc971000601a00101bb01a1018501837f1d0112030183020b11000901d3010b01c40101930238b8d1ffd0a582edd716a5b6fcd08ecfd38f01a782fbd2e9bfd4890f97c5b689cbcdbb0199e3a7e59aed0bb7fb84bd018386f519f507010a03018b0237d0d897c9cdf6ec8d18b7e3dfa58f8bc3e901cbd989e585fbffe90ab59dd2cc83ffa10ea4b5a48aa4c57fb9db85e560d0e4e916c4e901d901d101cb1f11010e03018902569b80eec0dfd5d3d5229580dec28a96875de79482bf91d332ccbba6968927bb8cff9105a5a6af0181fd350b010a03018302070001b700090b01040404040400090101000100
    (by decide) ⟨45, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock28 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨47,1,true⟩,⟨53,1,true⟩],81,4⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    21 638 0x404020005049c01a1023a9fedcadbf98b9a8f0d8cd6bffafa94a3f11cfeacf2fe84c5c92ebeeaa4ecda8111ebafdb9c8705e9c0eef301c083ff019c34000502e30159070c03019d023882f5d08281c0caed11b8818195e8ddecf50281bcd2c8d0b7b59f0194c8bef782a5eb05bceefc95bb029be6dda131fdb90fff2f1f13010c0301970237a3f8a78ed9d2b0b713c4c2c9bef89c938501f3ffde84f5ece2e307ca97e8d193e5a50ad6af8896f7b902dcb5c580c314f5aeab01e49307010a030195024e9884c397c0fbc39904f5a7bed29ce085c31791cae5d3a39de737a7d2c2fbf0a14fe0f4b8e0bb4ddeaadcaf0e8aabe902dfd301d935170b0c03018b0252b0a889f8dd8f9d81029aefd5d1eeaf978525a193e7ac969d11d98ffb828f01c0d496c106be9b01d97708030189024ee2c2ad81ba9adaab0983da899abce79e8b58939785e6c4f68362bfecfca98ce101eea4c1f6e6ef3ed5f8e3dd1ddee18301828301cb130a030183024caed3ef87a2f7d8c70de0d3bdac9ef892ab77d3fbbc95fe9ccb059cb893b1a5c8f30bae8084a99ff909bfbaa4c1972586e7b70191a901d901d101a11f07010e037f0255d5f9e9f6a9c1fba30c9ec8a1b5bce4ed85029ab883ddd1bdcec90b99e089d59499f104c8fbe1fbf9a10ec0ffb9e903c691e902a8c959170a0371026484d6d0e8fac2ea8b02d59bfdbe9c8581c90d9ec7ff86aff7c916b880b4fcee9905c787a4928537c595fd08c8e501a117010a031203dd00054e0101870239d7fab0c5a0a5eacd07a7b7c39bdfeedb912c9ff1e283b4a78156b4d7fa82859b019986ebf9e89739ac9efbff1fa2dfe304918f01d93511010c030183020342000811010713010a0e010501010401000b0101000100
    (by decide) ⟨40, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock29 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨47,1,true⟩,⟨53,1,true⟩,⟨73,1,true⟩],91,3⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    20 1759 0x507ca01c3025f97f8e884f1c2c1e90af4ca86eeed91df895bcdf3a7bfb4bc9557fd8dc2abdcad08b6c4dad89303c0d18fc701c6c9e93200067f01170b0c0301c1025e99d7dd81c2cab9970ccbb2d3e6ebb3ea9331cdc99090e3ed8301eef299ff9592d705e597d0a8efbf029c9baeea9169d0c6f90addb9189f4d0a0301bf0259a2b2a5f0d7f28dfd13bbbc86aaedd0d9d5289c8698cefde9a701b4e8968ffbe5d953d1bbd7d2e12187e8c28107bce3d702f49f79000909910185070e0301b50258a4919aeda8fa85ab139ff89a88b88b9b9301f0b6eae4af95d4c502e2b6d6bbf9b0db0183f09d81c9c33291f781188be301d96b010a0301b3026bcab4afe6ebe9fca702e2d5d0e4a1b9e2d5198a8a8aa88186fd3abd98b2c2a0cd55bd8ebbe79b239d93dcd90c93dc832ad34d11750005039401ad0267ece9a7bea482b4d507beb5aafcbbc9cd9d29d5e685b4d6d6eb0185ea99a4b285e33df9a7e2e4d728b191c39f1284f0c107b33500070396011f07010e0301a70265aeb7a1f8c9bdafc90adf95e4aaeeb6a4a727d883c3a2ddd0d11da1cad586d3990d91c3bdabdb01888d989739d68f30eb1d073b000504d00161d0ec99d081d5e7f70ea6dfdff0e8ccfda501c5a380bf82f6bb8107fea3b3eafec2ad5decd5c5f98d5099c2d8bd38c5bce701aedb350b37000504c80171d5d0c48e89b4cfc17be6a1a0b296fceb02dfa9fda598efbf03afc5d3f7bcb72ccca9949f02ec8daf6381231d112e000507bc017094f5ce9d92ce99f302ec98ede8e89aa08d02edb5bbcbbfb5b701b98195d3c7cb3fadf6af8f25feaa8505b58701d92f010a0301950268d1af80e8c0ce8ded0ad0e9b2de9092f1d501cd878ed4a9818bef03d0dc8fdb8cd7e527b9cd97cbaf13e7f68c9f028adcbd209b4d116c000504d20173a1d6b9b2e98abcfd01f988eabc9bfadb8307eeaec1aa9092f106dac1eec1eac504ea869caaed148bb3c30bf7bd15b101851d070135000507d8016e9bc3dba98fbaccff07b3f7f3b5adc7dddb61b9e4b1dfcce0fb0189bc92a297c7ed0184e1d2b1a8bd01859f879e9f0bf2aeaf04918f36000642014d0b010e030183026aece1f1f7feb082ab0ba490d99383e6edfb7fe8fed68794e4c169d9b7ff90a1d302a98befaab5f92d99b0d9af0382e49b0383f93c0006048001070c037f025f898bc18c82cafd851691f2f38da8f794ad04adcec086b5a08997168af89c90ddc2f301a9ed9aaf92dcef65b4ebf3cbff05bbe89ad907d4f501851f11010c0371025bdaa9d7daf1c0b2b11db58fe4cb8581aadd01b0909bd1e6cbb5a53eb0b596889f318bb8c7e302def8e302acc701d901a11d0a03207c000603a801a50259a1bdaebdebca988d03bba5a6fc93b2a68d14de98f8b98e89ab0ed9b094a884a73ab78dc4a136e9acb313bb352f000505d401a3025bf3ef9bf08ee2f1d103debcdbb7c5dbe7c5079ee4f2bada9ca103fed4c9c28c910feaa2a9ad7cb9b35fe101d9491331000502f00158b2a5d5c1b7e4e8b30884c99f85f9b7daf90288b2cc9499aaff9f02ab94b0a2a789bb0197ff91cbd7b354bf989afb0fe6ba9512c0ad01d901d113070c03019702579cb7e8dcc5bae5a90c8d90f7a186c9d8950feae8f9b6cf86fb19fcb1abd792a303fff7a9a3ad02aaf1ae85218ced01d901d14d110b0c0301950266cc91ecbbb3aaf7bd01c4c1c7b4cdbbf7fb78ad86b092868b328fbeea84c71bf087d3990182a3c53789350b010a03018b02658f9884d881e5a08f03f9b5fbb3bbb2f2bd7dd992989ecadd15c8c0fedd8506c984ee8f04cab4eb03c7d707080301890260d8aacdaded949a850afa9fa7d4d2ade5f91eda8cabdd9f99a526cf95f9c7c8e93184b8f38f8f059ea684f11798bf028e000b01c7018501837f77670112030183020f00040410000702f9010d02f601019f0259a8a4b98eea948c870ea7ba9cd8f19099209fc289e8f9fb27dbc3ccc2e301e1f58a9d7ae69d1ce94d17010a03019d025be9d7ccb3e996db876fb6dce9a2a780c90495f385ff9dc38d0b9ac69bd1dfd905ded4ff9d9b03df9089fd09a3f910c505010a030197025ace80e987f3d3b8e502faab9cab82cfbbb921cbcbcafae1bae523bdfa91a693d903d3c2aec4f3388ee4e511b1c301d901d101cb01bb01a1019501857f776b351d01140301950254c3cef8aca8838dbb0d8df4a4baf2add49d01d7ad92d2f7dfdddf01c4bc86a9d4d6a354f0a2c58ef51cc1b0cba9099ff1f55cf301a11d0b010c03018b0253a7f89580b2bfeb990f80eadb9ea490a2b50286dfdcecb7cfaa9d07d890a0f98edc8b06b3b08e8dfea905eed7e9f1b702ddcce2f53bdfa94ac54d1d0b0c0301890264b8fbe5bec5f3b7d1039edeeabff9ffcc8f0689afaa9de3f89d19a387c2a4bd02cce5c08b4ba19301d97711010a030183020d02e4000e0d01040404040400090101000100
    (by decide) ⟨45, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock30 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨47,1,true⟩,⟨53,1,true⟩,⟨73,1,false⟩],75,3⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveFourteenBlock29 (.nil))
    23 1231 0x708d601b702789bd0aeba99dbc7990492cde78f9fe4a1ad43b6b89ef7a7cebf02bb8ba5918d8a8b06bbf5908ef49903b6cbc9e0a147ed91f703e0d34f1f3a000501b601b50276f1ccd2dbc0a9dfef06a0f6c7dcb2c5c8b508d9e792a5f592e70fe6adfc8291830f83df87858506bee1d49102aeb8f91d0b0135000503b40172f3c1bfbfb494a9f10ab985fa91b3a4e0f362dad284dca2bfed01cda8dbbae78ea101de99f6c4fe8911ae819bfd339f954bed492313010c0301ad026ef5b6aca3a7fef3f30fec9a86a9ceedc7b522ee96debac286f301f188e5f59aa68305d48f8dd49b830891e7e0a9d903f5ab9d9752c5d14e9d01a7070179000503a8016ca1aef4e5f59ba59f12dcb1bfc0e49393f556b2ecb785a7e5e14fabb3ece0bc9f1fb4f094b7cf75a8e9a7078bfb01d9351332000503af017e9d9de8d2d080af8d02a6aab291bae2b78d06d595cbf0d6b8df09d587f5c3b4eb01e994a8f0a51a91ee9f02d48901d901d17707010c03019d0279b3e194dfe2fad2e7079dc8b2cbc2f19e9b6bf089a1dda4b8b502d0eef1c8e3f98963af8fdae7bd0db083a7fb02a6819b56c501971f0a030e00040476000c06a9010505a101bf025bc6e28589d5ff9ff714f3f893a6befce7856386c4d881e7c2cd7edcacc88fdcc35d94cdb3d7c721e6f0e5a102c1eee701d977070a0301b5025ac5a3b79daeedca811688a3c39ee8ffe88b7ae5dbfbe396a0ad05af8bc3bdd7838f0aa1909c86e3b902efcbb29cfd4bc387d307cbad59070a0301b3026eaae19f96bda5f6f504ad94a6e383c285e50381e1fbd1d3f7812ba7bddfacf91198c6c8c70589d0976ff92f07010a0301ad026ac0f9fea3e0f3e3ff07d6f8ac81e3a39dd701cf9f85a6ef83f08175e0d9a1d4a4b5028fbaa28e8eaf7fbef6bfa539feb69107f99f16971d170b0c0301a70267fab59381f8d2acdb0be3cfe5e3eca083e7648696a3cfe9c2df03fba698a3ddd7e90eb8afe092f1a511a9d8bcb6eb068af9d89d01889d59110a0301a3026490cdf28f9ca099e511a8b3fbd6aea2b8b71a8a9eaef580cfb51ab9f7dbb88f9102c9000602fb01018cf2b6c90399c508000a3d01772302000502fc0174c9f5c0d1d4859cc3028c9d8efbe3addfd90aa4e8a8fbcf88df61b995c19cf135ccc5b5830b92e6fb048af12c000b01b4019701857f77070112030197027384a3b5ce848bf7d903fbddf4cddceaabed0f9cccf78fe5d7c3208cb79bd8f6b105abd0db94a9198dcf8306cfcb3a000701fd01170c0301950277f88a85e8cdaba8f57fbfc6d2cca6f8bb0391ab98a3cf94a13ceaebfbf8f70af5f5cabf05a8a89f3385170b010a03018b02769b97dbafecbaacf70381d3c0f1eeffe1a50ccaa49ee49de5f92badb9e4dee6c335ddb6fa9e9d029cdcf78d02b2afa1680006018e0101bb01a101890185770110030189027184c0dc85c9e7b8fd0998eecda784e3d5bd19aadaeba696d7e118e1829aab998f0bebe690caf1068780b4f92ff7ff31a30185231f010c0301830217004c000501010401a3025d95dfa7e795c7ebe50da7d6e18edec18fb31ccdefc5f5b7a2f915a1cfb0ecb7f906a5f6a0cae702c0d4eaeb01fab0ed01a39101d901d101cb3511010e03019d0259cdfdf4c6d8b3fcef13c4fcd48fb4fafcb70589abc3e5f198b3038daaa6ebd7d949ba9090c105ff91d30480db110b050a03040004047b00120101000100
    (by decide) ⟨37, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock31 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨47,1,true⟩,⟨53,1,true⟩,⟨71,1,true⟩],85,3⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    22 2988 0x1c3025ef9ad938ddb8cfbf51791def3b98fdfd58736b2ffaff4c9b9ef3fc1c3feb2bcd708bbc4a2efe501aa9da48d26bbcf3200073901c101bb01a15906000503e801c10276bcffcbbac297d39924c7ade2b2fda0b32794c190f5abb1078eafb1b8d153b4e7ed4ff1fb2700074f01bf01000503ac01857f02000606b0011f1d171311011a0301bf0270a382a5aa86b6ca9307c9a798d585a88be114cfe881e7cd8def22b9e0f2e5bfab0dd3bfc1debf0393c9f0af59e6e53a00094301b501a1070e0301b5026f849cb7a6e0effbc50880daa9daa2a2c78d0197b3da95f7c5f3fd04e0bfbbdc8a8eab37d8a3c7eb9902fcb5d09907f99f3a0009029c01b34d070e0301b3026ba7eaed9cf09c8fdb0d99b7caada790bbb73fa69f96c68fbbd311a9e7e4babbbb45dbd4a4dd0feea0e102d9c90185370005089a01ad0267cbb9a392ffc8a3f111f4feadc4dda3ccbb1f97e6b588efe7bd5988c28bf0ebbb109fe987b4ab09b6a8bb05a2c31d0b0533000508e101658dedc78cb4bb86d513c5aefed7afe4d8b501cca69886cdfb919344be88d8a5a5d13dc4eda0c1cf21dcd1c2b109b6ecf108fbaf771d36000508e10175f1e3c6bfd8e8dd8f04c5c6e9a2f4aecef146a0beab8a81b6ed028ba7e98fa6c3fb12b192eddfff1299c9d3b701cebd994ac501d11136000508e00171b18ccb9286abd3ed0aa7afd8a4c6b2c1e706e79cc4dcd5e9d701b787ee9991ff17b3c8b5b703f3e329000c08ed01471f070110030197026ff0efccd895c1fbb70baf87f5a7e1aaa5ef5d93b7fcf29feccd0286f7b5a8b8b5c902cab5bde5d08728b694addf02c8efc503b1cb01d9170b0143000508f10174d3bccfa6cedcfddb07eba6bcfdc4c3fca75cdefe8de0d883fb02ffc7c4978de5af42d786fb8ad90ea5f8ded945b9fd7d9b018b11350005119e0172fcd0f6d6eedfa9f90ab9f08ae4feb79b8b07e4d3a99ae7c8830bf9dfdaa7f5a30b8be6c0cdaf2cc3c9c307f99f12d317013200050ea7016df88dece7cee6aed30fdaa6c6b3afea86d547d896ebc5f3f8ab03f1dbbf9de6da9102828ed9c2f4b35cebed82df04aadb832bd90b0536000508fa011b00040404000501e201a7025e8aa4d1c6c7d7b8d510f98de0c9f6d3aa8160bfdfb488809eeb01a296be96f397f148878fd4f2b903deeccdcd11eefd320008460135110b0e0301a3025acf81c2e2cba9e8eb168ad398f09d8ebf99018cf5c186dca5918502f1fef3c0e387af03a0f8c2c3abc51ddf86a5910491db9304c2c53e000b05ec019d0195018577594d47352f13011803019d026df1f784aae3c98eeb05e4a7f9bef183ecc916c9f9d1d1a8b1c50180f4bafda8a48d1dc0d3a0ebf30292dbe2f301b1ffa7038bbf0185070a03060004044f00100cd101c9025fbac4c0fd85b2a8911198edaadaf2d4cbcd5bef98c69df0829d01b1ca89db8acdfd15ebfbc0e8b105f5ec9a9301d19ecd01a3ad77110a0301c7025ebfde98b8f285b6c31182de8ae1d9dae8b7028bfcc1d5a0f880c303909b8fca80c2e30192e2b5c7ef937bd6b2d0b90d86d88f42817200053b01c5025cca91c7b0cbabd3a71497eed3f2c4b2f3af01afcd8eb3a3dbd8cf01eae3eeb0dbd4e76590ae91e69f1090cac693049aff9d01d9360005089101c1025bcfab9eecb7fee1d916a9f68cf2d0aadcd33ad5b0d7f7f1eeb138feadf592dde546f0cea6f3f953b9fc91f31591a9fd0499994d1d0a0301bf026dbcbccea8fed8a9b105e1bfe996af8bb1ab3b84e9f881d4b19d03edf9e98fdfbf4b8d98b79907bce3d708c8e501d9771d0a0301b5026ca1d1eed8d083f39707c8e2dacde491b2890fc2a88edc8eaba305c9e8a3f4ffb304a2e0c5b5bd04a08cf370cd01d111010a0301b30268d191cfe7c486d0c90bedb9be8181b3e9cd1cd0e49895e1cab901c386e5edbfd4a503d3d4d6fe87b701cfdcf5acb35efd91c53ef9ab01de000601f2011f07010e0301ad026580d1b0f6b889adfb0eb6f9abc7e3b898ed0286b9f4f3eaa8d1a101c3eee0849bf7fb1cc4b8c891b15c93f2ad358ee711d54d133c000505b60162cafbf1d5dae0c1c71386faf3c6acb79ce72eb78b9db7bac3e30188ad81ef879683019ddb85a4d08348bff1c59d03da83bd49971d1136000505b30172f9a6c2c3f3c8fd8503dfc0f6c48a918ba90ba4d4a5ecd6999f11aeb2b6ddbda10ec081aea6e70a94b8c2ad02dfdfb7028ad5350735000505b4016ec78196b4a1d9e0cf08a6dcd69691dadce157f2bef995d6b5ef01b1ccd193ec98c901dfd582d2c6ab018bedf0ebf12f9eda9b09a3f936000b06ad01970185776b674d47352f170118030197026d8bca87d9dbdfacbd0a9af7e69ebbd4cbb54181accdbdcbabf737ecc59fabbadb01ae9e82ffd555e1ffdf2c99a13f000705e301a10b0c0301950271def990e2dfcdcac90687ef97aecbdbcde701a1efccd9eafb95e103f6d6e296d3acf701a8a18ea7b8fd029c96d2abe102afb082cb01d9a2e715b13543000537018b02708dbbc48ccdd3ead3098f979bcb90dd969310d286d89893ebc122befca9cc98f124b8d3ff9b15efa5a301d901d1471332000508e20189026b9982de8a97e6caf10df4cbcbdc98caefab01809df7a7c998f19302bfd48fdfdc99d301bef7d2ce84c1078594c1eb56dadf5fe10737000605a90167f687c4ddf3f38b851193be91c7b5f6b4e301c7cbbbe3cadc9c89018adc86eadfc7c1258ce7cde5b307c1998a8b018794e301d901d11f11010c037f025cbbd8ac82f69eebcb1dd4ad9f83ad95fbef029a99a1f3c0b2d2a30e91df97f5dcf1bd2f8aa394aba2f309c8d7d19aef01b5abc5d318c9d115b14d13010c0371025998dd92d6d2ababdf20a1ba99e8efbdfce103bc90c1baddb5c3f304a3e1facec688b702ebeeac96f9b703a3a2c7c2ed15efa5a3059bf501a1170b010c032401bd000603ff01a9025f8aaad9ded9f4b7ad03ef80ebb585a2f2d10cf0dae2888e9e9107c28486f7b5c705bbd8b4baf702dfaeb0bf1ae08501d90185170a0301a7025ce6ea87f0aeaefb8107a0c4a9a9f3e0bdaf47d4f5afaa9bfcfb4aaeb39c88bd9f269ff9fbfec51a9792bb810ae5dd15d31d010a0301a30259b1c98d8aed86e0bf0ce2c1a6b8b493a08967f5a8ecc4ca82fb01cce4e8c9e7b4fd5891d3e0ffe10af2da8f9551e2a10185df01d91301a90005038a0155fca892a5abdec5fd12dfb7f4cbc1add1d54e99a89fb8ca94b901d2e5dcde9194e522c091d9eec305da81c1dd04a08cf302bcc1170b0a0301970254eac7e9ae95fbe7e714d69a8dec87c0cbed4d94dee7f6c7bddb02a5ccacccdf8bfd059dd0bac5e3ef01b2e4a4a89b1deed9c30383f901d9070a0301950263e4adb4f1f186d89309898fe1f38aa3c29901968e80f9b6a7b1d103fbecfabaf288dd03ee8292e3b8dd538391e0876af7edaf4ce9c901af000b02c8018b351f07011203018b0262acca9d8ddb95a9e10c8ca9fe8da9aaa9b531f98ca9dc9681ab01b1ceb1b6918a9b0186fab39689ab3db9aefbf714a4fca30698e101d97f0a030189025e85a0d5e199c19ecb1296c3d084e6e884eb7de4dbecf9efa5c5568ce7f8b884ff0ceeecdde0d902b5ac94f708c18b3513010a03018302110004040182000702fc010d02f90101a3025cedf3dad28defb3e30484e3d1eda7c7d0952edb98f196f7d08d17ffb8cd9c9da90792b18ab7f37ea69ef550fb9d15b16b0b0a03019d0259a7d5999bcddfdde90a9eacd6af9789fb8942b69689bc93fc9b028bd3b9c181988b01ddef91b1c1ad3ceef7a9f30ae1d2c1048af101d92f110b0c030197025890a0ae89b8afebeb0ccbbbbdb89aabb3fd26dbf1d6b3a9b99f36b2f0abe5d18520c5878cf19b6abfdbf916d3d701a700053e01cb01bb01a1019501857f776b07120301950267d4af96d1838eb3e70283a3eaaee9b8b2e904e88be2a5b08cc301d287899cff1b89e6eb04f98d01d901d101bb070a03018b026695babc8883fec5bd04badf8bcdeaa8a0d504caaec1c38fa78111accfd09b8704e786a8a102c0edcf01d6891f080301890261d8dcacad86cefabf0b88e5a1b39192b3db56dac6e2dbbba8e505b9f0dbf1bffbc708ea96d3fbc5e103ceffd7fadb01d4ddbc8301828d8715b101a107010c030183020d01bb000e0d010404040404000b0101000100
    (by decide) ⟨42, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock32 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨47,1,true⟩,⟨53,1,true⟩],67,4⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveFourteenBlock30 (.cons fangFiveFourteenBlock28 (.cons fangFiveFourteenBlock27 (.cons fangFiveFourteenBlock31 (.nil)))))
    30 3611 0x40401b902018f89e6cbcfe6a08dab02c1f1e8d9cefffcb902a8a99091958c9b57e5d49481e70381bdc4b725b7f92e0006018101771302000608b601018dbfb899a4be9cf5ed0483f5c1b295acb1b510e0c788e5f1e8d52bffc7c8e4e5d501cccce3fcc90283f9d30197c52f000612b1010708b6010188e0ad82a2c693afb30892ca8db099eca4f7718aeefa8b89a7bd03e1c6c99995acf301a5afdfcebf8101a1e8e1f4b522bfbaa711b1c33700091acd01ad01a301a10b1007000501fd018481a1eba0ce89e8f90db4eae5f7d6d391c144e1beb9bac2bf972198dea6e9d1d10cabfa84bec90da6bc990294ab01d91f0b32000503e6010901000d03f001bb0274f686a2d4d4d0a3f70eb0df9dcbb8a2c2833bb0bef1f5b6e59d19db8583cad6c108a6fbc9949701f59be6830185f3ed26ff01a1170a0301b50273d0d6e8ffc98ae6810eede1d792c4df888d01bbaceca282c5e7af1beac9ffc1c5d144aea0a9cac316a69a9bbd17c08917f301850b7100050faa016fe0c8bc80a6baac9f13a9dcb4dcb8d980f501b58982b0cea192b101c7d8d8fa898def01fab7cfb48fd52cf897c0b7048984d1029abd3600050eb201110c0301ad020182cbbfcee6a6a8cdf902bbb1c0a3def4d8b57bfad998cb93a727e5e69bb2b50a88efff8702e8aa81119907080301a7027fbb908da5e1f9d2fd05c5ad9cb3dda6d78b35bcd28c88eeeefb0196c1c297c6fb8166a9a1bab98d07c9d3cdf302d1fba552d377231d076e000506aa017ae2c8eb84fbb39ac30b94ccb8a3ae90a5a906edfe92eaa8fcf103ecbb849b80f36aa4f8dee52ce3b2fb1afbf72d00070987010b0100050fac010183fc90e7f7bcf9c7fb02c1c9c8addaa8b8c70789e8fe8fa7bbb918d1c9a4c5b28b0ef7cfc1ea8504eafbb9ff79f8f52adb77010a030e3700065501ab027681f2a1ccdcd5e3bb0adda1d4c19487e6910197d3c08affa7d8bf01a39cd0828582c755f3c5a4efcf34fcd5a7b309eacfed18991d0738000512fd010301000b16b6010616a9010611f701d9025dd68f9ec5bda18f9f14b6b1c2aa8cb2c3e70282f49ce3a4e3c6bd038cdbe8f7f6a8bf0191a0f7c1feef0ebb8680c70285ddc71ca3350b0a0301d3026fb297e8debedfa9e10599989bff9bcbecb322afc6a7d2ace2cb08ad85ba82d0c750b187aac508f487d104feb701cb6d00050cec01c7026ea2f1d0c3e7f695b306bea4e6cfa49dc5831bb6c4e2aeabf9b936a79595abd28717f889d9fbf94887dcd908c58501d977110a0301c5026c84a5a08ebaa3ecd707e5838b92a5f491ef01af85aac49df3bef9038b8dc18687f1e501dbd6e883aa8556acb78cbf0af8918704dde36f00073e01c14d010e0301c1026af4ff87f3e3bad8a909dc8bc6c4dabfc29b58cba9bdc7eaaf8f7fef9fd2dea7e31ae29fe0a98103ac9af0cd078e9537000703dd01bf01000613e20177675903000508c801160301bf0265a8c08eeeb1acf2c30ebcd2a6d8f4e1ebe50287a1bff480e3a7f90a9e9481f3f59cf10dc3c5e9f3e7db409cd9eaa107f4c19d63af01d91307013f0005098001649999f6d3dac3de9511a9f299aab1abbcc73f96e9f1a3e0e79f03d7f3c3d584f48922ab83fda6a50d9fabcbef02a6eea10fb11f3400066c01b302759ceca3c189ef86af0195e7f6b394f9c9d378bbcbc5b79cd7018181caf6e8cf21fcfee9bb7dfebf01889d4d112f00060ec5017194b995d9baade4ed05bfecc299d08c85f10ce4afcab5a1cc81169083a5d0d6d7069a8cc7dea33e88aadf07f99f169713110701340005098e016eb9c1e1e9dad7cec108a5daf9978ef3ee8f1fbdacd392b0fd877cdedac7e8efc33bf3eda2b59708ffa0bccd01d082a7019c9301d91f3600050bdd01a30276f390b0dcd7e4a39d38e9d09c9e81fd8501afcf8e8fffea911998f3d6e9c103b9e494ef01c782af018fc94f13013000050ed20172adc0d5ffbb93e797059edca999ecfce29d0edbf48898baf4f503bccacdc3ea8b2f939bebfd16a5b7e908acd901d96707310005098d0170ebd0e2b5dca3d3950681dccaa1adec9ddb77f9edb7b4c5aa9b04eaf8e59e8ebfbf05dedba289b6bf74b6af9ba103b492e70380c13500081087010b010e0301950269a2a1a0c581f2ef8b0f84f2bbc0dbd9c6dd0f8bae98b8f48ba702b3bcb8c3dcfd30e8e9d0fd05c5ef8f04dc9d591d3600060ed20167e0b1acfba382db890ee999aaffa9c9c3ef01fb90deb2baa9e2b361beb38399f6dd0bd28faba6cb01a4cf89d328ddc9170803018902639ae1d29e86b29f8315acd2cab3ead8cadd2ba0bbe782ceabcd3adbd6edf5aaa1138aa9dadfad11b5cfbaa92992bb79e51f17076a0006098b01609781eb8ac8d1f6ff159e8288d78eb081ab03a8c2a2cbb3879ecb33a4a1fce88fb2df5c898ef8a3d5eb0ac096cfd1fd02c1e5c98326bbcf3800064a011f07010e037f0255c9f2c286b0c0eaf11efa86828d99dbc4cf04c7dffdf3bffd84bf6e8fcdf9b3caba93029eadfbfaf182ad5df88ffbd1a31ef6c0dcd53d00054b0181e502000707b901851f0e03710252c692daf2f2e0c2ed1dede68b8bccf4ced308dbd785cfdae9cc9d01899cc0acdba0eba101d1bc82aba8edff38c0c083ade325dffab7e50adddfc1039bd501d901d14800050ccb016d025184a2e7a993f0aeeb1da7d68fcae6c193d50bc9e0b3aab9d998fd338c93b6b6fa9fe1748bbfadf5a9b919f18daad8bf06a186b59505b680c932cf2f0a036b02290001d1025be3afb7d9a5b6bff710c3fe9add99e99c9b03aab082c0a3bdc9a512c4efb4f0ecb5a323c185ba9e8da51384e5afd8d703a783b1d327edc132cf01d91f010c0301c7025aeda79ed984f1e2d513e7dba9abbcde8ced01a5f1d1d498a7d3b105dc98f19fde87a503c4d8db87d687089ef1e1f102cfb401bc00050b84016b110b0c0301c502709da7f8acebe2919b1ba18dea9ceed9b525e6b3edcfd1e948bd99a6ae950697909d9906fdaeb352df1f130b340005039801c1026f88b9b7b7d3b7ffe501c781d4cd9aa0bef905c184fdc5aec5910182e5f7cff5a517db8fe5cb03c99fa331a30185300005048001bf0269a090f2edd9e5a8d707cbac93c28bd8adef719b8498cafcc6a104dcf1e2e9e7bbb10cefadd6d6d09f02ded4c8c8eb018ead9ccf0ae29701d901d11d070c0301b502688ba2b1f8c1bb97a109bb9ab38afaa8a58336e4ffeeacb893cf2dcaefdfa5baeb1dc6afcdaf8702b8c4daef01848b77552f0a0301b30264ccd6ef98f8bce2ff0daff6eac3d7e4c8ad53adc7c1af92cb8901fc94b9c2fccaa901b3f4eca0adf73383dc9ab710b7bff901c4f101d91701b3000505c001618e8bacb9afbeaedd10e5c89bf2e9b590df01ae80e48df28ca9d104cacfece59ac4a7038a86d5d0d3a72788d594cf07b3e1e10488e536000703fe010c0301a70272dec5c7e6addedf9d7cfbb089b4dcd8df02fcc3e98fdfac8108dabae6a6c504dffbc9db31d3dd2aaf35110b0a0301a3026ec1f7ceca9fbefea305d4ba9cc2cc91afc31c9cceb9e4a98083188f97f888ded318aeccf6f0c10bc3bec30488e501d901d12f07010c03019d026aa5a9d5ae919f9da909f9b3e98bf19c92c167e38a9adb97e2f14dabceecbb9ee502899adec48eb723ffb6edf70bc8faad14954f130a03019702759cc69e9581b598a106c7bdb9a8c5fdd50ffae082b58ce706a5c2cc848f2093eb851dbad7168f01a11d010a030195026dadc48cd6cde3b8ff08f2c788ff8acec2bf0fd6aedefe9cd1ab72b5cabebddd22b19a93e307cedacd2da57717010288000505db016be490bcb0c3b9bfc509e698e2ca9db3e2ef018189f98cc08490dd3ce5a0a8cee7d118bd82d3bbc119d9c6b5b90ff4f0d102cbbb340007069801a12f02000605da016787f5cbbea4bbd3970edcc7d3f6cead8bf101b7fcbfa8fdbba8ed03d2cad7d08fb7fd0d87f4f3c698af01a8eab499972a93e9e321bd912aaf4d3a000503e301830263f58eaaf28fe7e0a3138aeecd9cfedaa58b58ac869ceff7c1af0be3f1ddd4bbe50e8ef4ede19f0aaccc93e902d1fba51e912f130a037f0258f3a4f8e7c7c28e8d2093f4ed87bfffb3b315d5e0f8e0dab1c325b9cfaefe8fa1089afe8d8fbf6ce0f4ed11978b68000603ab011d010c03710255e0bdd89bb2ee9b991f829be1a2b5e6c0a704c8fa87c1a19aab9727fbcf9ca7d1a6dd01e0e1cafc8f868b54af9280e5df20ecc0c8eb0dbbfbc903919f01d9110b0c03244a000504a70101af025ed9b6a19d8ba89689018fc4d8dccc89eab55582f7c78cb9a34cfbc8f6accb1fad82dddb1abff6bd06c3e501851f010a0301ad025bb583c5e7c68eaebb0688bfe5f0a8d788d341c5ebec90fdeaa721c49abb96a39737c99baabd830bbcbc8eed59d8a7759135010a0301a702599ce1de9997fd9487088ea09499c7ffdef501fd82bada90bc96871099adac839fb5951f83abfbb1a2e311829affcd8510ca8fb6df029efbf364cd01d97f1301ae000502a901a30255f8af82e3d2e3acb90fbdb7b099f38aded517e59c9f869b91954bd9a1f69b96910fdeffd1a19f78f6e2ad08eda501d901d11f0a03019d0252d3fca7ae8dc9c4eb1492a7fcd7cdc3b3997da4a480f4dbb9af29aa92e8e0bb950fabbfe691d326fdcbbd05b6eb68000601f20111010c0301970266eba39fcea68f8bdb01cfe5caffd3e687bd05afffaad79985ab0284a7e58aaba90186fdf9e59b0cd8b3d70698e135000501b701bb13070c030195025ff7eae1adc6e3fe850be6ada6d5d88dd5a930dca6b4a880b8b732acfcef9ac4d538dcd8c482cb01d8fccfd95dfcf721d501d1070a03018b025ec792d4f3e6f4fba70dc182d5a2ea90dae15fa6b98e81e8ddd904b1c18fbeedaca102dcc4e19699ab7bd28981cb44ee88ed01aff501d901d1591107010e030189026db9c2b9c7f881928901c699b7cefdc0c59501ecfda4b0b0a7e701d9eec3cef6d702f0f095d9ad0194c995ff07a89901d901d101cb01bb01a101854f0b011003018302130001c800050101040100190101000100
    (by decide) ⟨33, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock33 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨47,1,true⟩,⟨53,1,true⟩,⟨59,1,true⟩],75,3⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    26 501 0x40400040406000702b001ad02018dbe98e2858583908d0ad299c1d0b1fcd305c6c3f09aadc90187e8f8c2dd16e4eef501a0bb1d07080301a702018a8cb5a69ab0cbeee103f7c3abd8b9e6f4c908dc8b8990dde703b5a4f09e8756ef91950ed98b01d94d1d070a5c00050290018581e08cbab1f8fcdf07f689aaefe8befdb301de838cc6abc2f89d06eaef8cdbcba3ad03a3e592c9c69103b9e494ef42f1c932000802bd0101a177110e05000501fd018efdc8b4f48c93fcf737d0aeecc1b383bf1b92a797edb6d9068eeecfa3970199aca1850c88250008028501a11d010c030800040401a502789aa2d591b2e3a3cd11ce858a83aec99fa702a2a7a5eacbe9dcb910b89a80bcfdebcd339ac1fe829c8104c3c6d885b901b2d5e28109f39501d92f0a0301a30203004e000f01c10101a70276c1aaf086c4dbd89112a5c9d081819495ab728787ca93e1f29d14b7ad989ae9ed279c8897bac301c8c796d153e2fd4fd701d901d13b1f07010e0301a302018a96f8faa6a4fcb78349fcaafffba0a38702b4c88d94b38ccb09a4b8b2a8f5a109bba8ac98ff01b49d1d170803019d020184f381b0a9dbe897c906e797c483c28ed3a9138efb89a795cba12e989dacbbe3d508dd9f808cd94ad6ccd90e879b01d901d101cb01bb4d1f010e030601af000c1a0108010107070104040200130101000100
    (by decide) ⟨37, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock34 : (⟨[⟨5,1,true⟩,⟨7,1,false⟩,⟨11,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨47,1,false⟩],49,5⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveFourteenBlock26 (.cons fangFiveFourteenBlock25 (.cons fangFiveFourteenBlock24 (.cons fangFiveFourteenBlock32 (.cons fangFiveFourteenBlock33 (.nil))))))
    31 1609 0x40404040400060a010606010000000004000507f501d70277c0e5ca8dd799fd9b01d7b9a8daaad8da8d0ae9a2d0d8ef9fb10b83b1b1b9e3f106c79fe1f48703f9f2889101b8f9a53195170b0a0301d30270daeadcab9e89aaef089096f8cec6e497c7799df895f08f91c907c4d8a4d5e5fb3ffdf4f5f303d3ceef01fb8301d977170a0301c7026fc9ebca85bf9bf2bd0a92acd897e2eba1d712a4d7e3bed885f155eafea3ca8fb502aadb8bc693933693b5eb9510cadbc921d301a1130a0301c5026da7eda5ba81c181d90cb1a4abfbeda0cb9d2ba8e19aaae6ebb3369b8780adef9f3e87aa84a3f902e0bbecd75fcad576cd2f01de000605b901c1026c96ee9394a2d3c9a70da78bbfa3acd2eaf350f2afb9c4b8ffa17384f6e1d3d28902e1ac9fbbeb3c91d2cf0689ab300007018a01bf1107010e0301bf0266c1f2b7d7c8b0afad13e89585b198dfb38d1badb293d4d782c34eeed29e8bc9a501a087a9a3c39d5df0a6a1f90bca93f104c83c000704fc012f11010e0301b50265b0f3a5b1e9c2f6fb13cc91fdc5eedfe19b01ccecfff1cba4c69d06f8c3babddab1b908949ce184edf301faeee5cfdf0180cb8aa906fbfd40000901ee01b301a101857f1101120301b30276cea9cfeff1afaf81048bc3d299f6d5bfb517be87bc99a3e0c911b1e8fadbd8a51abec8f6e0870895f5bbb167a0f736ed01d91d0b0143000505c00172bfe2d0e6e9dec7a308ccd0e292ed909acd05cde3f6a0c988a105d884d7b2878d3a9bd09ff71b96fb81018cab01a71d010a0301a7026fe0ddfc8bb9fe828f0badb6858a87f8fa8718d197f9d4dfaba57cdedc98febef17392c1fdb9e3028492c1a90193dc8f2fad4d1d0a0301a30278a79293a0e5ba86f30393af82d6a183f1cb0ddeaabf9690b0d30d9d8be8d79eeb06f6cbcd84e54fd8cfbb27c18f019d000b02c8019d01857f774d49471f11011603019d0273dad1eed2f3c1cf9907e3979ad4bfb4fd9d2a979ca98df3ccd976a4c5e5a6b7db13d2d2e8d1d709d1c884f52bb28b0ea57f010a030197027296bcb7e3cdc491fb09c7efcfdaa7f4d7a11591e4bdeeb2a2f326d2fdd2a9a39b1ce090f7f18901bbf2b1f541beff01851f070a030195026ac1d1a5b78fd0dfe50f9bd4e0e3a6e6fbb302c588b3aba9a6f48d07d9b0b9879ea0ef02e3f8eacbd99102edb4c3bed918cdfabd06dcbf01b70005018601a11d0b010e03018b0268fdbbeec7e9d3a2c70effd1d8f7fce7a9c104a98eee9e9db9fce30eb5ebac87b8cd972694c1929387d718faf9e8b2d707bac5b5dd05c5bce74ac5110b050c0301890264b0fbc9f9f7daeaed1884c1d2cdefcbeadb1f8e9fbdd4cbc49174d8cdfecd859302b1b1fae8bff70281aff5f6ad1c8384f50da4b30181000902c201a1018501837f774d49011403018302210011000501010401b7025fb1e7d9d4cdd5d1ad0fa4a2a5d9f79da3d50181afa6f6a9f192e90296c4b19ca9bbc758b89395b49d1de1cd8db9048d8be744d701d94d3b00057a01b5025eaaf2c9e8f1cae4fb10fefdcac1e6acbd8f68f7ea81aad7a6b75685bd828fd9f123e4b6c098eb19948df6a90599efbf7d9b01d90195110b0c0301b3025b96939aa5ddaa9fe5169bfe9cffc1e2bfd70ee0fba7ecd9cded1587b8bff5c9971b8afed3ca8105f9bbafab02b8a5e3648301d901d113070c0301ad026efc9ab392c5f0b58503e9e6b6ddaa918f8908cdcacbfab198db02cdd7babea48d32e2ddf1a53090c4df218ced13e501851f1101af00060285016ca7fe96a9eeae8db907a78de1fce8d4f8a312d5c3f78df7f8974b84f0fee7baed0aacd085ccb72586fbaf24dd8d2e000c028c0101950185774d491f17130b0701180301a30268a9d3eb8ceb8ad2870be8fcf1d3b6b0bfc379a0b2c5e6cc868d0484aae1c184a4a33ed98ed9f0970af19ff78701eae08743ef1d0b0a03019d0264aba9bfefe7e796d511ad83a9ebf0a29a8760c8bf84d8ae819104c4d8ef8581a6db05a4c2c9d1d98509babefe950383d9f517f301d1070a030e00040401ad025cdea19280e3aaefe71190cc9e9dbf989ce701fdd6b9d1fe94d0d76bf5dbacd5fb8b0286c4cf98ffa33ed783feef059fd2ff04acad01d97713010c0301a7025ac1f8bee5f797b9e31687bbbdc78beae9c137b7d98dacd59ef302b4c18bdafe928504a982b289b2a937a097b9f31fddfac31ac9a101d901d101cb01bb01a301a14901100301a30205029400180101000100
    (by decide) ⟨24, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock35 : (⟨[⟨5,1,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨17,1,false⟩,⟨19,1,false⟩,⟨23,1,false⟩,⟨29,1,false⟩,⟨31,1,false⟩],33,6⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveFourteenBlock34 (.cons fangFiveFourteenBlock16 (.cons fangFiveFourteenBlock7 (.nil))))
    40 28 0x4040200051a010801010e1a010c1001050101040100140101000100
    (by decide) ⟨16, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock36 : (⟨[⟨5,1,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨17,1,false⟩,⟨19,1,false⟩,⟨23,1,false⟩],29,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveFourteenBlock4 (.cons fangFiveFourteenBlock35 (.cons fangFiveFourteenBlock6 (.nil))))
    35 150 0x4040200060198015b0201a884c99eadb881ad04cee9d9b4abfaad3793dae7adfb38e9a9a8ff2de2959506e1f523bf1d13010a0359020b8fc4ccbdebaad0c15fe1b099a4f1c09f02bd8c9ad889e4e302bcbbe08ddf9f01daa5b1b9f123e9c88108e39d01fd01d101cb01bb01a1018553110b10035302056f000a0a010a11010c01010509010404020005050104040200060101000100
    (by decide) ⟨14, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock37 : (⟨[⟨5,1,false⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨17,1,false⟩,⟨19,1,false⟩],25,9⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    25 33 0x40404040400051501000004040400090f01100a01040404040400080101000100
    (by decide) ⟨12, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock38 : (⟨[⟨5,1,false⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨17,1,false⟩],19,10⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveFourteenBlock3 (.cons fangFiveFourteenBlock37 (.cons fangFiveFourteenBlock36 (.nil))))
    21 28 0x608010501010401000d0c01070901070701040402000a0101000100
    (by decide) ⟨9, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock39 : (⟨[⟨5,1,true⟩,⟨7,1,false⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨23,1,true⟩,⟨31,1,false⟩],33,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    31 37 0x90101040502000818010613010b1201070901090d01060b01050701040400000000000700
    (by decide) ⟨16, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock40 : (⟨[⟨5,1,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,1,false⟩,⟨23,1,true⟩],29,9⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveFourteenBlock39 (.nil))
    18 39 0x60a0104040200080f01072301050101040100070f01040402000b080104040200060101000100
    (by decide) ⟨14, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock41 : (⟨[⟨5,1,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,1,false⟩,⟨19,1,false⟩],29,9⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    21 34 0x404040404000d13010c15010f18010501010401000a070104040200050101000100
    (by decide) ⟨14, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock42 : (⟨[⟨5,1,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,1,false⟩,⟨19,1,false⟩,⟨23,1,false⟩],31,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    21 30 0x404040404000a18011021010601010b0b010404040404000b0101000100
    (by decide) ⟨15, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock43 : (⟨[⟨5,1,false⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,1,false⟩,⟨19,1,false⟩,⟨23,1,false⟩],25,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveFourteenBlock42 (.nil))
    24 27 0x831010b2b01070c010605010913010d01010401000f0101000100
    (by decide) ⟨12, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock44 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨31,1,true⟩,⟨37,1,true⟩,⟨41,1,true⟩,⟨47,1,true⟩,⟨53,1,true⟩,⟨71,1,false⟩],73,3⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    22 35 0x506010a1b010819010b14010504010404050300090e010501010401000e0101000100
    (by decide) ⟨36, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock45 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨31,1,true⟩,⟨37,1,true⟩,⟨41,1,true⟩,⟨47,1,false⟩],49,5⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveFourteenBlock44 (.nil))
    30 37 0x404040404000c3101050100090a011123010a1f010a010109090104040200090101000100
    (by decide) ⟨24, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock46 : (⟨[⟨5,1,true⟩,⟨7,1,false⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨31,1,true⟩,⟨37,1,true⟩],43,7⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    19 25 0x60101070c010b090105070105050104040200060101000100
    (by decide) ⟨21, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock47 : (⟨[⟨5,1,true⟩,⟨7,1,false⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨31,1,true⟩],39,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    25 24 0x60101070e01101201090b01040404040400080101000100
    (by decide) ⟨19, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock48 : (⟨[⟨5,1,true⟩,⟨7,1,false⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩],33,9⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    26 24 0x701010401000a0b01060101080501040400000000000700
    (by decide) ⟨16, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock49 : (⟨[⟨5,1,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,1,false⟩,⟨17,1,false⟩,⟨29,1,true⟩],33,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    18 25 0x40402000a11010b0f010b0b01040404040400080101000100
    (by decide) ⟨16, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock50 : (⟨[⟨5,1,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,1,false⟩,⟨17,1,false⟩],31,9⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveFourteenBlock48 (.cons fangFiveFourteenBlock47 (.cons fangFiveFourteenBlock46 (.cons fangFiveFourteenBlock45 (.nil)))))
    31 21 0x601010913010a0e010501010401000e0101000100
    (by decide) ⟨15, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock51 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨41,1,true⟩,⟨47,1,true⟩,⟨53,1,true⟩,⟨61,1,true⟩],73,4⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    18 38 0x4040503000512010504040404000b1501071301050e01070b01040404040400060101000100
    (by decide) ⟨36, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock52 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨41,1,true⟩,⟨47,1,true⟩,⟨53,1,true⟩,⟨61,1,false⟩],63,4⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveFourteenBlock51 (.nil))
    23 34 0x4040004040506000712010a170105010104050200060701040402000e0101000100
    (by decide) ⟨31, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock53 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨41,1,true⟩,⟨47,1,true⟩,⟨53,1,false⟩],55,5⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveFourteenBlock52 (.nil))
    25 33 0x4040403000506010504040404040007000b080108050104040200090101000100
    (by decide) ⟨27, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock54 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨41,1,true⟩,⟨47,1,false⟩],49,6⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveFourteenBlock53 (.nil))
    25 25 0x70101040504000400090e010c090104040200060101000100
    (by decide) ⟨24, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock55 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨41,1,false⟩],43,7⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveFourteenBlock54 (.nil))
    27 24 0x601010516010a1501070901040404040400090101000100
    (by decide) ⟨21, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock56 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨37,1,true⟩,⟨47,1,true⟩,⟨53,1,true⟩,⟨61,1,false⟩],63,4⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    22 33 0x7250104040503000708010516010b1e01080101090901040402000a0101000100
    (by decide) ⟨31, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock57 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨37,1,true⟩,⟨47,1,false⟩],49,6⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveFourteenBlock56 (.nil))
    22 30 0x60101082701081501091201070e01070901040404040400090101000100
    (by decide) ⟨24, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock58 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨37,1,true⟩,⟨41,1,true⟩,⟨53,1,true⟩,⟨61,1,false⟩],63,4⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    23 32 0x71d01051a010a230109120105050104040200090901040402000a0101000100
    (by decide) ⟨31, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock59 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨37,1,true⟩,⟨41,1,true⟩,⟨47,1,true⟩,⟨61,1,false⟩],63,4⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    23 27 0x72001081d01071a011115010e10010501010401000f0101000100
    (by decide) ⟨31, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock60 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨37,1,true⟩,⟨41,1,true⟩,⟨47,1,true⟩,⟨53,1,true⟩],63,4⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    22 32 0x101c01101801051101071801080c0104040200080801040402000e0101000100
    (by decide) ⟨31, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock61 : (⟨[⟨5,1,true⟩,⟨7,1,false⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨37,1,true⟩,⟨41,1,true⟩],49,6⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveFourteenBlock58 (.nil))
    28 33 0x404040404001124011326010601010b1201070901040404040400090101000100
    (by decide) ⟨24, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock62 : (⟨[⟨5,1,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,1,false⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨37,1,true⟩,⟨41,1,false⟩],43,6⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveFourteenBlock61 (.cons fangFiveFourteenBlock59 (.cons fangFiveFourteenBlock60 (.nil))))
    33 30 0x918010d2e010901010401000c1401090b010404040404000f0101000100
    (by decide) ⟨21, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock63 : (⟨[⟨5,1,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,1,false⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨37,1,false⟩],39,7⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveFourteenBlock62 (.cons fangFiveFourteenBlock57 (.nil)))
    26 24 0x901010401000a07010709010404040404000b0101000100
    (by decide) ⟨19, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock64 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨31,1,true⟩,⟨47,1,true⟩,⟨53,1,false⟩],55,5⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    24 38 0x404040404000717010925010b16010c1a01081101040402000d080104040200090101000100
    (by decide) ⟨27, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock65 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨31,1,true⟩,⟨41,1,true⟩,⟨53,1,true⟩,⟨71,1,false⟩],73,4⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    19 31 0x4040003000717010d01010605010404020009090104040200060101000100
    (by decide) ⟨36, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock66 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨31,1,true⟩,⟨41,1,true⟩,⟨47,1,true⟩,⟨71,1,false⟩],73,4⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    19 24 0x817010c14010605010e10010501010401000b0101000100
    (by decide) ⟨36, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock67 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨31,1,true⟩,⟨41,1,true⟩,⟨47,1,true⟩],55,5⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveFourteenBlock66 (.nil))
    26 30 0x40404040400061501050e010c11010f0f010404040404000d0101000100
    (by decide) ⟨27, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock68 : (⟨[⟨5,1,true⟩,⟨7,1,false⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨31,1,true⟩,⟨41,1,true⟩],49,6⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveFourteenBlock65 (.nil))
    27 24 0xa30010c1301080a011218010901010401000f0101000100
    (by decide) ⟨24, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock69 : (⟨[⟨5,1,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,1,false⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨31,1,true⟩,⟨41,1,false⟩],43,6⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveFourteenBlock68 (.cons fangFiveFourteenBlock67 (.nil)))
    36 31 0x60101061a0104040200050f01050d01080a01040404040400180101000100
    (by decide) ⟨21, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock70 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨31,1,true⟩,⟨37,1,true⟩,⟨53,1,false⟩],55,5⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    27 24 0x60101061501050e011c12010501010401000d0101000100
    (by decide) ⟨27, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock71 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨31,1,true⟩,⟨37,1,true⟩,⟨47,1,true⟩],55,5⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    26 31 0x40402000832010510010c17010c1b010d1301070101040100110101000100
    (by decide) ⟨27, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock72 : (⟨[⟨5,1,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,1,false⟩,⟨17,1,false⟩,⟨23,1,true⟩,⟨31,1,true⟩,⟨37,1,true⟩],45,6⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveFourteenBlock70 (.cons fangFiveFourteenBlock71 (.nil)))
    34 37 0x100073901070501050301051d010d01010c1b01080101050501040402000b0101000100
    (by decide) ⟨22, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock73 : (⟨[⟨5,1,true⟩,⟨7,1,true⟩,⟨11,1,false⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨31,1,true⟩,⟨37,1,true⟩,⟨41,1,true⟩],55,5⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    27 32 0xa2701060c01040402000710010e2601080101100801040402000d0101000100
    (by decide) ⟨27, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock74 : (⟨[⟨5,1,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,1,false⟩,⟨17,1,false⟩,⟨23,1,false⟩,⟨31,1,true⟩,⟨37,1,true⟩,⟨41,1,true⟩],45,5⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveFourteenBlock73 (.nil))
    31 26 0x1b22010404020008080105050104040004040500170101000100
    (by decide) ⟨22, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock75 : (⟨[⟨5,1,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,1,false⟩,⟨17,1,false⟩,⟨23,1,false⟩,⟨31,1,false⟩],33,7⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveFourteenBlock69 (.cons fangFiveFourteenBlock64 (.cons fangFiveFourteenBlock72 (.cons fangFiveFourteenBlock74 (.nil)))))
    30 31 0x60301040402000716010a14010e12010e0e010404040404000b0101000100
    (by decide) ⟨16, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock76 : (⟨[⟨5,1,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,1,false⟩,⟨17,1,false⟩,⟨23,1,false⟩,⟨29,1,false⟩,⟨31,1,false⟩],33,6⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    20 33 0x300061601071a0105070105010104010006050104040200060101000100
    (by decide) ⟨16, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock77 : (⟨[⟨5,1,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,1,false⟩,⟨17,1,false⟩,⟨23,1,false⟩],31,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveFourteenBlock75 (.cons fangFiveFourteenBlock63 (.cons fangFiveFourteenBlock55 (.nil))))
    32 24 0x7010104000003000807010a0601040402000b0101000100
    (by decide) ⟨15, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock78 : (⟨[⟨5,2,false⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,1,false⟩,⟨17,1,false⟩,⟨23,1,false⟩],29,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    22 30 0x404000300060101091301080401080e0108050104040200060101000100
    (by decide) ⟨14, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock79 : (⟨[⟨5,1,false⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,1,false⟩,⟨17,1,false⟩],25,9⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveFourteenBlock50 (.cons fangFiveFourteenBlock49 (.nil)))
    24 28 0x91501051001050d0100000200090f010b01010401000f0101000100
    (by decide) ⟨12, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock80 : (⟨[⟨5,1,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,1,false⟩,⟨17,1,false⟩,⟨19,1,false⟩],33,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    20 22 0xa01010a1701060101070701040402000a0101000100
    (by decide) ⟨16, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock81 : (⟨[⟨5,1,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,1,false⟩,⟨17,1,false⟩,⟨19,1,false⟩,⟨29,1,false⟩],31,7⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    23 27 0x50301051301060501091b010610010d01010401000e0101000100
    (by decide) ⟨15, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock82 : (⟨[⟨5,1,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,1,false⟩,⟨17,1,false⟩,⟨19,1,false⟩,⟨23,1,false⟩],33,7⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    22 23 0x404000300071401050d010b01010401000d0101000100
    (by decide) ⟨16, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock83 : (⟨[⟨5,1,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,1,false⟩,⟨17,1,false⟩,⟨19,1,false⟩,⟨23,1,false⟩],29,7⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveFourteenBlock82 (.nil))
    21 31 0x2000c1a010c19010404000300050501040400040405000b0101000100
    (by decide) ⟨14, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock84 : (⟨[⟨5,1,false⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,1,false⟩,⟨17,1,false⟩,⟨19,1,false⟩],25,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveFourteenBlock81 (.cons fangFiveFourteenBlock80 (.nil)))
    26 26 0x40403000706010b1e010911010d0101040100110101000100
    (by decide) ⟨12, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock85 : (⟨[⟨5,1,false⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,1,false⟩,⟨17,1,false⟩],19,9⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveFourteenBlock79 (.cons fangFiveFourteenBlock78 (.cons fangFiveFourteenBlock77 (.cons fangFiveFourteenBlock76 (.cons fangFiveFourteenBlock84 (.cons fangFiveFourteenBlock83 (.nil)))))))
    27 24 0x100182701060501070f010b0101040100120101000100
    (by decide) ⟨9, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock86 : (⟨[⟨5,1,false⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,1,false⟩],15,10⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveFourteenBlock85 (.cons fangFiveFourteenBlock40 (.cons fangFiveFourteenBlock43 (.cons fangFiveFourteenBlock41 (.nil)))))
    22 25 0x80a010b1301060c0104040000040404040800100101000100
    (by decide) ⟨7, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock87 : (⟨[⟨5,1,false⟩,⟨7,1,false⟩],13,12⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveFourteenBlock2 (.nil))
    19 21 0x40402000e110104040000050406000b0101000100
    (by decide) ⟨6, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangFiveFourteenBlock88 : (⟨[⟨5,1,false⟩],7,13⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangFiveFourteenBlock0 (.cons fangFiveFourteenBlock87 (.cons fangFiveFourteenBlock86 (.cons fangFiveFourteenBlock38 (.nil)))))
    25 16 0xa0801060601040402001b0101000100
    (by decide) ⟨3, rfl⟩ (by decide +kernel)

theorem fangFiveFourteenRoot_closed : (⟨[⟨5,1,false⟩],7,13⟩ : Box).ClosedBelow (10 ^ 21) :=
  fangFiveFourteenBlock88

end OddWeirdSubproblems

namespace OddWeirdSubproblems

theorem noPrimitiveWeird10Pow21_coprimeThree_atLeastFourteen {n : ℕ}
    (hn : n < 10 ^ 21) (ho : Odd n) (h3 : ¬ 3 ∣ n)
    (hc : 14 ≤ n.primeFactors.card)
    (hproper : ∀ d ∈ n.properDivisors, d.Deficient) : ¬ n.Weird := by
  have hupper := coprimeThreeOddBelow10Pow21_primeFactors_card_le_fifteen hn ho h3
  by_cases h14 : n.primeFactors.card = 14
  · exact noPrimitiveWeird10Pow21_coprimeThree_of_root fangFiveFourteenRoot_closed
      hn ho h3 h14 hproper
  · exact noPrimitiveWeird10Pow21_coprimeThree_of_root fangFiveFifteenRoot_closed
      hn ho h3 (by omega) hproper


end OddWeirdSubproblems

open OddWeirdSubproblems

theorem OMA.solution : OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H2_R1_H2_R1.H1 := by
  intro n hn ho ha hp h3 hc
  by_contra hnp
  exact noPrimitiveWeird10Pow21_coprimeThree_atLeastFourteen hn ho h3 hc hp ⟨ha, hnp⟩
