import OMAReductions.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H1_R2
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

/-- A branch certificate whose soundness may use the current cutoff. -/
structure BoundedBranchPruning (B : ℕ) where
  verify : Box → List ℕ → Option (Bool × List ℕ)
  sound : ∀ {b data tail}, verify b data = some (true, tail) → b.ClosedBelow B

def BranchPruning.bounded (prune : BranchPruning) (B : ℕ) : BoundedBranchPruning B where
  verify := prune.verify
  sound h := closedBelow_of_closed (prune.sound h) B

/-- Verify a complete subtree. A certificate may close a box by an
unbounded rule. Size checks and the end of each last-prime sweep use `B`. -/
def replayWithSizeLimit (limited fast : Bool) (B : ℕ) (readPoint : PointReplay) (readSweep : SweepVerifier)
    (prune : BoundedBranchPruning B) (oddSplit : OddSplitReplay)
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
    {limited fast : Bool} {B : ℕ} {readPoint : PointReplay} {readSweep : SweepVerifier}
    {prune : BoundedBranchPruning B}
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
      · exact prune.sound hprune

def boundedStreamWith (fast : Bool) (B : ℕ) (readPoint : PointReplay) (readSweep : SweepVerifier)
    (prune : BranchPruning) (cut : Box → Bool) : ℕ → Box → List ℕ → Option (List ℕ) :=
  replayWithSizeLimit true fast B readPoint readSweep (prune.bounded B) .none cut

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
    replayWithSizeLimit false true 0 readPoint readSweep (prune.bounded 0) .none cut fuel b data =
      replayWithSizeLimit false true B readPoint readSweep (prune.bounded B) .none cut fuel b data := by
  induction fuel generalizing b data with
  | zero => rfl
  | succ fuel ih =>
    simp only [BranchPruning.bounded] at ih
    simp only [replayWithSizeLimit, Bool.false_and, Bool.false_eq_true, if_false,
      normalizeSlots, BranchPruning.bounded, Bool.not_false, Bool.true_or, if_true, ih]

def unboundedRankedStream (readPoint : PointReplay) (readSweep : SweepVerifier)
    (prune : BranchPruning) (cut : Box → Bool) : ℕ → Box → List ℕ → Option (List ℕ) :=
  replayWithSizeLimit false true 0 readPoint readSweep (prune.bounded 0) .none cut

theorem unboundedRankedStream_closes
    {readPoint : PointReplay} {readSweep : SweepVerifier} {prune : BranchPruning}
    {cut : Box → Bool} {fuel : ℕ} {b : Box} {data tail : List ℕ}
    (hcut : ∀ box, cut box = true → box.Closed)
    (hlo : 1 < b.next) (hodd : Odd b.next)
    (h : unboundedRankedStream readPoint readSweep prune cut fuel b data = some tail) :
    b.Closed := by
  intro xs ys hm hv hw hp
  let B := number (xs ++ ys) + 1
  change replayWithSizeLimit false true 0 readPoint readSweep (prune.bounded 0) .none cut fuel b data = some tail at h
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

def checkBoundedBlockWithPruning (oddSplit : OddSplitReplay) (fast : Bool) (B : ℕ)
    (prune : BoundedBranchPruning B) (fuel : ℕ) (b : Box) (cuts : List Box) (count value : ℕ) : Bool :=
  match expandPackedTokens count (bytesFromNat count value) 0 0 with
  | none => false
  | some data =>
    match replayWithSizeLimit true fast B boundedPoint boundedSweep prune oddSplit
        (fun q => cuts.any (boxEqual q)) fuel b data with
    | some [] => true
    | _ => false

theorem checkBoundedBlockWithPruning_closes {oddSplit : OddSplitReplay} {fast : Bool} {B : ℕ}
    {prune : BoundedBranchPruning B} {b : Box} {cuts : List Box}
    (hcuts : ClosedBelowCuts B cuts) (fuel count value : ℕ)
    (hlo : 1 < b.next) (hodd : Odd b.next)
    (h : checkBoundedBlockWithPruning oddSplit fast B prune fuel b cuts count value = true) :
    b.ClosedBelow B := by
  unfold checkBoundedBlockWithPruning at h
  split at h
  · contradiction
  · split at h
    · apply replayWithSizeLimit_closes _ hlo hodd ‹_›
      intro q hq
      obtain ⟨c, hc, he⟩ := List.any_eq_true.mp hq
      exact (boxEqual_iff_eq q c).mp he ▸ hcuts.closedOfMem hc
    · contradiction

def checkBoundedBlockUsing (oddSplit : OddSplitReplay) (fast : Bool) (B : ℕ) :
    ℕ → Box → List Box → ℕ → ℕ → Bool :=
  checkBoundedBlockWithPruning oddSplit fast B ((boundedPalettePruningWith fast).bounded B)

theorem checkBoundedBlockUsing_closes {oddSplit : OddSplitReplay} {fast : Bool} {B : ℕ} {b : Box} {cuts : List Box}
    (hcuts : ClosedBelowCuts B cuts) (fuel count value : ℕ)
    (hlo : 1 < b.next) (hodd : Odd b.next)
    (h : checkBoundedBlockUsing oddSplit fast B fuel b cuts count value = true) :
    b.ClosedBelow B :=
  checkBoundedBlockWithPruning_closes hcuts fuel count value hlo hodd h

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
private theorem fangThreeFourteenBlock0 : (⟨[⟨3,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨43,1,true⟩,⟨47,1,false⟩],49,5⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    21 1598 0x50905097702149780cc9ae9f7e7e30bea96b5c0a3cf87ef01b6c6e8c3c6f2aec101a7dcdfb0f9bbf501bdf1c6a0d59708fba78a9f01efd6cf69eb02ab130a037141000a3201018ea8ffb9f2c5d5d7299aea84b5a8d52ae8e4eaa88f1694f8f8d70487e0d501aac36d49170a036d28000a370104c9d0a0ece1d8eff70dcfa1c1859feae506d4a9ad8aa79976b48dc19d1ccdd2f7078fad13bb39130d010c036b0227bbdbe4abb3ffebe70ae496d9c5f5b5f8b97c9b9ca8d5c2e9a5089ab9f59ba5d5d3018cb6bff3c38f099cf7e7ed01d6e2e3018fc917030a03670236cdaeaab1c4b7f28b1fbcd4b4a0f0bbf111d68baa88afb51e80b7fb8bbb08a08b95cd01a8afc51e9d01dd350195000503930135f5d290a5d5bba3c107e1f9b2b0c38bd3c326d5a2e1faffa48703b1eb91d9d0a12c9a9bef870998a1b707cfe71db33b170a0361024ade829da9abffd9e101b4beeae8d0c3cefd0eabe0faa782f0b305f6b9c6d68ee101b59be3b79102d4aa8315d55949171166000508c1014c96fec7d0e7acacaf0a928fa1dae7a8e3b750f2f38af8eab1db6c8dccabefcfb76de0feffb1b517e3cbbfeb02cee7f105d6f302f902c302ab2b13010e03530248c187f0f3bbe7f2db0e8de8d0bbc4b2f4dd07919ed3bac2c295c52b8794e2aeaac0c57ed2df87b6829f26be869f830286ca973a854f491f130c034f0213006d0212c0a1e1ef82f9faad7f91d29a90cce9830bc78990d2a9c4d50397c7f6e2c1c70185f49bda83178af8ef03f3e302ab1f130a036b0213f3f7c99a91cd8c9308acbec3ee87b0eca90cc1a5fbc5a5dd9d08fab4b6c4affb07a492c3c1c901abd09aa930a3f30ceb332b1301ea000502a40113c2baebe994fec6a90bb8ced0ee99c5e2cd01e1bba6c3d4e4f39501bcbbb19c9c878145bed3b4e8e30dd5a9eeaf5ece9b7acb1d010a03650212dfc1b1879be1bad510e2f790f8fdf292e705e7dfd59c8ba68dd915b4b59ea4c3f3a137ec9cddf39bc90ab3fc90c1d90390e6c4b70a90cf20e701dd17010c03610235c4f49e9f89cbb0df05aab492e7d0a6f69114cccdabf18ce28514f0ede0eb9dd711d698ebbdd103c48bdce702ae8bb515d5594f1d170c03590242f1b4f6c4ffd4bae70592c8ffa2eca484c3138adcc8cd978bb305bbefbad0db81018ae989cacb0faaaee901d1b902f92b1f0a0353020d0069020ca19f88f0e7d9b1a364b2878dcab0dfcf02bcfcd488cdc0bf01e087e8d3e6b30d93fccad90389f4e701a6ef671f170d010c0367020f9498b5dc8bdc92b302e39fc1dccaa18cb1079baff2c9d9acf10786d08cd0849b01dbead99cff4795cfab309dc335c301dd1d0a03650213d980d2a9cde393c107f392ebe99993e59b1fcac39fdf8ea19511b397f49ce4f16dce87a0c91eb89bd30ab79102c3080361022cefddeb898381c9bd02d1eef79ed3808bed04c8b294ea80d2eb04aa8ecfa7b1e302adb1c4e6bb76c0dea3089abd01f72b0d0a0359020903c5000603c4016b0212a7f9b1a8aedfbfdf3ebb88bfafb185a501c7dbccaea0f1f302f8ff9df8a9dd038f86ade5ab31cdcfa302dfd32f00083d013b17010e0367021488ebafe1a7cdeac703b0b0bec4abb5d3eb08ff9ec0bfbbda9b05b1dff186deeb01d5c6dad1a30da2efaf16d2f302c302ab01f701dd4f2f010e03650213a38d91feb3fdb8db0d9882a0c2a3c8adc53ae9aae5f797e8b36a999c9ee3cf9f26fac2e6d689108dd8c5f304bdf48913911d010a03610231bcb7c7d8d581cdb90293a9afd1e2a783af10839ee3cca2eb8704c0e7f7ffbfcd01bb98edb6d303ce9aa54e9d170d010a0359023de3b3c1b288d9cba7048ab8818382dce48161879fcb87b0d11ae1b7fca0eb05e9dbf8cd07e4d30d01080353020b006502128f96b593b2bdf2c523c0f4c58bf4e3b72baefeb7a7a89307f4a1b2f7cf01a69ded9f028491d577b36117110a03610212ca9fa5acf181e1b710cff3c9ebc3b7bc9d0493b885d0b7e68fb71192a9bcb3accae946b3808c83b68102e6e1e897af12a2ed8706a4db592b13010c0359020502d1000536015d020eeea7fcb4a5ab97e73beda5f197e1d5932ce789c980d2d304938babfd9d02c5f6cbeb01abcaa55ba7110803592f00114201550204f0c081a8fcc7b79b03a4c09ba6c7b3c106c3c2b4e1c7eb0baca7e1ebbb0c84d482fd01c4e1c92d872b1f010a035302033300080101050701050501050900000000000700
    (by decide) ⟨24, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock1 : (⟨[⟨3,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨41,1,true⟩,⟨47,1,false⟩],49,5⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    23 2268 0x50905097b023bf28cf0a7f08ed7eb2896e6c091d786c760fefec891b99105a6c493fdeb5feb8ced019998e11a893527110a03710239e2ddfda9eeb4d6ff07e4a0c9fb9989e2b739f8e2b8b2d89cc501dcd1b6d8e5d09d01c2bbb6e3e6c10df9cbb3cf01aaf8dd02c36d491f0d0c036d02449fbbf6c1d6a4adcd51d1f3f9b7eae7a705ade7edf4fff1ff029beb898d91b7719cecaca306afdb8d01d18f1d08036b024990ee92f9d48e8aff01cd8c99f5e0c7d1c914978ed6cbd4bd0dd5d99d9bfd01a0a2d9991f9ce513bb67493b17010c03670247db8ca8f9e3effead05d9afe6ed8acfdb831db8dfbda2f1bc930293bbeb9dc8971cdbb49b8917daeba7069df30281000879011f130d0e0365024dd4fae59fb291c6b305bcbeb1ad99b4bce727fd9ad1d5a6c8db11b0bae3a9ee9103f1fca4c1f501c496b2cf5998fb28bf02f9470d3c000507f40151d7f0c9dce8d382ed0b99dff5c7e6fbc5df0296f581c6b7a0f8f523e2b09fd78ba507cee8bccbc301e0f193f5448c8b30000803c4013b0c03590264e0bc83f390f8cb9902f2c2bfbae9daf2b111a1ba9ff590cfff02bfb8c6dcc1fd01dceaf9dfbf0fa5dba502d2f5290d010a03530266c1c08dfbc2f3feef06e6e1d8c0dd98b2a721c7c3e6ba8ed9d901fef08ca9f99ecf0b8498f9d2d0d702ea92e7f28575d58bf705c4bb02f97200050ab30111010e034f021300730214e9a5b2cfe5eccfc70fb1ffe899cba3e1e143f7959fe3d9c19501b3d9aef797e2fb03d4bbbcbe81d303abdbee89449acf0ea535010a037142000a300103a788c9beeb8b94e101a0fe84bab58ea532d4eafd95f10f8995a0b10186def313911f08036d0228dcd3aaafa8cdd1fb06c49b97d7ced5e1cb35d9a0a0ccfdd4934a9ce8b2c0e0ad08f389eedfad03a6a8c48b03d1d68f139d1d030a036b02358c9eeff9d28dddf301eaad99f6fa80bccf04e99cd8ecedbdd306a3c5c69de0cb04d6f4ea93bf058aaac104acad671d018f000508980139f796fefd8089bec15292e2b1fab6ef8f04a3ace28eb5cee903a2dbd5e3cdaf01a8f4ddbf810cfcdcd3029497654f3b13010c33000c068a010a8d958084c4d685cd12f1f4eda2aa8db531cd96c29cf9a5218088cf97d302eeb9fef355b7f902f92800060ad00101dd614f473b35291f01140361024d8ee1f0f4eaecf2ad039dece7ddcfa2cca30dec83f6ea88e2c512a3d79bb9ffcf0691f6ddc1d90294d4fd830187a3d702f902ab1f13010c03590252b8b8a6f8e1e88cf908d2c2e5d1deb1efd725a2af90d2d2a6c96db0aec7dfc79744acf7e0a7b30dadedf1bb01dcc1eb499753470a03530211006d0214dbc7b8dda5bec6c90c92aea5d5caf8c3ed51e7becece86abff02c283d8abb2a48d22d0dc95a3e5078ae1dcbf019998e101818b02c33b11010c036b0213f8b7cec4a2f285dd11ebe0f5b6acd8c8bf03f799d8e4f6a99ae908fba6f0c7dcdaa501b3e295b7e6a114978bb3830cb1afa303c3fb01f8000508d201dd130c0367022ae4cacba6afc2fecf03888289b0eaa380b908e3c3b08b93e0b306b6a7ebb3e8b303a187f4a8bb68b98daf1192bb35c317110a0365023280abfec787dddaf50491d1efa592e1bc8d05c1e0bcc0eea3fd06b69eb692fdb9019ec2f7c4f520f4f7c5079be3148d036d0005039a0140c5a4cac4ddb0fdf505dae189edc282fed5389b94b9d3ecc4e903bcc28f8592b1b707bc9da8b8d1ff06f4a6f0fec90395ba9aef01abcaa501b58302f9595327130d01100359020b0065021491c1e4e3a3c696910ef18f9dfbbbd5a18701cabff4ecffe588f102ddeeccb1ed9abf09b2c2b0f8fe8733f1f5c6d92baab6ef02c302ab59130101850005059601080692016f0214d3aef599b1f2b2e50e90cfa183f2fdb6fb07e5b2a7a5ceb5e303eb95daa6ccdd04b5edfaabb302fdb880915ec8a50daf1f030a036d0214a2eed295b3a9ebb31291dca18cb4d4cbf12ee3dceac48ede8d03c585afa8bfd110c7edc98b01a4cbf501caa96b2f110a036b6c000a330104c9b2c0dde8ddbdbd19c69b8ec4f7d8d510cee8addeaf8305f2fea8a1d310c1b88901d5d3350803670229efbe9ef8e1d1d0d508c9febcabfa85858d10d3aaaec8e190fd02a5dde4c68383019ed1a9e8cb059c95d7258b3b0803650237d1c195ea8e81c18d02e4e7c0c2f3a1afc502f9ecd7c38acc9b05a2cad3b9b7bd019eec94dba502ecacc5039fa701dd29010a03610246a7f296fdc0f895f903dbc8d392c086ace71487ea8cc490e4ad0ffa9dcf85c5e10ce8e9de91bd07d7b0eaa315ba9519a7594f0a03590254e1d8c4f1acd799f70194d08efca5b7c6bf088a89b28fc8e4c915adbbca83ab0af0d388e702bf9ecb24b553350d0a0353020f006b0214c0aae0fca3efecd30c82b3c68b87e4f09f0a839fd9fad2cec502c6b3cfecd6f301a191f094d927a0dcff03c7d72f0d010a036702148db0928586cc8fe90eee87e0e7f496efef0285dc89ce8bd7e5c90588e680dcfcfdfd039ec5ebef869b37bbcac8ed0cbffa8902dcbb02c302ab49010c0365022bfeed91f6e3abd1c101f4e8f5d389f199e705bed2e7a096d2e3038cbce8fadfd750f0d2f08f49fb992895612903a1000501ab0135d181c6fa81f0e8d10a81d9fec1ff85acdf0ca9fe8cacc7baab01ef808bbeaccb018197a9e4f737c0f3dd1394d110fd1f030a0359020900630214da8fadf6a6ad8ddf06b5b6bec3aef2c1eb09b8bfb4b48fd59301bbd99ec6e98b70c297a6a10ec7ebd1069df313bb271f130d0c036102037200077c01630214f2cc82fe9394eba32a87e9e4cf94d8eb01b8a5d6d4cdbaab7a8ec5ffd7b901c0e8d49b318df122af6117110a03610213968191a0cea4a38b1193d8cc88fbf884b906ad8cbbd298e4d6ed11c7afa99de5e2e741b0d2a2a1cf8f0afbd6f4d7d3068883cba7029b8cd163815929110c03597300110190015d020bf2c9adec8fcddae901a7a6c595c0dcfbb703a6c6f6dc9cd7e702def9fbc9cf9501adeaf3c3b705d6d3b101e8d702c302ab01f759130d010e03590212f69db2e2a99ef3e70cf9a8a9bcc4d1e3b94e91bbb8ecd7dab902b4c9cef0c4d78f05e99ebc8afab304a9ede5e9ef01ebfeefcd6ec9fb01818b02f917110c03530205018100080101050701050501050900000000000700
    (by decide) ⟨24, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock2 : (⟨[⟨3,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨41,1,true⟩,⟨43,1,true⟩,⟨53,1,false⟩],55,4⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    22 3497 0x50905090187024cb8d0aacfaedae88906e1c0ef9e9ee79be939d3e0f480bf85ef02999affb6d385c303e6f2e995c3e301bb81f89d4adb4935110a0301830252bfddce8bf4a6a7f304eec5b9a4b8a1cac504b2b1aadee6acd305a2eca39ce4c703fcc7a3b5cb0192eb82ab0f8fbd21d302c349350d0c037f025ef1cf8783cbffcfb905bab59996e9e6be990af7d7c3cffeddab15bdac9ba891ab04bde19ce1970495cbddf967a49348b529110a0371025bc3d7cadf9bffd1950cc6bfe7c9b5bfde9709ce98f9a0aecfc704d0f6d0e1f99323b19bcf9704edd19367bb6d491f1101e000050adb0159ecdbeccd83ffd2830ef583a9eeddb6ad9d019dc5d292cbb9edeb02eeffbbc4e3a2b102e59ea7bb85e14bc681d8a709c799ef01a5ed6b130a036b0256bee4b0a8d3ffd3df1085edc6f7f3e491a30798d8eaeadbd099b301c2f0d798e0e1c701ddd69ed986fd2aca86948323cbb5e315ba9518f902f92b7700054501670254e7e8d296bbffd4cd0fddfce9ccc8c38fd90ae1fde9f7e0e3e98724dc9be3b59a96dd5bfd80f98cbef723d5b78cc39106eb99bedf02dec7cf01c5ef6549170d4200050dd601739485c2a1a783fa8515b2ad9ed9e4d9953cb8999e8280d51da1d5bf91f9109ed9ecc105cbbacd7ed36147290a03610269d4afa585be9a87dd0deed8b9c8c4fd869d039ff4fbdaebd3bbc729aa8c8c86c49306b4c8c7fdfb019486b5ed0189ca9732e1592b1166000504a2017c9eeea0fed99baa95048ce2e286e09e8cfb02d9b5f2c1b885d165feace2d3831bfe9cfbb102d396eb22af532b010a03530276a0bad6f5c0eeeab90ca7a4e6efecd7feab01bfccf2c2a68b8ff703d6ebc6d0aec3e565e7aacfdf8d2caf8990af0ae6fdd571ed02c31d17110c034f0217007d024fb7f4eeede2b6c4bb0394a3a3cee49ceebb06c388da8bdfb5a5149fb0d6d784a10e9fd79394e93c8db7bb17b8af02c3714f170d0c0371024ccffea99dfed4a98f0ae2ebddddece695b318c2da8c80818ef52b94ccefffae910c83f0a7928504dda19fcd01beade111992b1f0a036d024b9c8386b68ce39bb90daad1f0b8d783bae701afa5e9e9b5a791d3128895eee7e2b495099e9f92af8df509b081d887f1028b9488d301b6a685029c00063b014f2b0d0e036b025dccdb8bfaf3b9bec901a8df83e38ad1f7ef0bb1eaa890959bf908dacbe9d6d8c702bbe9fbffdf2dbbfadf12b0a535000909c50135130d01100367025be489e59a88e8ebab05d292d282f987b3d906f5fcb59cffb6d716bba794f8fc8504cfa1d8ee9730f5ad930adfef36000a048801654f473b1f170d01140365025892e797d8b3c7c4ef0c8b9280a09f85c3d5028eaee1a683bdb4e909e2ab82d0b1fa930786e59ce1cacb01b8a9d9d1bf07c7fcbb0281d54f1f0d46000509ba016afbdaad91c5e1af9104fcaca7a9f181ba9d2eebf0f6c4fbb1e36fd8b3fece829344c5e9f3fb10a698d70593c302f94f170d32000510b7016ad1a29dc38add86a90cc2c5eacbe1d2fac346c8ffd0adbeecdd02cde0b5aebcdedb0bc489e795b102e3a3d8eb0adfef19a73b1134000609b9017701000a09b90108b2adc399b5c2f1b50cb7b5f6fca1cfe910d499f095b5d90581e8a3fcef0afb87ed03aafd02c3713b11010c03710248a8d5d1ac96d090dd03fa948dac968ee98923aad19eedebf7cf0ceac3c19191b10e94ede2e305e199e906d9c302c302ab531f110c036d024f83c2b2bfa8fbd79532bd90ecb5cdb98d5b809eafd0b58b108df8a7d7d50395ba9aef61f2f90ea5271d170a036b024c89af958bf3ffb7990896e8c1adf7fadfc175a8d589b2dfcde3028ad2a0cab0c3b102c7fdcfb4bcf51eafcfcb8301a5b1e3018bfd02ab01cd000502d8014acca5c6b299c1a79b0d9cc0f09ccbcaf7c51f9be48cb7cbd9ad04e2c3a2e78ba701f39ae6db8735b2b99108aee102c301dd290a0365025cce8b98f1f8cce3f3018ee980a6b1a1a7e10bfe99c2e2adb08f07b9be9889fbd3059cc1ece4f5769ad59f0b82cd65000a09f801612b1f011003610254fcb791c7c788b6db0fe1e6a8f3e59c9aaf04c5b396d18be7caed0789e3e3e8a7f2db0596f8c7ebbadb0a92ced396df04bd998ad501dabebb43df130a45000509b8016f0233b485adbe9fc0d5f508a6eba1aee18ab98b22eab8fbd9d8a78133f7808babe5b30180b0ebf5cf0191c8e79915ba9516df351f0d36000506d6013fa0f0b0a3fac59efd1bdeede6d4eb90e90185e188d3b7bb13fcc7a5957b8cbd58cb01f73b0d0127000d09890108e2bedbd6a2c7bce361b4c1a8fbf3b4d703c6c3f6dad2dc9953a98bf5e9ff05b5f5fdf501dfb1ab0fff032b000506e60147eda9caa4dfe9dc9f02898bda87c7fdeddb01dd9fed80aec19501cbac9debdad57a89ac94b30e9cde930495a702c301f7170a0365024ce985e1f6fea88fbd0487cbeda7dcc7e6a304c2b1eaf5c083ed02d690b6cae1bb01cff7a0edf73a8ab79103c597611f130a0361020b0067022fd18d97adf7cedbad06f6d7d9afaec8a3f7449ab88dbed4aa9301d0be8eeaafcd9340bcedaed1e91ba88482e10bbadd9d04a7f9472917010c036501aa000c0add01790249af978ed4e1b59afb01d598a1d6b1cbbcff03aaa6add3b0e3c76a94a486d7f56bf59bc98d0b8fa8cf08a08111f33b290a0371024ee4a2aab2d593ff8101da9ec4b982ddcfe52fb2acc5caaeab3ef09f889cd711b3b7abe908aed8ab1ac502c32b130a036d024dab9e96ea8d91a3b705dfecc2d7cc9994cb0f99a284f0c2ad9917f1e792d48ae7028cc4b5dccd0e91d7ff01d7816b4f170d010c036b024ab995efd8fd8beca30d998f80fb9ccc94bd78cfd5d5b0c987ed06dacbd3cee3f48b02f9fc80d7c5bf0281cac3b4e738a592fb03eca901d500084001674f3b1f11011203670259fd98e8cfe29497c701a98ab598b09491bd06f1b29ff2bab2bd08cb9accc2d4fd01f8ff95ddfb02e9caa303e0e538000802d9014f1f010e0365025ad0d0ed8bc8ebe7a105c98ac4bfecbed4eb4a9b94b9cebcfbc13ce7c98ff7c1e70e8cd5eba9eb01d6d2d8f54ac3ef02f902c36129010c0361025393f0b9eef3d4b3990fb6d3ff93b5a7fdf50985c7a79d84e2bcc902d3878fa68badc50191aee3afa28d64bdd9d50e9bd91ac535290a0359026dd1e0bee79d87aac70684a0e0dcd182eac50f9790a2a4e8ebe328efe3fdf1e78106f59fd1f38f0fcad1eb02e5a5534f0d0a035302110073023ea6b8d5f894bdfe8d09acdff2a0c19ef319c9d29ef0c1a306a0dcbd8deb029398ace32d8fc714a702c31f010a0371023c8c94d7b6dec2cb9908a9c2a0ffe7d894cf1eceb5cf9ec08cf70ecef197bd9493058f93f995d102e6c9cd8901b79cfb52fd02c301f73b010c036d023aff82d89683c4f1df0bb6919490bebd9b8f01b0a3dbd4e680ffa10196e7bbf89b89a710e3abc49fdf0384bda5bf028380d502d1000801e3016b1f010e036b0246a1c3a380c5f9a6d907e3c3fbbc8cc5eeb705fb9fd781d1e0b97e958ae5fadd1ea69a90a901b1cbcf2fbd01dd35350005029c014cd9a199c09deae7b504c2e2d18c85dfb6d301998d81aeaaa4c7018386ccb8e7e107c1c7bf875e9b9f02c302ab65010a03650249d4babfe3dae09ef10d87a1f585d880e5af62a7d296f68f8dbf03cafdfc8da7b3a903f0be8ee9b2b101cacfadd58344d0b102c302ab6153130c03610257aee7c891d7bedff50bfdb6eface79794b75dd0ada9ebb0a79d4e84c0cf95fe8306ad95b2ecd301eed0b5af148ca302f901a1000803f20159532911100359020f006d0233f1a19ad492c4a6ad02e084f1b3d39eeb8b07c1fe88eabbee8302aed4befccbbb4da982e88d0ee8b1830199d501f729270a036b023cf298b885f3c8d1a1019bf6ccb386cbdba912fdfdb2c28ee99340c0f4c6cba30cb397bfd101b88ead4997670d010a0367023bdaecbbf6f08aaab306a9e1f0b6e289d1fb50a99491cfb3ad319f9fb9c28f1aead5cd9d06ddd8dd02d8e902c301f701a20005049501650246f9f2acdaafcddcfd02c690d38c9a9684ad0da993ef99fd80d115e6ab8fafd6b115fafc8398cb06a3aff99140f7952cdb1d110a036102093a00070299016b0238e4ded9d4cdc9beeb46bbcf85b2f99d0af7fd98b8db018dd4dadb03da8101f72b010803670237d7ccdab3f2cbe5b104f2abceff80fac7b512e4e6bfe2e2bfc505dd96f8a8da952f81fe9ce102dae4df35110803650235bda8dbf2bcd0b2bd0e90d0c4e6cbf9ebf97af7aea8a8eb819d02ec82e6ebd49bbb01b5f1dcb089a316c2d6c4c50294ef8711f31d010a0361024991f0e6e2e2c6e1af0aa49099a883d5d4d370e5cce6fcc7e5b502e8d0dac4dea8f5059de880d8f5a301aafd85e0836eeca4a70cb8fb15c74f13010c0359020900650232f3b696d8f4a7c1815abd95b6baedb2d108cdecb0f9a5b3d3039bd38f8f80d101b59be3b7914fe39aeb06e38702820006018f0101dd1d11010e036108000f029301050905096502149df0c9d6a1aad8b1128da1addad3dc8bdb0295fdccccfac894870798f6d58ee3fd8d02bcc5d4c8f3c92d84b3e6b530a3f33bef02c302ab1f170d010e03610239e4cbfce9a2e89af34f00093a0105b883c1cdb6a9a55ed7c6f6e9eb11b5d9ad9704e3a6f307f8f902c302ab01f759350d010e0359024898d2d3ada0a893db0280c6b5c59fbcba9b0b8985b7abcff7f9019c89facd95ff13efeff98106a4bdf508c0dd2fab53290d010c0353020700610213c0ccd9d4d8addfc511b9e6a7e6dcc3f0b709eecac382b4a6aeed33f9b9bdf69faca502a4a6c8e9d2acd5048acea3a2c5a9018f91fa8f8337c0f3dd24d78728bf02c35935170e0359020301ae000c0101000100
    (by decide) ⟨27, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock3 : (⟨[⟨3,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨41,1,true⟩,⟨43,1,true⟩,⟨47,1,true⟩,⟨59,1,false⟩],61,3⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    21 5480 0x509050901990270b8d0aee3c284b0dd0ac6aba392b5ad9cf11cc4fcbcaab5bfa106ca8a8ce9cbd105b8c38db4fd0299e2f781099f9d36000802b701493b010e030197026ef9ffcf9bebc5cc870c88c1e9dbfde39ed772c781a5cc8e9e8d0bb8eab3d999ebdf05fc86c99ae7f504fdbdd0c5e512daf5db08d0d901dd110a0301950267c0ebf1b5bb8bd4d91399f7879283b7b9b50598eff9d0b28fe49105edf9abe082c0d906d8c4819cb4fd08a2b59ad68102afb1f197018c96f952fd02c3018b290186000506c00166829b91ede4ccf08312f6c89c9bf2e7bab707cbd4f9f2c8a69f8d1a88c6ffffaae9c106e2a4cdf1e7a502e9d8dfefd70ec7cbbd0281d502c31d17110c030189020181829587e8b691dbb70289d5a5edb5e7ebcf01dd859ca3e9b7d538a0b682badb12e3def3bb5c90ad52fd01dd6e000714d0017d89f593a6d9ceddc307ade19fa0b2b9ab931fd0d3818ba1d7b720ef939d85c8f10684978c8dc50297eacccd25fed52f000906c801493b171110037f0276fbbae7aad2efcf8f0fce969992aba7c6cf03bec181cdce92a4cf12a4d386fdfcd6e711c3e39f958edd17faaa8cff8f0696e298c901f7f2bd41000a15fe01714902000705fc0111011803710272e0b7cbf1d1898f930f87b8c3a68a87c8d308e9f0cae1adcfbc9f0192aa93a2a4d2b9b93dcfaf95b8f28703e783d697b71f8782d104d7cf02f940000511850170d2f5fe959095ef950ee489d8aff9b7c9d50af6bee8a3b8aed2a3028087f2d29ac5eb811bc5d4b682be81e53cbed2daaaf78103cc9585809d33e896e30ae3cb40000601bc011301000510f5010188dcdecff9dabbdcf305abb1fdf482b98ca90b97cdf9f1aee1c120aea6d0e095c30db48bb3a7830a8e9ff3ad02f5b4b701b9e102c32f2738000506ac01018688f5d29099aab4c90896f9f7e2b798a8c75392f0becabee58d05c5b983ecaa9eab6bbfb3dade8d3693ab9da509eaacbf06f89d28bf110a0365020180e1a3d6bd9787e3f50db39fc1e1a6a7cedf02acce8cec8da7f7af01b5dcabab9493fd01ecb4839af3bd7ce2e4afdd35d4a8df0f8fbd73000918f8010520a601018f81c9e5dfb1aeebc904cec0a8b8e0c7da9706b2d7b685ddb9810ca1e89e97b9ab06a9b09bf6bd1e95e9d306f89d2f000612ed0147170c035902019587f3d4f38993dc8974fc97dec68a9db508d5ccd7fded8df103eafc97d3909554d5a9c9e5209ce9d102f902c31d170a035302018df0b1f8f3d8f3f6bd0888c3f4bbd4d789a701d3f296b490b4d49d02dbc9e4c29fd7b105e1d5e4a695af0598c0e8d98b6dfea6db22e2d727db7400053f014f021f00018d026ae6f58ec29191d4c50393bbcbfdc7c9fbc70ae8bcc3bb87cef321b2a1e9e5b2a72691c2d48ceb02f9d5c6c94180eb24b502c32b0d010c03018b026eb3bed7dae0cc978571fe9bb39fd0a1f7019fc2f7f9accaef01e683df8af3d310cfb8addf05bce1d502d48901891d110a0301890269c8cbe9add5e9c5d708e3e1fabdd997a8cb59fdd1b3f8f8c6eb049bdaecdecef3af0191c9ec93f0e5678ae192ab09d38ff103c901ab000506db012b1f0c0301830266abff9fe4f9a7e4e30e84a8ff9cb2f0f4910191eac1dd81e6d8a90aed9da5eb8d97b50ef4fcb19c979b08fdabfca0b17783b9cb1be2ff3e00080185017f4f470300080f80010118037f0278b7ef8fa6b6a1918b05ccbdb29cbaf8c2cf2fdd89c7b9d0c69901fab48bdc8d90af02b49cc4b1c3b101f1eba1b7875d88fca519e5d90f871f033f000504d1017c97d9fc9ac4b99af504d981b38bc295edbf07eee0c2d28eecd102fc9e9597a3a702dfb8ded4ad53aef1851acbbb2e000a0dfb01473b2f1f1312036d0279f484f8e0c0ebeaa3088bc187dc9cf48efb1a8ec088b0848aa71bf48cb1edbba106f5c4858b8769c0c1b31eb8a74f1f3900050dfc0175acdaf1ecb9d188ff0de3c8abb698b1b5f501c5f4c2c2a2eba8db069ae7fca4ed8bc504c7f089d9ccfb05b6d38bce8f01dc8e88a10197949b37fb47113d000507e201738985eeb2b683d8ad0f8ce2d3b4afd0feed03dea9a9fff5b6ddcd09a5ca86acc7da912382e1f59995c5099496f48fe707b2c0dbc75bf1df6de502f92f130c0365026ec1dbe7beaee8f7890ec09cebfeab9b8bc90adbff87bbfec68e8f61f6f9c0d4ccc8c9329d8fd4c4a2b929c0d894aac922cfb2d7c10489b7dd02daa101f70a0361027fecf3b9b58d83cdab0da7919d92a2afa58131948792acbaa6d515edb9f3ebe9e5039a8f89baff029b83b5a528cbe1108b4f0d0a0359020190aad0c394f1e5b4e578cad4ccd8aad3e105f79d888bdf81fd069cbeb28fe48903aabac6b2d5118596cd0cb48311f31f01ec00050df501190001870260e0b5e2f3e6e596fd07b8d2f3f59bccdab119e1fdbc85e5decd3397e5aab99ae105ebf4a5d0a9019dbc96a157f9cd64b901831f390005099b016bc3a4bcf8d28b829702eeeeeff8d6eaf526a2b997a39d0795aebeff05c1bcab5ba747170d25000509a7015fd689a389ca85e2d911dff2d4d99dfa8fb5058ececcbcb698abbf03deaad084dfedbd06f0f9bdb6a6c90386f296f78906a5e3d50998e502c3712f3b00050680015ca4cad2c5a396c7b5118fbce1c7ace0a3a10bdbb7868f9192dbbf4bc8dbd1f4a6d0d51ea28ebbbbec870b87b2ebd5cb06eeecc0e70e9bd9288302c32f130d010e036d0277e8b79f91c6af90c503b8cfb4929782b5fd03d799c6d6e197b702c692c587a0bb1ae485a88302a1b9cb0194f171000508e701dd1f0200050388017ba5a0a6ccd6bcefc30380f4a6b3e9918c8b11b5d59bfabde9b70be8a6b0a3dcf508efb8c9ce81169febb707b58901f7271d0a03670278f2e8ffa9d188deb9078ea4a5cddf8fc9a903db91bff790a903b6ede383850895d5d307b8b302f901f73b0162000503a4018dfab0e3c6a0bca50dd0f6c3f4f1b9989701b387d2a9a5edf1a70288dbd0e490feab05c185e0c795cb029cefbfa55ece9b1ebd030135000509bb0186a9c0caf3ded9d4bf038fecd58bcfccc0bd44f5a0e5c2bfd30eeae2aac7bf04fd96849101d1b901f73b0803590213007d0266cbaaaa9ea8ebfcab03f285c1d4d0b4b3fb26a7e7c1cb8df0a7168fc0ca94dda104aaadf5abad0485faa35fe301dd2f6200050ab80162fac0cfa0d2b8c9bf0ae1c38fdff39ea18f018ea8ffb9f2c5d5d704f49686b4c09983099ab2ab9490b102cbe6cd959948e1e89b02f8cb6d1f11010c036d0261928be1e1e79ef0890da98197d785cc93d302b897d3d4b8f4da9101e0dcb685dda3e902fbd89bb8f9d701b3b1b682a1528bc5e11d86c102c301f72f7b000512ac015dc1a286e490ebbd9d11acc5b9b89ccdede905dfdefce2d3c6f2bf3181a8b1a2a8b3a901fc8df8f89dc0e15db9d58d95ab0cdde6db9b02fdb8936de501f71d010c0367025bd8ed99a5a5d1e3e71181b6b78ab2b5fd8b09fcb5fcfda1fcaab72fc2a0e082df959106f6ec96eeedc7018694fca7d12c88e1af12e98117ed7d000516d40174bc9590ac928ba3ed06c6e0b7c1b889bb950ee08af4ddcbc4f109bce3e893adfd59b1de95b319f7b88504ceab02f902c32b13010c3500050ddc0173024dd9b3aeeae8d2f9810c94b8cbc9b5b1a7d30193c5c198e59184a3078da1b18bd49ab101e5abeec6a2e90acc96c89b0186def320e761290d010c0371025e8adbf587d49d80a102a5dce3d1ade1beb9049581f586eadef50d95a0c790fec70a948c9fca9103dba1abb752a3a701f7297100050d99015cade08cdfcbd1a89706c182959edcd2d7bb1bbec1abfea493b547b0d1c2a3b8b901f2a095a2e501a5e3e7d308e18302c302ab6b2b1d0d010e036b0265f593edc0c690bbc502b8cca18996d9ef83099c9c8789b894fb06a0bcc19586bb02b3e98bd4ab0be98cad01a1c5672f6c00050d950163f7ecf98690c9a7df06fab7ce97d6ff9e9319f99afeba98c6fb71d19f84b6bef935ecb6f585bb02b4f4bcaf018ca2ed1a8902c301f7290d0c0365020b000509050942000c14a10101890267bf848dd8b08fe6e304bffacec187d495950fe9f8db81a0e3dd35f5e095cbccd505809ac1c6e50296fde0850396d102c311010a03018302699d8183ebb2e880ed05cffe9c89ca929f8b15b5c6a0c0cc8eb306a0dffca588cf02d6eefde9b103a2c28302ca8d01dd29010a037f025dd09e92c4ac9a82e311afa8f68effc1d29709e8d4acc090b5e68d2baad0fde68ad7b10293b2eac2a9daaf059ac1c1c5daa369cbd6dadf149ad3ef01deff4f2b0d0c03710277b986d0e5cbb78af104c48fe1c4efdfe3df0be4a1fbd3eae4f139c1cfe4b3c134b59dbbf51defc4eb07839f01e200080182016d4f493b2f2b291f1d170d16036d027dabcbb29edbf4a3ad16d3c687a2f1b2bb2aa3c4a9b3b2cd0fa6ccb5dcb1068ff791d903b0b1af01cebd02ab133c000509e60178d3ea88f1a7b6c191078cbaf8ff91b0b1814eeb8bdeccfbc5fd06c2b9bf8d8be6d11392fbe7afccb30b80f6c985b501c2f4dabb17e3f737000a0587012f0d011003670276a7f9b49acd97d0830bbce7e8b0e89e8f850ac69e8bb9c3fff70cc1d494c0d3b305dad7a8e5a901aeeefe831ef3c712932b130a03650271d0988aed98d9ede70ef4c1db99aad091a7049db8a2cab286a6e13e8ee09bd4eadd24ca87b8eceb019d8e9dbb2096a12cdb0d030a0361020183b9f1a5b2fefcbfa506f5c9aab1ebde90e719befeab8b8e9f9f0fddf0c781e0d303e592caf0fd01be849ad729e7d11df3591f0a0359027acbc791cf98f6fd970ce187b3d2b0ace8c507bda7d39ed1a7c1d90be2e286f0a2d49b1b888ed18f938904818daa96a726aa92b70bcdc917030a035302150001830260b8bce0d9d1efbeef03d3c2ad908ab69fc90bf59be9c9b0e49b27acb797f79301f2a4b8af019ba8b901a1c502c353110a037f0262af84909dd6f9a8970dbec3e3b3cba3f38d65c7e099cfdcbbbd1a86899ac4fb890c85a1e4bead06c3aea9db019ba8b9714902d6000503ac015ef1aabf9de1bb9ffb11cd9ab5b7aab48ecf03cdc081d8b8bf8de50f8ccbaab9b9a7e702f3838bf6bfed36b0b7d7b71df997a901b5836d5317110c036d025d92bdd6dde6dc9bed11a3eebdecaae6e9f9079fc78dc69a9acdbb28aa8693dfdfe1fd6bb4ceb7b5b0dd7fb9d4f486ed2ea6e490fb0c93dc8303da817a000601aa016b532b0d10036b0276cafc87cacfc8f4e702fb95c7efe899eda162a48497def79938a9afd9c5d504b0d7c1ef13bfd701dd110803670274a49dd89b98cb9ce506ebc5c1b6a78bfa951b81d785b29cbd9304ddb9b8b9e9a905a0eafebdb9048acff58102dbe3fb3be902f902c30d010c03650277b0cd93c0bf9bfd8b0782edf9cf8b9fe1db3ecab2b1c2f48ea74edba1bdd3a7d307def8b6a69f05c389939d01b9a0db02f901a400080589015301000503ac016dc4acb2f1a3c996b30eafe389c9aeaf9ff309eae5bcb8f7a788ad238384998685be9f31bd9288dabfbd06cbcec3d5e12bf0b6c70ff3b902f939000604c201491f0e035902110079025c81d5a6b0e9f491a307ecd0b9eee5beefcb01b4ada98b8bf7f332f2bcd6d2a309fea5868f578ac71cc1490d010a03710265dfa7b2ebbda9f8d102be82c888a286b7f718db9481d4d1f79f3596b3af93cded0a8eb3efc9df0ab7f5a9a502b59f9702869102c302ab6d2717110e036d0263f0acc5efb0bae4e706d9efa5ffdcbfb8b50fa0e687d9c5f8e32dcfefeea5ffa50598c7bbc7eb52a99acb3784c123f96b591d110c036b026092b6ebf796dcbd930d97c0babbca96faa101f6bed0b9ccff84f51495a4bf9bd3a909eb948c95912983b9db04cc9d12c11f030a0367025ea3bbfefb89eda9a911bee1b6ea9e9ad3c501dad18195d0dcc4d70786e2a6affae0a704f1ebc4a8849502acd7cce4ab0182f39ded2adfa143df010a0365025ac5c6a582f08f81d510e68cbaffb082e4c109ecb3b8d3bfbb81c571f68da0afe7ccb75d9697c4dfa9b34095f3bb94a113b7c4c9ff03fcf7eb02b1b36149170d010e0361020d006f024d87cb90cedca6b5f30bd0af82c0f4dc9cb702f2e6fdabd78e87039baf82aba903f1dbe9a726eea513e93b2f01039e000504fe01d2cda38cd8a182b50ef6cecdc7edbaa8a50188fba5c0e7c092c5539997a3bde0cb5ad9fa96ecfb29dab5a10cdc930d8f0d31000504fe015bb4aff5d9e7aef9cd0683a2f7cd81b6e68b0aea98ccc2b9b8d92a93fddfd69ee709c98a8dfde9028dc4adbb27db01f71f31000506e70161fcbaa5f5d9c9d68b02bb94c5aa94a3f1f70393cee28cbd99f302f686d98fff930ea2df98d503a0e3dd05d4ef2d000905ed0161493b1d170112036502090005090e000a078a0179025ceeb7bef1f387eed702849aafe8ede2e3f301c3b087b9e9edcf02cef884fce9a101d69487a4870cefd8e50dc6e526a1710d0a03710261f49ff399bedcfdff01dff185adb8ecfce306c8a68a80c0a4a307e7c6ccf1b2fd058ff59c85a90eae808b04aaed02c36d2f0a036d0264e6b4dc8debd4828b01a3a9969dabbed185049fc1838ef6f58508a3ff8fea9a8101f5bfc9f4a116f4f8c5119adf148d531f13010c036b0261848a89db8aa9b38709efcab2c4d4cadcc57aa78bacb3a29311edd2c8e5ef01b6c7caa10ea51f13080367025f92f4e0c1d9d48bc50d8682a7e3ab8efaa7018bf4adef84eab8dd0383fa8490c99a810490d696bad1a102a784a7d7e523afe0ff08ff0288000741012f0c0365025bb0ca8e8ef8a9bcc110f9fa87a0a7d9adfd05cefdba9fcfdf9ecb14f6a4d4dff6f58f04ea918bb0f6fb57ea8ed4cb1b87beb305cacf3b000601dd016153110e03610276c4da90befcb4f1d50593d7b2e6f4dbabf30394b0eed6f8eee5099cc6b2bab49f069f8cad89fb698d86e30f8fbd5ba702ab010a0359020f0071024cc1f893bdbdc1f2ed08c8bce898cec4e9f101b5bed9c59c8a8f4f94bab2909503e39a8c9b70f1f737fb6d2b1f0a036d024b8e9deff2afbbfeeb0be0ced8bcabb5c3b10198e2dcd7cfcc96a940fcaa98fdaf8706dfdeadf8f53a8cc4c715ba951cc12b010a036b025ae1e0e6ee9de2cdd30399d0b6a9f4e18ce905a4c4e7edcbbbf1058382f8a381fd1fa8ec8eb913bda8a9059fcb01d7000601a501674f1f010e036702598095cda0a4d382e907f7fffdf3c9f9a8c904e9c3e4f7abb2c174f1cecf9ecb6bb08dcf0194c6db139129270d0a03650261fe8ed994d2e0f3e304f5b4a48fcdd0eccb0286f4a795d4b08f4fb0b6818785018dd4b08b05f2c102c302ab3b270a0361020b0067024da2edf082e0b5a1cd0390c2e9bd95c7ffef109887f7cffcde8f1d99d5cd85a8dd09cc95bf8f89048397f1830182d7ab02c302ab01f701dd650c0365020301ad000701a6016b024bfbb5f8c6f2aac28b06b789abd0b09f92d10e9fab9ccfdc9db9079dadd994f2f502da89d5818911a28cd103a8eb01dd1d010a0367024abecefef4dedbb3910b9edd8dcaf3e39dfd1ac4d2a1f5e8d7a53dddeb92b799d5168cd78db8b307d4c6abdd69de95469d1d170a03650259e6fbf68b8cb9dc8102fef2b88c94e9d9e501d1bfefa8b5aecd2ba4c8d9d49f36b1f7d106f3e961591f010a03610207019f000c0101000100
    (by decide) ⟨30, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock4 : (⟨[⟨3,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨41,1,true⟩,⟨43,1,true⟩,⟨47,1,true⟩,⟨53,1,true⟩],73,3⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    18 4269 0x1990270b1e0e6808cdf90db14ececf1f4b7d38caf0394e8af92f284fb8302c5a5ccd5affee501dfeef684d9d93c9fedcbb11faf82cd0dabc939000602a901170c030197026ef39bd9d0d0b1e5a114c9c09bd0fe8f83dd058bdedd90a8b1a6bd3a8ffd90fffad79d0280c6c2e5c283810e91ebf0eab703f7f4d4ff12e6a921e14f42000608ba010195020188eaa683da80aee6c90397a7cac0cdb3d8db0bd78ce5c6e3d2ad2cf4a0e4aaf9b148e1d0d4e5ff24e8c9c5f709ecb0a3038fb702c34f113b000605fe010186eea5bdd5838fded305dc86ebed829df4b711edb7da89b5e6df06c88bbc8685c7069baabdced145d2ec891694df2cb117010a030189020189ecd2b9caf68ea8bb04bd80e89b9dbf8d9b1eb7cea5d1e9c2cb058ba3f492912f89db9910945f000512ac014f2f0a03000506870185d1f096cdc2d0a99709f4dcb9fdf2a489cd1eccf4aeb2a284990ddbb181b9e5c503a4a28299c32c8adfd90ae0952e0009068c014f49352f2b291f1d110d16037f0276f4989c96ceb7abd90fcd9c8ad2f2c5e8990bc49aa9a1b8eba0bf01faae91df8fa6dea70bbfa9b0c1f5f0eb0ea7c8ee81f9e113ada492f79902d2dfadc9699fad4f0009119a014f49352f1f01140371020190cfade194d488a7a704d591ff80d5a5b6f904a3dbfae996c48303b598f1c0adb103a1bafef4bd6ff288ad0f9ef763816d2f273e0005068401018dfbd9c5c5ccd3a7e107bcb3efb9c7b3c5bb3d80db8bd0dad0fd02a6998ba4f19a8d62bfe3e1a19b11bfdacff901889af72cb1351f0a036b020188d4b18ea7bde9a8d50e9cbcdba1d2f1bcff23bdd184bf9bde8925e0c1edd5a2df1f84a899b1850bc3fbe7bd02d8888d018cef1d1770000514c6018680dcf2d8b6b4a98f0df99084fe99adb4ad03e2f0ccc6be80eca906b4c6dd81dddae50dc4b4cbc59af9028ca08a9ed530b5bcd306b6db02f96535110c0365020180d9b4bbbaa7caaa830db2b6d8b7a6a5a38909f397dd9896deaacf7ecbdbc0edadf3d502e8bccadbbc98ef04f2ee8fa592dd03efeacbe1bf02c5dee1617e000515d8016102018ef8eb8caceaaa9a8f0ca583ffa9c09580c11cd7928fa693b4e52ebc96f0a3f28b02e5bbf5abe101a9a8b2dd20b28102f934000802bc01592b1301100359020194fee5d2b4feb2b5cf07ebdcf6eeca82d3d53988dad5879aa1ef0392f0f1cfd2aaed018da1e7b2dcd12b93afc0c309e3c3d301ea9301dd2f0a0353021d000191026cd98391ebc4e3a6c31495938ef2ade2f6f7028dba8dbbd2ad8bff04e0e2eefd9fc8e910d091aebdf5cb0da2b5ddbcb342d793e90e9fa522af018b35010c03018b026b90eb93b6b5fcc9f113f081ac92e4aeeded04d49af5dbb4b7c0b71bb6a8aa8ae99af51ed8daec9f999b02b4b0e5c3f16bddeaaf1ba1b102c301f729110c0301890266b8a3989789c8b3fb2087ebdfc0efb9eb91019ca788e6808ccb78a58d9480a13ee0eacefd01e9de9301b89b2b08030183020183acc1d5dcabd8a6b104c7d1c5e2d5c1c7db2cf2caa590b6a3875ba2a2b2b4d5a323edf8a1feb513f7d1bba30ddaa99105c79702b400080be6017f5349352f2b1f170d0116037f027cf6eabae2a584d6b510b2ac8b97f3be80f50188a2eaefdccac6e301e1f2b8fc80e79110d1ca8ca1c901d7f489c1448c8b3f00060b9f01351f02000604af0178c0e4b6b684818ea10fe888c5d8e0d5eee1078babc6fbd387cc915880afc6d28eeec707afd8f993a0abbd07f9ac93a2aab303c39c918aab39f0b3a70ce8fb1ae71342000504a00176a5e1b49ff3bfaa970fc2f6e2f997a1e5d70acfbd8788e7bfc5c948bcbdfacf89e7d10393a9d39fa1e8d70688ccea8c99c1049e8cdfd58b01a782ece501b9bd9f148d01f72b0c036b02018fca89bcb39a88c9c10387dfd9a7d2d2dfe112a085a2e09fe4cf1789d9e5808cb502c7ccc4c1af748da8a113d3cd02f902c302ab7f0007079a018ce59bf6f0ac99e79306c8dfc6ba9abbf0e924c6f7f7b39eb6ff1a00080bf8012bb9b09595a710b78885cf0292fac701ea9365350a03650201879bc0ebead0bca2b70e899df59ba89db8a5108991f4f4cb8eb1088ff49fd9d281039681908dc150d99c891aefb91bf12f294b00050b85019697a1909bd495d49302d2c086aafaaed2df0bf4efa1a5ed8ae304a8edabead7a5388e84c2a116afbcf90afd9d59531f0d010c03590217000187026dec939d81ce8eb4d10bf98ba1849ff6838150bd9cd7e6dde59b01c2aeb6e4fac38f01f3bde7c78138c7fc971aa3df24ed49010a030183026abeeaca86b994e7e511d6cde6fdb8d2defb66ab96e0aaf9a1f954ca97d7dca9eb26bf87ecfca9238a9daccf0bb7b4bf01cff302c37f350d0c037f027da8c6bcdef4f992fd07f0d1a4a386878ccf5383d1a0a2ec85e702b1b4e89fb4d3b107eeefaae7a2b302d0b4b193df0bbafffb05f89d0de37127170d010e03710201819bea92a1a1cce183078e94d4898efbbdb909ecf6e4d3aca1cd03a8d4f5e59ad13c85dfe3fd0a98a3eb02a79d02c36d590d02a300050cf6017eecaca787fef6e6a509e0f9c7f6e2b0c2f9018184d5abbedfc1f10889a6baffadd0b708aea4fe8ecb9103ffa392f78701b9e385a907f5896b35293b00050386017a8db0d0d5b9caf0e91082f580decee5f5a90282ed9bb7b7f6bfa308bf99ce9e96b8c704c1d0df83a09302d683eee5fd1aeada8512c12f130d3900050ce90177ddf2e5bc96f4f68b0fdb8bcba4edc9ebcb05f2cafcfaa2cc95bb12b3e3ea80ec80c326c784b69ec1cb08feb5e1eadf03b8dfa481309dc352fd02f965491f010e03650272fef78f89d1c980cf0f8bb8e0b1ab91d88f0dc0918c91998fe9e537dfc2baae9db4fb019cbda7cfe68a990193efa9becacb76000501c10101c083ff3be902f902c35911010e03610211007d0267a2b2fed594bfd1831394a48d89b6e2d7b70798b0fc80ad8fb106f6c6ffffbcd96e8ec8de8513bda8a905a68d02c335270a03710263cebee3c3b5e0bfb712bdbcf0a5b4eac29b07dffcd08fd89c93c11dc0b78f82f4eba909c784e7d2e8a30becc6d2f7df04c396d4ad01ad89914e9d018500050c9e0161e4c4d5fac6b0f6d1129289a1f3b3eeb7cd0ad19bc081b8f1a58101a5b0e6a4888de1e7028dafb4ee97f09d5da884a1fce903eff4829d2fb3852895491d3e0005079b017cbfa49c9fa1ec969306f3daed97f8f996c307f1a1b28ec2cf9703f6bd8bdca0db03bb8ec6b5d7259bc2d101cda12e00050e820135170c0367020182bfc0dabab2ee96a302dd9fa0b884f89fa503f7cdc1b7dedcf902d7effddb89ff01b3fbccc5976599958b17e3f701dd0838000909e90171026df0fcd684b7ab8d9d039fe1dcdab1b8a3af03e89e9ad580c28b03ed86fca0cde101d1cfc4dced09c491810798c502c3492b0a0302000000003b000a0e82010187026eedffc0df8dedf5cd06c2daa9baa6bb95fd05f3f7a180a1d5c505c8ba9890a1dd04ae8e89cafb53ecdff10ecab502c302ab531d170c030183026bbcdbaf90fbecc2910bd88ba5dc94a198c101809bdeb6a7c0cf9701cfdf95e08c94b9028385f2a3c5e501f299f3b9c559ab99b91c86ab148d7f4f1f0c037f027ebcd7e0b7868d94c903a689e9b793e0a1cb03eef3aef89ea2ab06c7b8dffbcbe302cefcd68dbd228d8fc305c1af01ab000605920101dd71534f2f130d01120371020182b4c9ce97b3d78fb7028ab5dd8dfc8db7f307d7a2e58bd7f6c301a290cef9c8d918c79e86ed0df4dbcf19a7352f110a036d02018082a583f8b8cda6d105c8b9a1c882bb81d729f4a7cfc3f4b4e70285cdaeedfcb1930abbedc2f3af2caca2cd0d99b71d08036b027b9ddbefbac2b9d5850bf9f29caeac8f81b301be85ddefdeefddc70184ffd7f6ecc09924d3c2fadda505cdf4f0cb39b8d137fb35110a03670278ebb7a59bc7afec9f0fedd4eeeff6a0abdf019992a58fbdc4f4b3148c9fc1def9fdf32ee0aa9883d69d09ca86d8b8b1048eb9930198b902f9290d01ea000503aa017486ee90ddd19c9ad30f9da3f0e8fab8b49308f6d79ee9d58295df4beaa0e6bff7889706e8a4cebfc0b702a498878ed304bbe3a103c3fb13010a0361020186a1a5ecc99b88a7a90aa9f988ad828abe8d01d9c4c3e780abed8701f890d688f0d5dd34c7cbebc28d01f48e81bb02dca98137fb592f0a03590213007d0266c587ebe989d7fbdd0e87e0fbf9b7a2a9af029890bf80b09fe5e5058e8bcce897aebf0aa89081bda3cb078897c6f69b01bcd4e3bf01ecfae567bb01f73501ba000502dd0162f4bac4f1e8bfaaa912ace2f2dbe3a890c5059aabc0a0f883aad303b4b9cbb6a585a904d4fb8bedceed0189e6d0a7d529cabe8d0cb0cf02c302ab170d0c036d02618c93f1b697f381cf1281d6c1d1efcacfd3098e83cfe29d98a1eb0dbdfd8db8fced930e8b8cb3cfd4b90fb098ebdbbd05dce4a6ef0287c39377b32b1f7e000502cd017bcee1bdae88ad9acd04a5a3d1a0a2fd908f0a94dcee93abe8df10d4a8a0ebbae14aff81e6ef0fddb99906badd02c32b1f0a0367020181c9c7d0809fe7debd1f8f83848ad095890bfda0a3dbc38d0385fabf98fd18a0eab70a878d02c302ab01f7652b010c0365027cb8daaacee8878ed908fa9e80c3a583afb70ad5bfc3c2b3a2b1058daac0feedd901a0aec4959d07a798a7028691611f1301990006059001730261bed8c9ebaf8489c306d39dd1b286debbdd07b994b8c2d5c38505fb9ca9c5e1c904b1e5a9c7ab29c1d28f19cdf12ee501f72f0d010c0371026be6bcf69d908bbfb10198aef7e9d1d691d90b88caeebd999ef71afbeaf0fbf2b31c8ad281d68d0ea6f480fb0187d8a702c302ab6d2b010c036d0269e9a5bf9bb5afd88705c8f4bffadab1d5bd109583fbc1dec1830dced9d6e2d6930ff7c1fab2bd4bdeec8330eaa113bb6b352f01a9000502ad0165eef6d197fff889b30dfbf993a28ec5fd8147fafc82c7f5abef2c959cffb3a18f0dd9f197f2d504c88d8ff111fdc123cf352f11010c03670263f1df9a96a59ca28912c482838f91f4b9a535c0ff8bc9f7d8bd21f3f0c3e8daed0480ca86e1d32cc89ceb1694df20ad276a00050495010b000509050906000904d40177026bddcfc3f4f0a0bca9018794be99f3aaa2d702a89fc39e8ae7a303c4cc87eedcf301aa87c9fea75090c8972cf6f527db591d0a03710267f5bf8fd5c6f392c508d29ae6a6c3f9bda14fcd9a8cf7ef81ef04abf0819ceffdc710f9a1dbf6fed50ef8e58c8ab104be8af5c35fe301dd0d0a036d026681b6f5c5f29cbdd30cf9b8f3c9eeb395d93b8ad6a095f996ef13c6ac88a6e9a712f9f4f8ede303c99ca6fb1cb08327db01f73513010c036b026299a6c1a6c8ef93ef129bee9ed383d688f303b1b6a5c7f9d7d8fb048daf95a1e8d6cb09fffabec2dca904e8b4bbb2af1fa7e1f504abc717030a03670260a59ea796f498befd11eecac5e983ccf8c907bef1ebddcbeacbab31f395b3f588f4ab3ecdad8feaf8d50ea9ad8cb28d02a388cee31dfdf90ceb1d0a0365027aa7c3f6fd90b2f2df0482d48ac7fdd891cf0fc5fd98f4c9e39102e6e680be8fa50582f49f8cb903deb69fef1ce3e31acb2f110a0361020d006d0260feb1fdb7dee2898d03cedae498dbaaf88f028fa398c090f5cd03d5d4b2b5d3f9019ade92cdbd118596cd0cbbe70eb317110a036b026685fabfecb987ecbd0488c5a681eaa7e8b91facc7bf99c2c3eb1792beac9faed302db8ab7f89d0acab2d703b4cb02c302ab672b130c03670268f98fe2e598c2fba504a2f6fdd5abfb8ce301addbbbf6a1d3f17a80e4a4ca8f078fdba6ff4798bf20e71d17110a03650207000509048a0006410167025786eee991d7c7acab07c6c8bafdac85fdad1abad1fd95d0f3972da6879ba3dcf10cafdff598b50587a3dfe90184939167bb35170a036502033b00090101000100
    (by decide) ⟨36, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock5 : (⟨[⟨3,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨41,1,true⟩,⟨43,1,true⟩,⟨47,1,true⟩,⟨53,1,false⟩],55,3⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock4 (.nil))
    26 4888 0x19902019dd7a7b88790a6caa301f1fbd495f1b7aaed07ca9ad1c1cd9aeb0cb7bd9ad4edf70de1b0b5edbf04dbece1f701a3f2c343df3b1f113900070aec019bcbfdb0c488bab4f90496a4d1bbbeeededd13e3c394e4d7809709c689ffd5d58704da988df8f302bce08b9d088fc12f000608b30117010c0300050ae8019193ab8af4e19dcaa70e8a8197a8eebaf9c1028accf7f69380a68f07ffe6f1fbf7c29941b1d3ad94f55185aad38b32ace1d71084f102c3018b3b1d3b000617fb018f888183b1d9b1b4fd10e5ff8ae1c7d2bfdf01e481fef1d5e08391038aeadb9d8f96d701eed6f3b9eda73af6ffe1c93ce88137fb3b3500070ae70188e682ece8c1ecf4ff11f9d8fed287bde4bf07c3c6acecddfd80ed219cf4a787d3e1910fc4d69ccaad9b0188e08ae8e112a3dbc504c9ed02c301832f2717110e40000503f40184cfaedde2b294caab1ea4a1ed8cb1e0b5a11ae4f0eab69ee8e743b2c8c6feb0cb2bd0d5b1df9d0db084c2fb01ba96f723cf02c37f35000705e90194e4a0e0ac95eab2970fbdfdcef9cbea87c56e91d18ef393f6c902d4c4d7f9addff109ccb19eeb8cfd03a1f8a48ced15fbce9304f5b936000504ed01170d010e037102018fc28fde88cffb81fb0ef7e9a7f493f3f2f106d9838987f7a2a6a14aafded995c9869d0ceaf0a9d0c7a103e2c4e9bebf01c5fb84f720c3c56d611d43000611ff018cf1879cf6ed83a9ed0ed4df94b1b7f8e8c70a848b9bb684cbf6d937ea9d82acdcac8f70e7cca5b6e4a901aec8b8a4b2e525eee9a08117bdc1f10ea99318b73b1d41000517cf01a495b7c1f986fd99fd02abc28b9bbaeeef8b0bf5d38ca287859f09a4a0e1f2c2d703abf2ec969f2be3fed908ffcf2e000613b5016701000516d801670201a0fdb3f9eaa3b6b68705e6f1ebee9bc18eab0dd39dd192a9d99d14dadce49d81870dd0969da1892de0b28707f8f902c32f3400051fcf01170100060486018b020193d0d0b3e7dd96c79d049df3b1b8bfb59c9b0e9fadb5be80d2a101bdaadde3def701938de3e4a70784fd8d03c7ef01dd1d0135000606e70196f396f884b8e6feb50392d89698f889c18f04c4b2c8fb84fac507a8f995d091d501d59eaf9efb048adda34a9f01833b1331000813f10192a5b3c6b98992df9908cdbfa2a1bce2fe89498cb398989f9691029d85c7c2aeb9e902dbb0beed94b10ae7b4bee301dafca702caeb02c301dd1f010c3c000518ef019597d8f1a2abf1f7118aa7ccc492fe9db70ccffbf09c8e84a0f143ba91bb829b908147fde4d8aeebf5159fdbdab1d307ae8bd2fb4cdcbb02c32f3a000713e8019ea7f9cdafe48aab8903af92f6e0aafdbfc71082feb0d4bc88d111fbd7b8ead0a90db9e3ef86b9078afdf7d301d19b8b69eb6d3b1f130c030a00018902018fe6e3c4fc95dbf79908bae09ad2ccc9968910b5e0d4cdd584b90a95a1888db4ef01a4eeebe89d11c1b19702c302ab3b2f6f000604ef019583b4c1e480f8e3af04ebbc97f69a8f8d8f0bf3a7b5a1e1dfc10f9d97c2fef9890bfdb493d69502a7c08f9f2cabcf1ab37f29171135000504f40184cccdfc85aa94e4c111b396b2b9bae8d58108e6aa8aa48ba5b4895297d69c8385fd9901d28a9cdbe9a08501f580b2b68ed320fceedfbd199788b511a59b3e00080ace0135110110037102070005090b000a0101051bc90101a9020193dfbe908fc3db82a509a594c2fb80cfdc8703b3f0dca5acfe8578b4a7a5b9973cdda3ad0499e702c34935010a0301a702019a93c2928bb298afb30388de80818dbcd4f702d18bffe4f2f6f97ff79a9d94ef388ad9c6fd19a4f0870c81852963000508de01a3020194bd9a81dbedcc8b8d08ddfa808cf7b1d3bd24a78a9788cddcdd01d6a2878fb5f0b30183dc98b7a8db08ebc6d9cb01c9b7c50de3492b3900053f019d02018ee6f1f1aca8ffe6e70decef9c8f808fe981018cef93f684bbd0a902e1c4e3d78ba29b5edf93eee7c327ffb598b30aa6a9e501b395351f0d013c000607aa018cf4e4c19cbce6b08510c5d6f8d0c7b2f1b7349ec7fa9bc0f2850df0a48abec59b049ffd98faa70184c49eb374b5d932870332000707a80183baa1d0cd9fe79e9b119ffca6fabfea9bdb09bae9aa818eadee9512d6b4e5e6f1f49f1595a9dda5bda124ade8bda701d4c3e9019c8d2b13380006079f0181c894a0bdb3cde7b91bb6c1f9e5e0f0da8d01a59bc180d3f6daab0fb481f7b1e4bcc502bfe6a09fbdeb0bb08cf7af01d4a5d702fcb3491f3800060d8a019c9ad69fb8b8bf91f102ab9a98ba9cd4c7a70fd0f2c1f4ec92b507858cded689d97b9199b6895280a4df06ecc91e9d01831f0a33000507a90197b8938fe9c3bc9e850788aab7c2dbd7b9df2af689abb1e7efa17db4cfa0fbd48d028cafaed2b28f0186cbadd2f535848db90c909710c51f0339000607ae0186dfa89995a9f288cb0e82fc89c8f0d5b6e10aaedbdac6c892cfb72ae68786b3f08ae942d29fc78be9811481f98dfed901949bef9102eb9302f92f1f3c00060d83019daba2e391ef9484f3029f879be8f5efa58508e984cd88e4f4c5499ab0c293850bdff4c58b01f3caa1018fc9492b1f0a036d02019ab9df99d7fff3fbb5059ffae1ddd5b483c104eed0bdf1cd8b833284bf96f4f50684c8e1ed07a9836b1d08036b020194d6d886e4a1b3e8b909b9a7b58b8aa0eab101ddb68bc2f787e89b07e3d8a0878ca7b91aa8d8bd8a99ad17cf89b58dd52495ecaec719d7a2a501a1f3671701a1000607bf0191e594bdaab293defb0cc4ad99c5d5fd889501d396abc4f8a180cf048cafdbf1bb85dd04df85faa0a8b117ba8adfcd049b90b902affd49010a036502019cbecb91a6bfb0a09d03d1e9f7bcb78789d70798f6d58ee3fd8d05f1d281b2d4b902c490ceb4e928a6bae703bca361471d6e000507c6018fcaca9be082dd8cb50b85dea9c2bba4d9c905cafab2a4eadcd59128e6f3f8c9b6c2bd019aaea0daa796930598c6ceb78a9905e7b78a9de517e1cbc109803e00050ad70129110103000507b90185f3c9c3cb959eddc70aa6b6f1c0edf8c2a3099bd2e5c7c0d7cfc107868acdd4e695e9fd2ac3eaf1c9dedcfd01a7cafdc2ebe48d2d9ba8aaeda70ca8f9af9901cdb5bf4a9f45000504b0010e0353027fb9c988e7f6f593d31ec288bdcd95a1bae502fbb1a9f0c79dc1f907abb0fcffabe69f0684abdb9fef99088fb3c9c4fd01bcfab5a10ecab54f3d00050ecf014f022500019d026da7d08f85addae2d51dd786bfb681b289eb03e2bc9296a0bcc1991b87e08ce783f5d305a8f5cdafcac105e3b3efdbbd02d8f4c0d302e588d11db32917110c03019702018ed3fa87c5d591dcd95cd4b9defcf4ddf306daa4b0dafcd9ad07fad7f99ca0c306ecccc886fb3193a5f124adaf17ed11010a03019502018ea19f918bdac3f1ad03bc90af9fc0d2e9e501d5afe9c0999edd4ddfcef0e5a306ccb7dc89018395e921d501dd1d170a01b2000505f7018c9b9ed7e0a18786df05f3b38a9985d581b30b999bc9fce282912bb6c8bc9fde9301cf9be0e0f90cf29db103f89f2e000809d90101894f47352f29011209000505e50186899dabddf4d0c6f50d80bbe4919f80c4c340ffc198e5ea899970c9acaea6929d02c6e1fbe9b130c19e8f21979f2e000603f6014701000705e20181fd9cb98781d6f1d91187958dede7a8ae9901a5df9694a0aaf98b17beeae4c8988aef1bb8e8f1beafed0be2a4e6aabd30000602f601bab2cf02c302ab0d08000505d8010191e8f3b283e5b8e7fd05d8ece8dfaad2b4a71ca3cfc2ab92dea701dcf7db9b94b0a370d5cc8ef58706add3e5ab4ac3ef29bf4f010a037102018cd4999befa2b5d5c90ae8f88bfedba1d5ad018ea0a695b4f9c2d10ad0f7dfd8acd2a57c83f88de98735d695caab18eef0c501f8dd02ab29117300050de901018a89ec90e580f48caf0eafae80cbb0dfbe8d50eaacf6a0daf885078c95e5d0bc889d03e2c0d7f1b38d03afbe8faddb49f9d0a505c181189f1f3a00050dde0184f591fad0bdf0f9fb0deacccade8c9ddaf106ffb6ebc0ef85f8f9278a959ad18eacb1019690f7bdc3f49d52b2e5d8b1b308f6bca9df20e19b13bb02f91d3e000605d20182aae4efc69cafb0e10dc89befe7b9fce9a30a83a5a68f9fdca1a54bbeb6f9af85b6d562b1d8ecc7bead338e9f81a08d049b90b903d2d902f9650d3b000605d40197c393d7ffc3ddfca903d986dcd7b3cd9c811c9394f7d1ebc1f93afaddc7ebc1ab4caed18995ff02f2d083a101cbde83108b353300050af301019bb192f99ae1d1bb8301e888858da89deda30c8dbed0faffb6c904b09aa59ca7c902cae2b3aae70cc7ccf504f2bd2f000803a2015935110e0359020190f4a79f87d9ceeca10b92e5bdbbd5d4eae502ceb0e188e9dcf49f019fa3d9c994d2b702f58feaebd8df48f2cf8d930bbffecb05d9ff534f1f010c0353021d0001950269dbeca190f5dee9ed1f97b498c0ecb2feff3ab0f5a9edbb94eb6aeca0c993e5bf2ecfda92bfbb0de6b29e9d02b9b3cf01d1b902ab13018100056b018b020189e7b99ded849b94a921ddd2b6d19feacd1e98c9f6ac91b712c8cfd6d9c703d4e183c925c9d902c302ab1f130a030189020183e2f5a9cffbcf9ce308a4ccb8aea7dad4d112dc988786b1d5c70195ddbff4e29317c2a9b59d02f5b4b70183ad0183531f0d6700060583010188c7cebf97c98784b504fab6f4ffc9baf1df0dfcf091d9f7d2cf0e8afb8ce6deb103d5dc91f5c30182cf81df36b1d12ed1532f1f010c037f0279c0dd82e6ce8da89b0ff8edc19ea1b5a5db0981c3bb918da9a0b911b5a48ff0f2b2f719c8efb5bed9bb01a69fc0a9b92792c0df03c59771170d74000608910193e3e6d2dfebba80e51cd4a3c2db9bcbdf028daca783e8c8b305eac3f09eb5c503ae9c83ce913ccfedd30b82cd2d000801fd01350d010e036d02019188dcc5beaff8adb303cedae498dbaaf88f068ac1c1b6b2b29f04f1b987c283a705aa8bd8ff8f53a09fa70e879b02f902c3352b0d0c036b02018bd2c8aafbb8f586cf09f8e6d1c385d1d2f345e1d9c697be8a8502a3e28eebc0acdf03cce79f9cbdcd01efebb189019998e152fd02f9672f010c0367020188f7be9dd9fdb3b39d0ce08ecdb1eb83dffd018abe97b9e4c5a7c50c86d6ab8098e0a31ef5ea9e928edd07dfc5f1c1ff02b599ec8118869102f901dd170101be0005059a0183c1aa839786b08cb90dd7f1a1ac8ce9e4ab06f5fbbce6a282c4831588da84d6adc7a702be88edc3f9ab0696e298c922ade102f902c302ab01f701dd615347352f2b1d0114036102019288cc8780cccd969d08cbe6adcbaa93cccd389be3c081c3b68903af83998bbeeacb07a3a6f293ce9d71c4bed4af28e8e9a504868d02f95953350c0359021700018b026fdda385bca1e2bebd0c93a7e6b9e998a5ad01fbe1ba9f8fe8dd8d03e6bbadef9aa4cf10c4b8f7e1cf8b0e85e5e2debf06a4c3c8d1568acf108b170d030c030189026aeaf8b381c8bbcdbf13e8fdb79c8bdab48302a2fab28dd39f9cf118e8e0ddcfca9ba946d5cbc886ceff29de9b9dc791068390a0c70593c302c302ab11010c0301830267c9b1a6dab7ccaceb139bc1f488d5cdefff0887b4b4e6dddabbad3999acafea96d2fd07af94cb9ddaf101caf2a8ddbb4fd1bf34cb471d0a037f020182a582cbbe9c9dd9b107d58093bff2cd85a173cf9aff8385a8bb02c08bf9f4d99eb903c8eea6f5aaf106e184eeb8af049cbfbdc563e9e10f871f0a0371027dd6d7ba8ba7d8d7ad0ee0dc92decddda9ef49e9f094eaefd6b704a08392b9abbaf345be8fe7f5cf1bd79ac8bf04e3a6f302a7d36d351d110c036d027bafc1f1b1edb696ab109898a4a7c78f9beb02baa886f4ef99ed8f0dfdafefc3c8e2d912d0e5848dfca15888b782a72cb8e9f307e1f702c302ab17110c036b0276e196dffef8f194a70fcadce1949182d7e70991a9919dbac3e48363c4a5f4bee7f59704d49ab7a598d8e905b7d6fe9cbccf03e6ccc58fa301e2ef8bd30dabc9119935110c03670274ba8197a5beced3a50fa3feffcab5fcb5e50ba5ddeeffadbac99302a8d886c39fffa48103d2b1f597efd5d506a1e6d39af6b9069ac7d4a99b02fbbfb19566f1f552fd01dd2f0c036502018d829981ef89f5f1cb0693e2bec0adaef5f32de8d5e28fcdd3f901cd8e8fb3cead9b05eebbafb99fa303ef84c1ddad78abace90cb0cf02ab0d0a03610213007f0264b8a087bc8493e7ad12d18ca8e2cc88a7b909b698d7b3a9d8a2810ac5fae0e183bdcf0188c09f8be3b31685c4e8e902aed8d71baf351d17010c037102018091c4daadbef6a6bf03abd094efd1de86cd21a2b4d0ca8fe8db1bfdccf58ccea16ebda8dacb3aebb2cb0792d702c301dd170d010c036d027de4cbd596ac93eb8907b38bfdbdc6aeabf9119ae3bce5e9f6e504b7b5c1afc98333cffcf8c301bdcbe5189f6b47130a036b020181b7c9d8e6b39afc9f0785b6b8bbaeddf6b73de089e6df8c9113ed82a8a3bd01e68ae0d11ffa9d108b2917110a0367027ef5f083e891f3f68d09e1d7b1c38b9cce8101a7bdedc8aab4d4ad08d894c8d6bbc2b70497cce9fbedcd01e1a8fcd0f323b9eaa902b68935110a0365020b000509050975026ee5d1c6a19dd3efaf04e8cbf2adfbdcd8a90c9a81d4ab8b849908d185a0cfbdfd02cdcab7f1a9519895a30cdc930e9b47270a0371026aefd0f6dfbecb9eb30bcfdaa4d78efaa1c301c0d5efd2bcaff7b50df3d7d5dfebce8918f7ea9afdcbb90babdfc8b5cb02f6d0c78d3bb99d3cbb02c302ab6d472b130110030408f600150101000100
    (by decide) ⟨27, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock6 : (⟨[⟨3,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨41,1,true⟩,⟨43,1,false⟩],45,5⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock2 (.cons fangThreeFourteenBlock5 (.cons fangThreeFourteenBlock3 (.nil))))
    25 1165 0x50905097302418883cbe5ddd0ffe1029f9698d7afaef79502eb95b29dbdd7dd01f5d4c3e481ab018ab1a096c910f39ce501e08902c3711f0d010c0371023ee19dc2a8ae928c9d0a9995e4b3d58ef9bf4ce394fbc19effcf0288f4cc94cdcbd9048f87b9e5888b0293a3bbebed01b4d5cd71000804d1016d4f49472f2b291f1d171116036d023dcdeabdc9d6b2d2bb0ed0c78bcfffc4fb9737f5abb9f980eac102c7f1eac998cdf503828b94aad88b01ad83b9c68f0bbcd4c307b7ab17b1110a036b023ba784b48ca6f3def71386dfe9ad89cd92f504c7f6bf8ae5ba919302b0a7a6d88ffeef03b6f7ace7d9d304a5bcdcd502b3e2bb02ebc3674f2f0185000502d7013a93d1afadcf94a59512d7b2bbe7eceadbef08b080c6f9cba2ccbf67fcd0c1dde39fe904cbdbc2e5a08bcd108288e2fa8db50381fdecd7bf1baef5e101d18f02c34f1f0c0365025c9bf2d3b0b4a4e6e50af5d7e8dbf7c18d10f1f4db86d7c316fc9ba594d904c6f883a328cbe102c302ab290d0a03610258ded8a3f0f9b0d2a70eddb9d59f97e3a3f901a8e5e6baf0efafc93ae5c6a4a89f8710dce5b1e4fd50b1dbd732d2d110c52b010a0359026dba81b897989becab04d290efbcabf6d6af07f996c4fea2dc99128afac1f7a3970681a9e1f3dd02b7f7e5f901bdc6cb64b902ab1f13010c03530211006d023efa9081969ebbbce174fc97dec68a9db506abc2af8695b2e70f95acb28783d707c2f7afc964b4d516df2b0d010a036b023ea7b1ffd2ccc2c1db08b2bdefb7e8e5a0f331f890c09982cc9733f8f3b18acdf13cbabd8da4b90cedf58c9d19e08118f947170d010c0367023d8cc3d5b395ccb4810db78891cad3cde9ad13ba8481b0b8bab940e1c690a383a14ad6c498bf8921c6d5b70682ff01f717010a0365023ad6e780f4a7e098cd12ecfccda9b5f2a797049b99b19fc29295970f9e88c8f7c1cfe101d3c0c592a29102fd88aecf2d8fc703bf000802bd016153471d01100361025d9de88be39cd8afcb02ef879e84a6b6e1d70ed0aeb2bc9190cb088ba59dddede165a1da98a72facb3d30fe88701f717110a0359020b0065023ef5e0c9bab3f0b387039ca2b0fdb9f7d19306faffa58093f39b13d5968ec893db07eda1aaf897028dc4adbb42cbeb0de329010a036178000901cb016502398983dfc8e5e4c98303cee4f7bda2f0e8b30692b4dcc4c6e88706b7c3bbe5a2b902c0acb7e8f55484d5cf0bcdc902c32b010a0336000b4a0112dbf7d8dcfa8ebac901bff5bff2a593d5d307d1c9c3a8b5edc71491d78792c4bb109ac3f8a48d05e3dffe9b64b4d577b32f11010c035937000801cc0161023aa1e2c4ed86f58ed30ba489f4f1bbdea8c301b5f2e5cabbbe969b05fab2edc28eb1e102a9d8ddf1f1d7078cd8ef953586a702c302ab01f701dd592b130e0359020344000601010b7c0105095b020e91f889f394f3aa995cc289e4a481ade501a6ddfaf2e8a29502e1aab285d98f46d6928cb511ecaca709f7dd0de30803590213a2faebfcb8d9becd0e9fb3ebd0ecd8b3eb6faad1999c92fed902ceede58fb2ffc36fa9b4cbb89103c9ba8ff101fafbff01898153010a035302050000730007090105090200060101000100
    (by decide) ⟨22, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock7 : (⟨[⟨3,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,false⟩],33,7⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock0 (.cons fangThreeFourteenBlock6 (.cons fangThreeFourteenBlock1 (.nil))))
    20 36 0x60f0109150105090200050d010a110105090200060a01100901050902000b0101000100
    (by decide) ⟨16, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock8 : (⟨[⟨3,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,false⟩],31,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock7 (.nil))
    27 127 0x509050904000b07010570010509510232eee9cef2fac3c504dc98f8e58ee2e5038b81f0b89baf2ad981e5bd5ce3dd37fb01dd1308034f020eb494c7c1b9cfaa81059b84db9d8fb2bdbf2f80aac0e6fe97c305c8beb1d781d59f03a8caa283d6a504a6f8ceb4e703bac1e0ff05a68d02f9110d010c03046b00130101000100
    (by decide) ⟨15, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock9 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨41,1,true⟩,⟨47,1,false⟩],49,5⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    20 105 0x91201146e010d5a015d02028587b78d90df83ed8517dde28cea9ff4dbaf06eba4f8ecdbd1aded328cc79bd4b1dadf0189ed9cefb482e72ca1e9b8b7df0e92ada8b908d39b9d0e879b32e102c301fd29010e0359020300004f00070b01050705070400060101000100
    (by decide) ⟨24, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock10 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨41,1,false⟩],43,6⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock9 (.nil))
    23 93 0x507000300060201050702000b4701050757020285a7b194979bc3a191058ea99698f3efbf8d12b49d8dbbf2b8b924d9daed9ab1f503a2be84bce70191edf1d701d2bb53170b0a035302033c0006010108050105070200070101000100
    (by decide) ⟨21, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock11 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩],33,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    21 28 0x606010b0b01050705070400070801120c01050702000a0101000100
    (by decide) ⟨16, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock12 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩],31,9⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    20 35 0x50705070400060901071001050702000608010e0e0106080105070200050101000100
    (by decide) ⟨15, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock13 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,false⟩],25,9⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock12 (.cons fangThreeFourteenBlock11 (.cons fangThreeFourteenBlock10 (.nil))))
    25 29 0x60a01080b0105070200121001050701050501050702000e0101000100
    (by decide) ⟨12, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock14 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨17,1,true⟩,⟨19,1,false⟩],21,10⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock13 (.nil))
    24 23 0x60b0105070200050f010d0d01050702000e0101000100
    (by decide) ⟨10, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock15 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨37,1,true⟩,⟨41,1,true⟩],45,6⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    23 846 0x5076b0201c2f2b1b481d6e2caf33f919ccff9aac3ff8302cfabc3f0bb92babb04aefcf4af9ee5af6bd49ed888af0cadd8e8bf01d18ea901b2bf02d5018f67010c03670201bf8dfedebfe3ffdec941cdb39388c2e789c503fab4fca7e6c4b78902cbfd86f2d1a9e52edc8da8d0f50189f2a8c3018caab916f1018f3503010c03650201b7c599b3bbfeba85f547c6aee4aaf4c6add905c0bed6beb0ace5fd0ea6a29ddc80e89f19b2b9fdb5c5a328f9f893fcaf04e0b4c39309baf101bb000a04ac016147433b352f29250b1603610201a8b3ceddb4b3aed4cd52b4bf84ee88e5e88509ce9ca8a2b7d3fcc928b8cacfcba1dad90ba8a79cebccab138dc1cfc3cb01b1b484875fb5e102d502bf018f592f010e035902019d86b6dceedb868fcf61d08da1c1ae9c82e505f4dc9294c182a9d316ae98cbefa6b9c53d81adb287e8e521c5dda5a8f902a1afc0cf018ae7eb62c901fd350b0c0353020195bdd1b1eaf5c0b6fb6ef3f698cb999fa4d32fbd97d0a7859ef9039a82ffa5dfbac939a59fcac08102ad848fab30faa75fe34f1d0a034f0201f4b0e5c3c1eedbbfe70cc7a8908f82d3d09703ddece5d4849fe3f911bb9aadc1aa8add0781fb8c99e8c50499df8298c301a1dda0bf2cabcf41f5018f2f010c030e000507610201bbb0b5acb8c0aec1a540a9bab7b086e7ecb101c8e8b9c5edb7cdc9099e828f9fded08b06c4aca4be918501e4bba8e39519c994cb10e8e911870b03010c03590201aedfbed8f3fcdf93974bead2e0c5d38edced059eddead19fb8e0ef43c696cfd7d4c90e9ae09499ff07a28aceb71899fb018f1d010a038e000501e6015b0201c4eee8d3fac6eeb7d132f086f4cf90effa9f01f0e4d3fcc5d9f5a102e8c695faa7cfd307ac8fd081fce101a4d9abbda90be5a7f1059fcb3a0008550159170e0359020307000a01ac015b0201c6c8a99fe7e8c0c9811ff7f8a883a2daf8f90ea8c396adcdad97a95cc1b08acdded39923cc9caedcddc91490c5f48fc9018eb5bb970183c29b02d502bf02ab01fd018f594f473b352f1d1403590201b996eeb0aebdc0c48b3bfeb296f0b4aff99b04c28f9784a0dc8e930298ce88c18cafb901c2f8e9f7edbb5d8bc58cb30f98a6fb08acf102d5531d010c03530205019200060801080c01050a010c070105070200060101000100
    (by decide) ⟨22, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock16 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨23,1,true⟩,⟨29,1,false⟩],31,9⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock15 (.nil))
    20 38 0x5070200050e01050702000c1301060b010b0f0105070003000a0c0105070200090101000100
    (by decide) ⟨15, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock17 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨19,1,true⟩,⟨29,1,false⟩],31,9⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    21 38 0x5070507040006090107100105070200060801080a010f0d0106080105070200050101000100
    (by decide) ⟨15, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock18 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨31,1,false⟩],33,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    25 33 0x606010d0b0105070200070b0105070200091201100a01050702000a0101000100
    (by decide) ⟨16, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock19 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨41,1,false⟩],43,7⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    21 23 0x507020006090105070105050105070200210101000100
    (by decide) ⟨21, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock20 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩],45,7⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    19 22 0x507000004000f0b010c070105070200060101000100
    (by decide) ⟨22, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock21 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨41,1,true⟩,⟨47,1,false⟩],49,5⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    17 16 0x81001140b01050702000f0101000100
    (by decide) ⟨24, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock22 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨41,1,false⟩],43,6⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock21 (.nil))
    20 33 0x5070003000802010507000004000c0b010b0a0110090105070200070101000100
    (by decide) ⟨21, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock23 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,false⟩],33,7⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock22 (.cons fangThreeFourteenBlock20 (.nil)))
    19 27 0x60a01060f01080d01070b010909010507050704000d0101000100
    (by decide) ⟨16, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock24 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨19,1,false⟩],21,10⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock17 (.cons fangThreeFourteenBlock18 (.cons fangThreeFourteenBlock23 (.cons fangThreeFourteenBlock19 (.nil)))))
    25 35 0x507050704000609010711010716010a1101050702000d0a0105070200090101000100
    (by decide) ⟨10, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock25 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨37,1,true⟩,⟨41,1,true⟩],45,6⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    17 33 0x50703000e0e01080c01071101070e010507010a050105070200060101000100
    (by decide) ⟨22, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock26 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨37,1,false⟩],39,7⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock25 (.nil))
    18 32 0x50700050705000910010b160105070200100b010507050704000b0101000100
    (by decide) ⟨19, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock27 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨29,1,true⟩,⟨31,1,false⟩],33,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock26 (.nil))
    19 24 0x507050705070600070801100a01050702000a0101000100
    (by decide) ⟨16, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock28 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨31,1,true⟩,⟨37,1,true⟩,⟨41,1,true⟩],45,6⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    16 28 0x90f010c18010d15010b0a0107090107070105070200060101000100
    (by decide) ⟨22, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock29 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨31,1,true⟩,⟨37,1,true⟩],43,7⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    19 32 0x602010f1401081501080c010507020005080108050105070200070101000100
    (by decide) ⟨21, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock30 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨31,1,true⟩],39,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    18 27 0x602011210010916010a05010a0c01050705070400090101000100
    (by decide) ⟨19, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock31 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨23,1,true⟩],33,9⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    25 31 0x507050705070600070b01050702000d0f01140b01050702000a0101000100
    (by decide) ⟨16, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock32 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨41,1,false⟩],43,7⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    21 29 0x602010b1c0105070200080c010b09010c070105070200090101000100
    (by decide) ⟨21, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock33 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨37,1,true⟩],45,7⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    18 26 0x5070300080c01050700030010090105070200080101000100
    (by decide) ⟨22, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock34 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨37,1,true⟩,⟨41,1,true⟩,⟨47,1,false⟩],49,5⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    14 22 0xa0e010c0b01070a0108070105070200060101000100
    (by decide) ⟨24, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock35 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨37,1,true⟩,⟨41,1,false⟩],43,6⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock34 (.nil))
    18 32 0x507000300080201081101090b0105070003001a070105070200090101000100
    (by decide) ⟨21, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock36 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩],45,7⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    18 26 0x70c01070901090e01050702000a070105070200060101000100
    (by decide) ⟨22, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock37 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨41,1,true⟩,⟨47,1,false⟩],49,5⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    17 19 0x5070200190f010507050704000a0101000100
    (by decide) ⟨24, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock38 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨41,1,false⟩],43,6⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock37 (.nil))
    19 34 0x100060201060f010d19010a0d0108120105070105050105070200070101000100
    (by decide) ⟨21, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock39 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨37,1,true⟩],49,6⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    17 33 0x512010507000300100e01080c0105070507000500050701050700000000000700
    (by decide) ⟨24, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock40 : (⟨[⟨3,1,true⟩,⟨11,1,false⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨37,1,true⟩],43,6⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock39 (.nil))
    19 26 0x72301071d010d1c01090d0105070507050706000c0101000100
    (by decide) ⟨21, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock41 : (⟨[⟨3,1,true⟩,⟨11,1,false⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩],39,7⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock38 (.cons fangThreeFourteenBlock36 (.nil)))
    19 31 0x507050704000a0f01070b0106090105070105050105070200090101000100
    (by decide) ⟨19, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock42 : (⟨[⟨3,1,true⟩,⟨11,1,false⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩],33,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock32 (.cons fangThreeFourteenBlock35 (.cons fangThreeFourteenBlock33 (.nil))))
    20 32 0x5070200060d010917010615010c1301050701050501050702000b0101000100
    (by decide) ⟨16, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock43 : (⟨[⟨3,1,true⟩,⟨11,1,false⟩,⟨13,1,true⟩,⟨17,1,true⟩],25,10⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock27 (.nil))
    27 22 0xc2101111901060801060601050702000d0101000100
    (by decide) ⟨12, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock44 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨31,1,true⟩,⟨41,1,false⟩],43,7⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    19 28 0x602010b14010c1c010b0a010709010e070105070200070101000100
    (by decide) ⟨21, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock45 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨31,1,false⟩],33,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock44 (.nil))
    18 30 0x6080105070200060b01070e01050702000a0701050702000b0101000100
    (by decide) ⟨16, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock46 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨29,1,true⟩,⟨41,1,true⟩],45,7⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    17 25 0x5070004000e0701080c01090b0105070200080101000100
    (by decide) ⟨22, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock47 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨29,1,true⟩],43,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    16 22 0x507050704000907010e090105070200090101000100
    (by decide) ⟨21, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock48 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩],45,7⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    18 25 0x50d01061201100e0105070105050105070200060101000100
    (by decide) ⟨22, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock49 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨41,1,true⟩],45,6⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    17 22 0xb11010d0c01090b0109090105070200060101000100
    (by decide) ⟨22, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock50 : (⟨[⟨3,1,true⟩,⟨11,1,false⟩,⟨13,1,false⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩],39,7⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock48 (.cons fangThreeFourteenBlock49 (.nil)))
    21 40 0x50703000e17010b13010a1101090f01080d01070b010507020007070105070200090101000100
    (by decide) ⟨19, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock51 : (⟨[⟨3,1,true⟩,⟨11,1,false⟩,⟨13,1,false⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨29,1,false⟩],31,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock47 (.cons fangThreeFourteenBlock46 (.cons fangThreeFourteenBlock50 (.nil))))
    23 34 0x712010b2d010f0f01080d01070b01060901050701050501050702000e0101000100
    (by decide) ⟨15, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock52 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨41,1,true⟩],45,7⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    18 25 0x60b010b09010e150109070108050105070200080101000100
    (by decide) ⟨22, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock53 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩],43,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    19 30 0x507050705070600091001050901090d010b0b01050702000c0101000100
    (by decide) ⟨21, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock54 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨31,1,true⟩],45,7⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    16 28 0x60c010b15010b0b01080a0105080108050105070200060101000100
    (by decide) ⟨22, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock55 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨31,1,true⟩,⟨41,1,false⟩],43,6⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    18 26 0x5070507050706001a0e01140c01050705070400090101000100
    (by decide) ⟨21, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock56 : (⟨[⟨3,1,true⟩,⟨11,1,false⟩,⟨13,1,false⟩,⟨17,1,false⟩,⟨19,1,true⟩,⟨23,1,true⟩],33,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock53 (.cons fangThreeFourteenBlock52 (.nil)))
    24 31 0x60a011913010b2101060201061001050701050501050702000d0101000100
    (by decide) ⟨16, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock57 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨47,1,false⟩],49,6⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    15 19 0x90d010908010c070105070200060101000100
    (by decide) ⟨24, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock58 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨43,1,false⟩],45,6⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    17 28 0xe21010b11010a0e01060a0106080106060105070200080101000100
    (by decide) ⟨22, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock59 : (⟨[⟨3,1,true⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨41,1,false⟩],43,6⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    18 19 0xb0c010b0a0110090105070200090101000100
    (by decide) ⟨21, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock60 : (⟨[⟨3,1,true⟩,⟨11,1,false⟩,⟨13,1,false⟩,⟨17,1,false⟩,⟨19,1,false⟩,⟨23,1,false⟩,⟨29,1,false⟩],33,7⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock59 (.cons fangThreeFourteenBlock58 (.cons fangThreeFourteenBlock57 (.nil))))
    27 22 0x507050704000a0f01130701050702000d0101000100
    (by decide) ⟨16, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock61 : (⟨[⟨3,1,true⟩,⟨11,1,false⟩,⟨13,1,false⟩,⟨17,1,false⟩,⟨19,1,false⟩,⟨23,1,false⟩],31,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock56 (.cons fangThreeFourteenBlock55 (.cons fangThreeFourteenBlock54 (.nil))))
    28 30 0x60a010f13010c1201090e01070b010909010507050704000e0101000100
    (by decide) ⟨15, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock62 : (⟨[⟨3,1,true⟩,⟨11,1,false⟩,⟨13,1,false⟩,⟨17,1,false⟩,⟨19,1,false⟩,⟨23,1,false⟩],25,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock61 (.cons fangThreeFourteenBlock60 (.nil)))
    31 15 0x60a01050705070400140101000100
    (by decide) ⟨12, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock63 : (⟨[⟨3,1,true⟩,⟨11,1,false⟩,⟨13,1,false⟩,⟨17,1,false⟩],21,10⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock43 (.cons fangThreeFourteenBlock31 (.cons fangThreeFourteenBlock30 (.cons fangThreeFourteenBlock29 (.cons fangThreeFourteenBlock28 (.cons fangThreeFourteenBlock42 (.cons fangThreeFourteenBlock41 (.cons fangThreeFourteenBlock40 (.nil)))))))))
    36 30 0x4000a2301141d01050700030006020105070200120101000100
    (by decide) ⟨10, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock64 : (⟨[⟨3,1,true⟩,⟨11,1,false⟩,⟨13,1,false⟩],15,11⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock24 (.cons fangThreeFourteenBlock16 (.cons fangThreeFourteenBlock63 (.cons fangThreeFourteenBlock62 (.cons fangThreeFourteenBlock51 (.cons fangThreeFourteenBlock45 (.nil)))))))
    29 20 0x507020007050116130105070200100101000100
    (by decide) ⟨7, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock65 : (⟨[⟨3,1,true⟩],13,13⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock8 (.nil))
    33 29 0x50905090000050908000a070105010010110106090200130101000100
    (by decide) ⟨6, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock66 : (⟨[⟨3,2,false⟩,⟨11,1,false⟩,⟨13,1,false⟩],15,11⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    16 25 0x405040016100105070105050104050200060101000100
    (by decide) ⟨7, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock67 : (⟨[⟨3,1,true⟩],11,13⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock65 (.cons fangThreeFourteenBlock64 (.cons fangThreeFourteenBlock14 (.nil))))
    32 20 0x60702000a18010f1101060702000e0101000100
    (by decide) ⟨5, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock68 : (⟨[⟨3,1,true⟩,⟨7,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩],25,10⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    26 30 0x508050805080600060a010a1d011615010c070105080200060101000100
    (by decide) ⟨12, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock69 : (⟨[⟨3,1,true⟩,⟨7,1,true⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩,⟨37,1,true⟩,⟨41,1,false⟩],43,6⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    17 33 0x5060300081201071901070901120e0105070105050105060200070101000100
    (by decide) ⟨21, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock70 : (⟨[⟨3,1,true⟩,⟨7,1,true⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩],39,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    18 27 0x506050605060600070b010b0901110a0105060200090101000100
    (by decide) ⟨19, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock71 : (⟨[⟨3,1,true⟩,⟨7,1,true⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,false⟩],33,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock70 (.cons fangThreeFourteenBlock69 (.nil)))
    24 26 0x60c01091701050602000507010e0901050602000b0101000100
    (by decide) ⟨16, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock72 : (⟨[⟨3,1,true⟩,⟨7,1,true⟩,⟨17,1,true⟩,⟨23,1,false⟩],25,10⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock71 (.nil))
    24 19 0x131601050701050501050602000e0101000100
    (by decide) ⟨12, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock73 : (⟨[⟨3,1,true⟩,⟨7,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨29,1,true⟩,⟨31,1,false⟩],33,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    20 29 0x506050604000b1401090d0105060200110a01050602000b0101000100
    (by decide) ⟨16, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock74 : (⟨[⟨3,1,true⟩,⟨7,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨31,1,true⟩],39,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    17 25 0x5060400110f0115100108050105060200090101000100
    (by decide) ⟨19, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock75 : (⟨[⟨3,1,true⟩,⟨7,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨41,1,false⟩],43,7⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    15 13 0xe0b0105060200200101000100
    (by decide) ⟨21, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock76 : (⟨[⟨3,1,true⟩,⟨7,1,false⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,false⟩],33,7⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    20 30 0x606010c2f010915010713010a0e010709010506050604000d0101000100
    (by decide) ⟨16, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock77 : (⟨[⟨3,1,true⟩,⟨7,1,false⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩],31,9⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock74 (.nil))
    21 25 0x50605060400080d01070901070701050602000c0101000100
    (by decide) ⟨15, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock78 : (⟨[⟨3,1,true⟩,⟨7,1,false⟩,⟨17,1,true⟩,⟨19,1,false⟩],21,10⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock73 (.cons fangThreeFourteenBlock77 (.cons fangThreeFourteenBlock76 (.cons fangThreeFourteenBlock75 (.nil)))))
    27 26 0x60201050602001401010a0c010a0a0105060200080101000100
    (by decide) ⟨10, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock79 : (⟨[⟨3,1,true⟩,⟨7,1,true⟩,⟨13,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,false⟩],33,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    16 36 0x5030200060d01131901070f01080c01050305030005000c070105030200080101000100
    (by decide) ⟨16, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock80 : (⟨[⟨3,1,true⟩,⟨7,1,true⟩,⟨13,1,true⟩,⟨23,1,true⟩],25,10⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock79 (.nil))
    18 26 0x1324010c1b01070f01050302000b0701050302000b0101000100
    (by decide) ⟨12, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock81 : (⟨[⟨3,1,true⟩,⟨7,1,true⟩,⟨13,1,false⟩,⟨19,1,true⟩],25,10⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    21 28 0x60201040302000a0b010c0f01180e010403040304000b0101000100
    (by decide) ⟨12, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock82 : (⟨[⟨3,1,true⟩,⟨7,1,true⟩,⟨13,1,true⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨31,1,false⟩],33,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    17 33 0x802010d140104030200081901081001040302000c0801040302000a0101000100
    (by decide) ⟨16, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock83 : (⟨[⟨3,1,true⟩,⟨7,1,false⟩,⟨13,1,false⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩],33,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    18 28 0x802011714010813010403040304000d0801040302000a0101000100
    (by decide) ⟨16, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock84 : (⟨[⟨3,1,true⟩,⟨7,1,false⟩,⟨13,1,false⟩,⟨19,1,false⟩],21,10⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock81 (.cons fangThreeFourteenBlock82 (.cons fangThreeFourteenBlock83 (.nil))))
    26 28 0x4030003000c07010718010f130104030403040306000f0101000100
    (by decide) ⟨10, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock85 : (⟨[⟨3,1,true⟩,⟨7,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨29,1,true⟩,⟨31,1,true⟩],39,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    13 27 0x40304030403060013110106080106060104030200080101000100
    (by decide) ⟨19, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock86 : (⟨[⟨3,1,true⟩,⟨7,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨29,1,true⟩],33,9⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    16 27 0x4030403040306000a0b01090d010b0b0104030200080101000100
    (by decide) ⟨16, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock87 : (⟨[⟨3,1,true⟩,⟨7,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩],31,10⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    18 27 0x403040304030600081001070901120b0104030200090101000100
    (by decide) ⟨15, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock88 : (⟨[⟨3,1,true⟩,⟨7,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨37,1,false⟩],39,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    15 26 0x60201141101081001040302000c080104030200080101000100
    (by decide) ⟨19, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock89 : (⟨[⟨3,1,true⟩,⟨7,1,false⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨31,1,true⟩],39,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    15 31 0x60b01101701060e010813010403040304000d080104030200080101000100
    (by decide) ⟨19, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock90 : (⟨[⟨3,1,true⟩,⟨7,1,false⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩],39,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    16 35 0x403040304000917010b18010a0c0104030200080b0109090104030200080101000100
    (by decide) ⟨19, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock91 : (⟨[⟨3,1,true⟩,⟨7,1,false⟩,⟨13,1,false⟩,⟨17,1,false⟩,⟨23,1,true⟩,⟨29,1,false⟩],31,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock90 (.nil))
    21 23 0x100101070b0104030200050501040302000c0101000100
    (by decide) ⟨15, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock92 : (⟨[⟨3,1,true⟩,⟨7,1,false⟩,⟨13,1,false⟩,⟨17,1,false⟩,⟨23,1,false⟩],25,9⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock91 (.cons fangThreeFourteenBlock88 (.cons fangThreeFourteenBlock89 (.nil))))
    24 27 0x40303000c18010a1601060801060601040302000d0101000100
    (by decide) ⟨12, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock93 : (⟨[⟨3,1,true⟩,⟨7,1,false⟩,⟨13,1,true⟩,⟨17,1,true⟩,⟨19,1,true⟩,⟨31,1,false⟩],33,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    19 21 0x505010c1701090b010403040304000c0101000100
    (by decide) ⟨16, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock94 : (⟨[⟨3,1,true⟩,⟨7,1,false⟩,⟨13,1,false⟩,⟨17,1,false⟩,⟨19,1,false⟩,⟨29,1,false⟩],31,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    22 19 0x60b011317010d0f01040302000c0101000100
    (by decide) ⟨15, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock95 : (⟨[⟨3,1,true⟩,⟨7,1,false⟩,⟨13,1,false⟩,⟨17,1,false⟩,⟨19,1,false⟩,⟨23,1,false⟩],25,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    23 12 0x4030400270101000100
    (by decide) ⟨12, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock96 : (⟨[⟨3,1,true⟩,⟨7,1,false⟩,⟨13,1,false⟩,⟨17,1,false⟩],21,10⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock92 (.cons fangThreeFourteenBlock87 (.cons fangThreeFourteenBlock86 (.cons fangThreeFourteenBlock85 (.nil)))))
    26 29 0x40302000910010b0f01070b01060801060601040302000f0101000100
    (by decide) ⟨10, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock97 : (⟨[⟨3,1,true⟩,⟨7,1,false⟩,⟨13,1,false⟩],15,11⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock84 (.cons fangThreeFourteenBlock80 (.cons fangThreeFourteenBlock96 (.cons fangThreeFourteenBlock95 (.cons fangThreeFourteenBlock94 (.cons fangThreeFourteenBlock93 (.nil)))))))
    28 33 0x4030403040306000608010f09010403000004000f1101050302000e0101000100
    (by decide) ⟨7, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock98 : (⟨[⟨3,1,true⟩,⟨7,1,true⟩,⟨11,1,true⟩,⟨23,1,true⟩,⟨29,1,true⟩,⟨31,1,false⟩],33,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    17 33 0x50302000f1f01090101090d010503050300000600050701050300000000000700
    (by decide) ⟨16, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock99 : (⟨[⟨3,1,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨19,1,true⟩,⟨23,1,true⟩,⟨29,1,false⟩],31,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    21 23 0x815010a1001040302000c0a01040302000d0101000100
    (by decide) ⟨15, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock100 : (⟨[⟨3,1,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨19,1,true⟩],25,10⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    23 31 0x60201040302000d09010810010b0a01070901070701040300000000000700
    (by decide) ⟨12, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock101 : (⟨[⟨3,1,true⟩,⟨7,1,false⟩,⟨11,1,false⟩],21,11⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock98 (.nil))
    23 24 0x1016010c18010805010a0c010503050304000d0101000100
    (by decide) ⟨10, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock102 : (⟨[⟨3,1,true⟩,⟨7,1,false⟩,⟨11,1,true⟩,⟨17,1,true⟩,⟨29,1,true⟩,⟨31,1,false⟩],33,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    18 30 0x40303000514010912010403040304000c0901040302000b0101000100
    (by decide) ⟨16, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock103 : (⟨[⟨3,1,true⟩,⟨7,1,false⟩,⟨11,1,true⟩,⟨17,1,true⟩],31,10⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    19 27 0x403040304030600080901070c010a070104030200050101000100
    (by decide) ⟨15, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock104 : (⟨[⟨3,1,true⟩,⟨7,1,false⟩,⟨11,1,true⟩,⟨17,1,true⟩,⟨23,1,true⟩],33,9⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    18 19 0xe1701090b0109090104030200060101000100
    (by decide) ⟨16, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock105 : (⟨[⟨3,1,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨17,1,false⟩,⟨23,1,true⟩,⟨29,1,false⟩],31,8⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    20 16 0xc0e01160c01040302000a0101000100
    (by decide) ⟨15, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock106 : (⟨[⟨3,1,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨17,1,false⟩,⟨23,1,false⟩],25,9⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock105 (.cons fangThreeFourteenBlock104 (.nil)))
    23 16 0x50e01160c01040302000c0101000100
    (by decide) ⟨12, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock107 : (⟨[⟨3,1,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨17,1,false⟩,⟨19,1,false⟩],31,9⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    21 24 0x4030003000f1901080a0108080104030200070101000100
    (by decide) ⟨15, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock108 : (⟨[⟨3,1,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨17,1,false⟩,⟨19,1,false⟩],21,9⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock107 (.nil))
    25 22 0x40304000e17010a060104030200160101000100
    (by decide) ⟨10, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock109 : (⟨[⟨3,1,true⟩,⟨7,1,false⟩,⟨11,1,false⟩],19,11⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock101 (.cons fangThreeFourteenBlock100 (.cons fangThreeFourteenBlock99 (.nil))))
    27 28 0x51c0104030200090e010001000b0f010403040304000a0101000100
    (by decide) ⟨9, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock110 : (⟨[⟨3,1,true⟩,⟨7,1,false⟩,⟨11,1,true⟩,⟨13,1,true⟩,⟨29,1,true⟩],31,9⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    17 27 0x3000e0c010a13010b0a010e080104030200050101000100
    (by decide) ⟨15, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock111 : (⟨[⟨3,1,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,1,false⟩,⟨23,1,false⟩],31,9⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    22 19 0xb1401120d010e080104030200050101000100
    (by decide) ⟨15, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock112 : (⟨[⟨3,1,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,1,false⟩],25,10⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock110 (.nil))
    21 23 0x40302000b0a010908010c070104030200070101000100
    (by decide) ⟨12, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock113 : (⟨[⟨3,1,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,1,false⟩,⟨19,1,false⟩],21,9⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    22 22 0xe0e010d150106080106060104030200090101000100
    (by decide) ⟨10, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock114 : (⟨[⟨3,1,true⟩,⟨7,1,false⟩,⟨11,1,false⟩,⟨13,1,false⟩,⟨17,1,false⟩],19,9⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    23 22 0x4000d0b01100901040302000a0101000100
    (by decide) ⟨9, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock115 : (⟨[⟨3,1,true⟩,⟨7,1,false⟩,⟨11,1,false⟩],13,11⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock109 (.cons fangThreeFourteenBlock108 (.cons fangThreeFourteenBlock106 (.cons fangThreeFourteenBlock103 (.cons fangThreeFourteenBlock102 (.cons fangThreeFourteenBlock114 (.cons fangThreeFourteenBlock113 (.cons fangThreeFourteenBlock112 (.cons fangThreeFourteenBlock111 (.nil))))))))))
    29 29 0x112d0109130104030403000500090e01080501040302000d0101000100
    (by decide) ⟨6, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock116 : (⟨[⟨3,2,false⟩,⟨7,1,false⟩],15,12⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    18 16 0xa01010a0c0103030200090101000100
    (by decide) ⟨7, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock117 : (⟨[⟨3,2,false⟩,⟨7,1,false⟩],11,12⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock116 (.nil))
    16 16 0x15010110060103030200060101000100
    (by decide) ⟨5, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock118 : (⟨[⟨3,1,false⟩,⟨7,1,false⟩],9,12⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock117 (.cons fangThreeFourteenBlock115 (.cons fangThreeFourteenBlock97 (.cons fangThreeFourteenBlock68 (.cons fangThreeFourteenBlock78 (.cons fangThreeFourteenBlock72 (.nil)))))))
    34 18 0x506000300101201050802000f0101000100
    (by decide) ⟨4, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock119 : (⟨[⟨3,1,true⟩,⟨5,1,true⟩,⟨17,1,true⟩,⟨23,1,true⟩,⟨29,1,false⟩],31,9⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    17 6 0x2c0101000100
    (by decide) ⟨15, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock120 : (⟨[⟨3,1,true⟩,⟨5,1,false⟩,⟨17,1,false⟩,⟨19,1,true⟩],25,10⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    20 30 0x3060000050606000a01010c0b010c0a0106080105060200050101000100
    (by decide) ⟨12, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock121 : (⟨[⟨3,1,true⟩,⟨5,1,false⟩,⟨17,1,false⟩],21,11⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock119 (.nil))
    25 6 0x2c0101000100
    (by decide) ⟨10, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock122 : (⟨[⟨3,1,true⟩,⟨5,1,false⟩],19,12⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    27 19 0xd1e01070c010a070105060200170101000100
    (by decide) ⟨9, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock123 : (⟨[⟨3,1,true⟩,⟨5,1,true⟩,⟨13,1,true⟩,⟨23,1,true⟩,⟨29,1,false⟩],31,9⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    17 6 0x1f0101000100
    (by decide) ⟨15, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock124 : (⟨[⟨3,1,true⟩,⟨5,1,false⟩,⟨13,1,true⟩,⟨23,1,false⟩],25,10⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock123 (.nil))
    18 10 0x3040200200101000100
    (by decide) ⟨12, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock125 : (⟨[⟨3,1,true⟩,⟨5,1,false⟩,⟨13,1,false⟩,⟨19,1,false⟩],25,10⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    18 19 0x70c010a09010e080104040200050101000100
    (by decide) ⟨12, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock126 : (⟨[⟨3,1,true⟩,⟨5,1,false⟩,⟨13,1,false⟩,⟨19,1,false⟩],21,10⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock125 (.nil))
    20 13 0xa0c0104040200120101000100
    (by decide) ⟨10, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock127 : (⟨[⟨3,1,true⟩,⟨5,1,true⟩,⟨13,1,true⟩,⟨17,1,true⟩],29,10⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    14 6 0x300101000100
    (by decide) ⟨14, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock128 : (⟨[⟨3,1,true⟩,⟨5,1,false⟩,⟨13,1,false⟩,⟨17,1,false⟩],19,10⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock127 (.nil))
    21 13 0x40405002a0101000100
    (by decide) ⟨9, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock129 : (⟨[⟨3,1,true⟩,⟨5,1,false⟩],15,12⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock122 (.cons fangThreeFourteenBlock121 (.cons fangThreeFourteenBlock120 (.nil))))
    26 21 0x3060300050d01190e0105060200100101000100
    (by decide) ⟨7, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock130 : (⟨[⟨3,1,true⟩,⟨5,1,false⟩,⟨11,1,true⟩,⟨23,1,false⟩],25,10⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    17 22 0x80b01100e01070c010a070104020200080101000100
    (by decide) ⟨12, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock131 : (⟨[⟨3,1,true⟩,⟨5,1,false⟩,⟨11,1,false⟩,⟨19,1,false⟩],21,10⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    20 37 0x61a01040200030008200103020200061001060801080c010a0a0104020200070101000100
    (by decide) ⟨10, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock132 : (⟨[⟨3,1,true⟩,⟨5,1,false⟩,⟨11,1,false⟩,⟨17,1,false⟩],21,10⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    20 22 0xf27010b0901070d010b0701040202000a0101000100
    (by decide) ⟨10, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock133 : (⟨[⟨3,1,true⟩,⟨5,1,false⟩,⟨11,1,false⟩,⟨13,1,false⟩],15,10⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    19 19 0x909010b0801080501030202000d0101000100
    (by decide) ⟨7, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock134 : (⟨[⟨3,1,true⟩,⟨5,1,false⟩,⟨11,1,false⟩],13,11⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock133 (.cons fangThreeFourteenBlock131 (.cons fangThreeFourteenBlock130 (.cons fangThreeFourteenBlock132 (.nil)))))
    21 24 0x4020300060a01070c010a0701040202000d0101000100
    (by decide) ⟨6, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock135 : (⟨[⟨3,2,false⟩,⟨5,1,false⟩],11,12⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    15 19 0x601010b0b0109070103020200080101000100
    (by decide) ⟨5, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock136 : (⟨[⟨3,1,true⟩,⟨5,1,false⟩,⟨7,1,false⟩],19,11⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.nil)
    17 24 0x302030600071801101201040202000f0101000100
    (by decide) ⟨9, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock137 : (⟨[⟨3,1,false⟩,⟨5,1,false⟩],7,12⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock135 (.cons fangThreeFourteenBlock134 (.cons fangThreeFourteenBlock129 (.cons fangThreeFourteenBlock128 (.cons fangThreeFourteenBlock126 (.cons fangThreeFourteenBlock124 (.cons fangThreeFourteenBlock136 (.nil))))))))
    29 6 0x330101000100
    (by decide) ⟨3, rfl⟩ (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
private theorem fangThreeFourteenBlock138 : (⟨[⟨3,1,false⟩],5,13⟩ : Box).ClosedBelow (10 ^ 21) :=
  checkBoundedBlock_closes (B := 10 ^ 21) (.cons fangThreeFourteenBlock137 (.cons fangThreeFourteenBlock118 (.cons fangThreeFourteenBlock67 (.cons fangThreeFourteenBlock66 (.nil)))))
    24 18 0x4050300100d01040502000c0101000100
    (by decide) ⟨2, rfl⟩ (by decide +kernel)

theorem fangThreeFourteenRoot_closed : (⟨[⟨3,1,false⟩],5,13⟩ : Box).ClosedBelow (10 ^ 21) :=
  fangThreeFourteenBlock138

end OddWeirdSubproblems

namespace OddWeirdSubproblems

theorem noPrimitiveWeird10Pow21_threeDvd_atLeastFourteen {n : ℕ}
    (hn : n < 10 ^ 21) (ho : Odd n) (hthree : 3 ∣ n)
    (hc : 14 ≤ n.primeFactors.card)
    (hproper : ∀ d ∈ n.properDivisors, d.Deficient) : ¬ n.Weird := by
  intro hw
  have hupper := oddBelow10Pow21_primeFactors_card_le_sixteen hn ho
  obtain ⟨p, a, ys, hp, heq, hfit, ht, hlen⟩ := fangRoots_cover hn ho hw.1
  have hp3 : p = 3 := by
    rcases hp with h | rfl
    · exact h
    · obtain ⟨zs, hz, _⟩ := primeCoordinates_three ho hthree
      rw [hz] at heq
      simp at heq
  subst p
  have hr : (⟨[⟨3, 1, false⟩], 5, ys.length⟩ : Box).ClosedBelow (10 ^ 21) := by
    obtain h | h | h : ys.length = 13 ∨ ys.length = 14 ∨ ys.length = 15 := by omega
    · exact h.symm ▸ fangThreeFourteenRoot_closed
    · exact h.symm ▸ fangThreeFifteenRoot_closed
    · exact h.symm ▸ fangThreeSixteenRoot_closed
  have hnum : number ([(3, a)] ++ ys) = n := by
    rw [← heq]
    exact primeCoordinates_prod ho.pos.ne'
  have hcoords : PrimeCoordinates ([(3, a)] ++ ys) := by
    rw [← heq]
    exact ⟨fun x hx => (primeCoordinates_prime_pos hx).1, primeCoordinates_pairwise n⟩
  exact hr [(3, a)] ys ⟨.cons hfit .nil, ht, rfl⟩ hcoords
    (hnum.symm ▸ hn) (hnum.symm ▸ hw) (hnum.symm ▸ hproper)


end OddWeirdSubproblems

open OddWeirdSubproblems

theorem OMA.solution : OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H1_R2.H1 := by
  intro n hn ho ha hp hd hc
  by_contra hnp
  exact noPrimitiveWeird10Pow21_threeDvd_atLeastFourteen hn ho hd hc hp ⟨ha, hnp⟩
