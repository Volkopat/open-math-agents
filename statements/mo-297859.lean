import Mathlib

/-!
# Optimizing partitions of independently sampled coupons

Source: Penelope Benenati, https://mathoverflow.net/questions/297859 (CC BY-SA 3.0).
Credit: @connoranderson.

For a vector of type multiplicities, a partition fits in b groups precisely
when no type occurs more than b times and their total size is at most b*k.
There is a partition with at least t full groups precisely when the sum of
the multiplicities truncated at t is at least t*k. The two expectations are
therefore explicit multinomial sums over bounded occupancy vectors.

A row records a group as a finite set of types. Empty padding may be deleted.
Labeling the first t rows as full expresses the existence of t full groups;
all coupons must occur in the complete collection of rows.
-/
namespace OMA.S_mo_297859
open Finset
abbrev Counts (n : ℕ) := Fin n → ℕ
abbrev Groups (b n : ℕ) := Fin b → Finset (Fin n)
def multiplicity {b n : ℕ} (G : Groups b n) (a : Fin n) : ℕ :=
  ∑ j, if a ∈ G j then 1 else 0
def occupied {m n : ℕ} (w : Fin m → Fin n) (a : Fin n) : ℕ :=
  ∑ i, if w i=a then 1 else 0
def fits {n : ℕ} (c : Counts n) (b k : ℕ) : Prop :=
  ∃ G : Groups b n, multiplicity G=c ∧ ∀ j, (G j).card≤k
def full {n : ℕ} (c : Counts n) (t k : ℕ) : Prop :=
  ∃ G : Groups t n, (∀ a, multiplicity G a≤c a) ∧ ∀ j, (G j).card=k
def completeFull {n : ℕ} (c : Counts n) (t k : ℕ) : Prop :=
  ∃ (b : ℕ) (G : Groups (t+b) n), multiplicity G=c ∧
    (∀ j, (G j).card ≤ k) ∧ ∀ j : Fin t, (G (j.castAdd b)).card = k
noncomputable def minimumGroups {n : ℕ} (c : Counts n) (k : ℕ) := sInf {b | fits c b k}
noncomputable def maximumFull {n : ℕ} (c : Counts n) (k : ℕ) := sSup {t | completeFull c t k}
def smallFormula {n : ℕ} (c : Counts n) (k : ℕ) := max (((∑ a, c a)+k-1)/k) (univ.sup c)
def fullFormula {n : ℕ} (c : Counts n) (k : ℕ) :=
  (range ((∑ a,c a)+1)).sup (fun t => if t*k ≤ ∑ a, min (c a) t then t else 0)
noncomputable def expectation (m n : ℕ) (f : Counts n → ℕ) : ℚ :=
  (∑ w : Fin m → Fin n, (f (occupied w):ℚ))/(n:ℚ)^m
noncomputable def occupancyAverage (m n : ℕ) (f : Counts n → ℕ) : ℚ :=
  (∑ c : Fin n → Fin (m+1), if (∑ a, (c a).val)=m then
    (Nat.multinomial univ (fun a => (c a).val):ℚ)*f (fun a => (c a).val) else 0)/(n:ℚ)^m

theorem main :
    (∀ {n b k : ℕ} (c : Counts n), fits c b k ↔ (∑ a,c a) ≤ b*k ∧ ∀ a,c a ≤ b) ∧
    (∀ {n t k : ℕ} (c : Counts n), 0 < k → (completeFull c t k ↔ t*k ≤ ∑ a,min (c a) t)) ∧
    (∀ {n k : ℕ} (c : Counts n), 0 < k →
      minimumGroups c k = smallFormula c k ∧ maximumFull c k = fullFormula c k) ∧
    (∀ m n k : ℕ, 0 < n → 0 < k →
      expectation m n (fun c => minimumGroups c k) = occupancyAverage m n (fun c => smallFormula c k) ∧
      expectation m n (fun c => maximumFull c k) = occupancyAverage m n (fun c => fullFormula c k)) := by
  sorry

end OMA.S_mo_297859
