import Mathlib

/-!
# Wu's generating function and recurrence for the partitions in A325260

Gus Wiseman assigns a partition its sequence of lengths, repeatedly replacing
a multiset by the multiplicities of its distinct entries. A325260 counts
the partitions whose length sequence contains every integer from 1 through
the number of parts. The empty partition is included at index zero.

A partition is encoded by the increasing list of its distinct positive part
sizes and the multiplicity of each size. Its profile is that multiplicity
list. The positive gaps between successive sizes (starting from zero) are
independent. Reducing the first gap by one reduces the weight by the sum of
the remaining multiplicities, including the first multiplicity. If the gap
was one, that first size disappears. These two possibilities give the
enumeration in 'ways' below. The profile bound is the partition weight.

Sources: https://oeis.org/A325260, https://oeis.org/A325251.
Credit: Gus Wiseman (sequence), Chai Wah Wu (conjectures, January 13, 2021),
Robert Leshner (@rleshner, formalization).
-/

namespace OMA.S_oeis_a325260

/-- Each distinct entry contributes its positive multiplicity. -/
def mu (l : List ℕ) : List ℕ := l.dedup.map (fun x => l.count x)

/-- Iteration on a singleton continues at length one. Thus continuing the
orbit leaves the set of observed lengths unchanged. -/
def Covered (p : List ℕ) : Prop :=
  ∀ i : ℕ, 1 ≤ i → i ≤ p.sum →
    i = p.sum ∨ ∃ k : ℕ, ((mu^[k]) p).length = i

/-- All positive multiplicity lists of total at most the stated bound. -/
def profiles : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | n+1 => insert [] (((profiles n).image (1 :: ·)) ∪
      ((profiles n).image (fun l => match l with | [] => [] | a::t => (a+1)::t)))

/-- All positive gap vectors of length k with entries at most n. -/
def vectors (n : ℕ) : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | k+1 => (Finset.Icc 1 n).biUnion fun g => (vectors n k).image (g :: ·)

/-- Increasing every part size from position i onward by one gap adds that
gap times the sum of the multiplicities from i onward. -/
def weight : List ℕ → List ℕ → ℕ
  | a::p, g::v => (a::p).sum*g + weight p v
  | _, _ => 0

/-- Each counted vector gives the positive successive differences of the
increasing distinct part sizes; its partial sums recover those sizes. -/
def choices (p : List ℕ) (n : ℕ) : Finset (List ℕ) :=
  (vectors n p.length).filter (fun v => weight p v=n)

def ways (p : List ℕ) (n : ℕ) : ℕ := (choices p n).card

/-- Count the partitions after applying the original omega-sequence test. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact ∑ p ∈ (profiles n).filter Covered, ways p n

/-- Numerator after writing the conjectured denominator as
(1-x²)(1-x³)(1-x⁴). -/
noncomputable def numerator : Polynomial ℤ := 1+Polynomial.X+Polynomial.X^2+Polynomial.X^5-
  Polynomial.X^6+Polynomial.X^7+Polynomial.X^8+Polynomial.X^9

/-- The coefficient identity gives Wu's generating function, and its
  coefficients above degree nine give his homogeneous recurrence. -/
theorem main :
    ((1-PowerSeries.X^2)*(1-PowerSeries.X^3)*(1-PowerSeries.X^4)*
      (PowerSeries.mk fun n => (a n : ℤ)) = (numerator : PowerSeries ℤ)) ∧
    ∀ n : ℕ, 9 < n → (a n : ℤ) = (a (n-2) : ℤ) + a (n-3) + a (n-4) -
      a (n-5) - a (n-6) - a (n-7) + a (n-9) := by
  sorry

end OMA.S_oeis_a325260
