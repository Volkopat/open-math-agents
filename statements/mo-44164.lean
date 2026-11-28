import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Truthful multi-unit auctions that guarantee selling all items

Source: https://mathoverflow.net/questions/44164
Credit: @LDJAI

Jack's October 2010 question orders values strictly and requires a revenue
guarantee for every profile. In January 2011 Dave Pritchard gave a counterexample
using equal reports and singled out the remaining question about distinct bids.
The winner set below is deterministic. Quasilinear utility and ex-post participation
make the usual voluntary auction convention explicit. Payments are arbitrary real
transfers, so this formulation permits subsidies as well as ordinary payments.
-/
namespace AuctionQuestion
open scoped BigOperators
abbrev Profile (n : ℕ) := Fin n → ℝ

def Admissible {n} (b : Profile n) : Prop := ∀ i, 0 ≤ b i

def Utility {n} (A : Profile n → Finset (Fin n)) (p : Profile n → Fin n → ℝ)
    (b : Profile n) (i : Fin n) (v : ℝ) : ℝ := (if i ∈ A b then v else 0) - p b i

def DSIC {n} (A : Profile n → Finset (Fin n)) (p : Profile n → Fin n → ℝ) : Prop :=
  ∀ b, Admissible b → ∀ i r, 0 ≤ r →
    Utility A p (Function.update b i r) i (b i) ≤ Utility A p b i (b i)

def Participation {n} (A : Profile n → Finset (Fin n)) (p : Profile n → Fin n → ℝ) : Prop :=
  ∀ b, Admissible b → ∀ i, 0 ≤ Utility A p b i (b i)

/-- A top-k winner set, allowing an arbitrary choice at equal bids. -/
def Top {n} (k : ℕ) (b : Profile n) (s : Finset (Fin n)) : Prop :=
  s.card = k ∧ ∀ i ∈ s, ∀ j ∉ s, b j ≤ b i

/-- The highest losing bid for any top winner set equals the (k+1)st bid. -/
def RevenueGuarantee {n} (k : ℕ) (p : Profile n → Fin n → ℝ) : Prop :=
  ∀ b, Admissible b → ∀ s, Top k b s → ∀ j ∉ s, (∀ l ∉ s, b l ≤ b j) →
    (k:ℝ) * b j ≤ ∑ i, p b i

def DistinctProfileRigidity : Prop :=
  ∀ n k : ℕ, 0 < k → k < n → ∀ (A : Profile n → Finset (Fin n)) (p : Profile n → Fin n → ℝ),
    DSIC A p → Participation A p → (∀ b, Admissible b → (A b).card = k) →
    RevenueGuarantee k p → ∀ b, Admissible b → Function.Injective b → Top k b (A b)

end AuctionQuestion

namespace OMA.S_mo_44164

theorem main : AuctionQuestion.DistinctProfileRigidity := by
  sorry

end OMA.S_mo_44164
