import FormalConjectures.ErdosProblems.«889»

/-!
# The general case of Erdős Problem 889 follows from the case l = 0

A prime factor of n + k is counted by v(n, k) exactly when it exceeds k. Hence v(n + l, k') and
v(n, l + k') count prime factors of the same integer n + l + k', and they differ only by primes in
the interval (k', l + k'], of which there are at most l. Taking suprema gives
v_0(n + l) ≤ v_l(n) + l, so v_0(n) → ∞ forces v_l(n) → ∞ for every fixed l.

H1 is Erdős Problem 889 itself (open). H2 is the elementary comparison.

Source: Erdős and Selfridge, Some problems on the prime factors of consecutive integers,
Illinois J. Math. 11 (1967), 428-430.
-/
-- Reduction Erdos889.erdos_889.variants.general.R1 of Erdős Problem 889
-- Credit: @LordMike

open Finset Nat Filter Topology

namespace OMA.R_Erdos889_erdos_889_variants_general_R1

/-- Erdős Problem 889, the case l = 0: v_0(n) tends to infinity. -/
def H1 : Prop := Tendsto Erdos889.v₀ atTop (𝓝 ⊤)

/-- Moving the start from n to n + l removes at most l counted primes. -/
def H2 : Prop := ∀ l n k : ℕ, Erdos889.v (n + l) k ≤ Erdos889.v n (l + k) + l

lemma v₀_le (h2 : H2) (l n : ℕ) : Erdos889.v₀ (n + l) ≤ Erdos889.v_l l n + l := by
  unfold Erdos889.v₀ Erdos889.v_l
  refine iSup_le fun k ↦ ?_
  have h : (Erdos889.v (n + l) k : ℕ∞) ≤ (Erdos889.v n (l + k) : ℕ∞) + l := by
    exact_mod_cast h2 l n k
  refine h.trans ?_
  gcongr
  exact le_iSup₂_of_le (l + k) (Nat.le_add_right l k) le_rfl

theorem main : H1 → H2 → type_of% @Erdos889.erdos_889.variants.general := by
  intro h1 h2 l
  rw [H1, ENat.tendsto_nhds_top_iff_natCast_lt] at h1
  rw [ENat.tendsto_nhds_top_iff_natCast_lt]
  intro N
  obtain ⟨a, ha⟩ := eventually_atTop.mp (h1 (N + l))
  refine eventually_atTop.mpr ⟨a, fun n hn ↦ ?_⟩
  have h3 : ((N + l : ℕ) : ℕ∞) < Erdos889.v_l l n + l :=
    (ha (n + l) (by omega)).trans_le (v₀_le h2 l n)
  rw [Nat.cast_add] at h3
  exact (ENat.add_lt_add_iff_right (ENat.natCast_ne_top l)).mp h3

end OMA.R_Erdos889_erdos_889_variants_general_R1
