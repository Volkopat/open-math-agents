import OMAStatements.S_oeis_a236531

/-! The strengthened representation already implies positivity, apart from three explicit inputs. -/

namespace OMA.R_oeis_a236531_R1

open OMA.S_oeis_a236531

def H1 : Prop := ∀ n : ℕ, 3 < n → n ≠ 11 → n ≠ 125 →
  ∃ k m : ℕ, 0 < k ∧ 0 < m ∧ n = k + m ∧
    (6*k-1).Prime ∧ (6*k+1).Prime ∧ (prime m+2).Prime ∧ (3*prime m-10).Prime

def H2 : Prop := ∀ n : ℕ, 458 < n → ∃ p q : ℕ, 0 < q ∧ n = p+q ∧
  p.Prime ∧ (p+2).Prime ∧ (prime q+2).Prime

lemma positive {k m : ℕ} (hk : 0 < k) (hm : 0 < m) (h₁ : (6*k-1).Prime)
    (h₂ : (6*k+1).Prime) (h₃ : (prime m+2).Prime) : 0 < a (k+m) := by
  apply Finset.card_pos.mpr
  refine ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨hk,by omega⟩,h₁,h₂,?_,?_⟩⟩
  · exact Nat.prime_nth_prime _
  · simpa using h₃

lemma rank {q i : ℕ} (hq : q.Prime) (hc : Nat.count Nat.Prime q = i) : prime (i+1) = q := by
  simpa [prime,hc] using Nat.nth_count hq

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma exceptions : 0 < a 3 ∧ 0 < a 11 ∧ 0 < a 125 := by
  have h3 : prime 2 = 3 := rank (q := 3) (i := 1) (by decide) (by decide)
  have h29 : prime 10 = 29 := rank (q := 29) (i := 9) (by decide) (by decide)
  have h617 : prime 113 = 617 := rank (q := 617) (i := 112) (by decide) (by decide)
  exact ⟨positive (k := 1) (m := 2) (by decide) (by decide) (by decide) (by decide)
    (by rw [h3]; decide), positive (k := 1) (m := 10) (by decide) (by decide)
    (by decide) (by decide) (by rw [h29]; decide), positive (k := 12) (m := 113)
    (by decide) (by decide) (by decide) (by decide) (by rw [h617]; decide)⟩

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a236531.main := by
  intro h1 h2
  refine ⟨?_,h1,?_⟩
  · intro n hn
    by_cases h : n = 3
    · simpa [h] using exceptions.1
    by_cases h11 : n = 11
    · simpa [h11] using exceptions.2.1
    by_cases h125 : n = 125
    · simpa [h125] using exceptions.2.2
    obtain ⟨k,m,hk,hm,rfl,ha,hb,hc,_⟩ := h1 n (by omega) h11 h125
    exact positive hk hm ha hb hc
  · intro n hn
    obtain ⟨p,q,hq,he,ha,hb,hc⟩ := h2 n hn
    exact ⟨p,q,hq,he,ha,hb,Nat.prime_nth_prime _,hc⟩

end OMA.R_oeis_a236531_R1
