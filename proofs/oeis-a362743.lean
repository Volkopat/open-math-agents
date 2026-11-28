import OMAStatements.S_oeis_a362743

-- Problem: OEIS A362743, exact classification of positive integers not representable
-- as sums of distinct numbers 4^a + 5^b.
-- Credit: @CubeJerry
-- Original proof: finite subset-sum certificates and an explicit interval-extension induction.
-- Three new summands 4^k+1, 4^k+5, 4^k+25 extend the interval at every scale.

namespace A362743Interval

def Covers (S : Finset ℕ) (L U : ℕ) : Prop :=
  ∀ n : ℕ, L ≤ n → n ≤ U → ∃ T : Finset ℕ, T ⊆ S ∧ ∑ t ∈ T, t = n

theorem extend {S : Finset ℕ} {L U x : ℕ} (h : Covers S L U)
    (hx : x ∉ S) (hoverlap : L + x ≤ U + 1) : Covers (insert x S) L (U + x) := by
  intro n hLn hnU
  by_cases hn : n ≤ U
  · obtain ⟨T, hTS, hT⟩ := h n hLn hn
    exact ⟨T, fun y hy => Finset.mem_insert_of_mem (hTS hy), hT⟩
  · have hxn : x ≤ n := by omega
    obtain ⟨T, hTS, hT⟩ := h (n - x) (by omega) (by omega)
    refine ⟨insert x T, ?_, ?_⟩
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hTS hy)
    · have hxT : x ∉ T := fun hmem => hx (hTS hmem)
      rw [Finset.sum_insert hxT, hT]
      omega
end A362743Interval

namespace A362743Interval

theorem stages
    (hseed : ∃ S : Finset ℕ, (∀ x ∈ S, ∃ a b : ℕ, x = 4^a + 5^b) ∧
      (∀ x ∈ S, x ≤ 4^2+25) ∧ Covers S 19 (4^3+20)) :
    ∀ n : ℕ, ∃ S : Finset ℕ, (∀ x ∈ S, ∃ a b : ℕ, x = 4^a + 5^b) ∧
      (∀ x ∈ S, x ≤ 4^(n+2)+25) ∧ Covers S 19 (4^(n+3)+20) := by
  intro n
  induction n with
  | zero => simpa using hseed
  | succ n ih =>
    obtain ⟨S, hgood, hbound, hcover⟩ := ih
    have hpow : 4^(n+3) = 4^(n+2)*4 := by
      rw [show n+3 = (n+2)+1 by omega, pow_succ]
    have hpow' : 4^(n+4) = 4^(n+3)*4 := by
      rw [show n+4 = (n+3)+1 by omega, pow_succ]
    have hlarge : 16 ≤ 4^(n+2) := by
      have hpos : 1 ≤ 4^n := Nat.one_le_pow n 4 (by omega)
      rw [pow_add]
      norm_num
      omega
    have hx1 : 4^(n+3)+1 ∉ S := by
      intro h
      have := hbound _ h
      omega
    have hx2 : 4^(n+3)+5 ∉ insert (4^(n+3)+1) S := by
      simp only [Finset.mem_insert, not_or]
      constructor
      · omega
      · intro h
        have := hbound _ h
        omega
    have hx3 : 4^(n+3)+25 ∉ insert (4^(n+3)+5) (insert (4^(n+3)+1) S) := by
      simp only [Finset.mem_insert, not_or]
      refine ⟨by omega, by omega, ?_⟩
      intro h
      have := hbound _ h
      omega
    have hc1 := extend hcover hx1 (by omega)
    have hc2 := extend hc1 hx2 (by omega)
    have hc3 := extend hc2 hx3 (by omega)
    refine ⟨insert (4^(n+3)+25) (insert (4^(n+3)+5) (insert (4^(n+3)+1) S)), ?_, ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert] at hx
      rcases hx with rfl | rfl | rfl | hx
      · exact ⟨n+3, 2, by norm_num⟩
      · exact ⟨n+3, 1, by norm_num⟩
      · exact ⟨n+3, 0, by norm_num⟩
      · exact hgood x hx
    · intro x hx
      simp only [Finset.mem_insert] at hx
      have heq : n+1+2 = n+3 := by omega
      rw [heq]
      rcases hx with rfl | rfl | rfl | hx
      · omega
      · omega
      · omega
      · have := hbound x hx
        omega
    · intro m hmlo hmhi
      apply hc3 m hmlo
      have heq : n+1+3 = n+4 := by omega
      rw [heq, hpow'] at hmhi
      omega

theorem covers_all
    (hseed : ∃ S : Finset ℕ, (∀ x ∈ S, ∃ a b : ℕ, x = 4^a + 5^b) ∧
      (∀ x ∈ S, x ≤ 4^2+25) ∧ Covers S 19 (4^3+20))
    (m : ℕ) (hm : 19 ≤ m) :
    ∃ T : Finset ℕ, (∀ x ∈ T, ∃ a b : ℕ, x = 4^a + 5^b) ∧ ∑ x ∈ T, x = m := by
  obtain ⟨S, hgood, _, hcover⟩ := stages hseed m
  have hp : m ≤ 4^(m+3)+20 := by
    have haux : ∀ n : ℕ, n ≤ 4^(n+3) := by
      intro n
      induction n with
      | zero => omega
      | succ n ih =>
        have hpow : 4^(n+1+3) = 4^(n+3)*4 := by
          rw [show n+1+3 = (n+3)+1 by omega, pow_succ]
        have hpos : 1 ≤ 4^(n+3) := Nat.one_le_pow (n+3) 4 (by omega)
        rw [hpow]
        omega
    have := haux m
    omega
  obtain ⟨T, hsub, hsum⟩ := hcover m hm hp
  exact ⟨T, fun x hx => hgood x (hsub hx), hsum⟩

end A362743Interval

namespace OMA.A362743Proof

def seedSet : Finset ℕ := {2, 5, 6, 9, 17, 21, 26, 29, 41}

lemma seed_covers : A362743Interval.Covers seedSet 19 84 := by
  intro n hn hu
  interval_cases n
  · exact ⟨{2, 17}, by decide, by decide⟩
  · exact ⟨{5, 6, 9}, by decide, by decide⟩
  · exact ⟨{21}, by decide, by decide⟩
  · exact ⟨{2, 5, 6, 9}, by decide, by decide⟩
  · exact ⟨{6, 17}, by decide, by decide⟩
  · exact ⟨{2, 5, 17}, by decide, by decide⟩
  · exact ⟨{2, 6, 17}, by decide, by decide⟩
  · exact ⟨{9, 17}, by decide, by decide⟩
  · exact ⟨{6, 21}, by decide, by decide⟩
  · exact ⟨{5, 6, 17}, by decide, by decide⟩
  · exact ⟨{2, 6, 21}, by decide, by decide⟩
  · exact ⟨{2, 5, 6, 17}, by decide, by decide⟩
  · exact ⟨{5, 9, 17}, by decide, by decide⟩
  · exact ⟨{6, 9, 17}, by decide, by decide⟩
  · exact ⟨{2, 5, 9, 17}, by decide, by decide⟩
  · exact ⟨{2, 6, 9, 17}, by decide, by decide⟩
  · exact ⟨{5, 9, 21}, by decide, by decide⟩
  · exact ⟨{6, 9, 21}, by decide, by decide⟩
  · exact ⟨{5, 6, 9, 17}, by decide, by decide⟩
  · exact ⟨{2, 6, 9, 21}, by decide, by decide⟩
  · exact ⟨{2, 5, 6, 9, 17}, by decide, by decide⟩
  · exact ⟨{2, 17, 21}, by decide, by decide⟩
  · exact ⟨{5, 6, 9, 21}, by decide, by decide⟩
  · exact ⟨{2, 5, 9, 26}, by decide, by decide⟩
  · exact ⟨{2, 5, 6, 9, 21}, by decide, by decide⟩
  · exact ⟨{6, 17, 21}, by decide, by decide⟩
  · exact ⟨{2, 5, 17, 21}, by decide, by decide⟩
  · exact ⟨{2, 6, 17, 21}, by decide, by decide⟩
  · exact ⟨{9, 17, 21}, by decide, by decide⟩
  · exact ⟨{2, 5, 6, 9, 26}, by decide, by decide⟩
  · exact ⟨{5, 6, 17, 21}, by decide, by decide⟩
  · exact ⟨{2, 5, 17, 26}, by decide, by decide⟩
  · exact ⟨{2, 5, 6, 17, 21}, by decide, by decide⟩
  · exact ⟨{5, 9, 17, 21}, by decide, by decide⟩
  · exact ⟨{6, 9, 17, 21}, by decide, by decide⟩
  · exact ⟨{2, 5, 9, 17, 21}, by decide, by decide⟩
  · exact ⟨{2, 6, 9, 17, 21}, by decide, by decide⟩
  · exact ⟨{2, 5, 6, 17, 26}, by decide, by decide⟩
  · exact ⟨{5, 9, 17, 26}, by decide, by decide⟩
  · exact ⟨{5, 6, 9, 17, 21}, by decide, by decide⟩
  · exact ⟨{2, 5, 9, 17, 26}, by decide, by decide⟩
  · exact ⟨{2, 5, 6, 9, 17, 21}, by decide, by decide⟩
  · exact ⟨{5, 9, 21, 26}, by decide, by decide⟩
  · exact ⟨{6, 9, 21, 26}, by decide, by decide⟩
  · exact ⟨{5, 6, 9, 17, 26}, by decide, by decide⟩
  · exact ⟨{2, 6, 9, 21, 26}, by decide, by decide⟩
  · exact ⟨{2, 5, 6, 9, 17, 26}, by decide, by decide⟩
  · exact ⟨{2, 17, 21, 26}, by decide, by decide⟩
  · exact ⟨{5, 6, 9, 21, 26}, by decide, by decide⟩
  · exact ⟨{2, 5, 6, 9, 17, 29}, by decide, by decide⟩
  · exact ⟨{2, 5, 6, 9, 21, 26}, by decide, by decide⟩
  · exact ⟨{6, 17, 21, 26}, by decide, by decide⟩
  · exact ⟨{2, 5, 17, 21, 26}, by decide, by decide⟩
  · exact ⟨{2, 6, 17, 21, 26}, by decide, by decide⟩
  · exact ⟨{9, 17, 21, 26}, by decide, by decide⟩
  · exact ⟨{2, 5, 17, 21, 29}, by decide, by decide⟩
  · exact ⟨{5, 6, 17, 21, 26}, by decide, by decide⟩
  · exact ⟨{9, 17, 21, 29}, by decide, by decide⟩
  · exact ⟨{2, 5, 6, 17, 21, 26}, by decide, by decide⟩
  · exact ⟨{5, 9, 17, 21, 26}, by decide, by decide⟩
  · exact ⟨{6, 9, 17, 21, 26}, by decide, by decide⟩
  · exact ⟨{2, 5, 9, 17, 21, 26}, by decide, by decide⟩
  · exact ⟨{2, 6, 9, 17, 21, 26}, by decide, by decide⟩
  · exact ⟨{6, 9, 17, 21, 29}, by decide, by decide⟩
  · exact ⟨{2, 5, 9, 17, 21, 29}, by decide, by decide⟩
  · exact ⟨{5, 6, 9, 17, 21, 26}, by decide, by decide⟩

lemma seed_bound : ∀ x ∈ seedSet, x ≤ 41 := by decide

lemma seed_allowed : ∀ x ∈ seedSet, ∃ a b : ℕ, x = 4 ^ a + 5 ^ b := by
  intro x hx
  simp only [seedSet, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 0, by decide⟩
  · exact ⟨1, 0, by decide⟩
  · exact ⟨0, 1, by decide⟩
  · exact ⟨1, 1, by decide⟩
  · exact ⟨2, 0, by decide⟩
  · exact ⟨2, 1, by decide⟩
  · exact ⟨0, 2, by decide⟩
  · exact ⟨1, 2, by decide⟩
  · exact ⟨2, 2, by decide⟩

lemma seed : ∃ S : Finset ℕ, (∀ x ∈ S, ∃ a b : ℕ, x = 4 ^ a + 5 ^ b) ∧ (∀ x ∈ S, x ≤ 4^2+25) ∧ A362743Interval.Covers S 19 (4^3+20) := by
  exact ⟨seedSet, seed_allowed, seed_bound, seed_covers⟩

end OMA.A362743Proof

namespace OMA.A362743Proof
open OMA.S_oeis_a362743

def exceptions : Finset ℕ := {1, 3, 4, 10, 12, 18}
def smallValues : Finset ℕ := {2, 5, 6, 9, 17}

lemma small_allowed {x : ℕ} (hx : x ∈ smallValues) : ∃ a b : ℕ, x = 4^a + 5^b := by
  norm_num [smallValues] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact ⟨0,0,by norm_num⟩
  · exact ⟨1,0,by norm_num⟩
  · exact ⟨0,1,by norm_num⟩
  · exact ⟨1,1,by norm_num⟩
  · exact ⟨2,0,by norm_num⟩

lemma allowed_small {x : ℕ} (hx : x ≤ 18) (h : ∃ a b : ℕ, x = 4^a + 5^b) :
    x ∈ smallValues := by
  rcases h with ⟨a,b,rfl⟩
  have h4 : 4^a ≤ 18 := (Nat.le_add_right _ _).trans hx
  have h5 : 5^b ≤ 18 := (Nat.le_add_left _ _).trans hx
  have ha : a ≤ 2 := by
    by_contra h
    have hpow := Nat.pow_le_pow_right (by omega : 0 < (4:ℕ)) (by omega : 3 ≤ a)
    norm_num at hpow
    omega
  have hb : b ≤ 1 := by
    by_contra h
    have hpow := Nat.pow_le_pow_right (by omega : 0 < (5:ℕ)) (by omega : 2 ≤ b)
    norm_num at hpow
    omega
  interval_cases a <;> interval_cases b <;> norm_num [smallValues] at *

lemma small_nonrep (n : ℕ) (hn : n ∈ exceptions) : ¬ IsRepresentable n := by
  rintro ⟨S, hS, hsum⟩
  have hn18 : n ≤ 18 := by
    norm_num [exceptions] at hn
    omega
  have hsub : S ⊆ smallValues := by
    intro x hx
    apply allowed_small
    · have hle : x ≤ ∑ y ∈ S, y := Finset.single_le_sum (fun y hy => Nat.zero_le y) hx
      omega
    · exact hS x hx
  have hno : ∀ S ∈ smallValues.powerset, ∀ n ∈ exceptions, (∑ x ∈ S, x) ≠ n := by decide
  exact hno S (Finset.mem_powerset.mpr hsub) n hn hsum

lemma small_rep (n : ℕ) (hn : 0 < n) (hn18 : n ≤ 18) (hne : n ∉ exceptions) :
    IsRepresentable n := by
  have hyes : ∀ n ∈ Finset.Icc 1 18, n ∉ exceptions →
      ∃ S ∈ smallValues.powerset, (∑ x ∈ S, x) = n := by decide
  obtain ⟨S,hS,hs⟩ := hyes n (Finset.mem_Icc.mpr ⟨hn,hn18⟩) hne
  refine ⟨S,?_,hs⟩
  intro x hx
  exact small_allowed ((Finset.mem_powerset.mp hS) hx)

end OMA.A362743Proof

open OMA.S_oeis_a362743 OMA.A362743Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a362743.main := by
  ext n
  change (0 < n ∧ ¬ IsRepresentable n) ↔ _
  have h : (0 < n ∧ ¬ IsRepresentable n) ↔ n ∈ exceptions := by
    constructor
    · rintro ⟨hn, hnot⟩
      by_contra hne
      apply hnot
      by_cases hn18 : n ≤ 18
      · exact small_rep n hn hn18 hne
      · exact A362743Interval.covers_all seed n (by omega)
    · intro hn
      refine ⟨?_, small_nonrep n hn⟩
      norm_num [exceptions] at hn
      omega
  simpa [exceptions] using h
