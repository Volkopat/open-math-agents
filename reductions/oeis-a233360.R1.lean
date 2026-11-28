import OMAStatements.S_oeis_a233360

-- Reduction oeis-a233360.R1 of A233360: Primes of the form L(k) + q(m) with k > 0 and m > 0, where L(k) is the k-th Lucas number (A000204), and q(.) is the strict partiti
-- Credit: @Pixelstorm44
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_oeis_a233360_R1

open OMA.S_oeis_a233360

private theorem lucas_pos (k : ℕ) : 0 < L k := by
  induction k using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more k h₀ h₁ => simp only [L]; omega

private theorem index_le_lucas (k : ℕ) : k ≤ L k := by
  induction k using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more k h₀ h₁ => have := lucas_pos k; simp only [L]; omega

/-- Inject the possible smaller parts into the partitions with two distinct parts. -/
private theorem partition_lower_bound (m : ℕ) : (m-1)/2 ≤ q m := by
  let f (i : Fin ((m-1)/2)) : Nat.Partition m :=
    { parts := (i.val+1) ::ₘ {m-(i.val+1)}
      parts_pos := by
        intro j hj
        have := i.isLt
        simp only [Multiset.mem_cons, Multiset.mem_singleton] at hj
        omega
      parts_sum := by have := i.isLt; simp; omega }
  have mem (i : Fin ((m-1)/2)) : f i ∈ Nat.Partition.distincts m := by
    have := i.isLt
    simp [f, Nat.Partition.distincts]
    omega
  have inj : Function.Injective f := by
    intro i j hij
    have hm : i.val+1 ∈ (f j).parts := by
      rw [← hij]
      simp [f]
    have := i.isLt
    have := j.isLt
    simp [f] at hm
    apply Fin.ext
    omega
  simpa [q] using Finset.card_le_card_of_injOn (s := Finset.univ) f
    (t := Nat.Partition.distincts m) (fun i _ => mem i) inj.injOn

/-- Every representation with sum at most B lies on a diagonal at most 3B+2. -/
theorem diagonal_bound (k m : ℕ) : k + m ≤ 3*(L k + q m)+2 := by
  have := index_le_lucas k
  have := partition_lower_bound m
  omega

/-- Prime hits on arbitrarily large diagonals suffice, in particular under A233359. -/
theorem infinite_of_diagonal_hits
    (h : ∀ D : ℕ, ∃ k m : ℕ, 0 < k ∧ 0 < m ∧ D ≤ k+m ∧ (L k + q m).Prime) :
    S.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro B
  obtain ⟨k,m,hk,hm,hD,hp⟩ := h (3*B+3)
  refine ⟨L k + q m, ⟨hp,k,m,hk,hm,rfl⟩, ?_⟩
  have := diagonal_bound k m
  omega

/-- If v survives trial division through √(v/2), a composite v has
exactly two prime factors and the larger is less than twice the smaller. -/
theorem balanced_of_survives {v : ℕ}
    (hs : 2 ≤ v ∧ ∀ d : ℕ, d.Prime → d ∣ v → v < 2*d^2) (hc : ¬v.Prime) :
    ∃ p r : ℕ, p.Prime ∧ r.Prime ∧ p ≤ r ∧ r < 2*p ∧ v = p*r := by
  obtain ⟨hv,hs⟩ := hs
  let p := v.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  obtain ⟨r,he⟩ := Nat.minFac_dvd v
  change v = p*r at he
  have hr : 2 ≤ r := by
    by_contra! h
    interval_cases r <;> simp_all
  have hpr : p ≤ r := Nat.minFac_le_of_dvd hr ⟨p, by rw [he, Nat.mul_comm]⟩
  have hb := hs p hp (Nat.minFac_dvd v)
  have hlt : r < 2*p := by
    by_contra! h
    have := Nat.mul_le_mul_left p h
    nlinarith
  have hrp : r.Prime := by
    by_contra h
    have hrmin := Nat.minFac_prime (n := r) (by omega)
    have hd : r.minFac ∣ v := dvd_trans (Nat.minFac_dvd r) ⟨p, by rw [he, Nat.mul_comm]⟩
    have hpm : p ≤ r.minFac := Nat.minFac_le_of_dvd hrmin.two_le hd
    have hl := Nat.minFac_sq_le_self (n := r) (by omega) h
    nlinarith [Nat.mul_le_mul hpm hrmin.two_le]
  exact ⟨p,r,hp,hrp,hpr,hlt,he⟩

open Classical in
/-- On arbitrarily large blocks N ≤ k+m < 2N, at least N representations
survive trial division through the square root of half their value. -/
def H1 : Prop := ∀ D : ℕ, ∃ N ≥ D, N ≤
  (((Finset.Ico 1 (2*N)) ×ˢ (Finset.Ico 1 (2*N))).filter fun (k,m) =>
    N ≤ k+m ∧ k+m < 2*N ∧ 2 ≤ L k + q m ∧
    ∀ d : ℕ, d.Prime → d ∣ L k + q m → L k + q m < 2*d^2).card

open Classical in
/-- Eventually fewer than N representations per block are products of
two primes within a factor of two of one another. -/
def H2 : Prop := ∃ D : ℕ, ∀ N ≥ D,
  (((Finset.Ico 1 (2*N)) ×ˢ (Finset.Ico 1 (2*N))).filter fun (k,m) =>
    N ≤ k+m ∧ k+m < 2*N ∧
    ∃ p r : ℕ, p.Prime ∧ r.Prime ∧ p ≤ r ∧ r < 2*p ∧ L k + q m = p*r).card < N

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a233360.main := by
  classical
  intro h₁ h₂
  obtain ⟨D₀,h₂⟩ := h₂
  apply infinite_of_diagonal_hits
  intro D
  obtain ⟨N,hN,h₁⟩ := h₁ (max D D₀)
  have hu := h₂ N (le_trans (le_max_right _ _) hN)
  by_contra! h
  apply (Nat.not_lt_of_ge h₁) (lt_of_le_of_lt (Finset.card_le_card ?_) hu)
  rintro ⟨k,m⟩ hx
  obtain ⟨hkm,hn,hlt,hs⟩ := Finset.mem_filter.mp hx
  apply Finset.mem_filter.mpr
  refine ⟨hkm,hn,hlt,balanced_of_survives hs ?_⟩
  simp only [Finset.mem_product, Finset.mem_Ico] at hkm
  apply h k m (by omega) (by omega)
  exact (le_max_left D D₀).trans (hN.trans hn)

end OMA.R_oeis_a233360_R1
