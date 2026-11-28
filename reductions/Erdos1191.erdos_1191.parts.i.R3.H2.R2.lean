import OMAReductions.R_Erdos1191_erdos_1191_parts_i_R3

-- Reduction Erdos1191.erdos_1191.parts.i.R3.H2.R2 of the threshold-doubling step.
-- Credit: @ellisjr
--
-- At H = 2^(4*n), take the fixed early window (2^(5*n),2^(6*n)].
-- Classify positive short pairs by the lower mark's dyadic band.  M/(n*H)
-- is the normalized sum with per-band cap 1/n. An extra singleton band at
-- the upper endpoint can never own a positive pair.
--
-- The first step is a local geometric estimate. The second asks for a low
-- capped count, with a lower density assumption only at multiples of four.
-- arithmetic_of_doubling proves that the exact parent implies the second
-- step. Hence its fixed-window conclusion introduces no stronger conjecture.

namespace OMA.R_Erdos1191_erdos_1191_parts_i_R3_H2_R2

/-- A Sidon prefix above the critical lower bound on the early window
forces short-pair mass in a positive proportion of its lower bands. -/
def H1 : Prop :=
  ∀ a : ℕ, 0 < a → ∃ t N : ℕ, 0 < t ∧ 0 < N ∧
    ∀ n : ℕ, N ≤ n → ∀ S : Finset ℕ, IsSidon (S : Set ℕ) →
    (∀ j ∈ Finset.Icc (5*n) (6*n),
      512*2^j < (2*a)*(S.filter (· ≤ 2^j)).card^2*j) →
      let h := 2^(4*n)
      let W := S.filter (fun a => 2^(5*n) < a ∧ a ≤ 2^(6*n))
      let M := ∑ r ∈ Finset.range n, min h (n *
        ((W ×ˢ W).filter (fun p => p.1 < p.2 ∧ p.2 < p.1+h ∧
          2^(5*n+r) ≤ p.1 ∧ p.1 < 2^(5*n+r+1))).card)
      n*h < t*M

/-- For an attainable threshold, a Sidon prefix remaining large on the
four-exponent grid has a late early window with small capped pair mass. -/
def H2 : Prop :=
  ∀ a : ℕ, 0 < a →
    (∀ J : ℕ, ∃ K ≥ J, ∀ S : Finset ℕ,
      (S : Set ℕ) ⊆ Set.Icc 1 (2^K) → IsSidon (S : Set ℕ) →
      ∃ j ∈ Finset.Icc J K, a*(S.filter (· ≤ 2^j)).card^2*j ≤ 512*2^j) →
    ∀ t J N : ℕ, 0 < t → ∃ K ≥ J, ∀ S : Finset ℕ,
    (S : Set ℕ) ⊆ Set.Icc 1 (2^K) → IsSidon (S : Set ℕ) →
    (∀ r : ℕ, J ≤ 4*r → 4*r ≤ K →
      512*2^(4*r) < (2*a)*(S.filter (· ≤ 2^(4*r))).card^2*(4*r)) →
    ∃ n : ℕ, N ≤ n ∧ J ≤ 5*n ∧ 6*n ≤ K ∧
      let h := 2^(4*n)
      let W := S.filter (fun a => 2^(5*n) < a ∧ a ≤ 2^(6*n))
      let M := ∑ r ∈ Finset.range n, min h (n *
        ((W ×ˢ W).filter (fun p => p.1 < p.2 ∧ p.2 < p.1+h ∧
          2^(5*n+r) ≤ p.1 ∧ p.1 < 2^(5*n+r+1))).card)
      t*M ≤ n*h

theorem main : H1 → H2 → OMA.R_Erdos1191_erdos_1191_parts_i_R3.H2 := by
  intro geom arith a base
  by_cases hz : a=0
  · simpa only [hz, Nat.mul_zero] using base
  have ha : 0<a := Nat.pos_of_ne_zero hz
  intro J
  obtain ⟨t,N,ht,_,hforce⟩ := geom a ha
  obtain ⟨K,hK,hfind⟩ := arith a ha base t J N ht
  refine ⟨K,hK,?_⟩
  intro S hS hs
  by_contra hnone
  have dense (j : ℕ) (hj : j ∈ Finset.Icc J K) :
      512*2^j < (2*a)*(S.filter (· ≤ 2^j)).card^2*j :=
    Nat.lt_of_not_ge (fun h => hnone ⟨j,hj,h⟩)
  obtain ⟨n,hn,hstart,hend,hlo⟩ :=
    hfind S hS hs (fun r hr hr' => dense (4*r) (Finset.mem_Icc.mpr ⟨hr,hr'⟩))
  have hhi := hforce n hn S hs (fun j hj => dense j
    (Finset.mem_Icc.mpr ⟨hstart.trans (Finset.mem_Icc.mp hj).1,
      (Finset.mem_Icc.mp hj).2.trans hend⟩))
  exact (Nat.not_lt_of_ge hlo) hhi

/-- Monotonicity between two dyadic prefix counts. -/
lemma prefix_mono (S : Finset ℕ) {i j : ℕ} (hij : i ≤ j) :
    (S.filter (· ≤ 2^i)).card ≤ (S.filter (· ≤ 2^j)).card := by
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hs,h⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hs,h.trans (Nat.pow_le_pow_right (by decide) hij)⟩

/-- The arithmetic step follows from the parent by four doublings and
the bounded loss incurred between successive checkpoints. -/
theorem arithmetic_of_doubling (parent : OMA.R_Erdos1191_erdos_1191_parts_i_R3.H2) : H2 := by
  intro a ha base t J N ht
  let Att (b : ℕ) : Prop := ∀ U : ℕ, ∃ V ≥ U, ∀ S : Finset ℕ,
    (S : Set ℕ) ⊆ Set.Icc 1 (2^V) → IsSidon (S : Set ℕ) →
    ∃ j ∈ Finset.Icc U V, b*(S.filter (· ≤ 2^j)).card^2*j ≤ 512*2^j
  have step (b : ℕ) : Att b → Att (2*b) := parent b
  have h16 : Att (2*(2*(2*(2*a)))) := step _ (step _ (step _ (step a base)))
  rw [show 2*(2*(2*(2*a)))=16*a by ring] at h16
  obtain ⟨K,hK,hstop⟩ := h16 (J+4)
  refine ⟨K,by omega,?_⟩
  intro S hS hs grid
  exfalso
  obtain ⟨j,hj,hlo⟩ := hstop S hS hs
  obtain ⟨hjJ,hjK⟩ := Finset.mem_Icc.mp hj
  let r := j/4
  have hr : 4*r ≤ j := by dsimp [r]; omega
  have h3 : j ≤ 4*r+3 := by dsimp [r]; omega
  have hgrid := grid r (by omega) (by omega)
  have hc := prefix_mono S hr
  have hp : (2:ℕ)^j ≤ 8*2^(4*r) := calc
    _ ≤ 2^(4*r+3) := Nat.pow_le_pow_right (by decide) h3
    _ = _ := by rw [pow_add]; ring
  have hhi : 512*2^j < (16*a)*(S.filter (· ≤ 2^j)).card^2*j := calc
    _ ≤ 8*(512*2^(4*r)) := by omega
    _ < 8*((2*a)*(S.filter (· ≤ 2^(4*r))).card^2*(4*r)) :=
      Nat.mul_lt_mul_of_pos_left hgrid (by decide)
    _ ≤ 8*((2*a)*(S.filter (· ≤ 2^j)).card^2*j) := by gcongr
    _ = _ := by ring
  exact (Nat.not_lt_of_ge hlo) hhi

end OMA.R_Erdos1191_erdos_1191_parts_i_R3_H2_R2
