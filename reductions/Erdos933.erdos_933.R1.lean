import FormalConjectures.ErdosProblems.«933»

/-!
Reduction of Erdos933.erdos_933 (a concrete-type problem, no universe issues).

H1 is the upstream-proved base case of Erdos: for infinitely many n the quantity
2^k(n) 3^l(n) exceeds n log n (fully proved in the FormalConjectures module).
H2 is the genuinely open amplification core: if the exceedance holds infinitely
often at level C, then it holds infinitely often at level C+1.  Iterating H2 from
the proved level C = 1 makes the ratio unbounded infinitely often, which is
exactly the EReal limsup = top assertion of the target.

-- Credit: @PetrouilFan
-/

open Filter
open scoped Topology

namespace OMA.R_Erdos933_erdos_933_R1

/-- Upstream-proved base case: Erdos933.variants.lower_bound (full proof in the module). -/
def H1 : Prop :=
  Set.Infinite {n : ℕ | (n : ℝ) * Real.log (n : ℝ) <
    ((2 ^ Erdos933.k n * 3 ^ Erdos933.l n : ℕ) : ℝ)}

/-- Genuinely open amplification core: the lower bound can be raised by one infinitely often. -/
def H2 : Prop :=
  ∀ C : ℝ, 0 < C →
    Set.Infinite {n : ℕ | C * (n : ℝ) * Real.log (n : ℝ) <
      ((2 ^ Erdos933.k n * 3 ^ Erdos933.l n : ℕ) : ℝ)} →
    Set.Infinite {n : ℕ | (C + 1) * (n : ℝ) * Real.log (n : ℝ) <
      ((2 ^ Erdos933.k n * 3 ^ Erdos933.l n : ℕ) : ℝ)}

theorem main : H1 → H2 → type_of% @Erdos933.erdos_933 := by
  intro h1 h2
  let R : ℕ → EReal := fun n ↦
    ((((2 ^ Erdos933.k n * 3 ^ Erdos933.l n : ℕ) : ℝ) /
      ((n : ℝ) * Real.log (n : ℝ))) : EReal)
  have hpow : ∀ m : ℕ, Set.Infinite {n : ℕ |
      ((m : ℝ) + 1) * (n : ℝ) * Real.log (n : ℝ) <
        ((2 ^ Erdos933.k n * 3 ^ Erdos933.l n : ℕ) : ℝ)} := by
    intro m
    induction m with
    | zero => simpa [H1] using h1
    | succ m ih =>
        have hmpos : 0 < (m : ℝ) + 1 := by positivity
        have hnext := h2 ((m : ℝ) + 1) hmpos ih
        simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using hnext
  have hfreq : ∀ m : ℕ, ∃ᶠ n in atTop, ((m : ℝ) + 1 : EReal) ≤ R n := by
    intro m
    rw [frequently_atTop]
    intro a
    have hf : ({0, 1} : Set ℕ).Finite := by simp
    obtain ⟨n, hnset, han⟩ := ((hpow m).sdiff hf).exists_gt a
    refine ⟨n, le_of_lt han, ?_⟩
    have hnnot : n ∉ ({0, 1} : Set ℕ) := hnset.2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hnnot
    have hn2 : 2 ≤ n := by omega
    have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hdenpos : 0 < (n : ℝ) * Real.log (n : ℝ) := mul_pos (by positivity) hlogpos
    have hfrac : (m : ℝ) + 1 <
        ((2 ^ Erdos933.k n * 3 ^ Erdos933.l n : ℕ) : ℝ) /
          ((n : ℝ) * Real.log (n : ℝ)) := (lt_div_iff₀ hdenpos).2 (by
            simpa [mul_assoc] using hnset.1)
    dsimp [R]
    rw [← EReal.coe_natCast (n := 2 ^ Erdos933.k n * 3 ^ Erdos933.l n)]
    rw [← EReal.coe_natCast (n := n)]
    rw [← EReal.coe_mul]
    rw [← EReal.coe_div]
    exact (EReal.coe_le_coe_iff).2 (le_of_lt hfrac)
  have hle : ∀ m : ℕ, ((m : ℝ) + 1 : EReal) ≤ limsup R atTop := by
    intro m
    exact Filter.le_limsup_of_frequently_le (hfreq m)
  apply top_unique
  refine le_of_forall_lt ?_
  intro c hc
  by_cases hcbot : c = ⊥
  · subst c
    have h0 := hle 0
    norm_num at h0
    exact lt_of_lt_of_le (EReal.bot_lt_coe 1) h0
  · have hcne : c ≠ ⊤ := ne_of_lt hc
    have hceq : ((c.toReal : ℝ) : EReal) = c := EReal.coe_toReal hcne hcbot
    rw [← hceq]
    obtain ⟨m, hm⟩ := exists_nat_gt c.toReal
    have hmcast : ((c.toReal : ℝ) : EReal) < (m : EReal) := by
      rw [← EReal.coe_natCast (n := m)]
      exact EReal.coe_lt_coe hm
    have hmstep : (m : EReal) < ((m : ℝ) + 1 : EReal) := by
      rw [← EReal.coe_natCast (n := m)]
      exact EReal.coe_lt_coe (by linarith : (m : ℝ) < (m : ℝ) + 1)
    exact lt_of_lt_of_le (lt_trans hmcast hmstep) (by simpa [R] using hle m)

end OMA.R_Erdos933_erdos_933_R1
