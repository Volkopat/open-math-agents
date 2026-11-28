import OMAStatements.S_oeis_a144590

-- Credit: @Pixelstorm44
namespace OMA.R_oeis_a144590_R1

/-- A relaxed additive basis: the remainder may be prime or a square,
and the odd square on the left may be 1. -/
def H1 : Prop := ∀ D : ℕ, 21 ≤ D → D % 8 = 5 →
  ∃ k r : ℕ, D = (2*k+1)^2 + 4*r ∧ (r.Prime ∨ ∃ y : ℕ, r = y^2)

/-- Prime inputs: find a smaller prime at positive pronic distance.
The first two candidate distances have already been tested. -/
def H2 : Prop := ∀ p : ℕ, 5 ≤ p → p.Prime →
  ¬ (p-2).Prime → ¬ (p-6).Prime →
  ∃ q j : ℕ, q.Prime ∧ 0 < j ∧ q + j*(j+1) = p

/-- Composite inputs with a square remainder. Crossing from the representation
b(b+1)+y² to the indices y or y-1 has already been tried. -/
def H3 : Prop := ∀ b y : ℕ, Odd y → 5 ≤ b*(b+1)+y^2 →
  ¬ (b*(b+1)+y^2).Prime →
  ¬ (b*(b+1)-y).Prime →
  (1 < y → ¬ (b*(b+1)+y).Prime) →
  ∃ q j : ℕ, q.Prime ∧ 0 < j ∧ q + j*(j+1) = b*(b+1)+y^2

/-- Even on prime inputs no fixed finite list of pronic distances suffices. -/
lemma prime_inputs_escape (K B : ℕ) :
    ∃ p > B, p.Prime ∧ ∀ j, 0 < j → j ≤ K → ¬ (p-j*(j+1)).Prime := by
  let m := K*(K+1)+1
  let L := Nat.factorial m
  haveI : NeZero L := ⟨Nat.factorial_ne_zero _⟩
  obtain ⟨p, hp, hprime, hclass⟩ := Nat.forall_exists_prime_gt_and_eq_mod
    (show IsUnit (-1 : ZMod L) by simp) (B+2*m+2)
  have hL : L ∣ p+1 := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    push_cast
    rw [hclass]
    simp
  refine ⟨p, by omega, hprime, ?_⟩
  intro j hj hK hbad
  have hb : j*(j+1)+1 ≤ m :=
    Nat.add_le_add_right (Nat.mul_le_mul hK (by omega)) 1
  have hd : j*(j+1)+1 ∣ p+1 := (Nat.dvd_factorial (by omega) hb).trans hL
  have hdiff := Nat.dvd_sub hd (dvd_refl (j*(j+1)+1))
  rw [show p+1-(j*(j+1)+1) = p-j*(j+1) by omega] at hdiff
  have hone : 0 < j*(j+1) := by positivity
  rcases hbad.eq_one_or_self_of_dvd _ hdiff with h | h <;> omega

/-- The relaxed step is automatic on the entire sum-of-two-squares locus. -/
lemma norm_relaxed {D : ℕ} (hD : D % 8 = 5)
    (hnorm : ∀ q ∈ D.primeFactors, q % 4 = 3 → Even (padicValNat q D)) :
    ∃ k r : ℕ, D = (2*k+1)^2 + 4*r ∧ (r.Prime ∨ ∃ y : ℕ, r = y^2) := by
  obtain ⟨x, y, h⟩ := Nat.eq_sq_add_sq_iff.mpr hnorm
  have hp : x % 2 = 1 ∧ y % 2 = 0 ∨ y % 2 = 1 ∧ x % 2 = 0 := by
    have hm := congrArg (· % 2) h
    rw [Nat.add_mod, Nat.pow_mod x, Nat.pow_mod y] at hm
    rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
      rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;> simp [hx, hy] at hm ⊢ <;> omega
  have orient (a c : ℕ) (ha : a % 2 = 1) (hc : c % 2 = 0) (he : D = a^2+c^2) :
      ∃ k r : ℕ, D = (2*k+1)^2 + 4*r ∧ (r.Prime ∨ ∃ z : ℕ, r = z^2) := by
    refine ⟨a/2, (c/2)^2, ?_, Or.inr ⟨_, rfl⟩⟩
    have ea : 2*(a/2)+1 = a := by omega
    have ec : 2*(c/2) = c := by omega
    rw [ea, he, ← ec] <;> simp <;> ring
  rcases hp with ⟨hx, hy⟩ | ⟨hy, hx⟩
  · exact orient x y hx hy h
  · exact orient y x hy hx (by omega)

lemma count_witness {n q j : ℕ} (hq : q.Prime) (hj : 0 < j)
    (e : q + j*(j+1) = 2*n+1) : 0 < OMA.S_oeis_a144590.a n := by
  apply Finset.card_pos.mpr
  refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hj, by omega, ?_⟩⟩
  · nlinarith
  · rwa [show 2*n+1-j*(j+1) = q by omega]

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a144590.main := by
  intro basis gaps norms n hn
  have easy (j q : ℕ) (hj : 0 < j) (hq : q.Prime)
      (he : q + j*(j+1) = 2*n+1) := count_witness hq hj he
  by_cases h2 : (2*n+1-2).Prime
  · exact easy 1 _ (by decide) h2 (by omega)
  by_cases h6 : (2*n+1-6).Prime
  · have hp := h6.two_le
    exact easy 2 _ (by decide) h6 (by omega)
  by_cases inp : (2*n+1).Prime
  · obtain ⟨q, j, hq, hj, he⟩ := gaps _ (by omega) inp h2 h6
    exact easy j q hj hq he
  obtain ⟨b, r, he, hr⟩ := basis (8*n+5) (by omega) (by omega)
  have eq : r + b*(b+1) = 2*n+1 := by nlinarith
  rcases hr with hprime | ⟨y, rfl⟩
  · have hb : 0 < b := by
      by_contra! hz
      obtain rfl : b = 0 := by omega
      simp at eq
      exact inp (eq ▸ hprime)
    exact easy b r hb hprime eq
  · have odd_y : Odd y := by
      by_contra h
      have hey := Nat.not_odd_iff_even.mp h
      rcases hey with ⟨t, ht⟩
      rcases Nat.even_mul_succ_self b with ⟨s, hs⟩
      rw [ht, hs] at eq
      have hpar : 2*(2*t^2+s) = 2*n+1 := by nlinarith only [eq]
      omega
    have hy : 0 < y := by rcases odd_y with ⟨t, ht⟩; omega
    by_cases low : (b*(b+1)-y).Prime
    · have := low.two_le
      apply easy y _ hy low
      have sub : b*(b+1)-y+y = b*(b+1) := by omega
      nlinarith
    by_cases high : 1 < y ∧ (b*(b+1)+y).Prime
    · apply easy (y-1) _ (by omega) high.2
      have pred : y-1+1 = y := by omega
      rw [pred]
      nlinarith [congrArg (· * y) pred]
    have en : b*(b+1)+y^2 = 2*n+1 := by omega
    obtain ⟨q, j, hq, hj, hjq⟩ := norms b y odd_y (by omega) (en ▸ inp)
      low (by tauto)
    exact easy j q hj hq (hjq.trans en)

end OMA.R_oeis_a144590_R1
