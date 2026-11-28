import OMAReductions.R_OeisA38771_conjecture1_R1

/-! The offset range relevant to the two limit constants consists of
semiprimes. Any third prime factor would force the offset to be at least
the cube of the next prime. -/

namespace OMA.R_OeisA38771_conjecture1_R1_H2_R1

open Filter Finset

private theorem factor_ge_next {n c q : ℕ} (hq : q.Prime) (d : q ∣ c)
    (cp : 0 < c) (hc : ((∏ i ∈ range n, Nat.nth Nat.Prime i) + c).Prime) : Nat.nth Nat.Prime n ≤ q := by
  by_contra! lt
  have below : Nat.count Nat.Prime q < n := by
    have hcount := (Nat.count_le_iff_le_nth (p := Nat.Prime)
      Nat.infinite_setOfPred_prime).mpr (show q < Nat.nth Nat.Prime n from lt)
    rw [Nat.count_succ, if_pos hq] at hcount
    omega
  have dvdP : q ∣ (∏ i ∈ range n, Nat.nth Nat.Prime i) := by
    rw [← Nat.nth_count hq]
    exact Finset.dvd_prod_of_mem (fun i ↦ Nat.nth Nat.Prime i) (mem_range.mpr below)
  have eq := (Nat.prime_dvd_prime_iff_eq hq hc).mp (dvd_add dvdP d)
  have Qpos : 0 < (∏ i ∈ range n, Nat.nth Nat.Prime i) := Finset.prod_pos fun j _ ↦ (Nat.prime_nth_prime j).pos
  have qle := Nat.le_of_dvd cp d
  omega

private theorem least_admissible (n : ℕ) :
    1 < OeisA38771.a n ∧ ¬ (OeisA38771.a n).Prime ∧
      ((∏ i ∈ range n, Nat.nth Nat.Prime i) + OeisA38771.a n).Prime := by
  let S : Set ℕ := {c | (c > 1 ∧ ¬ c.Prime) ∧ ((∏ i ∈ range n, Nat.nth Nat.Prime i) + c).Prime}
  have nonempty : S.Nonempty := by
    by_contra h
    have he := Set.not_nonempty_iff_eq_empty.mp h
    have hz : OeisA38771.a n = 0 := by
      change sInf S = 0
      rw [he, Nat.sInf_empty]
    exact (OeisA38771.a_n_exists n) hz
  have h := Nat.sInf_mem nonempty
  change (OeisA38771.a n > 1 ∧ ¬ (OeisA38771.a n).Prime) ∧
    ((∏ i ∈ range n, Nat.nth Nat.Prime i) + OeisA38771.a n).Prime at h
  exact ⟨h.1.1, h.1.2, h.2⟩

private theorem below_cube {n c : ℕ} (hc : 1 < c) (hnp : ¬ c.Prime)
    (hQ : ((∏ i ∈ range n, Nat.nth Nat.Prime i) + c).Prime) (hsize : c < Nat.nth Nat.Prime n ^ 3) :
    ∃ q r : ℕ, (q.Prime ∧ r.Prime ∧ Nat.nth Nat.Prime n ≤ q ∧ Nat.nth Nat.Prime n ≤ r ∧
      ((∏ i ∈ range n, Nat.nth Nat.Prime i) + q * r).Prime) ∧ c = q * r := by
  let q := c.minFac
  let r := c / q
  have hq : q.Prime := Nat.minFac_prime (by omega)
  have dq : q ∣ c := Nat.minFac_dvd c
  have fac : c = q * r := (Nat.mul_div_cancel' dq).symm
  have dr : r ∣ c := ⟨q, by rw [fac, mul_comm]⟩
  have qlb := factor_ge_next hq dq (by omega) hQ
  have rlarge : 1 < r := by
    by_contra! h
    have rpos : 0 < r := Nat.pos_of_ne_zero fun hz ↦ by
      simp [hz] at fac
      omega
    have hone : r = 1 := le_antisymm h (Nat.succ_le_of_lt rpos)
    apply hnp
    have eq : c = q := by simpa [hone] using fac
    exact eq.symm ▸ hq
  have hr : r.Prime := by
    by_contra h
    have hrmin : r.minFac.Prime := Nat.minFac_prime (by omega)
    have lb := factor_ge_next hrmin ((Nat.minFac_dvd r).trans dr) (by omega) hQ
    have rlb : Nat.nth Nat.Prime n ^ 2 ≤ r :=
      (Nat.pow_le_pow_left lb 2).trans (by simpa [pow_two] using
        (Nat.minFac_sq_le_self (show 0 < r by omega) h))
    have hbig : Nat.nth Nat.Prime n ^ 3 ≤ c := by
      rw [fac, pow_succ, mul_comm (Nat.nth Nat.Prime n ^ 2)]
      exact Nat.mul_le_mul qlb rlb
    omega
  exact ⟨q, r, ⟨hq, hr, qlb, factor_ge_next hr dr (by omega) hQ, fac ▸ hQ⟩, fac⟩

private theorem min_le_pair {n q r : ℕ} (h : (q.Prime ∧ r.Prime ∧ Nat.nth Nat.Prime n ≤ q ∧ Nat.nth Nat.Prime n ≤ r ∧
      ((∏ i ∈ range n, Nat.nth Nat.Prime i) + q * r).Prime)) :
    OeisA38771.a n ≤ q * r := by
  obtain ⟨hq, hr, _, _, hp⟩ := h
  have hpq : 1 < q * r := (by decide : 1 < 2 * 2).trans_le
    (Nat.mul_le_mul hq.two_le hr.two_le)
  have hnp : ¬ (q * r).Prime := by
    intro p
    rcases (Nat.dvd_prime p).mp (dvd_mul_right q r) with h | h
    · exact hq.ne_one h
    · have hlt : q < q * r := by
        simpa using mul_lt_mul_of_pos_left hr.one_lt hq.pos
      exact hlt.ne h
  unfold OeisA38771.a
  apply Nat.sInf_le
  exact ⟨⟨hpq, hnp⟩, hp⟩

/-- Infinitely often there is an admissible semiprime just above the lower endpoint. -/
def H1 : Prop := ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop, ∃ q r : ℕ,
  (q.Prime ∧ r.Prime ∧ Nat.nth Nat.Prime n ≤ q ∧ Nat.nth Nat.Prime n ≤ r ∧
      ((∏ i ∈ range n, Nat.nth Nat.Prime i) + q * r).Prime) ∧ (q * r : ℝ) ≤ (1 + ε) * (Nat.nth Nat.Prime n : ℝ) ^ 2

/-- Eventually there is always an admissible semiprime below the upper endpoint with slack. -/
def H2 : Prop := ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∃ q r : ℕ,
  (q.Prime ∧ r.Prime ∧ Nat.nth Nat.Prime n ≤ q ∧ Nat.nth Nat.Prime n ≤ r ∧
      ((∏ i ∈ range n, Nat.nth Nat.Prime i) + q * r).Prime) ∧ (q * r : ℝ) ≤ (2 + ε) * (Nat.nth Nat.Prime n : ℝ) ^ 2

/-- Infinitely often every admissible semiprime is near the upper endpoint or higher. -/
def H3 : Prop := ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop, ∀ q r : ℕ,
  (q.Prime ∧ r.Prime ∧ Nat.nth Nat.Prime n ≤ q ∧ Nat.nth Nat.Prime n ≤ r ∧
      ((∏ i ∈ range n, Nat.nth Nat.Prime i) + q * r).Prime) → (2 - ε) * (Nat.nth Nat.Prime n : ℝ) ^ 2 ≤ (q * r : ℝ)

theorem main : H1 → H2 → H3 → OMA.R_OeisA38771_conjecture1_R1.H2 := by
  intro lower endpoint exclusion
  let s (n : ℕ) : ℝ := (OeisA38771.a n : ℝ) / (Nat.nth Nat.Prime n : ℝ) ^ 2
  change liminf s atTop ≤ 1 ∧ limsup s atTop = 2
  have pos (n : ℕ) : 0 < (Nat.nth Nat.Prime n : ℝ) := by exact_mod_cast (Nat.prime_nth_prime n).pos
  have sqpos (n : ℕ) : 0 < (Nat.nth Nat.Prime n : ℝ) ^ 2 := pow_pos (pos n) 2
  have pair_bound {n q r : ℕ} {B : ℝ} (h : (q.Prime ∧ r.Prime ∧ Nat.nth Nat.Prime n ≤ q ∧ Nat.nth Nat.Prime n ≤ r ∧
      ((∏ i ∈ range n, Nat.nth Nat.Prime i) + q * r).Prime))
      (hb : (q * r : ℝ) ≤ B * (Nat.nth Nat.Prime n : ℝ) ^ 2) : s n ≤ B := by
    apply (div_le_iff₀ (sqpos n)).2
    exact (by exact_mod_cast min_le_pair h : (OeisA38771.a n : ℝ) ≤ (q * r : ℝ)).trans hb
  have evUpper (ε : ℝ) (hε : 0 < ε) : ∀ᶠ n : ℕ in atTop, s n ≤ 2 + ε :=
    (endpoint ε hε).mono fun n ⟨q, r, h, hB⟩ ↦ pair_bound h hB
  have bUpper : IsBoundedUnder (· ≤ ·) atTop s := ⟨2 + 1, evUpper 1 (by norm_num)⟩
  have sNonneg : ∀ n, 0 ≤ s n := fun n ↦ div_nonneg (Nat.cast_nonneg _) (sqpos n).le
  have bLower : IsBoundedUnder (· ≥ ·) atTop s :=
    ⟨0, show ∀ᶠ n : ℕ in atTop, s n ≥ 0 from Eventually.of_forall sNonneg⟩
  refine ⟨?_, le_antisymm ?_ ?_⟩
  · rw [liminf_le_iff bUpper.isCoboundedUnder_ge bLower]
    intro y hy
    refine (lower ((y - 1) / 2) (by linarith)).mono ?_
    rintro n ⟨q, r, h, hB⟩
    exact (pair_bound h hB).trans_lt (by linarith)
  · rw [limsup_le_iff bLower.isCoboundedUnder_le bUpper]
    intro y hy
    exact (evUpper ((y - 2) / 2) (by linarith)).mono fun n h ↦ h.trans_lt (by linarith)
  · rw [le_limsup_iff bLower.isCoboundedUnder_le bUpper]
    intro y hy
    refine (exclusion ((2 - y) / 2) (by linarith)).mono ?_
    intro n h
    have near : y < 2 - (2 - y) / 2 := by linarith
    apply near.trans_le
    by_contra! small
    have hsmall := (div_lt_iff₀ (sqpos n)).1 small
    have h₂ : (2 : ℝ) ≤ Nat.nth Nat.Prime n := by exact_mod_cast (Nat.prime_nth_prime n).two_le
    have hsc : (2 - (2 - y) / 2) * (Nat.nth Nat.Prime n : ℝ) ^ 2 ≤
        (Nat.nth Nat.Prime n : ℝ) ^ (3 : ℕ) := by
      calc
        _ ≤ (Nat.nth Nat.Prime n : ℝ) * (Nat.nth Nat.Prime n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
        _ = _ := by ring
    have hn : OeisA38771.a n < Nat.nth Nat.Prime n ^ 3 := by
      exact_mod_cast hsmall.trans_le hsc
    obtain ⟨hp, hnP, hQ⟩ := least_admissible n
    obtain ⟨q, r, hr, heq⟩ := below_cube hp hnP hQ hn
    have contra := h q r hr
    have heq' : (OeisA38771.a n : ℝ) = (q * r : ℝ) := by exact_mod_cast heq
    exact (not_lt_of_ge contra) (by simpa only [heq'] using hsmall)

end OMA.R_OeisA38771_conjecture1_R1_H2_R1
