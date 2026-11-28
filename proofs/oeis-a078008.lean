import OMAStatements.S_oeis_a078008
import Mathlib

namespace MediantParity

open OMA.S_oeis_a078008

private def valid (g : Gap) : Prop := g.1.1 * g.2.2 + 1 = g.2.1 * g.1.2

private theorem valid_children (g : Gap) (hg : valid g) :
    valid (g.1, mediant g) ∧ valid (mediant g, g.2) := by
  unfold valid at hg ⊢
  dsimp [mediant]
  simp only [Nat.mul_add, Nat.add_mul]
  constructor <;> omega

private theorem valid_gaps (n : ℕ) : ∀ g ∈ gaps n, valid g := by
  induction n with
  | zero => simp [gaps, valid]
  | succ n ih =>
    intro g hg
    rw [gaps] at hg
    obtain ⟨c, hc, hgc⟩ := List.mem_flatMap.mp hg
    have hv := valid_children c (ih c hc)
    rcases (by simpa only [children, List.mem_cons, List.not_mem_nil, or_false] using hgc :
      g = (c.1, mediant c) ∨ g = (mediant c, c.2)) with rfl | rfl
    · exact hv.1
    · exact hv.2

private theorem reduced (g : Gap) (hg : valid g) :
    (mediant g).1.gcd (mediant g).2 = 1 := by
  let d := (mediant g).1.gcd (mediant g).2
  have hl : d ∣ (g.1.1 + g.2.1) * g.1.2 :=
    dvd_mul_of_dvd_left (Nat.gcd_dvd_left _ _) _
  have hr : d ∣ (g.1.2 + g.2.2) * g.1.1 :=
    dvd_mul_of_dvd_left (Nat.gcd_dvd_right _ _) _
  have hdiff : (g.1.1 + g.2.1) * g.1.2 - (g.1.2 + g.2.2) * g.1.1 = 1 := by
    simp only [valid] at hg
    simp only [Nat.add_mul, Nat.mul_comm g.1.2 g.1.1, Nat.mul_comm g.2.2 g.1.1]
    omega
  exact Nat.dvd_one.mp (hdiff ▸ Nat.dvd_sub hl hr)

private def counted (g : Gap) : Bool := evenDen (mediant g)

private theorem counted_parity (g : Gap) (hg : valid g) :
    counted g = ((g.1.2 + g.2.2) % 2 == 0) := by
  unfold counted evenDen
  rw [reduced g hg, Nat.div_one]
  rfl

private theorem children_count (g : Gap) (hg : valid g) :
    (children g).countP counted + (if counted g then 1 else 0) = 1 := by
  have hv := valid_children g hg
  have hn : ¬ (g.1.2 % 2 = 0 ∧ g.2.2 % 2 = 0) := by
    rintro ⟨hl, hr⟩
    have h₁ : 2 ∣ g.2.1 * g.1.2 := dvd_mul_of_dvd_right (Nat.dvd_of_mod_eq_zero hl) _
    have h₂ : 2 ∣ g.1.1 * g.2.2 := dvd_mul_of_dvd_right (Nat.dvd_of_mod_eq_zero hr) _
    have hdiff : g.2.1 * g.1.2 - g.1.1 * g.2.2 = 1 := by unfold valid at hg; omega
    exact (by decide : ¬ 2 ∣ 1) (hdiff ▸ Nat.dvd_sub h₁ h₂)
  have hs₁ : (g.1.2 + (g.1.2 + g.2.2)) % 2 = g.2.2 % 2 := by omega
  have hs₂ : (g.1.2 + g.2.2 + g.2.2) % 2 = g.1.2 % 2 := by omega
  have hleft : counted (g.1, mediant g) = (g.2.2 % 2 == 0) :=
    (counted_parity _ hv.1).trans (congrArg (fun x : ℕ => x == 0) hs₁)
  have hright : counted (mediant g, g.2) = (g.1.2 % 2 == 0) :=
    (counted_parity _ hv.2).trans (congrArg (fun x : ℕ => x == 0) hs₂)
  simp only [children, List.countP_cons, List.countP_nil,
    hleft, hright, counted_parity _ hg, beq_iff_eq]
  split_ifs <;> omega

private theorem lists_count (l : List Gap) (hl : ∀ g ∈ l, valid g) :
    (l.flatMap children).countP counted + l.countP counted = l.length := by
  induction l with
  | nil => simp
  | cons g l ih =>
    have hc := children_count g (hl g (by simp))
    have ht := ih (fun v hv => hl v (List.mem_cons_of_mem _ hv))
    simp only [List.flatMap_cons, List.countP_append, List.countP_cons, List.length_cons]
    omega

private theorem lists_length (l : List Gap) : (l.flatMap children).length = 2 * l.length := by
  induction l with
  | nil => simp
  | cons g l ih => simp [children, ih]; omega

private theorem length_gaps (n : ℕ) : (gaps n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [gaps, lists_length, ih, pow_succ, Nat.mul_comm]

private theorem step_count (n : ℕ) : fareyCount (n + 1) + fareyCount n = 2 ^ n := by
  change ((gaps n).flatMap children).countP counted + (gaps n).countP counted = _
  rw [lists_count _ (valid_gaps n), length_gaps]

private theorem values (n : ℕ) :
    a n = fareyCount n ∧ a (n + 1) = fareyCount (n + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    change a (n + 2) = fareyCount (n + 2)
    rw [a, ih.1, ih.2]
    have hs := step_count n
    have ht := step_count (n + 1)
    change fareyCount (n + 2) + fareyCount (n + 1) = 2 ^ (n + 1) at ht
    rw [pow_succ] at ht
    omega

end MediantParity

theorem OMA.solution : type_of% @OMA.S_oeis_a078008.main :=
  fun n => (MediantParity.values n).1