import OMAReductions.R_Green14_W_3_13_R3

/-! Transport finite coloring obstructions to translated and reflected intervals. -/
namespace GreenCoverage


theorem translate {N p d e P : ℕ} (hc : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) N p d e)
    (inside : p+d+e < N) (hp : p ≤ P) (lim : P+N ≤ p+160)
    (R : ℕ → Prop)
    (tr : ∀ a d, 0 < d → a+2*d < 160 →
      R a → R (a+d) → R (a+2*d) → False)
    (hit : ∀ a d, 0 < d → a+12*d < 160 → ∃ i : Fin 13, R (a+i.val*d))
    (r₀ : R P) (r₁ : R (P+d)) (r₂ : R (P+d+e))
    (b₀ : ∀ x, P<x → x<P+d → ¬R x)
    (b₁ : ∀ x, P+d<x → x<P+d+e → ¬R x) : False := by
  let S := fun x => x < N ∧ R (P-p+x)
  have local_lim (x : ℕ) (hx : x < N) : P-p+x < 160 := by omega
  apply hc S (fun _ hx => hx.1)
  · intro a t ht h₀ h₁ h₂
    apply tr (P-p+a) t ht (by have := local_lim _ h₂.1; omega) h₀.2
    · simpa only [Nat.add_assoc] using h₁.2
    · simpa only [Nat.add_assoc] using h₂.2
  · intro a t ht ha
    obtain ⟨i, hi⟩ := hit (P-p+a) t ht (by have := local_lim _ ha; omega)
    refine ⟨i, ?_, ?_⟩
    · have := Nat.mul_le_mul_right t (show i.val ≤ 12 by omega)
      omega
    · simpa only [Nat.add_assoc] using hi
  · refine ⟨by omega, ?_⟩
    simpa only [show P-p+p=P by omega] using r₀
  · refine ⟨by omega, ?_⟩
    simpa only [show P-p+(p+d)=P+d by omega] using r₁
  · refine ⟨inside, ?_⟩
    simpa only [show P-p+(p+d+e)=P+d+e by omega] using r₂
  · intro x h₀ h₁ hx
    exact b₀ (P-p+x) (by omega) (by omega) hx.2
  · intro x h₀ h₁ hx
    exact b₁ (P-p+x) (by omega) (by omega) hx.2

private theorem reflect_hits {N : ℕ} {R : ℕ → Prop}
    (hit : ∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) :
    ∀ a d, 0 < d → a+12*d < N →
      ∃ i : Fin 13, a+i.val*d < N ∧ R (N-1-(a+i.val*d)) := by
  intro a d hd ha
  obtain ⟨i, hi⟩ := hit (N-1-(a+12*d)) d hd (by omega)
  let j : Fin 13 := ⟨12-i.val, by omega⟩
  have hs : (12-i.val)*d + i.val*d = 12*d := by
    rw [← Nat.add_mul, Nat.sub_add_cancel (show i.val ≤ 12 by omega)]
  have he : N-1-(a+j.val*d) = N-1-(a+12*d)+i.val*d := by
    dsimp [j]
    omega
  refine ⟨j, ?_, ?_⟩
  · dsimp [j]
    omega
  · rwa [he]

theorem reflect {N p d e : ℕ} (inside : p+d+e < N)
    (hc : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) N (N-1-p-d-e) e d) : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) N p d e := by
  intro R bound tr hit r₀ r₁ r₂ b₀ b₁
  let S := fun x => x < N ∧ R (N-1-x)
  let q := N-1-p-d-e
  apply hc S (fun _ hx => hx.1)
  · intro a t ht h₀ h₁ h₂
    apply tr (N-1-(a+2*t)) t ht h₂.2
    · convert h₁.2 using 1 <;> omega
    · convert h₀.2 using 1 <;> omega
  · exact reflect_hits hit
  · refine ⟨by omega, ?_⟩
    simpa only [show N-1-(N-1-p-d-e)=p+d+e by omega] using r₂
  · refine ⟨by omega, ?_⟩
    simpa only [show N-1-(N-1-p-d-e+e)=p+d by omega] using r₁
  · refine ⟨by omega, ?_⟩
    simpa only [show N-1-(N-1-p-d-e+e+d)=p by omega] using r₀
  · intro x h₀ h₁ hx
    exact b₁ (N-1-x) (by omega) (by omega) hx.2
  · intro x h₀ h₁ hx
    exact b₀ (N-1-x) (by omega) (by omega) hx.2

end GreenCoverage


/-! Analytic shared-endpoint cases. All positions are zero based. -/
namespace GreenAnalyticReview




lemma equal_gaps {R : ℕ → Prop} {p d : ℕ} (hd : 0 < d)
    (hb : p + 2*d < 160) (g₁ : (fun (R : ℕ → Prop) (p q : ℕ) => R p ∧ R q ∧ ∀ x, p < x → x < q → ¬R x) R p (p+d))
    (g₂ : (fun (R : ℕ → Prop) (p q : ℕ) => R p ∧ R q ∧ ∀ x, p < x → x < q → ¬R x) R (p+d) (p+2*d)) (tr : (fun (R : ℕ → Prop) => ∀ a d, 0 < d → a+2*d < 160 → R a → R (a+d) → R (a+2*d) → False) R) : False :=
  tr p d hd hb g₁.1 g₁.2.1 g₂.2.1

lemma gaps_12_13 {R : ℕ → Prop} {p : ℕ} (hp : 1 ≤ p)
    (hb : p+25 < 160) (g₁ : (fun (R : ℕ → Prop) (p q : ℕ) => R p ∧ R q ∧ ∀ x, p < x → x < q → ¬R x) R p (p+12))
    (g₂ : (fun (R : ℕ → Prop) (p q : ℕ) => R p ∧ R q ∧ ∀ x, p < x → x < q → ¬R x) R (p+12) (p+25)) (tr : (fun (R : ℕ → Prop) => ∀ a d, 0 < d → a+2*d < 160 → R a → R (a+d) → R (a+2*d) → False) R) (hit : (fun (R : ℕ → Prop) => ∀ a d, 0 < d → a+12*d < 160 → ∃ i : Fin 13, R (a+i.val*d)) R) : False := by
  obtain ⟨i, hi⟩ := hit (p-1) 2 (by decide) (by omega)
  have hz : i.val = 0 := by
    by_contra hn
    have hi' := i.isLt
    by_cases h : i.val ≤ 6
    · exact g₁.2.2 _ (by omega) (by omega) hi
    · exact g₂.2.2 _ (by omega) (by omega) hi
  have hr : R (p-1) := by simpa [hz] using hi
  apply tr (p-1) 13 (by decide) (by omega) hr
  · convert g₁.2.1 using 1 <;> omega
  · convert g₂.2.1 using 1 <;> omega

lemma gaps_13_12 {R : ℕ → Prop} {p : ℕ}
    (hb : p+26 < 160) (g₁ : (fun (R : ℕ → Prop) (p q : ℕ) => R p ∧ R q ∧ ∀ x, p < x → x < q → ¬R x) R p (p+13))
    (g₂ : (fun (R : ℕ → Prop) (p q : ℕ) => R p ∧ R q ∧ ∀ x, p < x → x < q → ¬R x) R (p+13) (p+25)) (tr : (fun (R : ℕ → Prop) => ∀ a d, 0 < d → a+2*d < 160 → R a → R (a+d) → R (a+2*d) → False) R) (hit : (fun (R : ℕ → Prop) => ∀ a d, 0 < d → a+12*d < 160 → ∃ i : Fin 13, R (a+i.val*d)) R) : False := by
  obtain ⟨i, hi⟩ := hit (p+2) 2 (by decide) (by omega)
  have hz : i.val = 12 := by
    by_contra hn
    have hi' := i.isLt
    by_cases h : i.val ≤ 5
    · exact g₁.2.2 _ (by omega) (by omega) hi
    · exact g₂.2.2 _ (by omega) (by omega) hi
  have hr : R (p+26) := by convert hi using 1 <;> omega
  exact tr p 13 (by decide) (by omega) g₁.1 g₁.2.1 hr

end GreenAnalyticReview
namespace GreenCoverage


private theorem lift_core {N p d e P : ℕ} (hc : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) N p d e)
    (inside : p+d+e < N) (hp : p ≤ P) (lim : P+N ≤ p+160) :
    (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P d e := by
  intro R _ tr hit r₀ r₁ r₂ b₀ b₁
  exact translate hc inside hp lim R (fun a t ht _ => tr a t ht) hit r₀ r₁ r₂ b₀ b₁

private theorem family_8_6
    (c0 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 149 79 6 8)
    (c1 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 146 64 6 8)
    (P : ℕ) (h : (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P 8 6) : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P 8 6 := by
  have cover : (55 ≤ P ∧ P ≤ 66) ∨ (67 ≤ P ∧ P ≤ 81) := by
    omega
  rcases cover with h | h
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 149 55 8 6 from reflect (by decide) c0) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 146 67 8 6 from reflect (by decide) c1) (by decide) h.1 (by omega)

private theorem family_8_7
    (c2 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 146 96 7 8)
    (c3 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 153 88 7 8)
    (c4 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 144 71 7 8)
    (c5 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 152 74 8 7)
    (P : ℕ) (h : (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P 8 7) : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P 8 7 := by
  have cover : (34 ≤ P ∧ P ≤ 48) ∨ (49 ≤ P ∧ P ≤ 56) ∨ (57 ≤ P ∧ P ≤ 73) ∨ (74 ≤ P ∧ P ≤ 82) := by
    omega
  rcases cover with h | h | h | h
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 146 34 8 7 from reflect (by decide) c2) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 153 49 8 7 from reflect (by decide) c3) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 144 57 8 7 from reflect (by decide) c4) (by decide) h.1 (by omega)
  · exact lift_core c5 (by decide) h.1 (by omega)

private theorem family_8_9
    (c6 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 152 117 9 8)
    (c7 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 147 103 9 8)
    (c8 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 150 92 9 8)
    (c9 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 153 84 9 8)
    (c10 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 151 59 8 9)
    (c11 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 144 69 8 9)
    (P : ℕ) (h : (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P 8 9) : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P 8 9 := by
  have cover : (17 ≤ P ∧ P ≤ 25) ∨ (26 ≤ P ∧ P ≤ 39) ∨ (40 ≤ P ∧ P ≤ 50) ∨ (51 ≤ P ∧ P ≤ 58) ∨ (59 ≤ P ∧ P ≤ 68) ∨ (69 ≤ P ∧ P ≤ 85) := by
    omega
  rcases cover with h | h | h | h | h | h
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 152 17 8 9 from reflect (by decide) c6) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 147 26 8 9 from reflect (by decide) c7) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 150 40 8 9 from reflect (by decide) c8) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 153 51 8 9 from reflect (by decide) c9) (by decide) h.1 (by omega)
  · exact lift_core c10 (by decide) h.1 (by omega)
  · exact lift_core c11 (by decide) h.1 (by omega)

private theorem family_8_10
    (c12 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 112 10 8)
    (c13 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 142 93 10 8)
    (c14 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 49 8 10)
    (c15 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 155 62 8 10)
    (c16 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 68 8 10)
    (P : ℕ) (h : (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P 8 10) : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P 8 10 := by
  have cover : (17 ≤ P ∧ P ≤ 29) ∨ (30 ≤ P ∧ P ≤ 48) ∨ (49 ≤ P ∧ P ≤ 61) ∨ (62 ≤ P ∧ P ≤ 67) ∨ (68 ≤ P ∧ P ≤ 85) := by
    omega
  rcases cover with h | h | h | h | h
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 17 8 10 from reflect (by decide) c12) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 142 30 8 10 from reflect (by decide) c13) (by decide) h.1 (by omega)
  · exact lift_core c14 (by decide) h.1 (by omega)
  · exact lift_core c15 (by decide) h.1 (by omega)
  · exact lift_core c16 (by decide) h.1 (by omega)

private theorem family_8_11
    (c17 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 149 17 8 11)
    (c18 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 149 100 11 8)
    (c19 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 147 86 11 8)
    (c20 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 152 77 11 8)
    (c21 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 151 64 8 11)
    (c22 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 74 8 11)
    (P : ℕ) (h : (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P 8 11) : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P 8 11 := by
  have cover : (17 ≤ P ∧ P ≤ 28) ∨ (29 ≤ P ∧ P ≤ 40) ∨ (41 ≤ P ∧ P ≤ 54) ∨ (55 ≤ P ∧ P ≤ 63) ∨ (64 ≤ P ∧ P ≤ 73) ∨ (74 ≤ P ∧ P ≤ 91) := by
    omega
  rcases cover with h | h | h | h | h | h
  · exact lift_core c17 (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 149 29 8 11 from reflect (by decide) c18) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 147 41 8 11 from reflect (by decide) c19) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 152 55 8 11 from reflect (by decide) c20) (by decide) h.1 (by omega)
  · exact lift_core c21 (by decide) h.1 (by omega)
  · exact lift_core c22 (by decide) h.1 (by omega)

private theorem family_8_12
    (c23 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 142 104 12 8)
    (c24 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 142 85 12 8)
    (c25 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 138 62 12 8)
    (P : ℕ) (h : (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P 8 12) : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P 8 12 := by
  have cover : (17 ≤ P ∧ P ≤ 35) ∨ (36 ≤ P ∧ P ≤ 54) ∨ (55 ≤ P ∧ P ≤ 77) := by
    omega
  rcases cover with h | h | h
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 142 17 8 12 from reflect (by decide) c23) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 142 36 8 12 from reflect (by decide) c24) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 138 55 8 12 from reflect (by decide) c25) (by decide) h.1 (by omega)

private theorem family_8_13
    (c26 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 104 13 8)
    (c27 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 144 87 13 8)
    (c28 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 152 52 8 13)
    (c29 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 61 8 13)
    (P : ℕ) (h : (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P 8 13) : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P 8 13 := by
  have cover : (17 ≤ P ∧ P ≤ 34) ∨ (35 ≤ P ∧ P ≤ 51) ∨ (52 ≤ P ∧ P ≤ 60) ∨ (61 ≤ P ∧ P ≤ 78) := by
    omega
  rcases cover with h | h | h | h
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 17 8 13 from reflect (by decide) c26) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 144 35 8 13 from reflect (by decide) c27) (by decide) h.1 (by omega)
  · exact lift_core c28 (by decide) h.1 (by omega)
  · exact lift_core c29 (by decide) h.1 (by omega)

private theorem family_9_6
    (c30 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 146 76 6 9)
    (c31 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 58 6 9)
    (P : ℕ) (h : (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P 9 6) : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P 9 6 := by
  have cover : (54 ≤ P ∧ P ≤ 68) ∨ (69 ≤ P ∧ P ≤ 86) := by
    omega
  rcases cover with h | h
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 146 54 9 6 from reflect (by decide) c30) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 69 9 6 from reflect (by decide) c31) (by decide) h.1 (by omega)

private theorem family_9_7
    (c32 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 146 96 7 9)
    (c33 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 153 88 7 9)
    (c34 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 151 78 7 9)
    (c35 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 150 67 7 9)
    (P : ℕ) (h : (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P 9 7) : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P 9 7 := by
  have cover : (33 ≤ P ∧ P ≤ 47) ∨ (48 ≤ P ∧ P ≤ 55) ∨ (56 ≤ P ∧ P ≤ 65) ∨ (66 ≤ P ∧ P ≤ 76) := by
    omega
  rcases cover with h | h | h | h
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 146 33 9 7 from reflect (by decide) c32) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 153 48 9 7 from reflect (by decide) c33) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 151 56 9 7 from reflect (by decide) c34) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 150 66 9 7 from reflect (by decide) c35) (by decide) h.1 (by omega)

private theorem family_9_8
    (c36 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 151 116 8 9)
    (c37 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 154 109 8 9)
    (c38 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 142 90 8 9)
    (c39 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 72 8 9)
    (c40 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 150 61 8 9)
    (P : ℕ) (h : (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P 9 8) : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P 9 8 := by
  have cover : (17 ≤ P ∧ P ≤ 26) ∨ (27 ≤ P ∧ P ≤ 33) ∨ (34 ≤ P ∧ P ≤ 52) ∨ (53 ≤ P ∧ P ≤ 70) ∨ (71 ≤ P ∧ P ≤ 81) := by
    omega
  rcases cover with h | h | h | h | h
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 151 17 9 8 from reflect (by decide) c36) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 154 27 9 8 from reflect (by decide) c37) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 142 34 9 8 from reflect (by decide) c38) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 53 9 8 from reflect (by decide) c39) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 150 71 9 8 from reflect (by decide) c40) (by decide) h.1 (by omega)

private theorem family_9_10
    (c41 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 149 112 10 9)
    (c42 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 99 10 9)
    (c43 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 153 91 10 9)
    (c44 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 78 10 9)
    (c45 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 155 72 10 9)
    (c46 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 150 61 10 9)
    (P : ℕ) (h : (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P 9 10) : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P 9 10 := by
  have cover : (17 ≤ P ∧ P ≤ 28) ∨ (29 ≤ P ∧ P ≤ 41) ∨ (42 ≤ P ∧ P ≤ 49) ∨ (50 ≤ P ∧ P ≤ 62) ∨ (63 ≤ P ∧ P ≤ 68) ∨ (69 ≤ P ∧ P ≤ 79) := by
    omega
  rcases cover with h | h | h | h | h | h
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 149 17 9 10 from reflect (by decide) c41) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 29 9 10 from reflect (by decide) c42) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 153 42 9 10 from reflect (by decide) c43) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 50 9 10 from reflect (by decide) c44) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 155 63 9 10 from reflect (by decide) c45) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 150 69 9 10 from reflect (by decide) c46) (by decide) h.1 (by omega)

private theorem family_9_11
    (c47 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 147 109 11 9)
    (c48 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 150 98 11 9)
    (c49 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 152 89 11 9)
    (c50 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 85 11 9)
    (c51 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 156 80 11 9)
    (c52 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 152 60 9 11)
    (c53 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 69 9 11)
    (c54 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 152 73 9 11)
    (P : ℕ) (h : (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P 9 11) : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P 9 11 := by
  have cover : (17 ≤ P ∧ P ≤ 30) ∨ (31 ≤ P ∧ P ≤ 41) ∨ (42 ≤ P ∧ P ≤ 50) ∨ (51 ≤ P ∧ P ≤ 54) ∨ (55 ≤ P ∧ P ≤ 59) ∨ (60 ≤ P ∧ P ≤ 68) ∨ (69 ≤ P ∧ P ≤ 72) ∨ (73 ≤ P ∧ P ≤ 81) := by
    omega
  rcases cover with h | h | h | h | h | h | h | h
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 147 17 9 11 from reflect (by decide) c47) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 150 31 9 11 from reflect (by decide) c48) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 152 42 9 11 from reflect (by decide) c49) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 51 9 11 from reflect (by decide) c50) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 156 55 9 11 from reflect (by decide) c51) (by decide) h.1 (by omega)
  · exact lift_core c52 (by decide) h.1 (by omega)
  · exact lift_core c53 (by decide) h.1 (by omega)
  · exact lift_core c54 (by decide) h.1 (by omega)

private theorem family_9_12
    (c55 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 104 12 9)
    (c56 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 150 93 12 9)
    (c57 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 147 79 12 9)
    (c58 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 140 58 12 9)
    (P : ℕ) (h : (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P 9 12) : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P 9 12 := by
  have cover : (17 ≤ P ∧ P ≤ 34) ∨ (35 ≤ P ∧ P ≤ 45) ∨ (46 ≤ P ∧ P ≤ 59) ∨ (60 ≤ P ∧ P ≤ 80) := by
    omega
  rcases cover with h | h | h | h
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 17 9 12 from reflect (by decide) c55) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 150 35 9 12 from reflect (by decide) c56) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 147 46 9 12 from reflect (by decide) c57) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 140 60 9 12 from reflect (by decide) c58) (by decide) h.1 (by omega)

private theorem family_9_13
    (c59 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 147 107 13 9)
    (c60 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 151 97 13 9)
    (c61 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 93 13 9)
    (c62 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 89 13 9)
    (c63 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 85 13 9)
    (c64 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 158 82 13 9)
    (c65 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 154 56 9 13)
    (c66 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 151 63 9 13)
    (c67 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 150 73 9 13)
    (P : ℕ) (h : (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P 9 13) : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P 9 13 := by
  have cover : (17 ≤ P ∧ P ≤ 30) ∨ (31 ≤ P ∧ P ≤ 40) ∨ (41 ≤ P ∧ P ≤ 44) ∨ (45 ≤ P ∧ P ≤ 48) ∨ (49 ≤ P ∧ P ≤ 52) ∨ (53 ≤ P ∧ P ≤ 55) ∨ (56 ≤ P ∧ P ≤ 62) ∨ (63 ≤ P ∧ P ≤ 72) ∨ (73 ≤ P ∧ P ≤ 83) := by
    omega
  rcases cover with h | h | h | h | h | h | h | h | h
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 147 17 9 13 from reflect (by decide) c59) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 151 31 9 13 from reflect (by decide) c60) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 41 9 13 from reflect (by decide) c61) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 45 9 13 from reflect (by decide) c62) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 49 9 13 from reflect (by decide) c63) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 158 53 9 13 from reflect (by decide) c64) (by decide) h.1 (by omega)
  · exact lift_core c65 (by decide) h.1 (by omega)
  · exact lift_core c66 (by decide) h.1 (by omega)
  · exact lift_core c67 (by decide) h.1 (by omega)

private theorem family_10_6
    (c68 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 87 6 10)
    (c69 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 74 6 10)
    (c70 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 61 6 10)
    (P : ℕ) (h : (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P 10 6) : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P 10 6 := by
  have cover : (53 ≤ P ∧ P ≤ 56) ∨ (57 ≤ P ∧ P ≤ 69) ∨ (70 ≤ P ∧ P ≤ 82) := by
    omega
  rcases cover with h | h | h
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 53 10 6 from reflect (by decide) c68) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 57 10 6 from reflect (by decide) c69) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 70 10 6 from reflect (by decide) c70) (by decide) h.1 (by omega)

private theorem family_10_7
    (c71 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 145 95 7 10)
    (c72 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 151 85 7 10)
    (c73 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 81 7 10)
    (c74 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 77 7 10)
    (c75 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 73 7 10)
    (c76 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 154 66 7 10)
    (P : ℕ) (h : (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P 10 7) : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P 10 7 := by
  have cover : (32 ≤ P ∧ P ≤ 47) ∨ (48 ≤ P ∧ P ≤ 57) ∨ (58 ≤ P ∧ P ≤ 61) ∨ (62 ≤ P ∧ P ≤ 65) ∨ (66 ≤ P ∧ P ≤ 69) ∨ (70 ≤ P ∧ P ≤ 76) := by
    omega
  rcases cover with h | h | h | h | h | h
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 145 32 10 7 from reflect (by decide) c71) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 151 48 10 7 from reflect (by decide) c72) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 58 10 7 from reflect (by decide) c73) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 62 10 7 from reflect (by decide) c74) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 66 10 7 from reflect (by decide) c75) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 154 70 10 7 from reflect (by decide) c76) (by decide) h.1 (by omega)

private theorem family_10_8
    (c77 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 146 110 8 10)
    (c78 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 147 96 8 10)
    (c79 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 92 8 10)
    (c80 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 146 77 8 10)
    (c81 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 149 65 8 10)
    (P : ℕ) (h : (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P 10 8) : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P 10 8 := by
  have cover : (17 ≤ P ∧ P ≤ 31) ∨ (32 ≤ P ∧ P ≤ 45) ∨ (46 ≤ P ∧ P ≤ 49) ∨ (50 ≤ P ∧ P ≤ 64) ∨ (65 ≤ P ∧ P ≤ 76) := by
    omega
  rcases cover with h | h | h | h | h
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 146 17 10 8 from reflect (by decide) c77) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 147 32 10 8 from reflect (by decide) c78) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 46 10 8 from reflect (by decide) c79) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 146 50 10 8 from reflect (by decide) c80) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 149 65 10 8 from reflect (by decide) c81) (by decide) h.1 (by omega)

private theorem family_10_9
    (c82 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 154 117 9 10)
    (c83 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 146 102 9 10)
    (c84 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 150 91 9 10)
    (c85 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 147 50 10 9)
    (c86 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 153 64 10 9)
    (c87 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 72 10 9)
    (P : ℕ) (h : (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P 10 9) : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P 10 9 := by
  have cover : (17 ≤ P ∧ P ≤ 23) ∨ (24 ≤ P ∧ P ≤ 38) ∨ (39 ≤ P ∧ P ≤ 49) ∨ (50 ≤ P ∧ P ≤ 63) ∨ (64 ≤ P ∧ P ≤ 71) ∨ (72 ≤ P ∧ P ≤ 84) := by
    omega
  rcases cover with h | h | h | h | h | h
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 154 17 10 9 from reflect (by decide) c82) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 146 24 10 9 from reflect (by decide) c83) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 150 39 10 9 from reflect (by decide) c84) (by decide) h.1 (by omega)
  · exact lift_core c85 (by decide) h.1 (by omega)
  · exact lift_core c86 (by decide) h.1 (by omega)
  · exact lift_core c87 (by decide) h.1 (by omega)

private theorem family_10_11
    (c88 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 109 11 10)
    (c89 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 156 104 11 10)
    (c90 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 142 85 11 10)
    (c91 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 144 54 10 11)
    (c92 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 142 71 10 11)
    (P : ℕ) (h : (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P 10 11) : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P 10 11 := by
  have cover : (17 ≤ P ∧ P ≤ 29) ∨ (30 ≤ P ∧ P ≤ 34) ∨ (35 ≤ P ∧ P ≤ 53) ∨ (54 ≤ P ∧ P ≤ 70) ∨ (71 ≤ P ∧ P ≤ 89) := by
    omega
  rcases cover with h | h | h | h | h
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 17 10 11 from reflect (by decide) c88) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 156 30 10 11 from reflect (by decide) c89) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 142 35 10 11 from reflect (by decide) c90) (by decide) h.1 (by omega)
  · exact lift_core c91 (by decide) h.1 (by omega)
  · exact lift_core c92 (by decide) h.1 (by omega)

private theorem family_10_12
    (c93 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 108 12 10)
    (c94 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 147 94 12 10)
    (c95 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 90 12 10)
    (c96 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 152 81 12 10)
    (c97 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 145 65 12 10)
    (c98 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 139 43 12 10)
    (P : ℕ) (h : (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P 10 12) : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P 10 12 := by
  have cover : (17 ≤ P ∧ P ≤ 29) ∨ (30 ≤ P ∧ P ≤ 43) ∨ (44 ≤ P ∧ P ≤ 47) ∨ (48 ≤ P ∧ P ≤ 56) ∨ (57 ≤ P ∧ P ≤ 72) ∨ (73 ≤ P ∧ P ≤ 94) := by
    omega
  rcases cover with h | h | h | h | h | h
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 17 10 12 from reflect (by decide) c93) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 147 30 10 12 from reflect (by decide) c94) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 44 10 12 from reflect (by decide) c95) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 152 48 10 12 from reflect (by decide) c96) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 145 57 10 12 from reflect (by decide) c97) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 139 73 10 12 from reflect (by decide) c98) (by decide) h.1 (by omega)

private theorem family_10_13
    (c99 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 137 96 13 10)
    (c100 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 135 70 13 10)
    (c101 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 141 50 13 10)
    (P : ℕ) (h : (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P 10 13) : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P 10 13 := by
  have cover : (17 ≤ P ∧ P ≤ 40) ∨ (41 ≤ P ∧ P ≤ 66) ∨ (67 ≤ P ∧ P ≤ 86) := by
    omega
  rcases cover with h | h | h
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 137 17 10 13 from reflect (by decide) c99) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 135 41 10 13 from reflect (by decide) c100) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 141 67 10 13 from reflect (by decide) c101) (by decide) h.1 (by omega)

private theorem family_11_6
    (c102 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 144 74 6 11)
    (c103 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 142 55 6 11)
    (P : ℕ) (h : (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P 11 6) : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P 11 6 := by
  have cover : (52 ≤ P ∧ P ≤ 68) ∨ (69 ≤ P ∧ P ≤ 87) := by
    omega
  rcases cover with h | h
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 144 52 11 6 from reflect (by decide) c102) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 142 69 11 6 from reflect (by decide) c103) (by decide) h.1 (by omega)

private theorem family_11_7
    (c104 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 146 96 7 11)
    (c105 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 151 86 7 11)
    (c106 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 149 74 7 11)
    (c107 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 145 68 11 7)
    (P : ℕ) (h : (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P 11 7) : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P 11 7 := by
  have cover : (31 ≤ P ∧ P ≤ 45) ∨ (46 ≤ P ∧ P ≤ 55) ∨ (56 ≤ P ∧ P ≤ 67) ∨ (68 ≤ P ∧ P ≤ 83) := by
    omega
  rcases cover with h | h | h | h
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 146 31 11 7 from reflect (by decide) c104) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 151 46 11 7 from reflect (by decide) c105) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 149 56 11 7 from reflect (by decide) c106) (by decide) h.1 (by omega)
  · exact lift_core c107 (by decide) h.1 (by omega)

private theorem family_11_8
    (c108 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 152 115 8 11)
    (c109 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 155 109 8 11)
    (c110 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 105 8 11)
    (c111 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 101 8 11)
    (c112 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 97 8 11)
    (c113 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 154 90 8 11)
    (c114 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 72 8 11)
    (c115 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 59 8 11)
    (P : ℕ) (h : (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P 11 8) : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P 11 8 := by
  have cover : (17 ≤ P ∧ P ≤ 25) ∨ (26 ≤ P ∧ P ≤ 31) ∨ (32 ≤ P ∧ P ≤ 35) ∨ (36 ≤ P ∧ P ≤ 39) ∨ (40 ≤ P ∧ P ≤ 43) ∨ (44 ≤ P ∧ P ≤ 50) ∨ (51 ≤ P ∧ P ≤ 68) ∨ (69 ≤ P ∧ P ≤ 81) := by
    omega
  rcases cover with h | h | h | h | h | h | h | h
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 152 17 11 8 from reflect (by decide) c108) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 155 26 11 8 from reflect (by decide) c109) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 32 11 8 from reflect (by decide) c110) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 36 11 8 from reflect (by decide) c111) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 40 11 8 from reflect (by decide) c112) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 154 44 11 8 from reflect (by decide) c113) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 51 11 8 from reflect (by decide) c114) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 69 11 8 from reflect (by decide) c115) (by decide) h.1 (by omega)

private theorem family_11_9
    (c116 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 146 17 11 9)
    (c117 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 145 92 9 11)
    (c118 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 151 82 9 11)
    (c119 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 150 71 9 11)
    (c120 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 152 62 9 11)
    (P : ℕ) (h : (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P 11 9) : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P 11 9 := by
  have cover : (17 ≤ P ∧ P ≤ 31) ∨ (32 ≤ P ∧ P ≤ 47) ∨ (48 ≤ P ∧ P ≤ 57) ∨ (58 ≤ P ∧ P ≤ 68) ∨ (69 ≤ P ∧ P ≤ 77) := by
    omega
  rcases cover with h | h | h | h | h
  · exact lift_core c116 (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 145 32 11 9 from reflect (by decide) c117) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 151 48 11 9 from reflect (by decide) c118) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 150 58 11 9 from reflect (by decide) c119) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 152 69 11 9 from reflect (by decide) c120) (by decide) h.1 (by omega)

private theorem family_11_10
    (c121 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 149 110 10 11)
    (c122 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 92 10 11)
    (c123 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 79 10 11)
    (c124 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 146 64 10 11)
    (P : ℕ) (h : (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P 11 10) : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P 11 10 := by
  have cover : (17 ≤ P ∧ P ≤ 28) ∨ (29 ≤ P ∧ P ≤ 46) ∨ (47 ≤ P ∧ P ≤ 59) ∨ (60 ≤ P ∧ P ≤ 74) := by
    omega
  rcases cover with h | h | h | h
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 149 17 11 10 from reflect (by decide) c121) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 29 11 10 from reflect (by decide) c122) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 47 11 10 from reflect (by decide) c123) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 146 60 11 10 from reflect (by decide) c124) (by decide) h.1 (by omega)

private theorem family_11_12
    (c125 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 102 12 11)
    (c126 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 145 86 12 11)
    (c127 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 68 12 11)
    (c128 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 55 12 11)
    (P : ℕ) (h : (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P 11 12) : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P 11 12 := by
  have cover : (17 ≤ P ∧ P ≤ 34) ∨ (35 ≤ P ∧ P ≤ 50) ∨ (51 ≤ P ∧ P ≤ 68) ∨ (69 ≤ P ∧ P ≤ 81) := by
    omega
  rcases cover with h | h | h | h
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 17 11 12 from reflect (by decide) c125) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 145 35 11 12 from reflect (by decide) c126) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 51 11 12 from reflect (by decide) c127) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 69 11 12 from reflect (by decide) c128) (by decide) h.1 (by omega)

private theorem family_11_13
    (c129 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 101 13 11)
    (c130 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 142 82 13 11)
    (c131 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 146 54 11 13)
    (c132 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 147 69 11 13)
    (P : ℕ) (h : (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P 11 13) : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P 11 13 := by
  have cover : (17 ≤ P ∧ P ≤ 34) ∨ (35 ≤ P ∧ P ≤ 53) ∨ (54 ≤ P ∧ P ≤ 68) ∨ (69 ≤ P ∧ P ≤ 82) := by
    omega
  rcases cover with h | h | h | h
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 17 11 13 from reflect (by decide) c129) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 142 35 11 13 from reflect (by decide) c130) (by decide) h.1 (by omega)
  · exact lift_core c131 (by decide) h.1 (by omega)
  · exact lift_core c132 (by decide) h.1 (by omega)

private theorem family_12_6
    (c133 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 145 51 12 6)
    (c134 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 146 67 12 6)
    (P : ℕ) (h : (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P 12 6) : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P 12 6 := by
  have cover : (51 ≤ P ∧ P ≤ 66) ∨ (67 ≤ P ∧ P ≤ 81) := by
    omega
  rcases cover with h | h
  · exact lift_core c133 (by decide) h.1 (by omega)
  · exact lift_core c134 (by decide) h.1 (by omega)

private theorem family_12_7
    (c135 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 93 7 12)
    (c136 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 142 48 12 7)
    (c137 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 67 12 7)
    (P : ℕ) (h : (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P 12 7) : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P 12 7 := by
  have cover : (30 ≤ P ∧ P ≤ 47) ∨ (48 ≤ P ∧ P ≤ 66) ∨ (67 ≤ P ∧ P ≤ 79) := by
    omega
  rcases cover with h | h | h
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 30 12 7 from reflect (by decide) c135) (by decide) h.1 (by omega)
  · exact lift_core c136 (by decide) h.1 (by omega)
  · exact lift_core c137 (by decide) h.1 (by omega)

private theorem family_12_8
    (c138 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 153 17 12 8)
    (c139 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 102 8 12)
    (c140 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 140 81 8 12)
    (c141 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 59 12 8)
    (P : ℕ) (h : (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P 12 8) : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P 12 8 := by
  have cover : (17 ≤ P ∧ P ≤ 24) ∨ (25 ≤ P ∧ P ≤ 37) ∨ (38 ≤ P ∧ P ≤ 58) ∨ (59 ≤ P ∧ P ≤ 76) := by
    omega
  rcases cover with h | h | h | h
  · exact lift_core c138 (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 25 12 8 from reflect (by decide) c139) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 140 38 12 8 from reflect (by decide) c140) (by decide) h.1 (by omega)
  · exact lift_core c141 (by decide) h.1 (by omega)

private theorem family_12_9
    (c142 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 109 9 12)
    (c143 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 96 9 12)
    (c144 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 83 9 12)
    (c145 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 56 12 9)
    (c146 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 69 12 9)
    (P : ℕ) (h : (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P 12 9) : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P 12 9 := by
  have cover : (17 ≤ P ∧ P ≤ 29) ∨ (30 ≤ P ∧ P ≤ 42) ∨ (43 ≤ P ∧ P ≤ 55) ∨ (56 ≤ P ∧ P ≤ 68) ∨ (69 ≤ P ∧ P ≤ 86) := by
    omega
  rcases cover with h | h | h | h | h
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 17 12 9 from reflect (by decide) c142) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 30 12 9 from reflect (by decide) c143) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 43 12 9 from reflect (by decide) c144) (by decide) h.1 (by omega)
  · exact lift_core c145 (by decide) h.1 (by omega)
  · exact lift_core c146 (by decide) h.1 (by omega)

private theorem family_12_10
    (c147 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 149 109 10 12)
    (c148 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 138 86 10 12)
    (c149 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 147 72 10 12)
    (c150 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 141 66 12 10)
    (P : ℕ) (h : (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P 12 10) : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P 12 10 := by
  have cover : (17 ≤ P ∧ P ≤ 28) ∨ (29 ≤ P ∧ P ≤ 51) ∨ (52 ≤ P ∧ P ≤ 65) ∨ (66 ≤ P ∧ P ≤ 85) := by
    omega
  rcases cover with h | h | h | h
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 149 17 12 10 from reflect (by decide) c147) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 138 29 12 10 from reflect (by decide) c148) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 147 52 12 10 from reflect (by decide) c149) (by decide) h.1 (by omega)
  · exact lift_core c150 (by decide) h.1 (by omega)

private theorem family_12_11
    (c151 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 138 17 12 11)
    (c152 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 137 73 11 12)
    (c153 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 142 64 12 11)
    (P : ℕ) (h : (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P 12 11) : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P 12 11 := by
  have cover : (17 ≤ P ∧ P ≤ 39) ∨ (40 ≤ P ∧ P ≤ 63) ∨ (64 ≤ P ∧ P ≤ 82) := by
    omega
  rcases cover with h | h | h
  · exact lift_core c151 (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 137 40 12 11 from reflect (by decide) c152) (by decide) h.1 (by omega)
  · exact lift_core c153 (by decide) h.1 (by omega)

private theorem family_13_6
    (c154 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 156 86 6 13)
    (c155 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 144 69 6 13)
    (c156 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 144 52 6 13)
    (P : ℕ) (h : (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P 13 6) : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P 13 6 := by
  have cover : (50 ≤ P ∧ P ≤ 54) ∨ (55 ≤ P ∧ P ≤ 71) ∨ (72 ≤ P ∧ P ≤ 88) := by
    omega
  rcases cover with h | h | h
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 156 50 13 6 from reflect (by decide) c154) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 144 55 13 6 from reflect (by decide) c155) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 144 72 13 6 from reflect (by decide) c156) (by decide) h.1 (by omega)

private theorem family_13_7
    (c157 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 152 102 7 13)
    (c158 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 158 99 7 13)
    (c159 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 95 7 13)
    (c160 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 159 93 7 13)
    (c161 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 158 90 7 13)
    (c162 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 158 87 7 13)
    (c163 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 153 79 7 13)
    (c164 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 151 69 7 13)
    (c165 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 65 7 13)
    (P : ℕ) (h : (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P 13 7) : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P 13 7 := by
  have cover : (29 ≤ P ∧ P ≤ 37) ∨ (38 ≤ P ∧ P ≤ 40) ∨ (41 ≤ P ∧ P ≤ 44) ∨ (45 ≤ P ∧ P ≤ 46) ∨ (47 ≤ P ∧ P ≤ 49) ∨ (50 ≤ P ∧ P ≤ 52) ∨ (53 ≤ P ∧ P ≤ 60) ∨ (61 ≤ P ∧ P ≤ 70) ∨ (71 ≤ P ∧ P ≤ 74) := by
    omega
  rcases cover with h | h | h | h | h | h | h | h | h
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 152 29 13 7 from reflect (by decide) c157) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 158 38 13 7 from reflect (by decide) c158) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 41 13 7 from reflect (by decide) c159) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 159 45 13 7 from reflect (by decide) c160) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 158 47 13 7 from reflect (by decide) c161) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 158 50 13 7 from reflect (by decide) c162) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 153 53 13 7 from reflect (by decide) c163) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 151 61 13 7 from reflect (by decide) c164) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 71 13 7 from reflect (by decide) c165) (by decide) h.1 (by omega)

private theorem family_13_8
    (c166 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 145 17 13 8)
    (c167 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 140 85 8 13)
    (c168 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 152 76 8 13)
    (c169 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 144 59 8 13)
    (P : ℕ) (h : (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P 13 8) : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P 13 8 := by
  have cover : (17 ≤ P ∧ P ≤ 32) ∨ (33 ≤ P ∧ P ≤ 53) ∨ (54 ≤ P ∧ P ≤ 62) ∨ (63 ≤ P ∧ P ≤ 79) := by
    omega
  rcases cover with h | h | h | h
  · exact lift_core c166 (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 140 33 13 8 from reflect (by decide) c167) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 152 54 13 8 from reflect (by decide) c168) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 144 63 13 8 from reflect (by decide) c169) (by decide) h.1 (by omega)

private theorem family_13_9
    (c170 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 108 9 13)
    (c171 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 146 93 9 13)
    (c172 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 150 82 9 13)
    (c173 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 150 71 9 13)
    (c174 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 152 62 9 13)
    (P : ℕ) (h : (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P 13 9) : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P 13 9 := by
  have cover : (17 ≤ P ∧ P ≤ 29) ∨ (30 ≤ P ∧ P ≤ 44) ∨ (45 ≤ P ∧ P ≤ 55) ∨ (56 ≤ P ∧ P ≤ 66) ∨ (67 ≤ P ∧ P ≤ 75) := by
    omega
  rcases cover with h | h | h | h | h
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 17 13 9 from reflect (by decide) c170) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 146 30 13 9 from reflect (by decide) c171) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 150 45 13 9 from reflect (by decide) c172) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 150 56 13 9 from reflect (by decide) c173) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 152 67 13 9 from reflect (by decide) c174) (by decide) h.1 (by omega)

private theorem family_13_10
    (c175 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 102 10 13)
    (c176 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 141 82 10 13)
    (c177 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 139 55 13 10)
    (P : ℕ) (h : (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P 13 10) : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P 13 10 := by
  have cover : (17 ≤ P ∧ P ≤ 34) ∨ (35 ≤ P ∧ P ≤ 54) ∨ (55 ≤ P ∧ P ≤ 76) := by
    omega
  rcases cover with h | h | h
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 17 13 10 from reflect (by decide) c175) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 141 35 13 10 from reflect (by decide) c176) (by decide) h.1 (by omega)
  · exact lift_core c177 (by decide) h.1 (by omega)

private theorem family_13_11
    (c178 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 147 105 11 13)
    (c179 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 149 93 11 13)
    (c180 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 80 11 13)
    (c181 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 67 11 13)
    (c182 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 147 53 11 13)
    (P : ℕ) (h : (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P 13 11) : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P 13 11 := by
  have cover : (17 ≤ P ∧ P ≤ 30) ∨ (31 ≤ P ∧ P ≤ 42) ∨ (43 ≤ P ∧ P ≤ 55) ∨ (56 ≤ P ∧ P ≤ 68) ∨ (69 ≤ P ∧ P ≤ 82) := by
    omega
  rcases cover with h | h | h | h | h
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 147 17 13 11 from reflect (by decide) c178) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 149 31 13 11 from reflect (by decide) c179) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 43 13 11 from reflect (by decide) c180) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 56 13 11 from reflect (by decide) c181) (by decide) h.1 (by omega)
  · exact lift_core (show (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 147 69 13 11 from reflect (by decide) c182) (by decide) h.1 (by omega)

theorem finite_cover
    (c0 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 149 79 6 8)
    (c1 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 146 64 6 8)
    (c2 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 146 96 7 8)
    (c3 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 153 88 7 8)
    (c4 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 144 71 7 8)
    (c5 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 152 74 8 7)
    (c6 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 152 117 9 8)
    (c7 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 147 103 9 8)
    (c8 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 150 92 9 8)
    (c9 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 153 84 9 8)
    (c10 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 151 59 8 9)
    (c11 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 144 69 8 9)
    (c12 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 112 10 8)
    (c13 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 142 93 10 8)
    (c14 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 49 8 10)
    (c15 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 155 62 8 10)
    (c16 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 68 8 10)
    (c17 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 149 17 8 11)
    (c18 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 149 100 11 8)
    (c19 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 147 86 11 8)
    (c20 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 152 77 11 8)
    (c21 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 151 64 8 11)
    (c22 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 74 8 11)
    (c23 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 142 104 12 8)
    (c24 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 142 85 12 8)
    (c25 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 138 62 12 8)
    (c26 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 104 13 8)
    (c27 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 144 87 13 8)
    (c28 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 152 52 8 13)
    (c29 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 61 8 13)
    (c30 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 146 76 6 9)
    (c31 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 58 6 9)
    (c32 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 146 96 7 9)
    (c33 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 153 88 7 9)
    (c34 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 151 78 7 9)
    (c35 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 150 67 7 9)
    (c36 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 151 116 8 9)
    (c37 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 154 109 8 9)
    (c38 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 142 90 8 9)
    (c39 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 72 8 9)
    (c40 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 150 61 8 9)
    (c41 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 149 112 10 9)
    (c42 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 99 10 9)
    (c43 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 153 91 10 9)
    (c44 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 78 10 9)
    (c45 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 155 72 10 9)
    (c46 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 150 61 10 9)
    (c47 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 147 109 11 9)
    (c48 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 150 98 11 9)
    (c49 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 152 89 11 9)
    (c50 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 85 11 9)
    (c51 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 156 80 11 9)
    (c52 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 152 60 9 11)
    (c53 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 69 9 11)
    (c54 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 152 73 9 11)
    (c55 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 104 12 9)
    (c56 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 150 93 12 9)
    (c57 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 147 79 12 9)
    (c58 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 140 58 12 9)
    (c59 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 147 107 13 9)
    (c60 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 151 97 13 9)
    (c61 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 93 13 9)
    (c62 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 89 13 9)
    (c63 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 85 13 9)
    (c64 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 158 82 13 9)
    (c65 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 154 56 9 13)
    (c66 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 151 63 9 13)
    (c67 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 150 73 9 13)
    (c68 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 87 6 10)
    (c69 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 74 6 10)
    (c70 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 61 6 10)
    (c71 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 145 95 7 10)
    (c72 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 151 85 7 10)
    (c73 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 81 7 10)
    (c74 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 77 7 10)
    (c75 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 73 7 10)
    (c76 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 154 66 7 10)
    (c77 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 146 110 8 10)
    (c78 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 147 96 8 10)
    (c79 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 92 8 10)
    (c80 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 146 77 8 10)
    (c81 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 149 65 8 10)
    (c82 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 154 117 9 10)
    (c83 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 146 102 9 10)
    (c84 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 150 91 9 10)
    (c85 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 147 50 10 9)
    (c86 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 153 64 10 9)
    (c87 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 72 10 9)
    (c88 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 109 11 10)
    (c89 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 156 104 11 10)
    (c90 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 142 85 11 10)
    (c91 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 144 54 10 11)
    (c92 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 142 71 10 11)
    (c93 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 108 12 10)
    (c94 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 147 94 12 10)
    (c95 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 90 12 10)
    (c96 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 152 81 12 10)
    (c97 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 145 65 12 10)
    (c98 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 139 43 12 10)
    (c99 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 137 96 13 10)
    (c100 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 135 70 13 10)
    (c101 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 141 50 13 10)
    (c102 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 144 74 6 11)
    (c103 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 142 55 6 11)
    (c104 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 146 96 7 11)
    (c105 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 151 86 7 11)
    (c106 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 149 74 7 11)
    (c107 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 145 68 11 7)
    (c108 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 152 115 8 11)
    (c109 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 155 109 8 11)
    (c110 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 105 8 11)
    (c111 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 101 8 11)
    (c112 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 97 8 11)
    (c113 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 154 90 8 11)
    (c114 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 72 8 11)
    (c115 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 59 8 11)
    (c116 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 146 17 11 9)
    (c117 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 145 92 9 11)
    (c118 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 151 82 9 11)
    (c119 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 150 71 9 11)
    (c120 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 152 62 9 11)
    (c121 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 149 110 10 11)
    (c122 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 92 10 11)
    (c123 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 79 10 11)
    (c124 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 146 64 10 11)
    (c125 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 102 12 11)
    (c126 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 145 86 12 11)
    (c127 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 68 12 11)
    (c128 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 55 12 11)
    (c129 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 101 13 11)
    (c130 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 142 82 13 11)
    (c131 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 146 54 11 13)
    (c132 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 147 69 11 13)
    (c133 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 145 51 12 6)
    (c134 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 146 67 12 6)
    (c135 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 93 7 12)
    (c136 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 142 48 12 7)
    (c137 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 67 12 7)
    (c138 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 153 17 12 8)
    (c139 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 102 8 12)
    (c140 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 140 81 8 12)
    (c141 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 59 12 8)
    (c142 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 109 9 12)
    (c143 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 96 9 12)
    (c144 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 83 9 12)
    (c145 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 56 12 9)
    (c146 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 69 12 9)
    (c147 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 149 109 10 12)
    (c148 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 138 86 10 12)
    (c149 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 147 72 10 12)
    (c150 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 141 66 12 10)
    (c151 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 138 17 12 11)
    (c152 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 137 73 11 12)
    (c153 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 142 64 12 11)
    (c154 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 156 86 6 13)
    (c155 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 144 69 6 13)
    (c156 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 144 52 6 13)
    (c157 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 152 102 7 13)
    (c158 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 158 99 7 13)
    (c159 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 95 7 13)
    (c160 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 159 93 7 13)
    (c161 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 158 90 7 13)
    (c162 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 158 87 7 13)
    (c163 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 153 79 7 13)
    (c164 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 151 69 7 13)
    (c165 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 157 65 7 13)
    (c166 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 145 17 13 8)
    (c167 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 140 85 8 13)
    (c168 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 152 76 8 13)
    (c169 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 144 59 8 13)
    (c170 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 108 9 13)
    (c171 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 146 93 9 13)
    (c172 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 150 82 9 13)
    (c173 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 150 71 9 13)
    (c174 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 152 62 9 13)
    (c175 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 143 102 10 13)
    (c176 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 141 82 10 13)
    (c177 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 139 55 13 10)
    (c178 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 147 105 11 13)
    (c179 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 149 93 11 13)
    (c180 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 80 11 13)
    (c181 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 148 67 11 13)
    (c182 : (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 147 53 11 13)
    (P d e : ℕ) (h : (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P d e) (hd₀ : 8 ≤ d) (hd₁ : d ≤ 13)
    (he₀ : 6 ≤ e) (he₁ : e ≤ 13) (hne : d ≠ e)
    (h₁ : ¬ (d = 12 ∧ e = 13)) (h₂ : ¬ (d = 13 ∧ e = 12)) :
    (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P d e := by
  rcases (by omega : d = 8 ∨ d = 9 ∨ d = 10 ∨ d = 11 ∨ d = 12 ∨ d = 13) with rfl | rfl | rfl | rfl | rfl | rfl
  · rcases (by omega : e = 6 ∨ e = 7 ∨ e = 8 ∨ e = 9 ∨ e = 10 ∨ e = 11 ∨ e = 12 ∨ e = 13) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact family_8_6 c0 c1 P h
    · exact family_8_7 c2 c3 c4 c5 P h
    · omega
    · exact family_8_9 c6 c7 c8 c9 c10 c11 P h
    · exact family_8_10 c12 c13 c14 c15 c16 P h
    · exact family_8_11 c17 c18 c19 c20 c21 c22 P h
    · exact family_8_12 c23 c24 c25 P h
    · exact family_8_13 c26 c27 c28 c29 P h
  · rcases (by omega : e = 6 ∨ e = 7 ∨ e = 8 ∨ e = 9 ∨ e = 10 ∨ e = 11 ∨ e = 12 ∨ e = 13) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact family_9_6 c30 c31 P h
    · exact family_9_7 c32 c33 c34 c35 P h
    · exact family_9_8 c36 c37 c38 c39 c40 P h
    · omega
    · exact family_9_10 c41 c42 c43 c44 c45 c46 P h
    · exact family_9_11 c47 c48 c49 c50 c51 c52 c53 c54 P h
    · exact family_9_12 c55 c56 c57 c58 P h
    · exact family_9_13 c59 c60 c61 c62 c63 c64 c65 c66 c67 P h
  · rcases (by omega : e = 6 ∨ e = 7 ∨ e = 8 ∨ e = 9 ∨ e = 10 ∨ e = 11 ∨ e = 12 ∨ e = 13) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact family_10_6 c68 c69 c70 P h
    · exact family_10_7 c71 c72 c73 c74 c75 c76 P h
    · exact family_10_8 c77 c78 c79 c80 c81 P h
    · exact family_10_9 c82 c83 c84 c85 c86 c87 P h
    · omega
    · exact family_10_11 c88 c89 c90 c91 c92 P h
    · exact family_10_12 c93 c94 c95 c96 c97 c98 P h
    · exact family_10_13 c99 c100 c101 P h
  · rcases (by omega : e = 6 ∨ e = 7 ∨ e = 8 ∨ e = 9 ∨ e = 10 ∨ e = 11 ∨ e = 12 ∨ e = 13) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact family_11_6 c102 c103 P h
    · exact family_11_7 c104 c105 c106 c107 P h
    · exact family_11_8 c108 c109 c110 c111 c112 c113 c114 c115 P h
    · exact family_11_9 c116 c117 c118 c119 c120 P h
    · exact family_11_10 c121 c122 c123 c124 P h
    · omega
    · exact family_11_12 c125 c126 c127 c128 P h
    · exact family_11_13 c129 c130 c131 c132 P h
  · rcases (by omega : e = 6 ∨ e = 7 ∨ e = 8 ∨ e = 9 ∨ e = 10 ∨ e = 11 ∨ e = 12 ∨ e = 13) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact family_12_6 c133 c134 P h
    · exact family_12_7 c135 c136 c137 P h
    · exact family_12_8 c138 c139 c140 c141 P h
    · exact family_12_9 c142 c143 c144 c145 c146 P h
    · exact family_12_10 c147 c148 c149 c150 P h
    · exact family_12_11 c151 c152 c153 P h
    · omega
    · omega
  · rcases (by omega : e = 6 ∨ e = 7 ∨ e = 8 ∨ e = 9 ∨ e = 10 ∨ e = 11 ∨ e = 12 ∨ e = 13) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact family_13_6 c154 c155 c156 P h
    · exact family_13_7 c157 c158 c159 c160 c161 c162 c163 c164 c165 P h
    · exact family_13_8 c166 c167 c168 c169 P h
    · exact family_13_9 c170 c171 c172 c173 c174 P h
    · exact family_13_10 c175 c176 c177 P h
    · exact family_13_11 c178 c179 c180 c181 c182 P h
    · omega
    · omega

theorem shared_endpoint
    (covered : ∀ P d e, (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P d e → 8 ≤ d → d ≤ 13 → 6 ≤ e → e ≤ 13 →
      d ≠ e → ¬ (d = 12 ∧ e = 13) → ¬ (d = 13 ∧ e = 12) → (fun (N p d e : ℕ) => ∀ R : ℕ → Prop, (∀ x, R x → x < N) → (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) → (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) → R p → R (p+d) → R (p+d+e) → (∀ x, p<x → x<p+d → ¬R x) → (∀ x, p+d<x → x<p+d+e → ¬R x) → False) 160 P d e)
    (R : ℕ → Prop) (P Q V : ℕ)
    (w : 17 ≤ P ∧ P+8 ≤ Q ∧ Q ≤ P+13 ∧ P+Q ≤ 159 ∧
      Q+6 ≤ V ∧ V ≤ Q+13 ∧ V < 160 ∧
      (Q ≤ 62 → Q+7 ≤ V) ∧ (Q ≤ 41 → Q+8 ≤ V))
    (g₀ : R P ∧ R Q ∧ ∀ x, P < x → x < Q → ¬ R x)
    (g₁ : R Q ∧ R V ∧ ∀ x, Q < x → x < V → ¬ R x)
    (tr : ∀ a d, 0 < d → a+2*d < 160 → R a → R (a+d) → R (a+2*d) → False)
    (hit : ∀ a d, 0 < d → a+12*d < 160 → ∃ i : Fin 13, R (a+i.val*d)) : False := by
  rcases w with ⟨hP, hPQ, hQP, hsum, hQV, hVQ, hV, h62, h41⟩
  obtain ⟨d, rfl⟩ : ∃ d, Q = P+d := ⟨Q-P, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, V = P+d+e := ⟨V-(P+d), by omega⟩
  by_cases hne : d = e
  · subst e
    exact GreenAnalyticReview.equal_gaps (by omega) (by omega) g₀
      (by simpa only [show P+d+d = P+2*d by omega] using g₁) tr
  by_cases h₁ : d = 12 ∧ e = 13
  · rcases h₁ with ⟨rfl, rfl⟩
    exact GreenAnalyticReview.gaps_12_13 (by omega) (by omega) g₀
      (by simpa only [Nat.add_assoc] using g₁) tr hit
  by_cases h₂ : d = 13 ∧ e = 12
  · rcases h₂ with ⟨rfl, rfl⟩
    exact GreenAnalyticReview.gaps_13_12 (by omega) g₀
      (by simpa only [Nat.add_assoc] using g₁) tr hit
  have hw : (fun (P d e : ℕ) => 17 ≤ P ∧ 2*P+d ≤ 159 ∧ (P+d ≤ 62 → 7 ≤ e) ∧ (P+d ≤ 41 → 8 ≤ e)) P d e := by
    refine ⟨hP, by omega, ?_, ?_⟩
    · intro h
      have := h62 h
      omega
    · intro h
      have := h41 h
      omega

  have hc := covered P d e hw (by omega) (by omega) (by omega) (by omega) hne h₁ h₂
  exact translate hc (by omega) (by omega) (by omega) R tr hit g₀.1 g₀.2.1 g₁.2.1 g₀.2.2 g₁.2.2

end GreenCoverage

/-! Four balanced finite certificate bundles, with all geometric and coverage implications proved above. -/
namespace OMA.R_Green14_W_3_13_R3_H1_R3

def H1 : Prop :=
  ∀ N p d e : ℕ, (N,p,d,e) ∈ [(149,79,6,8),(144,69,8,9),(148,112,10,8),(143,74,8,11),(144,87,13,8),(143,72,8,9),(157,69,9,11),(150,93,12,9),(157,93,13,9),(157,89,13,9),(157,85,13,9),(154,56,9,13),(150,73,9,13),(148,74,6,10),(145,95,7,10),(157,81,7,10),(157,77,7,10),(146,110,8,10),(154,117,9,10),(147,50,10,9),(153,64,10,9),(144,54,10,11),(139,43,12,10),(137,96,13,10),(144,74,6,11),(149,74,7,11),(155,109,8,11),(157,101,8,11),(148,59,8,11),(150,71,9,11),(146,64,10,11),(143,102,12,11),(143,101,13,11),(146,54,11,13),(146,67,12,6),(148,102,8,12),(143,59,12,8),(148,83,9,12),(148,56,12,9),(147,72,10,12),(158,99,7,13),(158,87,7,13),(151,69,7,13),(157,65,7,13),(149,93,11,13)] →
  ∀ R : ℕ → Prop, (∀ x, R x → x < N) →
    (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) →
    (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) →
    R p → R (p+d) → R (p+d+e) →
    (∀ x, p<x → x<p+d → ¬R x) →
    (∀ x, p+d<x → x<p+d+e → ¬R x) → False

def H2 : Prop :=
  ∀ N p d e : ℕ, (N,p,d,e) ∈ [(153,88,7,8),(152,117,9,8),(142,93,10,8),(148,49,8,10),(155,62,8,10),(149,100,11,8),(147,86,11,8),(152,77,11,8),(142,104,12,8),(142,85,12,8),(138,62,12,8),(143,61,8,13),(146,76,6,9),(146,96,7,9),(154,109,8,9),(150,61,8,9),(153,91,10,9),(150,61,10,9),(150,98,11,9),(152,60,9,11),(143,104,12,9),(147,107,13,9),(157,87,6,10),(154,66,7,10),(157,92,8,10),(157,90,12,10),(141,50,13,10),(146,96,7,11),(151,86,7,11),(157,105,8,11),(154,90,8,11),(149,110,10,11),(148,79,10,11),(148,55,12,11),(147,69,11,13),(148,96,9,12),(143,69,12,9),(149,109,10,12),(138,86,10,12),(144,52,6,13),(145,17,13,8),(152,76,8,13),(148,108,9,13),(146,93,9,13),(152,62,9,13),(147,105,11,13)] →
  ∀ R : ℕ → Prop, (∀ x, R x → x < N) →
    (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) →
    (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) →
    R p → R (p+d) → R (p+d+e) →
    (∀ x, p<x → x<p+d → ¬R x) →
    (∀ x, p+d<x → x<p+d+e → ¬R x) → False

def H3 : Prop :=
  ∀ N p d e : ℕ, (N,p,d,e) ∈ [(146,96,7,8),(144,71,7,8),(147,103,9,8),(150,92,9,8),(149,17,8,11),(151,64,8,11),(150,67,7,9),(148,99,10,9),(147,109,11,9),(152,89,11,9),(156,80,11,9),(147,79,12,9),(140,58,12,9),(151,63,9,13),(146,102,9,10),(150,91,9,10),(148,72,10,9),(148,109,11,10),(156,104,11,10),(142,85,11,10),(142,71,10,11),(148,108,12,10),(147,94,12,10),(152,115,8,11),(157,97,8,11),(143,72,8,11),(146,17,11,9),(145,92,9,11),(151,82,9,11),(143,92,10,11),(143,68,12,11),(142,82,13,11),(143,93,7,12),(142,48,12,7),(148,67,12,7),(140,81,8,12),(141,66,12,10),(138,17,12,11),(142,64,12,11),(156,86,6,13),(144,69,6,13),(152,102,7,13),(157,95,7,13),(144,59,8,13),(148,80,11,13),(148,67,11,13)] →
  ∀ R : ℕ → Prop, (∀ x, R x → x < N) →
    (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) →
    (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) →
    R p → R (p+d) → R (p+d+e) →
    (∀ x, p<x → x<p+d → ¬R x) →
    (∀ x, p+d<x → x<p+d+e → ¬R x) → False

def H4 : Prop :=
  ∀ N p d e : ℕ, (N,p,d,e) ∈ [(146,64,6,8),(152,74,8,7),(153,84,9,8),(151,59,8,9),(143,68,8,10),(143,104,13,8),(152,52,8,13),(143,58,6,9),(153,88,7,9),(151,78,7,9),(151,116,8,9),(142,90,8,9),(149,112,10,9),(148,78,10,9),(155,72,10,9),(157,85,11,9),(152,73,9,11),(151,97,13,9),(158,82,13,9),(148,61,6,10),(151,85,7,10),(157,73,7,10),(147,96,8,10),(146,77,8,10),(149,65,8,10),(152,81,12,10),(145,65,12,10),(135,70,13,10),(142,55,6,11),(145,68,11,7),(152,62,9,11),(145,86,12,11),(145,51,12,6),(153,17,12,8),(148,109,9,12),(137,73,11,12),(159,93,7,13),(158,90,7,13),(153,79,7,13),(140,85,8,13),(150,82,9,13),(150,71,9,13),(143,102,10,13),(141,82,10,13),(139,55,13,10),(147,53,11,13)] →
  ∀ R : ℕ → Prop, (∀ x, R x → x < N) →
    (∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False) →
    (∀ a d, 0 < d → a+12*d < N → ∃ i : Fin 13, R (a+i.val*d)) →
    R p → R (p+d) → R (p+d+e) →
    (∀ x, p<x → x<p+d → ¬R x) →
    (∀ x, p+d<x → x<p+d+e → ¬R x) → False

theorem main : H1 → H2 → H3 → H4 → OMA.R_Green14_W_3_13_R3.H1 := by
  intro h1 h2 h3 h4 R P Q V widths gap₀ gap₁ _ free meets
  have c0 := h1 149 79 6 8 (by decide)
  have c1 := h4 146 64 6 8 (by decide)
  have c2 := h3 146 96 7 8 (by decide)
  have c3 := h2 153 88 7 8 (by decide)
  have c4 := h3 144 71 7 8 (by decide)
  have c5 := h4 152 74 8 7 (by decide)
  have c6 := h2 152 117 9 8 (by decide)
  have c7 := h3 147 103 9 8 (by decide)
  have c8 := h3 150 92 9 8 (by decide)
  have c9 := h4 153 84 9 8 (by decide)
  have c10 := h4 151 59 8 9 (by decide)
  have c11 := h1 144 69 8 9 (by decide)
  have c12 := h1 148 112 10 8 (by decide)
  have c13 := h2 142 93 10 8 (by decide)
  have c14 := h2 148 49 8 10 (by decide)
  have c15 := h2 155 62 8 10 (by decide)
  have c16 := h4 143 68 8 10 (by decide)
  have c17 := h3 149 17 8 11 (by decide)
  have c18 := h2 149 100 11 8 (by decide)
  have c19 := h2 147 86 11 8 (by decide)
  have c20 := h2 152 77 11 8 (by decide)
  have c21 := h3 151 64 8 11 (by decide)
  have c22 := h1 143 74 8 11 (by decide)
  have c23 := h2 142 104 12 8 (by decide)
  have c24 := h2 142 85 12 8 (by decide)
  have c25 := h2 138 62 12 8 (by decide)
  have c26 := h4 143 104 13 8 (by decide)
  have c27 := h1 144 87 13 8 (by decide)
  have c28 := h4 152 52 8 13 (by decide)
  have c29 := h2 143 61 8 13 (by decide)
  have c30 := h2 146 76 6 9 (by decide)
  have c31 := h4 143 58 6 9 (by decide)
  have c32 := h2 146 96 7 9 (by decide)
  have c33 := h4 153 88 7 9 (by decide)
  have c34 := h4 151 78 7 9 (by decide)
  have c35 := h3 150 67 7 9 (by decide)
  have c36 := h4 151 116 8 9 (by decide)
  have c37 := h2 154 109 8 9 (by decide)
  have c38 := h4 142 90 8 9 (by decide)
  have c39 := h1 143 72 8 9 (by decide)
  have c40 := h2 150 61 8 9 (by decide)
  have c41 := h4 149 112 10 9 (by decide)
  have c42 := h3 148 99 10 9 (by decide)
  have c43 := h2 153 91 10 9 (by decide)
  have c44 := h4 148 78 10 9 (by decide)
  have c45 := h4 155 72 10 9 (by decide)
  have c46 := h2 150 61 10 9 (by decide)
  have c47 := h3 147 109 11 9 (by decide)
  have c48 := h2 150 98 11 9 (by decide)
  have c49 := h3 152 89 11 9 (by decide)
  have c50 := h4 157 85 11 9 (by decide)
  have c51 := h3 156 80 11 9 (by decide)
  have c52 := h2 152 60 9 11 (by decide)
  have c53 := h1 157 69 9 11 (by decide)
  have c54 := h4 152 73 9 11 (by decide)
  have c55 := h2 143 104 12 9 (by decide)
  have c56 := h1 150 93 12 9 (by decide)
  have c57 := h3 147 79 12 9 (by decide)
  have c58 := h3 140 58 12 9 (by decide)
  have c59 := h2 147 107 13 9 (by decide)
  have c60 := h4 151 97 13 9 (by decide)
  have c61 := h1 157 93 13 9 (by decide)
  have c62 := h1 157 89 13 9 (by decide)
  have c63 := h1 157 85 13 9 (by decide)
  have c64 := h4 158 82 13 9 (by decide)
  have c65 := h1 154 56 9 13 (by decide)
  have c66 := h3 151 63 9 13 (by decide)
  have c67 := h1 150 73 9 13 (by decide)
  have c68 := h2 157 87 6 10 (by decide)
  have c69 := h1 148 74 6 10 (by decide)
  have c70 := h4 148 61 6 10 (by decide)
  have c71 := h1 145 95 7 10 (by decide)
  have c72 := h4 151 85 7 10 (by decide)
  have c73 := h1 157 81 7 10 (by decide)
  have c74 := h1 157 77 7 10 (by decide)
  have c75 := h4 157 73 7 10 (by decide)
  have c76 := h2 154 66 7 10 (by decide)
  have c77 := h1 146 110 8 10 (by decide)
  have c78 := h4 147 96 8 10 (by decide)
  have c79 := h2 157 92 8 10 (by decide)
  have c80 := h4 146 77 8 10 (by decide)
  have c81 := h4 149 65 8 10 (by decide)
  have c82 := h1 154 117 9 10 (by decide)
  have c83 := h3 146 102 9 10 (by decide)
  have c84 := h3 150 91 9 10 (by decide)
  have c85 := h1 147 50 10 9 (by decide)
  have c86 := h1 153 64 10 9 (by decide)
  have c87 := h3 148 72 10 9 (by decide)
  have c88 := h3 148 109 11 10 (by decide)
  have c89 := h3 156 104 11 10 (by decide)
  have c90 := h3 142 85 11 10 (by decide)
  have c91 := h1 144 54 10 11 (by decide)
  have c92 := h3 142 71 10 11 (by decide)
  have c93 := h3 148 108 12 10 (by decide)
  have c94 := h3 147 94 12 10 (by decide)
  have c95 := h2 157 90 12 10 (by decide)
  have c96 := h4 152 81 12 10 (by decide)
  have c97 := h4 145 65 12 10 (by decide)
  have c98 := h1 139 43 12 10 (by decide)
  have c99 := h1 137 96 13 10 (by decide)
  have c100 := h4 135 70 13 10 (by decide)
  have c101 := h2 141 50 13 10 (by decide)
  have c102 := h1 144 74 6 11 (by decide)
  have c103 := h4 142 55 6 11 (by decide)
  have c104 := h2 146 96 7 11 (by decide)
  have c105 := h2 151 86 7 11 (by decide)
  have c106 := h1 149 74 7 11 (by decide)
  have c107 := h4 145 68 11 7 (by decide)
  have c108 := h3 152 115 8 11 (by decide)
  have c109 := h1 155 109 8 11 (by decide)
  have c110 := h2 157 105 8 11 (by decide)
  have c111 := h1 157 101 8 11 (by decide)
  have c112 := h3 157 97 8 11 (by decide)
  have c113 := h2 154 90 8 11 (by decide)
  have c114 := h3 143 72 8 11 (by decide)
  have c115 := h1 148 59 8 11 (by decide)
  have c116 := h3 146 17 11 9 (by decide)
  have c117 := h3 145 92 9 11 (by decide)
  have c118 := h3 151 82 9 11 (by decide)
  have c119 := h1 150 71 9 11 (by decide)
  have c120 := h4 152 62 9 11 (by decide)
  have c121 := h2 149 110 10 11 (by decide)
  have c122 := h3 143 92 10 11 (by decide)
  have c123 := h2 148 79 10 11 (by decide)
  have c124 := h1 146 64 10 11 (by decide)
  have c125 := h1 143 102 12 11 (by decide)
  have c126 := h4 145 86 12 11 (by decide)
  have c127 := h3 143 68 12 11 (by decide)
  have c128 := h2 148 55 12 11 (by decide)
  have c129 := h1 143 101 13 11 (by decide)
  have c130 := h3 142 82 13 11 (by decide)
  have c131 := h1 146 54 11 13 (by decide)
  have c132 := h2 147 69 11 13 (by decide)
  have c133 := h4 145 51 12 6 (by decide)
  have c134 := h1 146 67 12 6 (by decide)
  have c135 := h3 143 93 7 12 (by decide)
  have c136 := h3 142 48 12 7 (by decide)
  have c137 := h3 148 67 12 7 (by decide)
  have c138 := h4 153 17 12 8 (by decide)
  have c139 := h1 148 102 8 12 (by decide)
  have c140 := h3 140 81 8 12 (by decide)
  have c141 := h1 143 59 12 8 (by decide)
  have c142 := h4 148 109 9 12 (by decide)
  have c143 := h2 148 96 9 12 (by decide)
  have c144 := h1 148 83 9 12 (by decide)
  have c145 := h1 148 56 12 9 (by decide)
  have c146 := h2 143 69 12 9 (by decide)
  have c147 := h2 149 109 10 12 (by decide)
  have c148 := h2 138 86 10 12 (by decide)
  have c149 := h1 147 72 10 12 (by decide)
  have c150 := h3 141 66 12 10 (by decide)
  have c151 := h3 138 17 12 11 (by decide)
  have c152 := h4 137 73 11 12 (by decide)
  have c153 := h3 142 64 12 11 (by decide)
  have c154 := h3 156 86 6 13 (by decide)
  have c155 := h3 144 69 6 13 (by decide)
  have c156 := h2 144 52 6 13 (by decide)
  have c157 := h3 152 102 7 13 (by decide)
  have c158 := h1 158 99 7 13 (by decide)
  have c159 := h3 157 95 7 13 (by decide)
  have c160 := h4 159 93 7 13 (by decide)
  have c161 := h4 158 90 7 13 (by decide)
  have c162 := h1 158 87 7 13 (by decide)
  have c163 := h4 153 79 7 13 (by decide)
  have c164 := h1 151 69 7 13 (by decide)
  have c165 := h1 157 65 7 13 (by decide)
  have c166 := h2 145 17 13 8 (by decide)
  have c167 := h4 140 85 8 13 (by decide)
  have c168 := h2 152 76 8 13 (by decide)
  have c169 := h3 144 59 8 13 (by decide)
  have c170 := h2 148 108 9 13 (by decide)
  have c171 := h2 146 93 9 13 (by decide)
  have c172 := h4 150 82 9 13 (by decide)
  have c173 := h4 150 71 9 13 (by decide)
  have c174 := h2 152 62 9 13 (by decide)
  have c175 := h4 143 102 10 13 (by decide)
  have c176 := h4 141 82 10 13 (by decide)
  have c177 := h4 139 55 13 10 (by decide)
  have c178 := h2 147 105 11 13 (by decide)
  have c179 := h1 149 93 11 13 (by decide)
  have c180 := h3 148 80 11 13 (by decide)
  have c181 := h3 148 67 11 13 (by decide)
  have c182 := h4 147 53 11 13 (by decide)
  exact GreenCoverage.shared_endpoint
    (GreenCoverage.finite_cover c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 c35 c36 c37 c38 c39 c40 c41 c42 c43 c44 c45 c46 c47 c48 c49 c50 c51 c52 c53 c54 c55 c56 c57 c58 c59 c60 c61 c62 c63 c64 c65 c66 c67 c68 c69 c70 c71 c72 c73 c74 c75 c76 c77 c78 c79 c80 c81 c82 c83 c84 c85 c86 c87 c88 c89 c90 c91 c92 c93 c94 c95 c96 c97 c98 c99 c100 c101 c102 c103 c104 c105 c106 c107 c108 c109 c110 c111 c112 c113 c114 c115 c116 c117 c118 c119 c120 c121 c122 c123 c124 c125 c126 c127 c128 c129 c130 c131 c132 c133 c134 c135 c136 c137 c138 c139 c140 c141 c142 c143 c144 c145 c146 c147 c148 c149 c150 c151 c152 c153 c154 c155 c156 c157 c158 c159 c160 c161 c162 c163 c164 c165 c166 c167 c168 c169 c170 c171 c172 c173 c174 c175 c176 c177 c178 c179 c180 c181 c182)
    R P Q V widths gap₀ gap₁ free meets

end OMA.R_Green14_W_3_13_R3_H1_R3
