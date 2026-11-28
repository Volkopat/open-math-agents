import OMAReductions.R_Erdos1191_erdos_1191_parts_i_R3
import Mathlib
import Mathlib.Order.Filter.Ultrafilter.Basic

/-!
The dyadic block estimate below improves the constant 512 to 42 for sufficiently
large starting exponents (at least one million for the constant 42). This proves finite attainability through coefficient
12. Beyond that range, failure of the doubled threshold supplies a single
infinite Sidon set. Each scale meeting the old bound then forces a dense annulus
in the next four exponents. The remaining two cases distinguish whether such
scales occupy a positive upper proportion of some fixed residue modulo four
on intervals [R,2R], or have vanishing relative frequency on those intervals.
In a fixed residue the corresponding four-exponent annuli are disjoint.
A common counting constraint bounds the sum of late-window pair counts in
terms of the population of an earlier interval. It follows by applying Cauchy–
Schwarz to all translates and counting each positive difference at most once.

The finite bound adapts Ronandt's dyadic-block argument (project PR 772).
The compactness argument uses the finite-prefix ultrafilter construction of
NicholasWierenga from the sibling reduction for part (ii).
-/

section

/- This quantitative estimate adapts @Ronandt's proof in PR 772
(https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/772).
The positive differences inject into ordered pairs of offsets in a short
interval. We also retain the lower endpoint in the harmonic sum. -/

open Filter Real Finset

open scoped Classical

namespace OMA.SidonQuantitative

lemma sidon_diff_inj {A : Set ℕ} (hA : IsSidon A)
    {a₁ b₁ a₂ b₂ : ℕ} (ha₁ : a₁ ∈ A) (hb₁ : b₁ ∈ A) (ha₂ : a₂ ∈ A) (hb₂ : b₂ ∈ A)
    (h₁ : a₁ < b₁) (h₂ : a₂ < b₂) (heq : b₁ - a₁ = b₂ - a₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  have hsum : b₁ + a₂ = b₂ + a₁ := by omega
  rcases hA b₁ hb₁ b₂ hb₂ a₂ ha₂ a₁ ha₁ hsum with ⟨hb, ha⟩ | ⟨hba, _⟩
  · exact ⟨ha.symm, hb⟩
  · omega

lemma sidonCount_mul_pred_le {A : Set ℕ} (hA : IsSidon A) (n : ℕ) :
    ((Finset.Icc 1 n).filter (· ∈ A)).card * (((Finset.Icc 1 n).filter (· ∈ A)).card - 1) ≤ 2 * n := by
  let S : Finset ℕ := (Finset.Icc 1 n).filter (· ∈ A)
  let P : Finset (ℕ × ℕ) := (S ×ˢ S).filter (fun p => p.1 < p.2)
  have hP_le : P.card ≤ n := by
    have hinj : Set.InjOn (fun p : ℕ × ℕ => p.2 - p.1) (P : Set (ℕ × ℕ)) := by
      intro p₁ hp₁ p₂ hp₂ heq
      simp only [Finset.mem_coe, P, Finset.mem_filter, Finset.mem_product, S] at hp₁ hp₂
      have ⟨h1, h2⟩ := sidon_diff_inj hA hp₁.1.1.2 hp₁.1.2.2 hp₂.1.1.2 hp₂.1.2.2 hp₁.2 hp₂.2 heq
      exact Prod.ext h1 h2
    have hmaps : Set.MapsTo (fun p : ℕ × ℕ => p.2 - p.1) (P : Set (ℕ × ℕ))
        (Finset.Icc 1 n : Set ℕ) := by
      intro p hp
      simp only [Finset.mem_coe, P, Finset.mem_filter, Finset.mem_product, S,
        Finset.mem_Icc] at hp ⊢
      omega
    have hle := Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.2 - p.1) hmaps hinj
    simpa using hle
  have h2P : 2 * P.card = S.card * (S.card - 1) := by
    let Q : Finset (ℕ × ℕ) := (S ×ˢ S).filter (fun p => p.2 < p.1)
    have hdisj : Disjoint P Q := by
      rw [Finset.disjoint_filter]
      intro p _ h1 h2
      omega
    have hunion : P ∪ Q = S.offDiag := by
      ext ⟨a, b⟩
      simp only [P, Q, Finset.mem_union, Finset.mem_filter, Finset.mem_product, Finset.mem_offDiag]
      constructor
      · rintro (⟨⟨ha, hb⟩, hlt⟩ | ⟨⟨ha, hb⟩, hlt⟩)
        · exact ⟨ha, hb, ne_of_lt hlt⟩
        · exact ⟨ha, hb, ne_of_gt hlt⟩
      · rintro ⟨ha, hb, hne⟩
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · exact Or.inl ⟨⟨ha, hb⟩, hlt⟩
        · exact Or.inr ⟨⟨ha, hb⟩, hlt⟩
    have hPQ : P.card = Q.card := by
      refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
      · intro p hp
        simp only [P, Q, Finset.mem_filter, Finset.mem_product] at hp ⊢
        exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
      · intro p₁ _ p₂ _ h
        exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
      · intro q hq
        simp only [P, Q, Finset.mem_filter, Finset.mem_product] at hq ⊢
        exact ⟨(q.2, q.1), ⟨⟨hq.1.2, hq.1.1⟩, hq.2⟩, rfl⟩
    have hoff : S.offDiag.card = S.card * S.card - S.card := Finset.offDiag_card S
    have hcard : P.card + Q.card = S.offDiag.card := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    have hmul : S.card * (S.card - 1) = S.card * S.card - S.card := by
      rw [Nat.mul_sub_left_distrib, mul_one]
    omega
  change S.card * (S.card - 1) ≤ 2 * n
  omega

lemma sidonCount_le_two_sqrt {A : Set ℕ} (hA : IsSidon A) {n : ℕ} (hn : 1 ≤ n) :
    (((Finset.Icc 1 n).filter (· ∈ A)).card : ℝ) ≤ 2 * Real.sqrt n := by
  have h1 : ((Finset.Icc 1 n).filter (· ∈ A)).card * (((Finset.Icc 1 n).filter (· ∈ A)).card - 1) ≤ 2 * n := sidonCount_mul_pred_le hA n
  have hsq : ((Finset.Icc 1 n).filter (· ∈ A)).card ^ 2 ≤ 4 * n := by
    rcases Nat.lt_or_ge (((Finset.Icc 1 n).filter (· ∈ A)).card) 2 with hk | hk
    · have : ((Finset.Icc 1 n).filter (· ∈ A)).card ≤ 1 := by omega
      nlinarith
    · have h2 : ((Finset.Icc 1 n).filter (· ∈ A)).card ≤ 2 * (((Finset.Icc 1 n).filter (· ∈ A)).card - 1) := by omega
      nlinarith
  have hsqR : ((((Finset.Icc 1 n).filter (· ∈ A)).card : ℝ)) ^ 2 ≤ (2 * Real.sqrt n) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    norm_num
    exact_mod_cast hsq
  nlinarith [Real.sqrt_nonneg n]

theorem geom_count_three_halves {n r : ℕ} (hr : 16 ≤ r) (h : n * (n-1) ≤ 2*(r^2+r)) :
    2*n ≤ 3*r := by
  by_contra! hv
  have hn : 1 ≤ n := by omega
  zify [hn] at hr h hv
  have hmul := mul_nonneg
    (show (0:ℤ) ≤ 2*n-3*r-1 by omega)
    (show (0:ℤ) ≤ 2*n+3*r-1 by omega)
  nlinarith [mul_nonneg (show (0:ℤ) ≤ r-16 by omega) (Int.natCast_nonneg r)]

lemma sidon_window_sq_sum_le {A : Set ℕ} (hA : IsSidon A) {r : ℕ} (hr : 16 ≤ r) :
    2 * (∑ j ∈ Finset.Icc 1 (r ^ 2), (((Finset.Ioc j (j + r)).filter (· ∈ A)).card) ^ 2) ≤
      5 * r ^ 2 := by
  let W : ℕ → Finset ℕ := fun j => (Finset.Ioc j (j + r)).filter (· ∈ A)
  let P : ℕ → Finset (ℕ × ℕ) := fun j => (W j ×ˢ W j).filter (fun p => p.1 < p.2)
  have hpair_sum : 2 * (∑ j ∈ Finset.Icc 1 (r ^ 2), (P j).card) ≤ r ^ 2 := by
    rw [← Finset.card_sigma]
    let T := (Finset.Icc 1 (r ^ 2)).sigma P
    have hinj : Set.InjOn (fun x : Σ _ : ℕ, ℕ × ℕ => (x.2.1 - x.1, x.2.2 - x.1)) (T : Set _) := by
      intro x₁ hx₁ x₂ hx₂ heq
      simp only [Finset.mem_coe, T, Finset.mem_sigma, P, W, Finset.mem_filter,
        Finset.mem_product, Finset.mem_Ioc] at hx₁ hx₂
      have hshift : x₁.2.1 - x₁.1 = x₂.2.1 - x₂.1 := congrArg Prod.fst heq
      have htop : x₁.2.2 - x₁.1 = x₂.2.2 - x₂.1 := congrArg Prod.snd heq
      have hdiff : x₁.2.2 - x₁.2.1 = x₂.2.2 - x₂.2.1 := by omega
      have ⟨ha, hb⟩ := sidon_diff_inj hA hx₁.2.1.1.2 hx₁.2.1.2.2 hx₂.2.1.1.2 hx₂.2.1.2.2
        hx₁.2.2 hx₂.2.2 hdiff
      have hj : x₁.1 = x₂.1 := by omega
      cases x₁; cases x₂
      simp only at ha hb hj
      subst hj
      exact congrArg (Sigma.mk _) (Prod.ext ha hb)
    have hmaps : Set.MapsTo (fun x : Σ _ : ℕ, ℕ × ℕ => (x.2.1 - x.1, x.2.2 - x.1)) (T : Set _)
        (((Finset.Icc 1 r ×ˢ Finset.Icc 1 r).filter (fun p : ℕ × ℕ => p.1 < p.2)) : Set (ℕ × ℕ)) := by
      intro x hx
      simp only [Finset.mem_coe, T, Finset.mem_sigma, P, W, Finset.mem_filter,
        Finset.mem_product, Finset.mem_Ioc, Finset.mem_Icc] at hx ⊢
      exact ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, by omega⟩
    have hle := Finset.card_le_card_of_injOn _ hmaps hinj
    rw [Finset.card_product_filter_lt] at hle
    have he : (Finset.Icc 1 r).card = r := by simp
    change 2 * T.card ≤ r ^ 2
    rw [he, Nat.choose_two_right] at hle
    have hp : r * (r - 1) ≤ r ^ 2 := by
      simpa [sq] using Nat.mul_le_mul_left r (Nat.sub_le r 1)
    omega
  have hlin_sum : ∑ j ∈ Finset.Icc 1 (r ^ 2), (W j).card ≤ ((Finset.Icc 1 (r ^ 2 + r)).filter (· ∈ A)).card * r := by
    rw [← Finset.card_sigma]
    let T₁ := (Finset.Icc 1 (r ^ 2)).sigma W
    let S := (Finset.Icc 1 (r ^ 2 + r)).filter (· ∈ A)
    have hinj : Set.InjOn (fun x : Σ _ : ℕ, ℕ => (x.2, x.2 - x.1)) (T₁ : Set _) := by
      intro x₁ hx₁ x₂ hx₂ heq
      simp only [Finset.mem_coe, T₁, Finset.mem_sigma, W, Finset.mem_filter,
        Finset.mem_Ioc] at hx₁ hx₂
      have ha : x₁.2 = x₂.2 := congrArg Prod.fst heq
      have hshift : x₁.2 - x₁.1 = x₂.2 - x₂.1 := congrArg Prod.snd heq
      have hj : x₁.1 = x₂.1 := by omega
      cases x₁; cases x₂
      simp only at ha hj
      subst hj; subst ha; rfl
    have hmaps : Set.MapsTo (fun x : Σ _ : ℕ, ℕ => (x.2, x.2 - x.1)) (T₁ : Set _)
        ((S ×ˢ Finset.Icc 1 r : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
      intro x hx
      simp only [Finset.mem_coe, T₁, Finset.mem_sigma, W, S, Finset.mem_filter,
        Finset.mem_product, Finset.mem_Ioc, Finset.mem_Icc] at hx ⊢
      exact ⟨⟨⟨by omega, by omega⟩, hx.2.2⟩, ⟨by omega, by omega⟩⟩
    have hle := Finset.card_le_card_of_injOn _ hmaps hinj
    simpa [T₁, S] using hle
  have hcnt : 2 * ((Finset.Icc 1 (r ^ 2 + r)).filter (· ∈ A)).card ≤ 3 * r :=
    geom_count_three_halves hr (sidonCount_mul_pred_le hA (r^2+r))
  have hsq_decomp : ∀ j, (W j).card ^ 2 = 2 * (P j).card + (W j).card := by
    intro j
    let Q := (W j ×ˢ W j).filter (fun p => p.2 < p.1)
    have hdisj : Disjoint (P j) Q := by
      rw [Finset.disjoint_filter]
      intro p _ h1 h2
      omega
    have hunion : P j ∪ Q = (W j).offDiag := by
      ext ⟨a, b⟩
      simp only [P, Q, Finset.mem_union, Finset.mem_filter, Finset.mem_product, Finset.mem_offDiag]
      constructor
      · rintro (⟨⟨ha, hb⟩, hlt⟩ | ⟨⟨ha, hb⟩, hlt⟩)
        · exact ⟨ha, hb, ne_of_lt hlt⟩
        · exact ⟨ha, hb, ne_of_gt hlt⟩
      · rintro ⟨ha, hb, hne⟩
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · exact Or.inl ⟨⟨ha, hb⟩, hlt⟩
        · exact Or.inr ⟨⟨ha, hb⟩, hlt⟩
    have hPQ : (P j).card = Q.card := by
      refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
      · intro p hp
        simp only [P, Q, Finset.mem_filter, Finset.mem_product] at hp ⊢
        exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
      · intro p₁ _ p₂ _ h
        exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
      · intro q hq
        simp only [P, Q, Finset.mem_filter, Finset.mem_product] at hq ⊢
        exact ⟨(q.2, q.1), ⟨⟨hq.1.2, hq.1.1⟩, hq.2⟩, rfl⟩
    have hoff : (W j).offDiag.card = (W j).card * (W j).card - (W j).card := Finset.offDiag_card (W j)
    have hcard : (P j).card + Q.card = (W j).offDiag.card := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    have hle : (W j).card ≤ (W j).card * (W j).card := Nat.le_mul_self _
    rw [sq]
    omega
  have hsum_eq : ∑ j ∈ Finset.Icc 1 (r ^ 2), (W j).card ^ 2 =
      2 * (∑ j ∈ Finset.Icc 1 (r ^ 2), (P j).card) +
        ∑ j ∈ Finset.Icc 1 (r ^ 2), (W j).card := by
    simp_rw [hsq_decomp, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hsum_eq]
  have hlin' : 2 * (∑ j ∈ Finset.Icc 1 (r ^ 2), (W j).card) ≤ 3 * r ^ 2 := by
    calc 2 * (∑ j ∈ Finset.Icc 1 (r ^ 2), (W j).card) ≤ 2*(((Finset.Icc 1 (r ^ 2 + r)).filter (· ∈ A)).card * r) :=
          Nat.mul_le_mul_left _ hlin_sum
      _ = (2*((Finset.Icc 1 (r ^ 2 + r)).filter (· ∈ A)).card)*r := by ring
      _ ≤ (3*r)*r := Nat.mul_le_mul_right r hcnt
      _ = 3 * r ^ 2 := by ring
  omega

lemma abel_sum (S b : ℕ → ℝ) (M N : ℕ) (hMN : M ≤ N) :
    ∑ k ∈ Finset.Ioc M N, (S k - S (k - 1)) * b k =
      S N * b N - S M * b M + ∑ k ∈ Finset.Ico M N, S k * (b k - b (k + 1)) := by
  induction N, hMN using Nat.le_induction with
  | base => simp
  | succ N hMN ih =>
    have hIoc : Finset.Ioc M (N + 1) = insert (N + 1) (Finset.Ioc M N) := by
      ext k
      simp only [Finset.mem_Ioc, Finset.mem_insert]
      omega
    have hIco : Finset.Ico M (N + 1) = insert N (Finset.Ico M N) := by
      ext k
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    rw [hIoc, Finset.sum_insert (by simp), hIco, Finset.sum_insert (by simp), ih]
    simp only [Nat.add_sub_cancel]
    ring

lemma harmonic_Icc_le_log {M N : ℕ} (hM : 2 ≤ M) (hMN : M ≤ N) :
    ∑ k ∈ Finset.Icc M N, (1 / (k : ℝ)) ≤ Real.log (N : ℝ) - Real.log ((M - 1 : ℕ) : ℝ) := by
  have htel : ∑ k ∈ Finset.Icc M N, (Real.log (k : ℝ) - Real.log ((k - 1 : ℕ) : ℝ)) =
      Real.log (N : ℝ) - Real.log ((M - 1 : ℕ) : ℝ) := by
    induction N, hMN using Nat.le_induction with
    | base => simp
    | succ N hMN ih =>
      have hIcc : Finset.Icc M (N + 1) = insert (N + 1) (Finset.Icc M N) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hIcc, Finset.sum_insert (by simp), ih]
      simp only [Nat.add_sub_cancel]
      ring
  have hstep : ∑ k ∈ Finset.Icc M N, (1 / (k : ℝ)) ≤
      ∑ k ∈ Finset.Icc M N, (Real.log (k : ℝ) - Real.log ((k - 1 : ℕ) : ℝ)) := by
    refine Finset.sum_le_sum fun k hk => ?_
    have hk2 : 2 ≤ k := by simp only [Finset.mem_Icc] at hk; omega
    have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
    have hk1pos : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
    have h1 := Real.log_le_sub_one_of_pos (div_pos hk1pos hkpos)
    rw [Real.log_div hk1pos.ne' hkpos.ne'] at h1
    have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    have h2 : ((k - 1 : ℕ) : ℝ) / (k : ℝ) - 1 = -(1 / (k : ℝ)) := by
      rw [hcast]
      field_simp
      ring
    linarith
  exact hstep.trans htel.le

lemma dyadic_sqrt_diff (k : ℕ) :
    7 / (24 * Real.sqrt ((2 ^ k : ℕ) : ℝ)) ≤
      1 / Real.sqrt ((2 ^ k : ℕ) : ℝ) - 1 / Real.sqrt ((2 ^ (k + 1) : ℕ) : ℝ) := by
  have ha : 0 < Real.sqrt ((2 ^ k : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hs2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2_ge : (24 / 17 : ℝ) ≤ Real.sqrt 2 := by
    have hsq : (24 / 17 : ℝ) ^ 2 ≤ Real.sqrt 2 ^ 2 := by
      rw [Real.sq_sqrt (by norm_num)]; norm_num
    nlinarith [Real.sqrt_nonneg 2]
  have hpow : Real.sqrt ((2 ^ (k + 1) : ℕ) : ℝ) =
      Real.sqrt ((2 ^ k : ℕ) : ℝ) * Real.sqrt 2 := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    push_cast [pow_succ]
    ring
  rw [hpow]
  have hsub :
      1 / Real.sqrt ((2 ^ k : ℕ) : ℝ) - 1 / (Real.sqrt ((2 ^ k : ℕ) : ℝ) * Real.sqrt 2) -
        7 / (24 * Real.sqrt ((2 ^ k : ℕ) : ℝ)) =
      (17 * Real.sqrt 2 - 24) / (24 * Real.sqrt ((2 ^ k : ℕ) : ℝ) * Real.sqrt 2) := by
    field_simp
    ring
  have hnn : 0 ≤ (17 * Real.sqrt 2 - 24) / (24 * Real.sqrt ((2 ^ k : ℕ) : ℝ) * Real.sqrt 2) :=
    div_nonneg (by linarith) (by positivity)
  linarith

end OMA.SidonQuantitative

open OMA.SidonQuantitative

theorem OMA.SidonQuantitative.block42 :
    ∀ (R : ℕ) (S : Finset ℕ), 1000000 ≤ R →
      (S : Set ℕ) ⊆ Set.Icc 1 (2 ^ (2 * R)) → IsSidon (S : Set ℕ) →
      ∃ k ∈ Set.Icc R (2 * R), (S.filter (· ≤ 2 ^ k)).card ^ 2 * k ≤ 42 * 2 ^ k := by
  intro R S hR hS hAsid
  by_contra hno
  let A : Set ℕ := (S : Set ℕ)
  let cnt (n : ℕ) := ((Finset.Icc 1 n).filter (· ∈ A)).card
  have hcnt_eq : ∀ n : ℕ, (S.filter (· ≤ n)).card = cnt n := by
    intro n
    unfold cnt
    refine Finset.card_bij (fun x _ => x) ?_ (fun _ _ _ _ h => h) ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_Icc, A, Finset.mem_coe] at hx ⊢
      exact ⟨⟨(hS (Finset.mem_coe.mpr hx.1)).1, hx.2⟩, hx.1⟩
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_Icc, A, Finset.mem_coe] at hx ⊢
      exact ⟨x, ⟨hx.2, hx.1.2⟩, rfl⟩
  have hgt_nat : ∀ k ∈ Set.Icc R (2 * R), 42 * 2 ^ k < cnt (2 ^ k) ^ 2 * k := by
    intro k hk
    by_contra hle
    have hle' : (S.filter (· ≤ 2 ^ k)).card ^ 2 * k ≤ 42 * 2 ^ k := by
      rw [hcnt_eq]
      exact Nat.le_of_not_lt hle
    exact hno ⟨k, hk, hle'⟩
  let r : ℕ := 2 ^ R
  have hr1 : 1 ≤ r := Nat.one_le_two_pow
  have hr2 : 2 ≤ r := by
    have : 2 ^ 1 ≤ 2 ^ R := Nat.pow_le_pow_right (by omega) (by omega)
    simpa [r] using this
  have h2r_le_r2 : 2 * r ≤ r ^ 2 := by nlinarith
  have h2r_eq : 2 * r = 2 ^ (R + 1) := by dsimp [r]; rw [pow_succ, mul_comm]
  have hr2_eq : r ^ 2 = 2 ^ (2 * R) := by dsimp [r]; rw [← pow_mul, mul_comm]
  let W : ℕ → Finset ℕ := fun j => (Finset.Ioc j (j + r)).filter (· ∈ A)
  have hsum_swap : (r : ℝ) * ∑ a ∈ (Finset.Ioc (2 * r) (r ^ 2)).filter (· ∈ A),
        (1 / Real.sqrt a) ≤
      ∑ j ∈ Finset.Icc r (r ^ 2), ((W j).card : ℝ) / Real.sqrt j := by
    have h1 : ∑ j ∈ Finset.Icc r (r ^ 2), ((W j).card : ℝ) / Real.sqrt j =
        ∑ j ∈ Finset.Icc r (r ^ 2), ∑ a ∈ W j, (1 / Real.sqrt j) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [div_eq_mul_inv]
    rw [h1]
    have h2 : ∑ j ∈ Finset.Icc r (r ^ 2), ∑ a ∈ W j, (1 / Real.sqrt j) ≥
        ∑ j ∈ Finset.Icc r (r ^ 2),
          ∑ a ∈ (Finset.Ioc (2 * r) (r ^ 2)).filter (· ∈ A),
            (if a ∈ W j then 1 / Real.sqrt j else 0) := by
      refine Finset.sum_le_sum fun j _ => ?_
      rw [← Finset.sum_filter]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
      intro a ha
      exact (Finset.mem_filter.mp ha).2
    rw [Finset.sum_comm] at h2
    refine le_trans ?_ h2
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a ha => ?_
    simp only [Finset.mem_filter, Finset.mem_Ioc] at ha
    have hsub : Finset.Ico (a - r) a ⊆ (Finset.Icc r (r ^ 2)).filter (fun j => a ∈ W j) := by
      intro j hj
      simp only [Finset.mem_Ico] at hj
      simp only [Finset.mem_filter, Finset.mem_Icc, W, Finset.mem_Ioc]
      exact ⟨⟨by omega, by omega⟩, ⟨⟨by omega, by omega⟩, ha.2⟩⟩
    calc (r : ℝ) * (1 / Real.sqrt a)
        = ∑ _j ∈ Finset.Ico (a - r) a, (1 / Real.sqrt a) := by
          rw [Finset.sum_const, Nat.card_Ico, show a - (a - r) = r by omega, nsmul_eq_mul]
      _ ≤ ∑ j ∈ Finset.Ico (a - r) a, (1 / Real.sqrt j) := by
          refine Finset.sum_le_sum fun j hj => ?_
          simp only [Finset.mem_Ico] at hj
          have hjpos : (0 : ℝ) < j := Nat.cast_pos.mpr (by omega)
          exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hjpos)
            (Real.sqrt_le_sqrt (by exact_mod_cast hj.2.le))
      _ ≤ ∑ j ∈ (Finset.Icc r (r ^ 2)).filter (fun j => a ∈ W j), (1 / Real.sqrt j) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = ∑ j ∈ Finset.Icc r (r ^ 2), if a ∈ W j then 1 / Real.sqrt j else 0 := by
          rw [Finset.sum_filter]
  have habel_step : (133 / 100 : ℝ) * Real.sqrt (R : ℝ) ≤
      ∑ a ∈ (Finset.Ioc (2 * r) (r ^ 2)).filter (· ∈ A), (1 / Real.sqrt a) := by
    rw [h2r_eq, hr2_eq]
    let B : ℕ → Finset ℕ := fun k => (Finset.Ioc (2 ^ (k - 1)) (2 ^ k)).filter (· ∈ A)
    have hpd : Set.PairwiseDisjoint (Finset.Ioc (R + 1) (2 * R) : Set ℕ) B := by
      intro k₁ hk₁ k₂ hk₂ hne
      change Disjoint (B k₁) (B k₂)
      rw [Finset.disjoint_left]
      intro x hx₁ hx₂
      simp only [B, Finset.mem_filter, Finset.mem_Ioc] at hx₁ hx₂
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hpow : 2 ^ k₁ ≤ 2 ^ (k₂ - 1) := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      · have hpow : 2 ^ k₂ ≤ 2 ^ (k₁ - 1) := Nat.pow_le_pow_right (by omega) (by omega)
        omega
    have hbiUnion :
        (Finset.Ioc (R + 1) (2 * R)).biUnion B =
          (Finset.Ioc (2 ^ (R + 1)) (2 ^ (2 * R))).filter (· ∈ A) := by
      ext x
      simp only [Finset.mem_biUnion, B, Finset.mem_filter, Finset.mem_Ioc]
      constructor
      · rintro ⟨k, ⟨hk1, hk2⟩, ⟨hx1, hx2⟩, hxA⟩
        have hlo : 2 ^ (R + 1) ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by omega) (by omega)
        have hhi : 2 ^ k ≤ 2 ^ (2 * R) := Nat.pow_le_pow_right (by omega) hk2
        exact ⟨⟨by omega, by omega⟩, hxA⟩
      · rintro ⟨⟨hx1, hx2⟩, hxA⟩
        have hex : ∃ k, x ≤ 2 ^ k := ⟨2 * R, hx2⟩
        let k := Nat.find hex
        have hk_spec : x ≤ 2 ^ k := Nat.find_spec hex
        have hk_le : k ≤ 2 * R := Nat.find_min' hex hx2
        have hk_gt : R + 1 < k := by
          by_contra hle
          have hpow : 2 ^ k ≤ 2 ^ (R + 1) := Nat.pow_le_pow_right (by omega) (by omega)
          omega
        have hk_prev : 2 ^ (k - 1) < x := by
          have hlt : k - 1 < k := by omega
          have hnot := Nat.find_min hex hlt
          omega
        exact ⟨k, ⟨hk_gt, hk_le⟩, ⟨hk_prev, hk_spec⟩, hxA⟩
    have hdyadic_ge :
        ∑ k ∈ Finset.Ioc (R + 1) (2 * R),
          ((cnt (2 ^ k) : ℝ) - (cnt (2 ^ (k - 1)) : ℝ)) *
            (1 / Real.sqrt ((2 ^ k : ℕ) : ℝ)) ≤
        ∑ a ∈ (Finset.Ioc (2 ^ (R + 1)) (2 ^ (2 * R))).filter (· ∈ A), (1 / Real.sqrt a) := by
      rw [← hbiUnion, Finset.sum_biUnion hpd]
      refine Finset.sum_le_sum fun k hk => ?_
      have hk1 : 1 ≤ k := by simp only [Finset.mem_Ioc] at hk; omega
      have hcard_B :
          ((B k).card : ℝ) = (cnt (2 ^ k) : ℝ) - (cnt (2 ^ (k - 1)) : ℝ) := by
        have hpow_le : 2 ^ (k - 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
        have hdisj : Disjoint ((Finset.Icc 1 (2 ^ (k - 1))).filter (· ∈ A)) (B k) := by
          rw [Finset.disjoint_left]
          intro x hx1 hx2
          simp only [B, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at hx1 hx2
          omega
        have hunion :
            (Finset.Icc 1 (2 ^ (k - 1))).filter (· ∈ A) ∪ B k =
              (Finset.Icc 1 (2 ^ k)).filter (· ∈ A) := by
          ext x
          simp only [B, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
          constructor
          · rintro (⟨⟨h1, h2⟩, hxA⟩ | ⟨⟨h1, h2⟩, hxA⟩)
            · exact ⟨⟨h1, h2.trans hpow_le⟩, hxA⟩
            · have : 1 ≤ 2 ^ (k - 1) := Nat.one_le_two_pow
              exact ⟨⟨by omega, h2⟩, hxA⟩
          · rintro ⟨⟨h1, h2⟩, hxA⟩
            by_cases hle : x ≤ 2 ^ (k - 1)
            · exact Or.inl ⟨⟨h1, hle⟩, hxA⟩
            · exact Or.inr ⟨⟨by omega, h2⟩, hxA⟩
        have hadd : cnt (2 ^ (k - 1)) + (B k).card = cnt (2 ^ k) := by
          dsimp only [cnt]
          rw [← Finset.card_union_of_disjoint hdisj, hunion]
        have haddR :
            (cnt (2 ^ (k - 1)) : ℝ) + ((B k).card : ℝ) =
              (cnt (2 ^ k) : ℝ) := by
          exact_mod_cast hadd
        linarith
      rw [← hcard_B]
      calc ((B k).card : ℝ) * (1 / Real.sqrt ((2 ^ k : ℕ) : ℝ))
          = ∑ _a ∈ B k, (1 / Real.sqrt ((2 ^ k : ℕ) : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ a ∈ B k, (1 / Real.sqrt (a : ℝ)) := by
            refine Finset.sum_le_sum fun a ha => ?_
            simp only [B, Finset.mem_filter, Finset.mem_Ioc] at ha
            have hapos : (0 : ℝ) < a := Nat.cast_pos.mpr (by
              have : 1 ≤ 2 ^ (k - 1) := Nat.one_le_two_pow
              omega)
            exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hapos)
              (Real.sqrt_le_sqrt (by exact_mod_cast ha.1.2))
    refine le_trans ?_ hdyadic_ge
    rw [abel_sum (fun k => (cnt (2 ^ k) : ℝ))
      (fun k => 1 / Real.sqrt ((2 ^ k : ℕ) : ℝ)) (R + 1) (2 * R) (by omega)]
    have htail :
        0 ≤ (cnt (2 ^ (2 * R)) : ℝ) * (1 / Real.sqrt ((2 ^ (2 * R) : ℕ) : ℝ)) := by
      positivity
    have hhead :
        (cnt (2 ^ (R + 1)) : ℝ) * (1 / Real.sqrt ((2 ^ (R + 1) : ℕ) : ℝ)) ≤ 2 := by
      have h1 : (cnt (2 ^ (R+1)) : ℝ) ≤ 2 * Real.sqrt ((2 ^ (R+1) : ℕ) : ℝ) := by
        convert sidonCount_le_two_sqrt (A := A) hAsid (Nat.one_le_two_pow : 1 ≤ 2 ^ (R+1)) using 1
        dsimp only [cnt]
        congr 2
        first | exact Subsingleton.elim _ _ | ext x; simp
      have hspos : 0 < Real.sqrt ((2 ^ (R + 1) : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
      calc (cnt (2 ^ (R + 1)) : ℝ) * (1 / Real.sqrt ((2 ^ (R + 1) : ℕ) : ℝ))
          ≤ (2 * Real.sqrt ((2 ^ (R + 1) : ℕ) : ℝ)) * (1 / Real.sqrt ((2 ^ (R + 1) : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = 2 := by field_simp
    have hRpos : (0 : ℝ) < (R : ℝ) := Nat.cast_pos.mpr (by omega)
    have hsR_pos : 0 < Real.sqrt (R : ℝ) := Real.sqrt_pos.mpr hRpos
    have hmain_sum :
        ((R - 1 : ℕ) : ℝ) * ((1603/1200 : ℝ) / Real.sqrt (R : ℝ)) ≤
          ∑ k ∈ Finset.Ico (R + 1) (2 * R),
            (cnt (2 ^ k) : ℝ) *
              (1 / Real.sqrt ((2 ^ k : ℕ) : ℝ) - 1 / Real.sqrt ((2 ^ (k + 1) : ℕ) : ℝ)) := by
      have hterm : ∀ k ∈ Finset.Ico (R + 1) (2 * R),
          (1603/1200 : ℝ) / Real.sqrt (R : ℝ) ≤
            (cnt (2 ^ k) : ℝ) *
              (1 / Real.sqrt ((2 ^ k : ℕ) : ℝ) - 1 / Real.sqrt ((2 ^ (k + 1) : ℕ) : ℝ)) := by
        intro k hk
        simp only [Finset.mem_Ico] at hk
        have hgt_k := hgt_nat k ⟨by omega, by omega⟩
        have hmul_le : cnt (2 ^ k) ^ 2 * k ≤ cnt (2 ^ k) ^ 2 * (2 * R) :=
          Nat.mul_le_mul_left _ (by omega)
        have hmul_eq : cnt (2 ^ k) ^ 2 * (2 * R) = 2 * (cnt (2 ^ k) ^ 2 * R) := by
          ring
        have h256 : 21 * 2 ^ k ≤ cnt (2 ^ k) ^ 2 * R := by omega
        have h256R :
            21 * ((2 ^ k : ℕ) : ℝ) ≤ (cnt (2 ^ k) : ℝ) ^ 2 * (R : ℝ) := by
          exact_mod_cast h256
        have hcnt_ge :
            (229/50 : ℝ) * Real.sqrt ((2 ^ k : ℕ) : ℝ) / Real.sqrt (R : ℝ) ≤
              (cnt (2 ^ k) : ℝ) := by
          have ha_nn : 0 ≤ (229/50 : ℝ) * Real.sqrt ((2 ^ k : ℕ) : ℝ) / Real.sqrt (R : ℝ) := by positivity
          have hsq :
              ((229/50 : ℝ) * Real.sqrt ((2 ^ k : ℕ) : ℝ) / Real.sqrt (R : ℝ)) ^ 2 ≤
                (cnt (2 ^ k) : ℝ) ^ 2 := by
            rw [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt hRpos.le,
              div_le_iff₀ hRpos]
            linarith
          nlinarith [ha_nn, Nat.cast_nonneg (α := ℝ) (cnt (2 ^ k))]
        have hdiff := dyadic_sqrt_diff k
        have hmul := mul_le_mul hcnt_ge hdiff (by positivity) (Nat.cast_nonneg _)
        have hsimpl :
            ((229/50 : ℝ) * Real.sqrt ((2 ^ k : ℕ) : ℝ) / Real.sqrt (R : ℝ)) *
              (7 / (24 * Real.sqrt ((2 ^ k : ℕ) : ℝ))) = (1603/1200 : ℝ) / Real.sqrt (R : ℝ) := by
          have hs2k : Real.sqrt ((2 ^ k : ℕ) : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
          field_simp
          ring
        linarith
      calc ((R - 1 : ℕ) : ℝ) * ((1603/1200 : ℝ) / Real.sqrt (R : ℝ))
          = ∑ _k ∈ Finset.Ico (R + 1) (2 * R), ((1603/1200 : ℝ) / Real.sqrt (R : ℝ)) := by
            rw [Finset.sum_const, Nat.card_Ico, show 2 * R - (R + 1) = R - 1 by omega, nsmul_eq_mul]
        _ ≤ ∑ k ∈ Finset.Ico (R + 1) (2 * R),
              (cnt (2 ^ k) : ℝ) *
                (1 / Real.sqrt ((2 ^ k : ℕ) : ℝ) - 1 / Real.sqrt ((2 ^ (k + 1) : ℕ) : ℝ)) :=
            Finset.sum_le_sum hterm
    have hR_arith :
        (133 / 100 : ℝ) * Real.sqrt (R : ℝ) ≤ ((R - 1 : ℕ) : ℝ) * ((1603/1200 : ℝ) / Real.sqrt (R : ℝ)) - 2 := by
      have hR1 : ((R - 1 : ℕ) : ℝ) = (R : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ R), Nat.cast_one]
      have hsR_sq := Real.sq_sqrt hRpos.le
      have hbig : (1000000 : ℝ) ≤ R := by exact_mod_cast hR
      have h64 : (1000 : ℝ) ≤ Real.sqrt (R : ℝ) := by
        nlinarith [Real.sqrt_nonneg (R : ℝ)]
      rw [hR1, le_sub_iff_add_le, ← mul_div_assoc, le_div_iff₀ hsR_pos]
      nlinarith [mul_nonneg (sub_nonneg.mpr h64) (sub_nonneg.mpr h64)]
    linarith
  have hL : (133 / 100 : ℝ) * (r : ℝ) * Real.sqrt (R : ℝ) ≤
      ∑ j ∈ Finset.Icc r (r ^ 2), ((W j).card : ℝ) / Real.sqrt j := by
    calc (133 / 100 : ℝ) * (r : ℝ) * Real.sqrt (R : ℝ)
        = (r : ℝ) * ((133 / 100 : ℝ) * Real.sqrt (R : ℝ)) := by ring
      _ ≤ (r : ℝ) * ∑ a ∈ (Finset.Ioc (2 * r) (r ^ 2)).filter (· ∈ A), (1 / Real.sqrt a) :=
          mul_le_mul_of_nonneg_left habel_step (Nat.cast_nonneg r)
      _ ≤ ∑ j ∈ Finset.Icc r (r ^ 2), ((W j).card : ℝ) / Real.sqrt j := hsum_swap
  have hCS : (∑ j ∈ Finset.Icc r (r ^ 2), ((W j).card : ℝ) / Real.sqrt j) ^ 2 ≤
      (∑ j ∈ Finset.Icc r (r ^ 2), ((W j).card : ℝ) ^ 2) *
        (∑ j ∈ Finset.Icc r (r ^ 2), (1 / (j : ℝ))) := by
    have hraw := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc r (r ^ 2))
      (fun j => ((W j).card : ℝ)) (fun j => 1 / Real.sqrt j)
    have hlhs : ∑ j ∈ Finset.Icc r (r ^ 2), ((W j).card : ℝ) * (1 / Real.sqrt j) =
        ∑ j ∈ Finset.Icc r (r ^ 2), ((W j).card : ℝ) / Real.sqrt j :=
      Finset.sum_congr rfl fun j _ => by ring
    have hrhs : ∑ j ∈ Finset.Icc r (r ^ 2), (1 / Real.sqrt j) ^ 2 =
        ∑ j ∈ Finset.Icc r (r ^ 2), (1 / (j : ℝ)) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg j)]
    rw [hlhs, hrhs] at hraw
    exact hraw
  have hsum_sq : ∑ j ∈ Finset.Icc r (r ^ 2), ((W j).card : ℝ) ^ 2 ≤ (5/2 : ℝ) * (r : ℝ) ^ 2 := by
    have hsub : Finset.Icc r (r ^ 2) ⊆ Finset.Icc 1 (r ^ 2) :=
      Finset.Icc_subset_Icc hr1 le_rfl
    have h1 : ∑ j ∈ Finset.Icc r (r ^ 2), ((W j).card : ℝ) ^ 2 ≤
        ∑ j ∈ Finset.Icc 1 (r ^ 2), ((W j).card : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
    have h2 : ∑ j ∈ Finset.Icc 1 (r ^ 2), ((W j).card : ℝ) ^ 2 ≤ (5/2 : ℝ) * (r : ℝ) ^ 2 := by
      have hr16 : 16 ≤ r := by
        change 2 ^ 4 ≤ 2 ^ R
        exact Nat.pow_le_pow_right (by omega) (by omega)
      have hh : (2:ℝ) * (∑ j ∈ Finset.Icc 1 (r^2), ((W j).card : ℝ)^2) ≤ 5 * (r:ℝ)^2 := by
        exact_mod_cast sidon_window_sq_sum_le hAsid hr16
      linarith
    exact h1.trans h2
  have hsum_harm : ∑ j ∈ Finset.Icc r (r ^ 2), (1 / (j : ℝ)) ≤ (7 / 10 : ℝ) * R := by
    have h1 := harmonic_Icc_le_log hr2 (Nat.le_self_pow (by norm_num : 2 ≠ 0) r)
    have hrpos : (0 : ℝ) < r := by exact_mod_cast hr1
    have hr2R : (2 : ℝ) ≤ r := by exact_mod_cast hr2
    have hp : ((r-1 : ℕ) : ℝ) = (r : ℝ)-1 := by push_cast [Nat.cast_sub hr1]; ring
    have hlog := Real.log_le_log (show (0 : ℝ) < r / 2 by positivity)
      (show (r : ℝ) / 2 ≤ ((r-1 : ℕ) : ℝ) by rw [hp]; linarith)
    rw [Real.log_div hrpos.ne' (by norm_num)] at hlog
    push_cast at h1
    rw [Real.log_pow, Nat.cast_ofNat] at h1
    have hlr : Real.log (r : ℝ) = (R : ℝ) * Real.log 2 := by
      have he : (r : ℝ) = (2 : ℝ) ^ R := by dsimp [r]; push_cast; rfl
      rw [he, Real.log_pow]
    have hsmall : Real.log 2 ≤ (139/200 : ℝ) := by linarith [Real.log_two_lt_d9]
    have hRcast : (1000000 : ℝ) ≤ R := by exact_mod_cast hR
    have hprod := mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg (α := ℝ) R)
    linarith
  have hLHS_sq : (17689 / 10000 : ℝ) * (r : ℝ) ^ 2 * (R : ℝ) ≤
      (∑ j ∈ Finset.Icc r (r ^ 2), ((W j).card : ℝ) / Real.sqrt j) ^ 2 := by
    have h1 : ((133 / 100 : ℝ) * (r : ℝ) * Real.sqrt (R : ℝ)) ^ 2 ≤
        (∑ j ∈ Finset.Icc r (r ^ 2), ((W j).card : ℝ) / Real.sqrt j) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hL 2
    have h2 : ((133 / 100 : ℝ) * (r : ℝ) * Real.sqrt (R : ℝ)) ^ 2 =
        (17689 / 10000 : ℝ) * (r : ℝ) ^ 2 * (R : ℝ) := by
      have hsR : Real.sqrt (R : ℝ) ^ 2 = (R : ℝ) := Real.sq_sqrt (Nat.cast_nonneg R)
      calc ((133 / 100 : ℝ) * (r : ℝ) * Real.sqrt (R : ℝ)) ^ 2
          = (17689 / 10000 : ℝ) * (r : ℝ) ^ 2 * Real.sqrt (R : ℝ) ^ 2 := by ring
        _ = (17689 / 10000 : ℝ) * (r : ℝ) ^ 2 * (R : ℝ) := by rw [hsR]
    linarith
  have hRHS_le : (∑ j ∈ Finset.Icc r (r ^ 2), ((W j).card : ℝ) ^ 2) *
        (∑ j ∈ Finset.Icc r (r ^ 2), (1 / (j : ℝ))) ≤
        (7/4 : ℝ) * (r : ℝ) ^ 2 * R := by
    calc _ ≤ ((5/2:ℝ) * (r : ℝ) ^ 2) * ((7/10 : ℝ) * R) :=
          mul_le_mul hsum_sq hsum_harm
            (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
      _ = _ := by ring
  have hpos : 0 < (r : ℝ) ^ 2 * R := by
    have hrpos : (0 : ℝ) < r := by exact_mod_cast hr1
    have hRpos : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
    positivity
  have hc := hLHS_sq.trans (hCS.trans hRHS_le)
  nlinarith only [hpos, hc]


/-- The finite window is uniform over all Sidon sets and every threshold through twelve. -/
theorem SidonDoubling.small_attainable (b : ℕ) (hb : b ≤ 12) :
    ∀ J : ℕ, ∃ K ≥ J, ∀ S : Finset ℕ,
      (S : Set ℕ) ⊆ Set.Icc 1 (2 ^ K) → IsSidon (S : Set ℕ) →
        ∃ j ∈ Finset.Icc J K, b * (S.filter (· ≤ 2 ^ j)).card ^ 2 * j ≤ 512 * 2 ^ j := by
  intro J
  let R := max 1000000 J
  have hjr : J ≤ R := le_max_right _ _
  refine ⟨2*R, by omega, fun S hs hsid => ?_⟩
  obtain ⟨j, hj, hbound⟩ := OMA.SidonQuantitative.block42 R S (le_max_left _ _) hs hsid
  refine ⟨j, Finset.mem_Icc.mpr ⟨hjr.trans hj.1,hj.2⟩, ?_⟩
  calc
    b * (S.filter (· ≤ 2 ^ j)).card ^ 2 * j =
        b * ((S.filter (· ≤ 2 ^ j)).card ^ 2 * j) := by ring
    _ ≤ 12 * (42 * 2 ^ j) := Nat.mul_le_mul hb hbound
    _ ≤ _ := by nlinarith

end

section

/- Extracting a positive infinite Sidon set from arbitrarily long dyadic obstructions. -/

namespace SidonDoubling

open Set Filter

lemma infinite_of_persistent_bad (A : Set ℕ) (d J : ℕ)
    (h : ∀ j ≥ J, 512 * 2 ^ j < d * (A ∩ Icc 1 (2 ^ j)).ncard ^ 2 * j) :
    A.Infinite := by
  intro hfin
  let r := max J (d * A.ncard ^ 2)
  have hJ : J ≤ r := le_max_left _ _
  have hr : d * A.ncard ^ 2 ≤ r := le_max_right _ _
  have hp : r ≤ 2^r := r.lt_two_pow_self.le
  have hc : (A ∩ Icc 1 (2^(r+r))).ncard ≤ A.ncard := ncard_le_ncard inter_subset_left hfin
  have hb := h (r+r) (by omega)
  apply hb.not_ge
  calc
    _ ≤ r * (r+r) := Nat.mul_le_mul_right _ ((Nat.mul_le_mul_left d (Nat.pow_le_pow_left hc 2)).trans hr)
    _ = 2 * (r*r) := by ring
    _ ≤ 2 * (2^r * 2^r) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul hp hp)
    _ ≤ 512 * 2^(r+r) := by rw [pow_add]; omega

/-- The finite-prefix ultrafilter argument also used by NicholasWierenga in
    the sibling reduction for part (ii), with the starting scale held fixed. -/
lemma sidon_of_persistent_witnesses (d J : ℕ)
    (h : ∀ K ≥ J, ∃ S : Finset ℕ, (S : Set ℕ) ⊆ Icc 1 (2 ^ K) ∧ IsSidon (S : Set ℕ) ∧
      ∀ j ∈ Finset.Icc J K, 512 * 2^j < d * (S.filter (· ≤ 2^j)).card ^ 2 * j) :
    ∃ A : Set ℕ, A ⊆ Ici 1 ∧ A.Infinite ∧ IsSidon A ∧
      ∀ j ≥ J, 512 * 2 ^ j < d * (A ∩ Icc 1 (2 ^ j)).ncard ^ 2 * j := by
  classical
  choose W hW using fun n : ℕ => h (J+n) (by omega)
  let F : Ultrafilter ℕ := hyperfilter ℕ
  let A : Set ℕ := {a | ∀ᶠ n in (F : Filter ℕ), a ∈ W n}
  have hp (a : ℕ) : ∀ᶠ n in (F : Filter ℕ), a ∈ W n ↔ a ∈ A := by
    by_cases ha : a ∈ A
    · exact (show ∀ᶠ n in (F : Filter ℕ), a ∈ W n from ha).mono fun _ hn => iff_of_true hn ha
    · have hn : ∀ᶠ n in (F : Filter ℕ), a ∉ W n := Ultrafilter.eventually_not.mpr ha
      exact hn.mono fun _ hh => iff_of_false hh ha
  have agrees (bound : ℕ) : ∃ n ≥ bound, ∀ a ≤ bound, a ∈ W n ↔ a ∈ A := by
    have hfinite := (eventually_all_finset (l := (F : Filter ℕ)) (Finset.range (bound+1))).2
      (fun a _ => hp a)
    have hlarge : ∀ᶠ n in (F : Filter ℕ), bound ≤ n := Nat.hyperfilter_le_atTop (eventually_ge_atTop bound)
    obtain ⟨n, hn, he⟩ := (hlarge.and hfinite).exists
    exact ⟨n,hn,fun a ha => he a (Finset.mem_range.mpr (by omega))⟩
  have hpos : A ⊆ Ici 1 := by
    intro a ha
    obtain ⟨n, _, he⟩ := agrees a
    exact ((hW n).1 ((he a le_rfl).mpr ha)).1
  have hsid : IsSidon A := by
    intro a ha b hb c hc e he hs
    obtain ⟨n, _, hw⟩ := agrees (a+b+c+e)
    exact (hW n).2.1 a ((hw _ (by omega)).mpr ha) b ((hw _ (by omega)).mpr hb)
      c ((hw _ (by omega)).mpr hc) e ((hw _ (by omega)).mpr he) hs
  have hbad (j : ℕ) (hj : j ≥ J) : 512 * 2^j < d * (A ∩ Icc 1 (2^j)).ncard ^ 2 * j := by
    obtain ⟨n,hn,hw⟩ := agrees (2^j)
    have heq : (((W n).filter (· ≤ 2^j) : Finset ℕ) : Set ℕ) = A ∩ Icc 1 (2^j) := by
      ext a
      simp only [Finset.mem_coe, Finset.mem_filter, mem_inter_iff, mem_Icc]
      exact ⟨fun h => ⟨(hw _ h.2).mp h.1, ((hW n).1 h.1).1, h.2⟩,
        fun h => ⟨(hw _ h.2.2).mpr h.1, h.2.2⟩⟩
    rw [← heq, ncard_coe_finset]
    have hjn : j ≤ n := j.lt_two_pow_self.le.trans hn
    exact (hW n).2.2 j (Finset.mem_Icc.mpr ⟨hj, by omega⟩)
  exact ⟨A, hpos, infinite_of_persistent_bad A d J hbad, hsid, hbad⟩

lemma sidon_of_not_attainable (d : ℕ)
    (h : ¬ ∀ J : ℕ, ∃ K ≥ J, ∀ S : Finset ℕ,
      (S : Set ℕ) ⊆ Icc 1 (2^K) → IsSidon (S : Set ℕ) →
        ∃ j ∈ Finset.Icc J K, d * (S.filter (· ≤ 2^j)).card ^ 2 * j ≤ 512 * 2^j) :
    ∃ (J : ℕ) (A : Set ℕ), A ⊆ Ici 1 ∧ A.Infinite ∧ IsSidon A ∧
      ∀ j ≥ J, 512 * 2 ^ j < d * (A ∩ Icc 1 (2 ^ j)).ncard ^ 2 * j := by
  push Not at h
  obtain ⟨J,hJ⟩ := h
  exact ⟨J, sidon_of_persistent_witnesses d J hJ⟩

end SidonDoubling

end

section

/- Prefix counts and dyadic annular growth. -/

namespace SidonDoubling

open Set

/-- A uniform finite threshold gives cofinally many good scales for each fixed Sidon set. -/
theorem cofinal_good {a : ℕ} (h : 
      ∀ J : ℕ, ∃ K ≥ J, ∀ S : Finset ℕ,
      (S : Set ℕ) ⊆ Set.Icc 1 (2^K) → IsSidon (S : Set ℕ) →
        ∃ j ∈ Finset.Icc J K, a * (S.filter (· ≤ 2^j)).card^2*j ≤ 512*2^j) (A : Set ℕ) (hsid : IsSidon A) (J : ℕ) :
    ∃ j ≥ J, a*(A ∩ Icc 1 (2^j)).ncard^2*j ≤ 512*2^j := by
  classical
  obtain ⟨K, _, hK⟩ := h J
  have hfin : (A ∩ Icc 1 (2^K)).Finite := (finite_Icc _ _).subset inter_subset_right
  let S := hfin.toFinset
  have hcoe : (S : Set ℕ) = A ∩ Icc 1 (2^K) := hfin.coe_toFinset
  have hsub : (S : Set ℕ) ⊆ Icc 1 (2^K) := hcoe ▸ inter_subset_right
  have hs : IsSidon (S : Set ℕ) := by
    rw [hcoe]
    intro a ha b hb c hc d hd he
    exact hsid a ha.1 b hb.1 c hc.1 d hd.1 he
  obtain ⟨j, hj, hcount⟩ := hK S hsub hs
  obtain ⟨hj₁,hj₂⟩ := Finset.mem_Icc.mp hj
  have hp : (2:ℕ)^j ≤ 2^K := Nat.pow_le_pow_right (by decide) hj₂
  rw [OMA.R_Erdos1191_erdos_1191_parts_i_R3.prefix_filter_card S (fun x hx => (hsub hx).1),
    hcoe, inter_assoc, inter_eq_right.mpr (Icc_subset_Icc_right hp)] at hcount
  exact ⟨j,hj₁,hcount⟩

theorem prefix_add_shell (A : Set ℕ) (j : ℕ) :
    (A ∩ Icc 1 (2^j)).ncard + (A ∩ Ioc (2^j) (2^(j+4))).ncard = (A ∩ Icc 1 (2^(j+4))).ncard := by
  have hs : 2^j ≤ (2:ℕ)^(j+4) := Nat.pow_le_pow_right (by decide) (by omega)
  have hd : Disjoint (A ∩ Icc 1 (2^j)) (A ∩ Ioc (2^j) (2^(j+4))) := by
    rw [Set.disjoint_left]
    intro x hx hy
    exact (not_lt_of_ge hx.2.2) hy.2.1
  have hu : (A ∩ Icc 1 (2^j)) ∪ (A ∩ Ioc (2^j) (2^(j+4))) = A ∩ Icc 1 (2^(j+4)) := by
    ext x
    simp only [mem_union,mem_inter_iff,mem_Icc,mem_Ioc]
    have : 0 < (2:ℕ)^j := by positivity
    grind
  exact ((ncard_union_eq hd ((finite_Icc _ _).subset inter_subset_right)
    ((finite_Ioc _ _).subset inter_subset_right)).symm.trans (congrArg Set.ncard hu))

/-- When the old threshold holds at j but its double fails four scales later,
    the next annulus has more points than the entire prefix. -/
theorem dense_shell {A : Set ℕ} {a j : ℕ} (hj : 4 ≤ j)
    (ho : a*(A ∩ Icc 1 (2^j)).ncard^2*j ≤ 512*2^j) (hn : ¬ (2*a)*(A ∩ Icc 1 (2^(j+4))).ncard^2*(j+4) ≤ 512*2^(j+4)) :
    (A ∩ Icc 1 (2^j)).ncard < (A ∩ Ioc (2^j) (2^(j+4))).ncard ∧
      1024 * 2^j < a * ((A ∩ Ioc (2^j) (2^(j+4))).ncard)^2 * (j+4) := by
  let c (j : ℕ) := (A ∩ Icc 1 (2^j)).ncard
  let s := (A ∩ Ioc (2^j) (2^(j+4))).ncard
  change c j < s ∧ 1024*2^j < a*s^2*(j+4)
  change a * (c j)^2 * j ≤ 512*2^j at ho
  change ¬ (2*a)*(c (j+4))^2*(j+4) ≤ 512*2^(j+4) at hn
  rw [not_le] at hn
  have hsum : c j + s = c (j+4) := prefix_add_shell A j
  have hd : c j < s := by
    by_contra! hsmall
    have hc : c (j+4) ≤ 2*c j := by omega
    have hfour : j+4 ≤ 2*j := by omega
    have hupper : (2*a)*(c (j+4))^2*(j+4) ≤ 512*2^(j+4) := calc
      _ ≤ (2*a)*(2*c j)^2*(2*j) := by gcongr
      _ = 16*(a*(c j)^2*j) := by ring
      _ ≤ 16*(512*2^j) := by gcongr
      _ = _ := by rw [pow_add]; ring
    exact (not_lt_of_ge hupper) hn
  refine ⟨hd,?_⟩
  have hc : c (j+4) ≤ 2 * s := by omega
  have hh : 8 * (1024*2^j) < 8 * (a*(s)^2*(j+4)) := calc
    _ = 512*2^(j+4) := by rw [pow_add]; ring
    _ < (2*a)*(c (j+4))^2*(j+4) := hn
    _ ≤ (2*a)*(2*s)^2*(j+4) := by gcongr
    _ = _ := by ring
  omega

end SidonDoubling

end

section

/- A cofinally dense family of dyadic scales is cofinally dense in one fixed residue modulo four. -/

namespace SidonDoubling

open scoped Classical

lemma scale_dichotomy (P : Nat → Prop) :
    (∃ q < 4, ∃ m : Nat, 0 < m ∧ ∀ N, ∃ R ≥ N,
      R ≤ m * (((Finset.Icc R (2*R)).filter P).filter (fun j => j % 4 = q)).card) ∨
    (∀ m : Nat, 0 < m → ∃ N : Nat, ∀ R ≥ N, m * ((Finset.Icc R (2*R)).filter P).card < R) := by
  classical
  let scales (R : Nat) := (Finset.Icc R (2*R)).filter P
  let residueScales (R q : Nat) := (scales R).filter (fun j => j % 4 = q)
  change (∃ q < 4, ∃ m : Nat, 0 < m ∧ ∀ N, ∃ R ≥ N, R ≤ m * (residueScales R q).card) ∨
    (∀ m : Nat, 0 < m → ∃ N : Nat, ∀ R ≥ N, m * (scales R).card < R)
  by_cases h : ∃ q < 4, ∃ m : Nat, 0 < m ∧ ∀ N, ∃ R ≥ N, R ≤ m * (residueScales R q).card
  · exact Or.inl h
  right
  intro m hm
  push Not at h
  have sparse (q : Fin 4) : ∃ N, ∀ R ≥ N, (4*m) * (residueScales R q.val).card < R :=
    h q.val q.isLt (4*m) (by omega)
  choose cutoff hc using sparse
  refine ⟨Finset.univ.sup cutoff, fun R hR => ?_⟩
  have small (q : Nat) (hq : q ∈ Finset.range 4) : (4*m) * (residueScales R q).card < R := by
    let i : Fin 4 := ⟨q, Finset.mem_range.mp hq⟩
    exact hc i R ((Finset.le_sup (f := cutoff) (Finset.mem_univ i)).trans hR)
  have partition : (scales R).card = ∑ q ∈ Finset.range 4, (residueScales R q).card :=
    Finset.card_eq_sum_card_fiberwise (f := fun j : Nat => j % 4)
      (fun j _ => Finset.mem_range.mpr (Nat.mod_lt j (by decide)))
  have hsum : 4 * (m * (scales R).card) < 4 * R := calc
    _ = ∑ q ∈ Finset.range 4, (4*m) * (residueScales R q).card := by
      rw [← Finset.mul_sum, ← partition, Nat.mul_assoc]
    _ < ∑ _q ∈ Finset.range 4, R := Finset.sum_lt_sum_of_nonempty (by decide) small
    _ = 4 * R := by simp
  omega

end SidonDoubling

end

section

/- The unused short differences bound the pair counts of later sliding windows. -/

namespace SidonDoubling

open Finset
open scoped Classical

/-- A difference whose smaller endpoint is already at most X removes exactly r-d
    available offsets from the triangular capacity for all later width-r windows. -/
lemma sidon_window_reserve {A : Set ℕ} (hA : IsSidon A) (r X : ℕ) (J D : Finset ℕ)
    (hJ : ∀ j ∈ J, X ≤ j)
    (hD : ∀ d ∈ D, ∃ a ∈ A, ∃ b ∈ A, a ≤ X ∧ a < b ∧ b - a = d) :
    (∑ j ∈ J, (((Ioc j (j+r)).filter (· ∈ A)).card.choose 2)) +
      ∑ d ∈ D, (r-d) ≤ r.choose 2 := by
  classical
  have unique {a b c e : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (he : e ∈ A)
      (hab : a < b) (hce : c < e) (hd : b-a = e-c) : a = c ∧ b = e := by
    have hs : b+c = e+a := by omega
    rcases hA b hb e he c hc a ha hs with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · exact ⟨h₂.symm,h₁⟩
    · omega
  let W (j : ℕ) := (Ioc j (j+r)).filter (· ∈ A)
  let pairs (S : Finset ℕ) := (S ×ˢ S).filter (fun p => p.1 < p.2)
  let tri := pairs (Icc 1 r)
  let used (p : ℕ × ℕ) := p.2 - p.1 ∈ D
  let late := J.sigma (fun j => pairs (W j))
  let offset (x : Σ _ : ℕ, ℕ × ℕ) := (x.2.1 - x.1, x.2.2 - x.1)
  have hlate : late.card ≤ (tri.filter (fun p => ¬used p)).card := by
    apply card_le_card_of_injOn offset
    · rintro ⟨j,a,b⟩ hx
      simp only [late, mem_coe, mem_sigma, pairs, W, mem_filter, mem_product, mem_Ioc] at hx
      rcases hx with ⟨hj, ⟨⟨⟨hja, haU⟩,ha⟩,⟨⟨hjb,hbU⟩,hb⟩⟩,hab⟩
      simp only [offset, mem_coe, mem_filter, tri, pairs, mem_product, mem_Icc, used]
      refine ⟨⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, by omega⟩, ?_⟩
      intro hd
      obtain ⟨c,hc,e,he,hcX,hce,heq⟩ := hD _ hd
      have hdiff : b-a = e-c := by omega
      have heq' := (unique ha hb hc he hab hce hdiff).1
      have := hJ j hj
      omega
    · rintro ⟨j,a,b⟩ hx ⟨k,c,e⟩ hy heq
      simp only [late, mem_coe, mem_sigma, pairs, W, mem_filter, mem_product, mem_Ioc] at hx hy
      rcases hx with ⟨_, ⟨⟨⟨hja, _⟩,ha⟩,⟨⟨hjb,_⟩,hb⟩⟩,hab⟩
      rcases hy with ⟨_, ⟨⟨⟨hkc, _⟩,hc⟩,⟨⟨hke,_⟩,he⟩⟩,hce⟩
      change (a-j,b-j) = (c-k,e-k) at heq
      obtain ⟨hp,hq⟩ := Prod.mk.inj heq
      obtain ⟨rfl,rfl⟩ := unique ha hb hc he hab hce (by omega)
      have : j=k := by omega
      subst k
      rfl
  let early := D.sigma (fun d => Icc 1 (r-d))
  let label (x : Σ _ : ℕ, ℕ) := (x.2, x.2 + x.1)
  have hearly : early.card ≤ (tri.filter used).card := by
    apply card_le_card_of_injOn label
    · rintro ⟨d,s⟩ hx
      simp only [early, mem_coe, mem_sigma, mem_Icc] at hx
      obtain ⟨hd,hs,hsr⟩ := hx
      obtain ⟨a,_,b,_,_,hab,heq⟩ := hD d hd
      simp only [label, mem_coe, mem_filter, tri, pairs, mem_product, mem_Icc, used]
      exact ⟨⟨⟨⟨hs,by omega⟩,⟨by omega,by omega⟩⟩,by omega⟩, by simpa using hd⟩
    · rintro ⟨d,s⟩ _ ⟨e,t⟩ _ heq
      change (s,s+d) = (t,t+e) at heq
      obtain ⟨rfl,h⟩ := Prod.mk.inj heq
      have : d=e := by omega
      subst e
      rfl
  have hsum := card_filter_add_card_filter_not (s := tri) used
  have htri : tri.card = r.choose 2 := by simp [tri,pairs,card_product_filter_lt]
  have hE : early.card = ∑ d ∈ D, (r-d) := by simp [early,card_sigma]
  have hL : late.card = ∑ j ∈ J, (W j).card.choose 2 := by
    simp [late,pairs,card_sigma,card_product_filter_lt]
  change (∑ j ∈ J, (W j).card.choose 2) + ∑ d ∈ D, (r-d) ≤ r.choose 2
  omega



/-- Enough triangular difference capacity must be available to support all
    translates of a finite population of size E.card in L consecutive integers. -/
lemma annulus_population_reserve (E D : Finset ℕ) (u L r : ℕ)
    (hr : 0 < r) (hI : ∀ a ∈ E, u ≤ a ∧ a < u+L)
    (hS : IsSidon (E : Set ℕ))
    (hD : ∀ a ∈ E, ∀ b ∈ E, a < b → b-a < r → b-a ∈ D) :
    (r * E.card)^2 ≤ (L+r-1) * (r * E.card + 2 * ∑ d ∈ D, (r-d)) := by
  let Z := Ico u (u+(L+r-1))
  let W (z : ℕ) := E.filter (fun a => a ≤ z ∧ z < a+r)
  have hcount : (∑ z ∈ Z, (W z).card) = r * E.card := by
    have cell (a : ℕ) (ha : a ∈ E) : Z.filter (fun z => a ≤ z ∧ z < a+r) = Ico a (a+r) := by
      ext z
      have := hI a ha
      simp only [Z, mem_filter, mem_Ico]
      omega
    simp_rw [W, card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    calc
      _ = ∑ _a ∈ E, r := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [← Finset.sum_filter, ← card_eq_sum_ones, cell a ha]
        simp
      _ = _ := by simp [Nat.mul_comm]
  let P (z : ℕ) := (W z ×ˢ W z).filter (fun p => p.1 < p.2)
  let T := Z.sigma P
  let U := D.sigma (fun d => range (r-d))
  let label (x : Σ _ : ℕ, ℕ × ℕ) : Σ _ : ℕ, ℕ := ⟨x.2.2-x.2.1, x.1-x.2.2⟩
  have hpair : T.card ≤ U.card := by
    apply card_le_card_of_injOn label
    · rintro ⟨z,a,b⟩ hx
      simp only [T, mem_coe, mem_sigma, P, W, mem_filter, mem_product] at hx
      obtain ⟨_, ⟨⟨ha,haz,hza⟩,⟨hb,hbz,_⟩⟩,hab⟩ := hx
      exact mem_sigma.mpr ⟨hD a ha b hb hab (by omega), mem_range.mpr (by change z-b < r-(b-a); omega)⟩
    · rintro ⟨z,a,b⟩ hx ⟨w,c,e⟩ hy heq
      simp only [T, mem_coe, mem_sigma, P, W, mem_filter, mem_product] at hx hy
      obtain ⟨_, ⟨⟨ha,haz,_⟩,⟨hb,hbz,_⟩⟩,hab⟩ := hx
      obtain ⟨_, ⟨⟨hc,hcw,_⟩,⟨he,hew,_⟩⟩,hce⟩ := hy
      have hd : b-a = e-c := congrArg Sigma.fst heq
      have hs : z-b = w-e := congrArg (fun x : Σ _ : ℕ, ℕ => x.2) heq
      have hadd : b+c = e+a := by omega
      rcases hS b hb e he c hc a ha hadd with ⟨rfl,rfl⟩ | ⟨h,_⟩
      · have : z=w := by omega
        subst w
        rfl
      · omega
  have hc : (∑ z ∈ Z, (W z).card.choose 2) ≤ ∑ d ∈ D, (r-d) := by
    simpa [T,U,P,card_sigma,card_product_filter_lt] using hpair
  have nsq (n : ℕ) : n^2 = n + 2 * n.choose 2 := by
    cases n with
    | zero => decide
    | succ k =>
      have h := Nat.choose_succ_right_eq (k+1) 1
      simp only [Nat.choose_one_right, Nat.add_one_sub_one] at h
      nlinarith
  have hsq : (∑ z ∈ Z, (W z).card ^ 2) ≤ r * E.card + 2 * ∑ d ∈ D, (r-d) := by
    simp_rw [nsq]
    rw [sum_add_distrib, ← mul_sum, hcount]
    omega
  have hcs := sum_mul_sq_le_sq_mul_sq Z (fun _ => (1 : ℕ)) (fun z => (W z).card)
  simp only [one_mul, one_pow, sum_const, smul_eq_mul, mul_one, hcount] at hcs
  have hZ : Z.card = L+r-1 := by simp [Z]
  rw [hZ] at hcs
  exact hcs.trans (Nat.mul_le_mul_left _ hsq)


/-- A dense earlier annulus directly reduces the subsequent sliding-window pair count. -/
lemma annulus_late_tradeoff {A : Set ℕ} (hA : IsSidon A) (E J : Finset ℕ)
    (u L r : ℕ) (hr : 0 < r) (hE : (E : Set ℕ) ⊆ A)
    (hI : ∀ a ∈ E, u ≤ a ∧ a < u+L) (hJ : ∀ j ∈ J, u+L ≤ j) :
    (r * E.card)^2 +
      (L+r-1) * (2 * ∑ j ∈ J, (((Ioc j (j+r)).filter (· ∈ A)).card.choose 2)) ≤
      (L+r-1) * (r * E.card + 2 * r.choose 2) := by
  classical
  let D := (Ico 1 (r+1)).filter
    (fun d => ∃ a ∈ E, ∃ b ∈ E, a < b ∧ b-a = d)
  have upper := annulus_population_reserve E D u L r hr hI (Set.IsSidon.subset hA hE) (by
    intro a ha b hb hab hdr
    exact mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, by omega⟩, a, ha, b, hb, hab, rfl⟩)
  have budget := sidon_window_reserve hA r (u+L) J D hJ (by
    intro d hd
    obtain ⟨a,ha,b,hb,hab,hdiff⟩ := (mem_filter.mp hd).2
    exact ⟨a, hE ha, b, hE hb, (hI a ha).2.le, hab, hdiff⟩)
  let late := ∑ j ∈ J, (((Ioc j (j+r)).filter (· ∈ A)).card.choose 2)
  change (r*E.card)^2 + (L+r-1)*(2*late) ≤ _
  change late + ∑ d ∈ D, (r-d) ≤ r.choose 2 at budget
  calc
    _ ≤ (L+r-1)*(r*E.card+2*∑ d ∈ D, (r-d)) + (L+r-1)*(2*late) :=
      Nat.add_le_add_right upper _
    _ = (L+r-1)*(r*E.card+2*(late+∑ d ∈ D, (r-d))) := by ring
    _ ≤ _ := by gcongr

end SidonDoubling

end

namespace OMA.R_Erdos1191_erdos_1191_parts_i_R3_H2_R1

open SidonDoubling
open scoped Classical

/-- Positive upper density of good scales in one residue class. -/
def H1 : Prop := ∀ a : ℕ, 7 ≤ a → ∀ (A : Set ℕ), A ⊆ Set.Ici 1 → A.Infinite → ∀ J : ℕ,
  let c (j : ℕ) := (A ∩ Set.Icc 1 (2^j)).ncard
  let s (j : ℕ) := (A ∩ Set.Ioc (2^j) (2^(j+4))).ncard
  let good (j : ℕ) := a*(c j)^2*j ≤ 512*2^j
  let selected (R : ℕ) := @Finset.filter ℕ good (fun j => Classical.propDecidable (good j)) (Finset.Icc R (2*R))
  (∀ j ≥ J, 512*2^j < (2*a)*(c j)^2*j) →
  (∀ j ≥ J, good j → c j < s j ∧ 1024*2^j < a*(s j)^2*(j+4)) →
  (∀ (E : Finset ℕ) (u L r : ℕ) (W : Finset ℕ), 0 < r →
    (↑E : Set ℕ) ⊆ A → (∀ x ∈ E, u ≤ x ∧ x < u+L) → (∀ w ∈ W, u+L ≤ w) →
    (r*E.card)^2 + (L+r-1)*(2*∑ w ∈ W, (((Finset.Ioc w (w+r)).filter (· ∈ A)).card.choose 2)) ≤
      (L+r-1)*(r*E.card+2*r.choose 2)) →
  (∃ q < 4, ∃ m : ℕ, 0 < m ∧ ∀ N, ∃ R ≥ N,
    R ≤ m * ((selected R).filter (fun j => j%4=q)).card) → ¬ IsSidon A

/-- Good scales are cofinal but have density zero on the exponent intervals. -/
def H2 : Prop := ∀ a : ℕ, 7 ≤ a → ∀ (A : Set ℕ), A ⊆ Set.Ici 1 → A.Infinite → ∀ J : ℕ,
  let c (j : ℕ) := (A ∩ Set.Icc 1 (2^j)).ncard
  let s (j : ℕ) := (A ∩ Set.Ioc (2^j) (2^(j+4))).ncard
  let good (j : ℕ) := a*(c j)^2*j ≤ 512*2^j
  let selected (R : ℕ) := @Finset.filter ℕ good (fun j => Classical.propDecidable (good j)) (Finset.Icc R (2*R))
  (∀ j ≥ J, 512*2^j < (2*a)*(c j)^2*j) →
  (∀ j ≥ J, good j → c j < s j ∧ 1024*2^j < a*(s j)^2*(j+4)) →
  (∀ (E : Finset ℕ) (u L r : ℕ) (W : Finset ℕ), 0 < r →
    (↑E : Set ℕ) ⊆ A → (∀ x ∈ E, u ≤ x ∧ x < u+L) → (∀ w ∈ W, u+L ≤ w) →
    (r*E.card)^2 + (L+r-1)*(2*∑ w ∈ W, (((Finset.Ioc w (w+r)).filter (· ∈ A)).card.choose 2)) ≤
      (L+r-1)*(r*E.card+2*r.choose 2)) →
  (∀ N, ∃ j ≥ N, good j) →
  (∀ m : ℕ, 0 < m → ∃ N, ∀ R ≥ N, m * (selected R).card < R) →
  ¬ IsSidon A

theorem main : H1 → H2 → OMA.R_Erdos1191_erdos_1191_parts_i_R3.H2 := by
  classical
  intro h₁ h₂ a old
  by_cases ha : 2*a ≤ 12
  · exact small_attainable (2*a) ha
  by_contra hfail
  obtain ⟨B,A,hpos,hinf,hsid,hbad⟩ := sidon_of_not_attainable (2*a) hfail
  let J := max 4 B
  let c (j : ℕ) := (A ∩ Set.Icc 1 (2^j)).ncard
  let s (j : ℕ) := (A ∩ Set.Ioc (2^j) (2^(j+4))).ncard
  let good (j : ℕ) := a*(c j)^2*j ≤ 512*2^j
  have bad (j : ℕ) (hj : J ≤ j) : 512*2^j < (2*a)*(c j)^2*j :=
    hbad j ((le_max_right 4 B).trans hj)
  have burst (j : ℕ) (hj : J ≤ j) (hg : good j) :
      c j < s j ∧ 1024*2^j < a*(s j)^2*(j+4) :=
    dense_shell ((le_max_left 4 B).trans hj) hg
      (not_le_of_gt (bad (j+4) (by omega)))
  rcases scale_dichotomy good with dense | sparse
  · exact h₁ a (by omega) A hpos hinf J bad burst (fun E u L r W hr hE hI hW => annulus_late_tradeoff hsid E W u L r hr hE hI hW) dense hsid
  · exact h₂ a (by omega) A hpos hinf J bad burst (fun E u L r W hr hE hI hW => annulus_late_tradeoff hsid E W u L r hr hE hI hW)
      (cofinal_good old A hsid) sparse hsid

end OMA.R_Erdos1191_erdos_1191_parts_i_R3_H2_R1
