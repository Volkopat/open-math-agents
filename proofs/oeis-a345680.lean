import OMAStatements.S_oeis_a345680

/-!
Proves the arbitrary-length run conjecture by finite-set synchronization.
Two-digit blocks give additive signed weights. A high prefix realizes any
integer weight, allowing translated digit maps to be lifted backwards through
an orbit. Large pair distances contract; a finite certificate merges every
small distance. Induction on the finite set then gives a successful common
translation for any prescribed finite set of inputs.
-/

namespace A345680

def g (n : ℕ) : ℤ :=
  (((Nat.digits 10 n).map fun d => (d : ℤ) ^ 2).alternatingSum)

def delta (c d : ℕ) : ℕ := (g (c + d) - g c).natAbs

def F (n : ℕ) : ℕ := (g n).natAbs

def Term (n : ℕ) : Prop := ∃ j : ℕ, F^[j] n = 0

def Good (T : Finset ℕ) : Prop := ∃ m : ℕ, ∀ x ∈ T, Term (m + x)

end A345680

namespace A345680

lemma g_step (n : ℕ) : g n = ((n % 10 : ℕ) : ℤ) ^ 2 - g (n / 10) := by
  by_cases hn : n = 0
  · simp [hn, g, Nat.digits_zero]
  · unfold g
    rw [Nat.digits_eq_cons_digits_div (by omega : 1 < 10) hn]
    exact List.alternatingSum_cons _ _

lemma g_zero : g 0 = 0 := by simp [g, Nat.digits_zero]

lemma g_block (q r : ℕ) (hr : r < 100) :
    g (100 * q + r) = g q + ((r % 10 : ℕ) : ℤ) ^ 2 - ((r / 10 : ℕ) : ℤ) ^ 2 := by
  rw [g_step, g_step ((100 * q + r) / 10)]
  have h₁ : (100 * q + r) % 10 = r % 10 := by omega
  have h₂ : ((100 * q + r) / 10) % 10 = r / 10 := by omega
  have h₃ : (100 * q + r) / 10 / 10 = q := by omega
  rw [h₁, h₂, h₃]
  ring

lemma g_concat (p k x : ℕ) (hx : x < 100 ^ k) :
    g (p * 100 ^ k + x) = g p + g x := by
  induction k generalizing x with
  | zero =>
      have hx0 : x = 0 := by simpa using hx
      simp [hx0, g_zero]
  | succ k ih =>
      have hx' : x / 100 < 100 ^ k := by
        apply (Nat.div_lt_iff_lt_mul (by omega : 0 < 100)).2
        simpa [pow_succ] using hx
      have he : p * 100 ^ (k + 1) + x = 100 * (p * 100 ^ k + x / 100) + x % 100 := by
        rw [pow_succ]
        have hdiv := Nat.mod_add_div x 100
        calc
          p * (100 ^ k * 100) + x = (p * 100 ^ k) * 100 + x := by ring
          _ = 100 * (p * 100 ^ k + x / 100) + x % 100 := by omega
      have he' : 100 * (x / 100) + x % 100 = x := by omega
      rw [he, g_block _ _ (Nat.mod_lt _ (by omega)), ih _ hx']
      have htail := g_block (x / 100) (x % 100) (Nat.mod_lt x (by omega : 0 < 100))
      rw [he'] at htail
      rw [htail]
      ring

lemma g_realize_nat (n : ℕ) : ∃ p : ℕ, g p = (n : ℤ) := by
  induction n with
  | zero => exact ⟨0, g_zero⟩
  | succ n ih =>
      obtain ⟨p, hp⟩ := ih
      refine ⟨100 * p + 1, ?_⟩
      rw [g_block p 1 (by omega), hp]
      push_cast
      norm_num

lemma g_realize_neg_nat (n : ℕ) : ∃ p : ℕ, g p = -(n : ℤ) := by
  induction n with
  | zero => exact ⟨0, by simpa using g_zero⟩
  | succ n ih =>
      obtain ⟨p, hp⟩ := ih
      refine ⟨100 * p + 10, ?_⟩
      rw [g_block p 10 (by omega), hp]
      push_cast
      norm_num
      ring

lemma g_surjective (z : ℤ) : ∃ p : ℕ, g p = z := by
  cases z with
  | ofNat n => exact g_realize_nat n
  | negSucc n =>
      obtain ⟨p, hp⟩ := g_realize_neg_nat (n + 1)
      refine ⟨p, ?_⟩
      rw [hp]
      rfl

lemma pair_translate (a b c : ℕ) :
    ∃ s : ℕ, (g (a + s) - g (b + s)).natAbs = delta c (Nat.dist a b) := by
  let k := a + b + c + 1
  have hpow : a + b + c + 1 < 100 ^ k := Nat.lt_pow_self (by omega : 1 < 100)
  have hc : c < 100 ^ k := by omega
  by_cases hab : a ≤ b
  · let s := 100 ^ k + c - a
    have ha : a + s = 1 * 100 ^ k + c := by dsimp [s]; omega
    have hb : b + s = 1 * 100 ^ k + (c + (b - a)) := by dsimp [s]; omega
    have hcb : c + (b - a) < 100 ^ k := by omega
    refine ⟨s, ?_⟩
    rw [ha, hb, g_concat 1 k c hc, g_concat 1 k (c + (b - a)) hcb]
    rw [delta, Nat.dist_eq_sub_of_le hab]
    have he : g 1 + g c - (g 1 + g (c + (b - a))) = -(g (c + (b - a)) - g c) := by ring
    rw [he, Int.natAbs_neg]
  · have hba : b ≤ a := by omega
    let s := 100 ^ k + c - b
    have ha : a + s = 1 * 100 ^ k + (c + (a - b)) := by dsimp [s]; omega
    have hb : b + s = 1 * 100 ^ k + c := by dsimp [s]; omega
    have hca : c + (a - b) < 100 ^ k := by omega
    refine ⟨s, ?_⟩
    rw [ha, hb, g_concat 1 k (c + (a - b)) hca, g_concat 1 k c hc]
    rw [delta, Nat.dist_eq_sub_of_le_right hba]
    congr 1
    ring

end A345680

namespace A345680

lemma g_linear_bound_of_step
    (hs : ∀ n : ℕ, g n = ((n % 10 : ℕ) : ℤ) ^ 2 - g (n / 10)) :
    ∀ n : ℕ, (g n).natAbs ≤ 9 * n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · simp [hn, g]
    have hrem : n % 10 < 10 := Nat.mod_lt n (by decide)
    have hsquare : (n % 10) ^ 2 ≤ 9 * (n % 10) := by
      simpa [pow_two, Nat.mul_comm] using Nat.mul_le_mul_left (n % 10) (show n % 10 ≤ 9 by omega)
    have hdiv : n / 10 < n := Nat.div_lt_self (by omega) (by decide)
    have hrec := ih (n / 10) hdiv
    have hdigits := Nat.mod_add_div n 10
    calc
      (g n).natAbs = (((n % 10 : ℕ) : ℤ) ^ 2 - g (n / 10)).natAbs := by rw [hs n]
      _ ≤ (((n % 10 : ℕ) : ℤ) ^ 2).natAbs + (g (n / 10)).natAbs :=
        Int.natAbs_sub_le _ _
      _ = (n % 10) ^ 2 + (g (n / 10)).natAbs := by
        simp only [Int.natAbs_pow, Int.natAbs_natCast]
      _ ≤ 9 * (n % 10) + 9 * (n / 10) := Nat.add_le_add hsquare hrec
      _ ≤ 9 * n := by omega

lemma g_contract_of_step
    (hs : ∀ n : ℕ, g n = ((n % 10 : ℕ) : ℤ) ^ 2 - g (n / 10))
    {n : ℕ} (hn : 100 ≤ n) : (g n).natAbs < n := by
  have hblock : g n =
      (((n % 10 : ℕ) : ℤ) ^ 2 - ((n / 10 % 10 : ℕ) : ℤ) ^ 2) + g (n / 100) := by
    rw [hs n, hs (n / 10), Nat.div_div_eq_div_mul]
    norm_num
    ring
  have hrem₀ : n % 10 < 10 := Nat.mod_lt _ (by decide)
  have hrem₁ : n / 10 % 10 < 10 := Nat.mod_lt _ (by decide)
  have hb₀ : ((n % 10 : ℕ) : ℤ) ^ 2 ≤ 81 := by
    have : ((n % 10 : ℕ) : ℤ) ≤ 9 := by omega
    nlinarith [mul_le_mul (show ((n % 10 : ℕ) : ℤ) ≤ 9 by omega) (show ((n % 10 : ℕ) : ℤ) ≤ 9 by omega) (show (0 : ℤ) ≤ ((n % 10 : ℕ) : ℤ) by omega) (show (0 : ℤ) ≤ 9 by omega)]
  have hb₁ : ((n / 10 % 10 : ℕ) : ℤ) ^ 2 ≤ 81 := by
    have : ((n / 10 % 10 : ℕ) : ℤ) ≤ 9 := by omega
    nlinarith [mul_le_mul (show ((n / 10 % 10 : ℕ) : ℤ) ≤ 9 by omega) (show ((n / 10 % 10 : ℕ) : ℤ) ≤ 9 by omega) (show (0 : ℤ) ≤ ((n / 10 % 10 : ℕ) : ℤ) by omega) (show (0 : ℤ) ≤ 9 by omega)]
  have hb : ((((n % 10 : ℕ) : ℤ) ^ 2 - ((n / 10 % 10 : ℕ) : ℤ) ^ 2).natAbs : ℤ) ≤ 81 := by
    rw [Int.natCast_natAbs, abs_le]
    constructor <;> nlinarith [sq_nonneg ((n % 10 : ℕ) : ℤ), sq_nonneg ((n / 10 % 10 : ℕ) : ℤ)]
  have hbn : (((n % 10 : ℕ) : ℤ) ^ 2 - ((n / 10 % 10 : ℕ) : ℤ) ^ 2).natAbs ≤ 81 := by
    exact_mod_cast hb
  have hstep : (g n).natAbs ≤ 81 + (g (n / 100)).natAbs := by
    rw [hblock]
    exact le_trans (Int.natAbs_add_le _ _) (Nat.add_le_add_right hbn _)
  have hrec := g_linear_bound_of_step hs (n / 100)
  have hdiv : 100 * (n / 100) ≤ n := Nat.mul_div_le n 100
  have hq : 1 ≤ n / 100 := by omega
  omega

lemma g_contract {n : ℕ} (hn : 100 ≤ n) : (g n).natAbs < n :=
  g_contract_of_step g_step hn

lemma delta_contract {n : ℕ} (hn : 100 ≤ n) : delta 0 n < n := by
  simpa [delta, g_zero] using g_contract hn

end A345680

namespace A345680

def mergeFirst (d : ℕ) : ℕ :=
  (#[0, 5, 5, 1, 1, 1, 1, 2, 0, 29, 50, 0, 2, 3, 0, 0, 0, 0, 1, 4, 50, 7, 0, 1, 4, 1, 1, 1, 2, 0, 10, 4, 4, 0, 1, 1, 2, 2, 0, 8, 10, 0, 3, 3, 0, 11, 2, 0, 0, 1, 10, 0, 2, 8, 3, 0, 0, 0, 1, 1, 10, 0, 2, 2, 7, 0, 0, 0, 1, 8, 20, 0, 2, 3, 0, 0, 0, 0, 0, 5, 0, 2, 3, 0, 0, 5, 4, 0, 0, 3, 290, 6, 0, 1, 1, 1, 1, 6, 4, 0] : Array ℕ).getD d 0

def mergeSecond (d : ℕ) : ℕ :=
  (#[0, 0, 30, 89, 30, 62, 158, 0, 14, 0, 0, 0, 0, 379, 89, 30, 62, 158, 23, 0, 30, 0, 0, 0, 0, 4, 0, 49, 40, 0, 89, 0, 0, 0, 89, 379, 998, 45, 0, 4, 30, 89, 0, 0, 0, 0, 0, 0, 158, 379, 62, 30, 40, 0, 89, 0, 0, 30, 0, 168, 158, 62, 30, 89, 403, 0, 0, 40, 0, 14, 0, 158, 168, 0, 0, 30, 40, 0, 89, 897, 14, 49, 158, 0, 158, 804, 403, 89, 0, 84, 0, 45, 0, 0, 67, 41, 0, 379, 0, 0] : Array ℕ).getD d 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma small_merge_check : ∀ d : Fin 100,
    delta (mergeSecond d) (delta (mergeFirst d) d) = 0 := by
  decide

lemma small_merge {d : ℕ} (hd : d < 100) :
    ∃ c1 c2 : ℕ, delta c2 (delta c1 d) = 0 := by
  exact ⟨mergeFirst d, mergeSecond d, small_merge_check ⟨d, hd⟩⟩

end A345680

namespace A345680

theorem term_zero : Term 0 := ⟨0, rfl⟩

theorem term_of_F_zero {n : ℕ} (h : F n = 0) : Term n := by
  exact ⟨1, h⟩

theorem term_of_F_term {n : ℕ} (h : Term (F n)) : Term n := by
  rcases h with ⟨j, hj⟩
  exact ⟨j + 1, by simpa only [Function.iterate_succ_apply] using hj⟩

theorem good_empty : Good ∅ := by
  exact ⟨0, by simp⟩

theorem good_subset {S T : Finset ℕ} (hST : S ⊆ T) (hT : Good T) : Good S := by
  rcases hT with ⟨m, hm⟩
  exact ⟨m, fun x hx => hm x (hST hx)⟩

theorem lt_hundred_pow_succ (x : ℕ) : x < 100 ^ (x + 1) := by
  induction x with
  | zero => norm_num
  | succ x ih =>
      rw [pow_succ]
      nlinarith

theorem good_singleton_of_digits
    (concat : ∀ p k x : ℕ, x < 100 ^ k → g (p * 100 ^ k + x) = g p + g x)
    (surj : ∀ z : ℤ, ∃ p : ℕ, g p = z) (x : ℕ) : Good {x} := by
  obtain ⟨p, hp⟩ := surj (-g x)
  refine ⟨p * 100 ^ (x + 1), ?_⟩
  intro y hy
  have hyx : y = x := Finset.mem_singleton.mp hy
  subst y
  apply term_of_F_zero
  unfold F
  rw [concat p (x + 1) x (lt_hundred_pow_succ x), hp]
  simp

end A345680

namespace A345680

theorem good_of_image_of_digits
    (concat : ∀ p k x : ℕ, x < 100 ^ k → g (p * 100 ^ k + x) = g p + g x)
    (surj : ∀ z : ℤ, ∃ p : ℕ, g p = z)
    (T : Finset ℕ) (s : ℕ) (C : ℤ)
    (hC : ∀ x ∈ T, 0 ≤ C + g (x + s)) :
    Good (T.image (fun x => (C + g (x + s)).toNat)) → Good T := by
  intro hGood
  obtain ⟨m, hm⟩ := hGood
  let k := T.sup (fun x => x + s) + 1
  obtain ⟨p, hp⟩ := surj ((m : ℤ) + C)
  refine ⟨p * 100 ^ k + s, ?_⟩
  intro x hx
  apply term_of_F_term
  have htail : x + s < 100 ^ k := by
    have hsup : x + s ≤ T.sup (fun y => y + s) := Finset.le_sup (f := fun y : ℕ => y + s) hx
    exact lt_of_le_of_lt hsup (lt_hundred_pow_succ _)
  have hg : g (p * 100 ^ k + s + x) = (m : ℤ) + C + g (x + s) := by
    calc
      g (p * 100 ^ k + s + x) = g (p * 100 ^ k + (x + s)) := by congr 1; omega
      _ = g p + g (x + s) := concat p k (x + s) htail
      _ = (m : ℤ) + C + g (x + s) := by rw [hp]
  have hcast : (m : ℤ) + C + g (x + s) =
      ((m + (C + g (x + s)).toNat : ℕ) : ℤ) := by
    rw [Nat.cast_add, Int.toNat_of_nonneg (hC x hx)]
    omega
  have hf : F (p * 100 ^ k + s + x) = m + (C + g (x + s)).toNat := by
    unfold F
    rw [hg, hcast, Int.natAbs_natCast]
  rw [hf]
  exact hm _ (Finset.mem_image_of_mem _ hx)

end A345680

/-!
Finite-set synchronization from a contracting distance map and a finite
two-step merging certificate. The application supplies digit translations.
-/

namespace A345680Synchronize

theorem dist_toNat_shift (C x y : ℤ) (hx : 0 ≤ C + x) (hy : 0 ≤ C + y) :
    Nat.dist (C + x).toNat (C + y).toNat = (x - y).natAbs := by
  have hx' := Int.toNat_of_nonneg hx
  have hy' := Int.toNat_of_nonneg hy
  unfold Nat.dist
  by_cases hxy : x ≤ y
  · have habs := Int.ofNat_natAbs_of_nonpos (show x - y ≤ 0 by omega)
    omega
  · have habs := Int.natAbs_of_nonneg (show 0 ≤ x - y by omega)
    omega

private theorem card_image_lt_of_collision (T : Finset ℕ) (F : ℕ → ℕ)
    {a b : ℕ} (ha : a ∈ T) (hb : b ∈ T) (hab : a ≠ b) (hF : F a = F b) :
    (T.image F).card < T.card := by
  have hle := Finset.card_image_le (s := T) (f := F)
  have hne : (T.image F).card ≠ T.card := by
    intro heq
    exact hab ((Finset.card_image_iff.mp heq) ha hb hF)
  omega

variable (Good : Finset ℕ → Prop) (delta : ℕ → ℕ → ℕ)

/-- A permitted transformation is allowed to depend on the finite set and on
the pair being merged. Its only required effect is the displayed distance. -/
def HasSteps : Prop :=
  ∀ (T : Finset ℕ) (a b c : ℕ), a ∈ T → b ∈ T →
    ∃ F : ℕ → ℕ,
      (Good (T.image F) → Good T) ∧
      Nat.dist (F a) (F b) = delta c (Nat.dist a b)

theorem reduce_card
    (steps : HasSteps Good delta)
    (contract : ∀ d : ℕ, 100 ≤ d → delta 0 d < d)
    (small : ∀ d : ℕ, d < 100 → ∃ c₁ c₂ : ℕ, delta c₂ (delta c₁ d) = 0)
    (T : Finset ℕ) {a b : ℕ} (ha : a ∈ T) (hb : b ∈ T) (hab : a ≠ b) :
    ∃ U : Finset ℕ, U.card < T.card ∧ (Good U → Good T) := by
  classical
  have aux : ∀ d : ℕ, ∀ (T : Finset ℕ) (a b : ℕ),
      a ∈ T → b ∈ T → a ≠ b → Nat.dist a b = d →
      ∃ U : Finset ℕ, U.card < T.card ∧ (Good U → Good T) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro T a b ha hb hab hd
      by_cases hsmall : d < 100
      · obtain ⟨c₁, c₂, hmerge⟩ := small d hsmall
        obtain ⟨F₁, hback₁, hdist₁⟩ := steps T a b c₁ ha hb
        have ha₁ : F₁ a ∈ T.image F₁ := Finset.mem_image_of_mem F₁ ha
        have hb₁ : F₁ b ∈ T.image F₁ := Finset.mem_image_of_mem F₁ hb
        obtain ⟨F₂, hback₂, hdist₂⟩ := steps (T.image F₁) (F₁ a) (F₁ b) c₂ ha₁ hb₁
        have hsame : F₂ (F₁ a) = F₂ (F₁ b) := by
          apply Nat.eq_of_dist_eq_zero
          rw [hdist₂, hdist₁, hd, hmerge]
        refine ⟨(T.image F₁).image F₂, ?_, fun h => hback₁ (hback₂ h)⟩
        simpa only [Finset.image_image] using
          card_image_lt_of_collision T (F₂ ∘ F₁) ha hb hab hsame
      · obtain ⟨F, hback, hdist⟩ := steps T a b 0 ha hb
        have ha' : F a ∈ T.image F := Finset.mem_image_of_mem F ha
        have hb' : F b ∈ T.image F := Finset.mem_image_of_mem F hb
        by_cases hsame : F a = F b
        · exact ⟨T.image F, card_image_lt_of_collision T F ha hb hab hsame, hback⟩
        · have hlt : Nat.dist (F a) (F b) < d := by
            rw [hdist, hd]
            exact contract d (by omega)
          obtain ⟨U, hU, hUback⟩ := ih (Nat.dist (F a) (F b)) hlt
            (T.image F) (F a) (F b) ha' hb' hsame rfl
          exact ⟨U, lt_of_lt_of_le hU Finset.card_image_le,
            fun h => hback (hUback h)⟩
  exact aux (Nat.dist a b) T a b ha hb hab rfl

theorem all_good
    (steps : HasSteps Good delta)
    (contract : ∀ d : ℕ, 100 ≤ d → delta 0 d < d)
    (small : ∀ d : ℕ, d < 100 → ∃ c₁ c₂ : ℕ, delta c₂ (delta c₁ d) = 0)
    (empty : Good ∅) (singleton : ∀ a : ℕ, Good {a}) :
    ∀ T : Finset ℕ, Good T := by
  have aux : ∀ n : ℕ, ∀ T : Finset ℕ, T.card = n → Good T := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro T hcard
      by_cases hzero : T.card = 0
      · have hT : T = ∅ := Finset.card_eq_zero.mp hzero
        simpa only [hT] using empty
      by_cases hone : T.card = 1
      · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hone
        exact singleton a
      have hlarge : 1 < T.card := by omega
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hlarge
      obtain ⟨U, hU, hback⟩ := reduce_card Good delta steps contract small T ha hb hab
      exact hback (ih U.card (by omega) U rfl)
  intro T
  exact aux T.card T rfl

end A345680Synchronize

namespace A345680

def shiftBound (T : Finset ℕ) (s : ℕ) : ℕ :=
  ∑ x ∈ T, (g (x + s)).natAbs

theorem shiftBound_nonneg (T : Finset ℕ) (s : ℕ) {x : ℕ} (hx : x ∈ T) :
    0 ≤ (shiftBound T s : ℤ) + g (x + s) := by
  have hle : (g (x + s)).natAbs ≤ shiftBound T s := by
    unfold shiftBound
    exact Finset.single_le_sum (f := fun y => (g (y + s)).natAbs)
      (fun _ _ => Nat.zero_le _) hx
  have hneg : -g (x + s) ≤ ((g (x + s)).natAbs : ℤ) := by
    simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -g (x + s)))
  omega

theorem hasSteps_of_lifts
    (pair : ∀ a b c : ℕ, ∃ s : ℕ,
      (g (a + s) - g (b + s)).natAbs = delta c (Nat.dist a b))
    (back : ∀ (T : Finset ℕ) (s : ℕ) (C : ℤ),
      (∀ x ∈ T, 0 ≤ C + g (x + s)) →
      Good (T.image (fun x => (C + g (x + s)).toNat)) → Good T) :
    A345680Synchronize.HasSteps Good delta := by
  intro T a b c ha hb
  obtain ⟨s, hs⟩ := pair a b c
  let C : ℤ := shiftBound T s
  have hC : ∀ x ∈ T, 0 ≤ C + g (x + s) :=
    fun _ hx => shiftBound_nonneg T s hx
  refine ⟨fun x => (C + g (x + s)).toNat, back T s C hC, ?_⟩
  rw [A345680Synchronize.dist_toNat_shift C (g (a + s)) (g (b + s))
    (hC a ha) (hC b hb), hs]

end A345680

theorem OMA.solution : type_of% @OMA.S_oeis_a345680.main := by
  intro L
  have allGood := A345680Synchronize.all_good A345680.Good A345680.delta
    (A345680.hasSteps_of_lifts A345680.pair_translate
      (A345680.good_of_image_of_digits A345680.g_concat A345680.g_surjective))
    (fun _ hn => A345680.delta_contract hn)
    (fun _ hn => A345680.small_merge hn)
    A345680.good_empty
    (A345680.good_singleton_of_digits A345680.g_concat A345680.g_surjective)
  obtain ⟨m, hm⟩ := allGood (Finset.range L)
  exact ⟨m, fun i hi => hm i (Finset.mem_range.mpr hi)⟩
