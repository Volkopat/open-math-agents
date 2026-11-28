import OMAStatements.S_oeis_a259565
import Mathlib

namespace OMA.A259565Proof

open OMA.S_oeis_a259565

open Classical

/-! ## The greedy recursion -/

/-- The eligible set after the list `l` of earlier terms. -/
def E (l : List ℕ) : Set ℕ :=
  {k : ℕ | 1 ≤ k ∧ k ∉ l ∧ 2 ∣ l.getLastD 0 + k ∧ Squarefree ((l.getLastD 0 + k) / 2)}

lemma mem_E (l : List ℕ) (k : ℕ) :
    k ∈ E l ↔ 1 ≤ k ∧ k ∉ l ∧ 2 ∣ l.getLastD 0 + k ∧ Squarefree ((l.getLastD 0 + k) / 2) :=
  Iff.rfl

lemma getLastD_snoc (l : List ℕ) (b d : ℕ) : (l ++ [b]).getLastD d = b := by
  simp

lemma pre_two (n : ℕ) : pre (n + 1 + 1) = pre (n + 1) ++ [sInf (E (pre (n + 1)))] := rfl

lemma a_one : a 1 = 1 := rfl

lemma getLastD_pre (n : ℕ) : (pre n).getLastD 0 = a n := rfl

lemma a_two (n : ℕ) : a (n + 1 + 1) = sInf (E (pre (n + 1))) := by
  show (pre (n + 1 + 1)).getLastD 0 = _
  rw [pre_two, getLastD_snoc]

lemma pre_succ (n : ℕ) : pre (n + 1) = pre n ++ [a (n + 1)] := by
  rcases n with _ | n
  · rfl
  · rw [a_two, pre_two]

lemma mem_pre (n k : ℕ) : k ∈ pre n ↔ ∃ i, 1 ≤ i ∧ i ≤ n ∧ a i = k := by
  induction n with
  | zero =>
    constructor
    · intro h
      simp [pre] at h
    · rintro ⟨i, h1, h2, -⟩
      omega
  | succ n ih =>
    rw [pre_succ, List.mem_append, List.mem_singleton, ih]
    constructor
    · rintro (⟨i, h1, h2, h3⟩ | h)
      · exact ⟨i, h1, by omega, h3⟩
      · exact ⟨n + 1, by omega, le_refl _, h.symm⟩
    · rintro ⟨i, h1, h2, h3⟩
      rcases Nat.lt_or_ge i (n + 1) with h | h
      · exact Or.inl ⟨i, h1, by omega, h3⟩
      · have hi : i = n + 1 := by omega
        subst hi
        exact Or.inr h3.symm

lemma list_bdd (l : List ℕ) : ∃ M, ∀ y ∈ l, y ≤ M := by
  induction l with
  | nil => exact ⟨0, fun y hy => absurd hy (by simp)⟩
  | cons x xs ih =>
    obtain ⟨M, hM⟩ := ih
    refine ⟨max x M, fun y hy => ?_⟩
    rcases List.mem_cons.mp hy with h | h
    · rw [h]
      exact le_max_left _ _
    · exact le_trans (hM y h) (le_max_right _ _)

lemma sqf_of_prime {p : ℕ} (hp : p.Prime) : Squarefree p :=
  Irreducible.squarefree hp

lemma E_nonempty (l : List ℕ) : (E l).Nonempty := by
  obtain ⟨M, hM⟩ := list_bdd l
  obtain ⟨p, hp1, hp⟩ := Nat.exists_infinite_primes (l.getLastD 0 + M + 1)
  refine ⟨2 * p - l.getLastD 0, (mem_E _ _).mpr ⟨by omega, fun h => ?_, by omega, ?_⟩⟩
  · have := hM _ h
    omega
  · have e : (l.getLastD 0 + (2 * p - l.getLastD 0)) / 2 = p := by omega
    rw [e]
    exact sqf_of_prime hp

lemma a_succ_eq (n : ℕ) (hn : 1 ≤ n) : a (n + 1) = sInf (E (pre n)) := by
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  exact a_two n

lemma a_succ_mem (n : ℕ) (hn : 1 ≤ n) : a (n + 1) ∈ E (pre n) := by
  rw [a_succ_eq n hn]
  exact Nat.sInf_mem (E_nonempty _)

lemma a_succ_min (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : k ∈ E (pre n)) : a (n + 1) ≤ k := by
  rw [a_succ_eq n hn]
  exact Nat.sInf_le hk

/-! ## Oddness and injectivity -/

lemma a_odd (n : ℕ) (hn : 1 ≤ n) : Odd (a n) := by
  induction n with
  | zero => exact absurd hn (by norm_num)
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      show Odd (a 1)
      rw [a_one]
      exact odd_one
    · have h1 := Nat.odd_iff.mp (ih (by omega))
      have h2 := ((mem_E _ _).mp (a_succ_mem n (by omega))).2.2.1
      rw [getLastD_pre] at h2
      exact Nat.odd_iff.mpr (by omega)

lemma a_ne_of_lt (i j : ℕ) (hi : 1 ≤ i) (hij : i < j) : a i ≠ a j := by
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  have h := ((mem_E _ _).mp (a_succ_mem n hn)).2.1
  intro heq
  apply h
  rw [mem_pre]
  exact ⟨i, hi, by omega, heq⟩

lemma a_inj (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (h : a i = a j) : i = j := by
  rcases lt_trichotomy i j with hij | hij | hij
  · exact absurd h (a_ne_of_lt i j hi hij)
  · exact hij
  · exact absurd h.symm (a_ne_of_lt j i hj hij)

lemma a_unbounded (B : ℕ) : ∃ j, 1 ≤ j ∧ B ≤ a j := by
  by_contra hcon
  push Not at hcon
  have hc : (Finset.range B).card < (Finset.Icc 1 (B + 1)).card := by
    rw [Finset.card_range, Nat.card_Icc]
    omega
  have hmaps : Set.MapsTo a (Finset.Icc 1 (B + 1) : Set ℕ) (Finset.range B : Set ℕ) := by
    intro x hx
    rw [Finset.mem_coe, Finset.mem_Icc] at hx
    rw [Finset.mem_coe, Finset.mem_range]
    exact hcon x hx.1
  obtain ⟨i, hi, j, hj, hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hc hmaps
  exact hne (a_inj i j (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hj).1 heq)

/-! ## Finite bookkeeping -/

lemma exists_T (m : ℕ) (hm : ∀ m' < m, Odd m' → ∃ i, 1 ≤ i ∧ a i = m') :
    ∃ T, 1 ≤ T ∧ ∀ m' < m, Odd m' → ∃ i, 1 ≤ i ∧ i ≤ T ∧ a i = m' := by
  induction m with
  | zero => exact ⟨1, le_refl _, fun m' h => absurd h (Nat.not_lt_zero _)⟩
  | succ m ih =>
    obtain ⟨T, hT1, hT⟩ := ih (fun m' h hodd => hm m' (by omega) hodd)
    by_cases hodd : Odd m
    · obtain ⟨i, hi1, hi⟩ := hm m (by omega) hodd
      refine ⟨max T i, le_trans hT1 (le_max_left _ _), ?_⟩
      intro m' hm' hm'odd
      rcases Nat.lt_or_ge m' m with h | h
      · obtain ⟨j, hj1, hj2, hj⟩ := hT m' h hm'odd
        exact ⟨j, hj1, le_trans hj2 (le_max_left _ _), hj⟩
      · have he : m' = m := by omega
        rw [he]
        exact ⟨i, hi1, le_max_right _ _, hi⟩
    · refine ⟨T, hT1, ?_⟩
      intro m' hm' hm'odd
      rcases Nat.lt_or_ge m' m with h | h
      · exact hT m' h hm'odd
      · have he : m' = m := by omega
        rw [he] at hm'odd
        exact absurd hm'odd hodd

lemma exists_K (T : ℕ) : ∃ K, ∀ i, i ≤ T → a i ≤ K := by
  induction T with
  | zero => exact ⟨a 0, fun i hi => by rw [Nat.le_zero.mp hi]⟩
  | succ T ih =>
    obtain ⟨K, hK⟩ := ih
    refine ⟨max K (a (T + 1)), fun i hi => ?_⟩
    rcases Nat.lt_or_ge i (T + 1) with h | h
    · exact le_trans (hK i (by omega)) (le_max_left _ _)
    · have he : i = T + 1 := by omega
      rw [he]
      exact le_max_right _ _

/-! ## Counting non-squarefree numbers in an interval -/

lemma card_dvd_le (q s L α : ℕ) (hq : 0 < q) :
    ((Finset.Ico s (s + L)).filter (fun u => q ∣ u + α)).card ≤ L / q + 2 := by
  have hmaps : Set.MapsTo (fun u => (u + α) / q)
      ((Finset.Ico s (s + L)).filter (fun u => q ∣ u + α) : Set ℕ)
      (Finset.Icc ((s + α) / q) ((s + L + α) / q) : Set ℕ) := by
    intro u hu
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico] at hu
    rw [Finset.mem_coe, Finset.mem_Icc]
    show (s + α) / q ≤ (u + α) / q ∧ (u + α) / q ≤ (s + L + α) / q
    constructor
    · exact Nat.div_le_div_right (by omega)
    · exact Nat.div_le_div_right (by omega)
  have hinj : Set.InjOn (fun u => (u + α) / q)
      ((Finset.Ico s (s + L)).filter (fun u => q ∣ u + α) : Set ℕ) := by
    intro u hu v hv huv
    have hu' := (Finset.mem_filter.mp (Finset.mem_coe.mp hu)).2
    have hv' := (Finset.mem_filter.mp (Finset.mem_coe.mp hv)).2
    have huv' : (u + α) / q = (v + α) / q := huv
    have e : u + α = v + α := by
      calc u + α = (u + α) / q * q := (Nat.div_mul_cancel hu').symm
        _ = (v + α) / q * q := by rw [huv']
        _ = v + α := Nat.div_mul_cancel hv'
    omega
  have hcard := Finset.card_le_card_of_injOn (fun u => (u + α) / q) hmaps hinj
  rw [Nat.card_Icc] at hcard
  have key : (s + L + α) / q ≤ (s + α) / q + L / q + 1 := by
    have e1 := Nat.div_add_mod (s + α) q
    have e2 := Nat.div_add_mod L q
    have e3 := Nat.mul_div_le (s + L + α) q
    have r1 := Nat.mod_lt (s + α) hq
    have r2 := Nat.mod_lt L hq
    by_contra hcon
    have hcon' : (s + α) / q + L / q + 2 ≤ (s + L + α) / q := by omega
    have hm := Nat.mul_le_mul (le_refl q) hcon'
    rw [Nat.mul_add, Nat.mul_add] at hm
    omega
  have hd : 0 ≤ L / q := Nat.zero_le _
  omega

lemma card_nsf_le (s L α M : ℕ) (hX : s + L + α ≤ (2 * M + 3) * (2 * M + 3)) :
    ((Finset.Ico s (s + L)).filter (fun u => ¬ Squarefree (u + α))).card ≤
      ((Finset.Ico s (s + L)).filter (fun u => 4 ∣ u + α)).card +
      ∑ k ∈ Finset.range M,
        ((Finset.Ico s (s + L)).filter (fun u => (2 * k + 3) * (2 * k + 3) ∣ u + α)).card := by
  have hsub : (Finset.Ico s (s + L)).filter (fun u => ¬ Squarefree (u + α)) ⊆
      (Finset.Ico s (s + L)).filter (fun u => 4 ∣ u + α) ∪
      (Finset.range M).biUnion
        (fun k => (Finset.Ico s (s + L)).filter (fun u => (2 * k + 3) * (2 * k + 3) ∣ u + α)) := by
    intro u hu
    rw [Finset.mem_filter] at hu
    obtain ⟨hu1, hu2⟩ := hu
    have hrange := Finset.mem_Ico.mp hu1
    rw [Finset.mem_union]
    by_cases h4 : 4 ∣ u + α
    · exact Or.inl (Finset.mem_filter.mpr ⟨hu1, h4⟩)
    · right
      rw [Finset.mem_biUnion]
      have hu3 : ∃ x : ℕ, x * x ∣ u + α ∧ ¬ IsUnit x := by
        by_contra hcon
        push Not at hcon
        exact hu2 hcon
      obtain ⟨x, hx, hxu⟩ := hu3
      have hx1 : x ≠ 1 := fun h => hxu (by rw [h]; exact isUnit_one)
      obtain ⟨p, hp, hpp⟩ : ∃ p : ℕ, p.Prime ∧ p * p ∣ u + α :=
        ⟨Nat.minFac x, Nat.minFac_prime hx1,
          dvd_trans (mul_dvd_mul (Nat.minFac_dvd x) (Nat.minFac_dvd x)) hx⟩
      have hpos : 0 < u + α := by
        rcases Nat.eq_zero_or_pos (u + α) with h | h
        · exact absurd (h ▸ dvd_zero 4) h4
        · exact h
      have hp2 : p ≠ 2 := by
        rintro rfl
        omega
      have hpodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
      have hp3 : 2 ≤ p := hp.two_le
      have hle : p * p ≤ u + α := Nat.le_of_dvd hpos hpp
      have hlt : p < 2 * M + 3 := by
        by_contra hc
        push Not at hc
        have hsq := Nat.mul_le_mul hc hc
        have hu2' := hrange.2
        omega
      refine ⟨(p - 3) / 2, Finset.mem_range.mpr (by omega), Finset.mem_filter.mpr ⟨hu1, ?_⟩⟩
      have e : 2 * ((p - 3) / 2) + 3 = p := by omega
      rw [e]
      exact hpp
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add_left Finset.card_biUnion_le _

lemma card_dvd_real (q s L α : ℕ) (hq : 0 < q) :
    (((Finset.Ico s (s + L)).filter (fun u => q ∣ u + α)).card : ℝ) ≤ (L : ℝ) / (q : ℝ) + 2 := by
  have h1 := card_dvd_le q s L α hq
  have h2 : ((L / q : ℕ) : ℝ) ≤ (L : ℝ) / (q : ℝ) := Nat.cast_div_le
  have h3 : (((Finset.Ico s (s + L)).filter (fun u => q ∣ u + α)).card : ℝ) ≤
      ((L / q : ℕ) : ℝ) + 2 := by
    exact_mod_cast h1
  linarith

lemma step_ineq (n : ℕ) :
    (1 : ℝ) / ((2 * ((n + 1 : ℕ) : ℝ) + 3) * (2 * ((n + 1 : ℕ) : ℝ) + 3)) ≤
      1 / (4 * ((n : ℝ) + 2)) - 1 / (4 * ((n : ℝ) + 3)) := by
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  have h3 : (n : ℝ) + 3 ≠ 0 := by positivity
  have e : (1 : ℝ) / (4 * ((n : ℝ) + 2)) - 1 / (4 * ((n : ℝ) + 3)) =
      1 / (4 * (((n : ℝ) + 2) * ((n : ℝ) + 3))) := by
    field_simp
    ring
  rw [e]
  apply one_div_le_one_div_of_le
  · positivity
  · push_cast
    nlinarith

lemma sum_inv_sq_aux (M : ℕ) :
    ∑ k ∈ Finset.range (M + 1), (1 : ℝ) / ((2 * (k : ℝ) + 3) * (2 * (k : ℝ) + 3)) ≤
      17 / 72 - 1 / (4 * ((M : ℝ) + 2)) := by
  induction M with
  | zero => norm_num [Finset.sum_range_one]
  | succ M ih =>
    rw [Finset.sum_range_succ]
    have hs := step_ineq M
    have e : ((M + 1 : ℕ) : ℝ) + 2 = (M : ℝ) + 3 := by
      push_cast
      ring
    rw [e]
    linarith

lemma sum_inv_sq_le (M : ℕ) :
    ∑ k ∈ Finset.range M, (1 : ℝ) / ((2 * (k : ℝ) + 3) * (2 * (k : ℝ) + 3)) ≤ 17 / 72 := by
  rcases M with _ | M
  · norm_num
  · have h := sum_inv_sq_aux M
    have hpos : (0 : ℝ) < 1 / (4 * ((M : ℝ) + 2)) := by positivity
    linarith

lemma card_nsf_real (s L α M : ℕ) (hX : s + L + α ≤ (2 * M + 3) * (2 * M + 3)) :
    (((Finset.Ico s (s + L)).filter (fun u => ¬ Squarefree (u + α))).card : ℝ) ≤
      35 / 72 * (L : ℝ) + 2 * (M : ℝ) + 2 := by
  have h1 := card_nsf_le s L α M hX
  have h1r : (((Finset.Ico s (s + L)).filter (fun u => ¬ Squarefree (u + α))).card : ℝ) ≤
      (((Finset.Ico s (s + L)).filter (fun u => 4 ∣ u + α)).card : ℝ) +
      ∑ k ∈ Finset.range M,
        (((Finset.Ico s (s + L)).filter (fun u => (2 * k + 3) * (2 * k + 3) ∣ u + α)).card : ℝ) := by
    exact_mod_cast h1
  have h4 := card_dvd_real 4 s L α (by norm_num)
  have e4 : ((4 : ℕ) : ℝ) = 4 := by norm_num
  rw [e4] at h4
  have hk : ∀ k ∈ Finset.range M,
      (((Finset.Ico s (s + L)).filter (fun u => (2 * k + 3) * (2 * k + 3) ∣ u + α)).card : ℝ) ≤
        (L : ℝ) * (1 / ((2 * (k : ℝ) + 3) * (2 * (k : ℝ) + 3))) + 2 := by
    intro k _
    have hq : 0 < (2 * k + 3) * (2 * k + 3) := by positivity
    have hb := card_dvd_real ((2 * k + 3) * (2 * k + 3)) s L α hq
    have e : (((2 * k + 3) * (2 * k + 3) : ℕ) : ℝ) = (2 * (k : ℝ) + 3) * (2 * (k : ℝ) + 3) := by
      push_cast
      ring
    rw [e] at hb
    rw [mul_one_div]
    exact hb
  have hsum := Finset.sum_le_sum hk
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hS := sum_inv_sq_le M
  have hLS : (L : ℝ) * ∑ k ∈ Finset.range M, (1 : ℝ) / ((2 * (k : ℝ) + 3) * (2 * (k : ℝ) + 3)) ≤
      (L : ℝ) * (17 / 72) :=
    mul_le_mul_of_nonneg_left hS (Nat.cast_nonneg L)
  linarith

/-! ## Surjectivity: a density contradiction at a record step -/

lemma no_missing (m : ℕ) (hodd : Odd m) (hnever : ∀ n, 1 ≤ n → a n ≠ m)
    (hmin : ∀ m' < m, Odd m' → ∃ i, 1 ≤ i ∧ a i = m') : False := by
  obtain ⟨T, hT1, hT⟩ := exists_T m hmin
  obtain ⟨K, hK⟩ := exists_K T
  have hm1 := Nat.odd_iff.mp hodd
  -- (A): from index `T` on, the mean with `m` is never squarefree (else `m` would be chosen).
  have hA : ∀ i, T ≤ i → ¬ Squarefree ((a i + m) / 2) := by
    intro i hi hsq
    have hi1 : 1 ≤ i := le_trans hT1 hi
    have hai := Nat.odd_iff.mp (a_odd i hi1)
    have hmE : m ∈ E (pre i) := by
      rw [mem_E, getLastD_pre]
      refine ⟨by omega, ?_, by omega, hsq⟩
      rw [mem_pre]
      rintro ⟨j, hj1, -, hj⟩
      exact hnever j hj1 hj
    have hle := a_succ_min i hi1 m hmE
    have hne := hnever (i + 1) (by omega)
    have hlt : a (i + 1) < m := lt_of_le_of_ne hle hne
    obtain ⟨j, hj1, hj2, hj⟩ := hT (a (i + 1)) hlt (a_odd (i + 1) (by omega))
    have := a_inj j (i + 1) hj1 (by omega) hj
    omega
  -- `g > K` with squarefree mean with `m` is never a term.
  have hG : ∀ g, K < g → Squarefree ((g + m) / 2) → ∀ i, 1 ≤ i → a i ≠ g := by
    intro g hg hsq i hi heq
    rcases le_total i T with h | h
    · have := hK i h
      omega
    · apply hA i h
      rw [heq]
      exact hsq
  -- a record step with a large record value
  obtain ⟨C, hC⟩ : ∃ C, C = 291 + 2 * K + m := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = 288 * (290 + C) + C := ⟨_, rfl⟩
  obtain ⟨j0, hj01, hj0⟩ := a_unbounded B
  have hex : ∃ j, 1 ≤ j ∧ B ≤ a j := ⟨j0, hj01, hj0⟩
  obtain ⟨j, ⟨hj1, hjB⟩, hjmin⟩ : ∃ j, (1 ≤ j ∧ B ≤ a j) ∧ ∀ i < j, ¬ (1 ≤ i ∧ B ≤ a i) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩
  have hj2 : 2 ≤ j := by
    by_contra h
    have hj : j = 1 := by omega
    rw [hj, a_one] at hjB
    omega
  obtain ⟨t, rfl⟩ : ∃ t, j = t + 1 := ⟨j - 1, by omega⟩
  have ht1 : 1 ≤ t := by omega
  have hxt : a t < B := by
    have := hjmin t (by omega)
    push Not at this
    exact this ht1
  have hx := Nat.odd_iff.mp (a_odd t ht1)
  have hxN : a t < a (t + 1) := lt_of_lt_of_le hxt hjB
  obtain ⟨L, hL⟩ : ∃ L, L = (a (t + 1) - 2 * K - 2) / 2 := ⟨_, rfl⟩
  obtain ⟨α, hα⟩ : ∃ α, α = (m + 1) / 2 := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, β = (a t + 1) / 2 := ⟨_, rfl⟩
  -- (B): every `u` in the window has a non-squarefree shift by `α` or by `β`.
  have hcover : ∀ u ∈ Finset.Ico (K + 1) (K + 1 + L),
      ¬ Squarefree (u + α) ∨ ¬ Squarefree (u + β) := by
    intro u hu
    rw [Finset.mem_Ico] at hu
    by_contra hcon
    push Not at hcon
    obtain ⟨hsa, hsb⟩ := hcon
    have e1 : (2 * u + 1 + m) / 2 = u + α := by omega
    have e2 : (a t + (2 * u + 1)) / 2 = u + β := by omega
    have hg := hG (2 * u + 1) (by omega) (by rw [e1]; exact hsa)
    have hgE : 2 * u + 1 ∈ E (pre t) := by
      rw [mem_E, getLastD_pre]
      refine ⟨by omega, ?_, by omega, by rw [e2]; exact hsb⟩
      rw [mem_pre]
      rintro ⟨i, hi1, -, hi⟩
      exact hg i hi1 hi
    have hle := a_succ_min t ht1 _ hgE
    omega
  have hcardL : L ≤ ((Finset.Ico (K + 1) (K + 1 + L)).filter (fun u => ¬ Squarefree (u + α))).card +
      ((Finset.Ico (K + 1) (K + 1 + L)).filter (fun u => ¬ Squarefree (u + β))).card := by
    have hsub : Finset.Ico (K + 1) (K + 1 + L) ⊆
        (Finset.Ico (K + 1) (K + 1 + L)).filter (fun u => ¬ Squarefree (u + α)) ∪
        (Finset.Ico (K + 1) (K + 1 + L)).filter (fun u => ¬ Squarefree (u + β)) := by
      intro u hu
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      rcases hcover u hu with h | h
      · exact Or.inl ⟨hu, h⟩
      · exact Or.inr ⟨hu, h⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le
      ((Finset.Ico (K + 1) (K + 1 + L)).filter (fun u => ¬ Squarefree (u + α)))
      ((Finset.Ico (K + 1) (K + 1 + L)).filter (fun u => ¬ Squarefree (u + β)))
    rw [Nat.card_Ico] at h1
    omega
  -- the window and both shifts lie below `(2 * M + 3) ^ 2`, `M = sqrt (N + m)`
  obtain ⟨M, hM⟩ : ∃ M, M = Nat.sqrt (a (t + 1) + m) := ⟨_, rfl⟩
  have hM1 : M * M ≤ a (t + 1) + m := by
    rw [hM]
    exact Nat.sqrt_le _
  have hM2 : a (t + 1) + m < (M + 1) * (M + 1) := by
    rw [hM]
    exact Nat.lt_succ_sqrt _
  have hM3 : (M + 1) * (M + 1) ≤ (2 * M + 3) * (2 * M + 3) := Nat.mul_le_mul (by omega) (by omega)
  have hXα : K + 1 + L + α ≤ (2 * M + 3) * (2 * M + 3) := by omega
  have hXβ : K + 1 + L + β ≤ (2 * M + 3) * (2 * M + 3) := by omega
  have hcα := card_nsf_real (K + 1) L α M hXα
  have hcβ := card_nsf_real (K + 1) L β M hXβ
  have hcardLr : (L : ℝ) ≤
      (((Finset.Ico (K + 1) (K + 1 + L)).filter (fun u => ¬ Squarefree (u + α))).card : ℝ) +
      (((Finset.Ico (K + 1) (K + 1 + L)).filter (fun u => ¬ Squarefree (u + β))).card : ℝ) := by
    exact_mod_cast hcardL
  have hLr : (L : ℝ) ≤ 144 * (M : ℝ) + 144 := by linarith
  have hL144 : L ≤ 144 * M + 144 := by exact_mod_cast hLr
  -- the density gap: `L` grows like `N / 2` but is at most `144 * (sqrt (N + m) + 1)`
  have hN2 : a (t + 1) ≤ 2 * L + 2 * K + 3 := by omega
  have hMM : M * M ≤ 288 * M + C := by omega
  have hMC : M ≤ 289 + C := by
    by_contra hcon
    have hcon' : 290 + C ≤ M := by omega
    have h1 : (290 + C) * M ≤ M * M := Nat.mul_le_mul hcon' (le_refl M)
    have h2 : C * 1 ≤ C * M := Nat.mul_le_mul (le_refl C) (by omega)
    nlinarith
  omega

/-! ## The three parts -/

lemma a_surj (m : ℕ) (hm : Odd m) : ∃ n, 1 ≤ n ∧ a n = m := by
  by_contra hcon
  have hex : ∃ m, Odd m ∧ ∀ n, 1 ≤ n → a n ≠ m :=
    ⟨m, hm, fun n hn h => hcon ⟨n, hn, h⟩⟩
  obtain ⟨m0, ⟨hm0, hnever⟩, hmin0⟩ : ∃ m0, (Odd m0 ∧ ∀ n, 1 ≤ n → a n ≠ m0) ∧
      ∀ m' < m0, ¬ (Odd m' ∧ ∀ n, 1 ≤ n → a n ≠ m') :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m' hm' => Nat.find_min hex hm'⟩
  apply no_missing m0 hm0 hnever
  intro m' hm' hodd'
  have := hmin0 m' hm'
  push Not at this
  exact this hodd'

end OMA.A259565Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a259565.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    exact OMA.A259565Proof.a_odd n hn
  · intro i j hi hj h
    exact OMA.A259565Proof.a_inj i j hi hj h
  · intro m hm
    exact OMA.A259565Proof.a_surj m hm
