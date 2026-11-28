import OMAStatements.S_oeis_a101282
import Mathlib

namespace OMA.P_oeis_a101282

open OMA.S_oeis_a101282

-- Part 1: First-return decomposition and generating function of Schroder paths with valleys

private lemma stepLen_append (p q : List SchroderStep) :
    stepLen (p ++ q) = stepLen p + stepLen q := by
  induction p with
  | nil => simp [stepLen]
  | cons s l ih => cases s <;> simp [stepLen, ih, Nat.add_assoc]

private lemma length_le_stepLen (p : List SchroderStep) : p.length ≤ stepLen p := by
  induction p with
  | nil => simp [stepLen]
  | cons s l ih => cases s <;> simp [stepLen] <;> omega

private lemma isSchroderAux_append (h : ℕ) (p q : List SchroderStep)
    (hp : isSchroderAux 0 p) :
    isSchroderAux h (p ++ q) ↔ isSchroderAux h q := by
  have aux : ∀ p : List SchroderStep, ∀ d : ℕ,
      isSchroderAux d p → (isSchroderAux (h + d) (p ++ q) ↔ isSchroderAux h q) := by
    intro p
    induction p with
    | nil =>
      intro d hd; simp only [isSchroderAux] at hd; subst hd; simp
    | cons s l ih =>
      intro d hd
      cases s with
      | U =>
        simp only [isSchroderAux] at hd
        simp only [List.cons_append, isSchroderAux]
        rw [Nat.add_assoc]
        exact ih (d + 1) hd
      | D =>
        simp only [isSchroderAux] at hd
        simp only [List.cons_append, isSchroderAux]
        have hpos : 0 < h + d := by omega
        have hsub : h + d - 1 = h + (d - 1) := by omega
        rw [hsub]
        exact ⟨fun ⟨_, h2⟩ => (ih (d - 1) hd.2).mp h2, fun hq => ⟨hpos, (ih (d - 1) hd.2).mpr hq⟩⟩
      | H =>
        simp only [isSchroderAux] at hd
        simp only [List.cons_append, isSchroderAux]
        exact ih d hd
  simpa using aux p 0 hp

private lemma valleys_append_D (p q : List SchroderStep) :
    valleys (p ++ .D :: q) =
      valleys (p ++ [.D]) + valleys q + (match q with | .U :: _ => 1 | _ => 0) := by
  induction p with
  | nil =>
    cases q with
    | nil => simp [valleys]
    | cons s l => cases s <;> (simp [valleys]; try omega)
  | cons s l ih =>
    cases l with
    | nil =>
      cases s <;> cases q with
      | nil => simp [valleys]
      | cons s' l' => cases s' <;> (simp [valleys]; try omega)
    | cons s2 l2 =>
      cases s <;> cases s2 <;> simp only [List.cons_append, valleys] at ih ⊢ <;> omega

private lemma valleys_U_cons (p : List SchroderStep) :
    valleys (.U :: p) = valleys p := by
  cases p <;> simp [valleys]

private lemma valleys_H_cons (p : List SchroderStep) :
    valleys (.H :: p) = valleys p := by
  cases p <;> simp [valleys]

private lemma valleys_append_D_nil (p : List SchroderStep) :
    valleys (p ++ [.D]) = valleys p := by
  induction p with
  | nil => simp [valleys]
  | cons s l ih =>
    cases l with
    | nil => cases s <;> simp [valleys]
    | cons s2 l2 =>
      cases s <;> cases s2 <;> simp only [List.cons_append, valleys] at ih ⊢ <;> omega

private lemma valleys_lt_stepLen (p : List SchroderStep) :
    valleys p ≤ stepLen p / 2 := by
  have h2 : ∀ n : ℕ, ∀ q : List SchroderStep, q.length = n → 2 * valleys q ≤ stepLen q := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro q hq
      cases q with
      | nil => simp [valleys, stepLen]
      | cons s l =>
        cases s with
        | U =>
          have := ih l.length (by simp [← hq]) l rfl
          simp [valleys, stepLen]; omega
        | H =>
          have := ih l.length (by simp [← hq]) l rfl
          simp [valleys, stepLen]; omega
        | D =>
          cases l with
          | nil => simp [valleys, stepLen]
          | cons s2 l2 =>
            cases s2 with
            | U =>
              have := ih l2.length (by simp [← hq]) l2 rfl
              simp [valleys, stepLen]; omega
            | D =>
              have := ih (SchroderStep.D :: l2).length (by simp [← hq]) (SchroderStep.D :: l2) rfl
              simp only [valleys, stepLen] at this ⊢; omega
            | H =>
              have := ih (SchroderStep.H :: l2).length (by simp [← hq]) (SchroderStep.H :: l2) rfl
              simp only [valleys, stepLen] at this ⊢; omega
  have := h2 p.length p rfl
  omega

-- First return split for a path starting with U (i.e. isSchroderAux 1 l)
private def splitFirstReturn : ℕ → List SchroderStep → List SchroderStep × List SchroderStep
  | _, [] => ([], [])
  | 0, .D :: l => ([], l)
  | h + 1, .D :: l =>
    let (a, b) := splitFirstReturn h l
    (.D :: a, b)
  | h, .U :: l =>
    let (a, b) := splitFirstReturn (h + 1) l
    (.U :: a, b)
  | h, .H :: l =>
    let (a, b) := splitFirstReturn h l
    (.H :: a, b)

private lemma splitFirstReturn_spec :
    ∀ (h : ℕ) (l : List SchroderStep), isSchroderAux (h + 1) l →
      let (a, b) := splitFirstReturn h l
      l = a ++ .D :: b ∧ isSchroderAux h a ∧ isSchroderAux 0 b := by
  intro h l
  induction l generalizing h with
  | nil => simp [isSchroderAux]
  | cons s l ih =>
    intro hl
    cases s with
    | U =>
      simp only [isSchroderAux] at hl
      simp only [splitFirstReturn]
      have hspec := ih (h + 1) hl
      rcases h1 : splitFirstReturn (h + 1) l with ⟨a, b⟩
      rw [h1] at hspec
      refine ⟨by simp [hspec.1], hspec.2.1, hspec.2.2⟩
    | H =>
      simp only [isSchroderAux] at hl
      simp only [splitFirstReturn]
      have hspec := ih h hl
      rcases h1 : splitFirstReturn h l with ⟨a, b⟩
      rw [h1] at hspec
      refine ⟨by simp [hspec.1], hspec.2.1, hspec.2.2⟩
    | D =>
      cases h with
      | zero =>
        simp only [isSchroderAux] at hl
        simp only [splitFirstReturn, List.nil_append, isSchroderAux]
        exact ⟨trivial, trivial, hl.2⟩
      | succ h' =>
        simp only [isSchroderAux] at hl
        simp only [splitFirstReturn]
        have hspec := ih h' hl.2
        rcases h1 : splitFirstReturn h' l with ⟨a, b⟩
        rw [h1] at hspec
        refine ⟨by simp [hspec.1], ⟨Nat.succ_pos h', hspec.2.1⟩, hspec.2.2⟩

private lemma splitFirstReturn_append :
    ∀ (h : ℕ) (a b : List SchroderStep), isSchroderAux h a →
      splitFirstReturn h (a ++ .D :: b) = (a, b) := by
  intro h a
  induction a generalizing h with
  | nil =>
    intro b ha
    simp only [isSchroderAux] at ha; subst ha
    simp [splitFirstReturn]
  | cons s l ih =>
    intro b ha
    cases s with
    | U =>
      simp only [isSchroderAux] at ha
      simp only [List.cons_append, splitFirstReturn, ih (h + 1) b ha]
    | H =>
      simp only [isSchroderAux] at ha
      simp only [List.cons_append, splitFirstReturn, ih h b ha]
    | D =>
      simp only [isSchroderAux] at ha
      obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
      simp only [List.cons_append, splitFirstReturn, ih h' b ha.2]

-- Finiteness of Schroder paths of semilength n
private def schroderSet (n : ℕ) : Set (List SchroderStep) :=
  {p | isSchroderAux 0 p ∧ stepLen p = 2 * n}

private lemma finite_schroderStep : Finite SchroderStep := by
  refine Finite.of_injective (fun s : SchroderStep => match s with | .U => (0 : Fin 3) | .D => 1 | .H => 2) ?_
  intro a b h
  cases a <;> cases b <;> simp at h <;> rfl

private lemma schroderSet_finite (n : ℕ) : (schroderSet n).Finite := by
  have : Finite SchroderStep := finite_schroderStep
  have hsub : schroderSet n ⊆
      ⋃ m ∈ Finset.range (2 * n + 1),
        (fun f : Fin m → SchroderStep => List.ofFn f) '' Set.univ := by
    intro p hp
    simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_image, Set.mem_univ, true_and]
    refine ⟨p.length, ?_, fun i => p.get i, List.ofFn_get p⟩
    have hlen := length_le_stepLen p
    have h2n := hp.2
    omega
  exact (Set.Finite.biUnion (Finset.finite_toSet _) fun m _ =>
    (Set.finite_univ.image _)).subset hsub

private noncomputable def schroderFinset (n : ℕ) : Finset (List SchroderStep) :=
  (schroderSet_finite n).toFinset

private lemma mem_schroderFinset {n : ℕ} {p : List SchroderStep} :
    p ∈ schroderFinset n ↔ isSchroderAux 0 p ∧ stepLen p = 2 * n := by
  simp [schroderFinset, schroderSet]

private lemma schroderRowPoly_eq_sum (n : ℕ) :
    schroderRowPoly n = ∑ p ∈ schroderFinset n, (Polynomial.X : Polynomial ℤ) ^ valleys p := by
  unfold schroderRowPoly
  have hcard : ∀ k, schroderValleyCount n k =
      ((schroderFinset n).filter (fun p => valleys p = k)).card := by
    intro k
    unfold schroderValleyCount
    rw [← Set.ncard_coe_finset]
    congr 1; ext p; simp [mem_schroderFinset, and_assoc]
  simp_rw [hcard]
  rw [← Finset.sum_fiberwise_of_maps_to (g := valleys) (t := Finset.range (n + 1))]
  · apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_congr rfl (fun p hp => by rw [(Finset.mem_filter.mp hp).2])]
    rw [Finset.sum_const, nsmul_eq_mul]
  · intro p hp
    rw [Finset.mem_range]
    have hlen := (mem_schroderFinset.mp hp).2
    have hv := valleys_lt_stepLen p
    omega

-- Partition schroderFinset n into empty (n=0), starts with H, starts with U
private lemma schroderRowPoly_zero : schroderRowPoly 0 = 1 := by
  rw [schroderRowPoly_eq_sum]
  have h0 : schroderFinset 0 = {[]} := by
    ext p; simp only [mem_schroderFinset, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hlen⟩
      cases p with
      | nil => rfl
      | cons s l => cases s <;> simp [stepLen] at hlen
    · rintro rfl; simp [isSchroderAux, stepLen]
  rw [h0]; simp [valleys]

private lemma schroderRowPoly_succ (n : ℕ) :
    schroderRowPoly (n + 1) =
      schroderRowPoly n +
        ∑ j ∈ Finset.range (n + 1),
          schroderRowPoly j *
            (if n - j = 0 then 1
             else schroderRowPoly (n - j - 1) +
               Polynomial.X * (schroderRowPoly (n - j) - schroderRowPoly (n - j - 1))) := by
  -- Define U-starting and H-starting subsets of schroderFinset m
  let isH : List SchroderStep → Bool := fun p => match p with | .H :: _ => true | _ => false
  let isU : List SchroderStep → Bool := fun p => match p with | .U :: _ => true | _ => false
  have hH_sum : ∀ m : ℕ,
      ∑ p ∈ (schroderFinset (m + 1)).filter (fun p => isH p = true),
        (Polynomial.X : Polynomial ℤ) ^ valleys p = schroderRowPoly m := by
    intro m
    rw [schroderRowPoly_eq_sum]
    apply Finset.sum_nbij (fun p => p.tail)
    · intro p hp
      simp only [Finset.mem_filter, mem_schroderFinset] at hp ⊢
      cases p with
      | nil => simp [isH] at hp
      | cons s l =>
        cases s with
        | H => exact ⟨hp.1.1, by have h2 := hp.1.2; simp only [stepLen] at h2; dsimp only [List.tail]; omega⟩
        | U => simp [isH] at hp
        | D => simp [isH] at hp
    · intro p1 hp1 p2 hp2 htail
      simp only [Finset.mem_coe, Finset.mem_filter] at hp1 hp2
      cases p1 with
      | nil => simp [isH] at hp1
      | cons s1 l1 =>
        cases p2 with
        | nil => simp [isH] at hp2
        | cons s2 l2 =>
          cases s1 with
          | U => simp [isH] at hp1
          | D => simp [isH] at hp1
          | H =>
            cases s2 with
            | U => simp [isH] at hp2
            | D => simp [isH] at hp2
            | H =>
              dsimp only [List.tail] at htail
              subst htail; rfl
    · intro q hq
      simp only [Finset.mem_coe, mem_schroderFinset] at hq
      refine ⟨.H :: q, ?_, rfl⟩
      simp only [Finset.mem_coe, Finset.mem_filter, mem_schroderFinset]
      exact ⟨⟨hq.1, by simp [stepLen, hq.2]; omega⟩, rfl⟩
    · intro p hp
      simp only [Finset.mem_filter] at hp
      cases p with
      | nil => simp [isH] at hp
      | cons s l =>
        cases s with
        | U => simp [isH] at hp
        | D => simp [isH] at hp
        | H => simp [valleys_H_cons]
  have hHU_part : ∀ m : ℕ,
      schroderFinset (m + 1) =
        (schroderFinset (m + 1)).filter (fun p => isH p = true) ∪
        (schroderFinset (m + 1)).filter (fun p => isU p = true) := by
    intro m; ext p
    simp only [Finset.mem_union, Finset.mem_filter, mem_schroderFinset]
    constructor
    · intro hp
      cases p with
      | nil => simp [stepLen] at hp
      | cons s l =>
        cases s with
        | U => right; exact ⟨hp, rfl⟩
        | H => left; exact ⟨hp, rfl⟩
        | D => simp [isSchroderAux] at hp
    · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
  have hHU_disj : ∀ m : ℕ,
      Disjoint
        ((schroderFinset (m + 1)).filter (fun p => isH p = true))
        ((schroderFinset (m + 1)).filter (fun p => isU p = true)) := by
    intro m; rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_filter] at hp1 hp2
    cases p with
    | nil => simp [isH] at hp1
    | cons s _ => cases s <;> simp [isH, isU] at hp1 hp2
  have hU_sum : ∀ m : ℕ,
      ∑ p ∈ (schroderFinset (m + 1)).filter (fun p => isU p = true),
        (Polynomial.X : Polynomial ℤ) ^ valleys p =
        schroderRowPoly (m + 1) - schroderRowPoly m := by
    intro m
    have htot := schroderRowPoly_eq_sum (m + 1)
    rw [hHU_part m, Finset.sum_union (hHU_disj m), hH_sum m] at htot
    linear_combination -htot
  -- Now evaluate the U-starting sum for n + 1 via first-return bijection!
  have hU_biject :
      ∑ p ∈ (schroderFinset (n + 1)).filter (fun p => isU p = true),
        (Polynomial.X : Polynomial ℤ) ^ valleys p =
      ∑ j ∈ Finset.range (n + 1),
        ∑ a ∈ schroderFinset j, ∑ b ∈ schroderFinset (n - j),
          (Polynomial.X : Polynomial ℤ) ^
            (valleys a + valleys b + (match b with | .U :: _ => 1 | _ => 0)) := by
    -- Bijection between U-starting paths in schroderFinset (n + 1) and
    -- sigma (j in range (n + 1)), schroderFinset j × schroderFinset (n - j)
    let T := (Finset.range (n + 1)).sigma fun j =>
      (schroderFinset j) ×ˢ (schroderFinset (n - j))
    have hT :
        ∑ x ∈ T,
          (Polynomial.X : Polynomial ℤ) ^
            (valleys x.2.1 + valleys x.2.2 + (match x.2.2 with | .U :: _ => 1 | _ => 0)) =
        ∑ j ∈ Finset.range (n + 1),
          ∑ a ∈ schroderFinset j, ∑ b ∈ schroderFinset (n - j),
            (Polynomial.X : Polynomial ℤ) ^
              (valleys a + valleys b + (match b with | .U :: _ => 1 | _ => 0)) := by
      simp only [T, Finset.sum_sigma, Finset.sum_product]
    rw [← hT]
    apply Finset.sum_nbij'
      (fun p =>
        let (a, b) := splitFirstReturn 0 p.tail
        ⟨stepLen a / 2, (a, b)⟩)
      (fun x => .U :: (x.2.1 ++ .D :: x.2.2))
    · intro p hp
      simp only [Finset.mem_filter, mem_schroderFinset] at hp
      cases p with
      | nil => simp [isU] at hp
      | cons s l =>
        cases s <;> simp [isU] at hp
        have hspec := splitFirstReturn_spec 0 l hp.1
        rcases hsp : splitFirstReturn 0 l with ⟨a, b⟩
        rw [hsp] at hspec
        have hlen : stepLen a + stepLen b = 2 * n := by
          have := hp.2
          rw [hspec.1] at this
          simp [stepLen, stepLen_append] at this
          omega
        -- stepLen of a Schroder path is even
        have heven : ∀ q : List SchroderStep, ∀ h : ℕ, isSchroderAux h q → (stepLen q + h) % 2 = 0 := by
          intro q
          induction q with
          | nil => intro h hq; simp [isSchroderAux] at hq; subst hq; simp [stepLen]
          | cons s' l' ih =>
            intro h hq
            cases s' with
            | U => have := ih (h + 1) hq; simp [stepLen]; omega
            | D => have := ih (h - 1) hq.2; have := hq.1; simp [stepLen]; omega
            | H => have := ih h hq; simp [stepLen]; omega
        have ha_even : stepLen a % 2 = 0 := by simpa using heven a 0 hspec.2.1
        have hb_even : stepLen b % 2 = 0 := by simpa using heven b 0 hspec.2.2
        simp only [T, Finset.mem_sigma, Finset.mem_range, Finset.mem_product, mem_schroderFinset,
          List.tail_cons, hsp]
        refine ⟨by omega, ⟨hspec.2.1, by omega⟩, ⟨hspec.2.2, by omega⟩⟩
    · intro x hx
      simp only [T, Finset.mem_sigma, Finset.mem_range, Finset.mem_product, mem_schroderFinset] at hx
      simp only [Finset.mem_filter, mem_schroderFinset]
      refine ⟨⟨?_, ?_⟩, rfl⟩
      · simp only [isSchroderAux]
        rw [isSchroderAux_append 1 x.2.1 (.D :: x.2.2) hx.2.1.1]
        simp [isSchroderAux, hx.2.2.1]
      · simp [stepLen, stepLen_append, hx.2.1.2, hx.2.2.2]; omega
    · intro p hp
      simp only [Finset.mem_filter, mem_schroderFinset] at hp
      cases p with
      | nil => simp [isU] at hp
      | cons s l =>
        cases s <;> simp [isU] at hp
        have hspec := splitFirstReturn_spec 0 l hp.1
        rcases hsp : splitFirstReturn 0 l with ⟨a, b⟩
        rw [hsp] at hspec
        simp only [List.tail_cons, hsp]
        rw [← hspec.1]
    · intro x hx
      rcases x with ⟨j, ⟨a, b⟩⟩
      simp only [T, Finset.mem_sigma, Finset.mem_range, Finset.mem_product, mem_schroderFinset] at hx
      simp only [List.tail_cons, splitFirstReturn_append 0 a b hx.2.1.1, Sigma.mk.inj_iff,
        heq_eq_eq, and_true]
      have := hx.2.1.2
      omega
    · intro p hp
      simp only [Finset.mem_filter, mem_schroderFinset] at hp
      cases p with
      | nil => simp [isU] at hp
      | cons s l =>
        cases s <;> simp [isU] at hp
        have hspec := splitFirstReturn_spec 0 l hp.1
        rcases hsp : splitFirstReturn 0 l with ⟨a, b⟩
        rw [hsp] at hspec
        simp only [List.tail_cons, hsp]
        rw [hspec.1, valleys_U_cons, valleys_append_D, valleys_append_D_nil]
  -- Evaluate the inner sum over b in schroderFinset m
  have hb_sum : ∀ m : ℕ,
      ∑ b ∈ schroderFinset m,
        (Polynomial.X : Polynomial ℤ) ^ (valleys b + (match b with | .U :: _ => 1 | _ => 0)) =
      if m = 0 then 1
      else schroderRowPoly (m - 1) +
        Polynomial.X * (schroderRowPoly m - schroderRowPoly (m - 1)) := by
    intro m
    cases m with
    | zero =>
      simp only [↓reduceIte]
      have h0 : schroderFinset 0 = {[]} := by
        ext p; simp only [mem_schroderFinset, Finset.mem_singleton]
        constructor
        · rintro ⟨_, hlen⟩; cases p with | nil => rfl | cons s _ => cases s <;> simp [stepLen] at hlen
        · rintro rfl; simp [isSchroderAux, stepLen]
      rw [h0]; simp [valleys]
    | succ m' =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [hHU_part m', Finset.sum_union (hHU_disj m')]
      have h1 : ∑ b ∈ (schroderFinset (m' + 1)).filter (fun p => isH p = true),
          (Polynomial.X : Polynomial ℤ) ^ (valleys b + (match b with | .U :: _ => 1 | _ => 0)) =
          schroderRowPoly m' := by
        rw [← hH_sum m']
        apply Finset.sum_congr rfl
        intro b hb
        simp only [Finset.mem_filter] at hb
        cases b with
        | nil => simp [isH] at hb
        | cons s l => cases s <;> simp [isH] at hb; simp
      have h2 : ∑ b ∈ (schroderFinset (m' + 1)).filter (fun p => isU p = true),
          (Polynomial.X : Polynomial ℤ) ^ (valleys b + (match b with | .U :: _ => 1 | _ => 0)) =
          Polynomial.X * (schroderRowPoly (m' + 1) - schroderRowPoly m') := by
        rw [← hU_sum m', Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        simp only [Finset.mem_filter] at hb
        cases b with
        | nil => simp [isU] at hb
        | cons s l => cases s <;> simp [isU] at hb; rw [pow_succ']
      rw [h1, h2]
  have htot := schroderRowPoly_eq_sum (n + 1)
  rw [hHU_part n, Finset.sum_union (hHU_disj n), hH_sum n, hU_biject] at htot
  rw [htot]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hfactor :
      ∑ a ∈ schroderFinset j, ∑ b ∈ schroderFinset (n - j),
        (Polynomial.X : Polynomial ℤ) ^
          (valleys a + valleys b + (match b with | .U :: _ => 1 | _ => 0)) =
      (∑ a ∈ schroderFinset j, (Polynomial.X : Polynomial ℤ) ^ valleys a) *
      (∑ b ∈ schroderFinset (n - j),
        (Polynomial.X : Polynomial ℤ) ^ (valleys b + (match b with | .U :: _ => 1 | _ => 0))) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [add_assoc, pow_add]
  rw [hfactor, ← schroderRowPoly_eq_sum j, hb_sum (n - j)]

-- Part 2: PowerSeries over Polynomial ℤ — Riordan array proof for kurkovR

private abbrev R := Polynomial ℤ
private abbrev PS := PowerSeries R

private noncomputable def narayanaSeq : ℕ → R
  | 0 => 1
  | n + 1 =>
    Polynomial.X * narayanaSeq n +
      ∑ i : Fin (n + 1), narayanaSeq i.1 * narayanaSeq (n - i.1)

private noncomputable def Bseries : PS := PowerSeries.mk narayanaSeq

private lemma Bseries_eq :
    Bseries = 1 + PowerSeries.C Polynomial.X * PowerSeries.X * Bseries +
      PowerSeries.X * (Bseries * Bseries) := by
  ext n
  cases n with
  | zero => simp [Bseries, narayanaSeq]
  | succ n =>
    simp only [Bseries, PowerSeries.coeff_mk, map_add, PowerSeries.coeff_one, Nat.succ_ne_zero,
      ↓reduceIte, zero_add, PowerSeries.coeff_succ_X_mul]
    rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk]
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [PowerSeries.coeff_mk, narayanaSeq]
    congr 1
    rw [← Fin.sum_univ_eq_sum_range (fun i => narayanaSeq i * narayanaSeq (n - i))]

private noncomputable def Sseries : PS := PowerSeries.mk schroderRowPoly

private lemma Sseries_eq :
    Sseries = 1 + PowerSeries.C (2 - Polynomial.X) * PowerSeries.X * Sseries +
      (PowerSeries.C Polynomial.X * PowerSeries.X +
        PowerSeries.C (1 - Polynomial.X) * PowerSeries.X ^ 2) * (Sseries * Sseries) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [Sseries, schroderRowPoly_zero]
  | succ n =>
    have hrec := schroderRowPoly_succ n
    -- Rewrite RHS coefficient of X^(n+1)
    have h1 : PowerSeries.coeff (n + 1)
        (PowerSeries.C (2 - Polynomial.X) * PowerSeries.X * Sseries) =
        (2 - Polynomial.X) * schroderRowPoly n := by
      rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul, Sseries, PowerSeries.coeff_mk]
    have h2 : PowerSeries.coeff (n + 1)
        (PowerSeries.C Polynomial.X * PowerSeries.X * (Sseries * Sseries)) =
        Polynomial.X * ∑ j ∈ Finset.range (n + 1), schroderRowPoly j * schroderRowPoly (n - j) := by
      rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp [Sseries]
    have h3 : PowerSeries.coeff (n + 1)
        (PowerSeries.C (1 - Polynomial.X) * PowerSeries.X ^ 2 * (Sseries * Sseries)) =
        (1 - Polynomial.X) *
          if n = 0 then 0
          else ∑ j ∈ Finset.range n, schroderRowPoly j * schroderRowPoly (n - 1 - j) := by
      rw [mul_assoc, PowerSeries.coeff_C_mul, pow_two, mul_assoc, PowerSeries.coeff_succ_X_mul]
      cases n with
      | zero => simp
      | succ m =>
        simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
        rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        simp [Sseries]
    simp only [add_mul, map_add, PowerSeries.coeff_one, Nat.succ_ne_zero, ↓reduceIte, zero_add,
      h1, h2, h3]
    simp only [Sseries, PowerSeries.coeff_mk]
    rw [hrec]
    -- Split the j = n term from the sum in hrec!
    rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, ↓reduceIte, mul_one]
    have hsplit :
        ∑ j ∈ Finset.range n,
          schroderRowPoly j *
            (if n - j = 0 then 1
             else schroderRowPoly (n - j - 1) +
               Polynomial.X * (schroderRowPoly (n - j) - schroderRowPoly (n - j - 1))) =
        (1 - Polynomial.X) * (∑ j ∈ Finset.range n, schroderRowPoly j * schroderRowPoly (n - 1 - j)) +
        Polynomial.X * (∑ j ∈ Finset.range n, schroderRowPoly j * schroderRowPoly (n - j)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      have hlt : j < n := Finset.mem_range.mp hj
      have hne : n - j ≠ 0 := by omega
      have hsub : n - j - 1 = n - 1 - j := by omega
      simp only [hne, ↓reduceIte, hsub]
      ring
    rw [hsplit]
    cases n with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, ↓reduceIte, schroderRowPoly_zero,
        Nat.zero_add, Finset.range_one, Finset.sum_singleton, Nat.sub_self]
      ring
    | succ m =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [Finset.sum_range_succ (fun j => schroderRowPoly j * schroderRowPoly (m + 1 - j)) (m + 1)]
      simp only [Nat.sub_self, schroderRowPoly_zero, mul_one]
      ring

private lemma one_sub_X_sub_XB_mul_S :
    (1 - PowerSeries.X - PowerSeries.X * Bseries) * Sseries = 1 := by
  -- Define S' = inv(1 - X - X * B) and show S' satisfies the same quadratic equation as Sseries!
  have hu : IsUnit (1 - PowerSeries.X - PowerSeries.X * Bseries : PS) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simp
  obtain ⟨u, hu_eq⟩ := hu
  let S' : PS := ↑u⁻¹
  have hS'_mul : (1 - PowerSeries.X - PowerSeries.X * Bseries) * S' = 1 := by
    rw [← hu_eq]; exact Units.mul_inv u
  have hXB : PowerSeries.X * Bseries * S' = (1 - PowerSeries.X) * S' - 1 := by
    linear_combination -hS'_mul
  have hB_quad : (PowerSeries.X * Bseries) ^ 2 -
      (1 - PowerSeries.C Polynomial.X * PowerSeries.X) * (PowerSeries.X * Bseries) +
      PowerSeries.X = 0 := by
    have h1 := congr_arg (PowerSeries.X * ·) Bseries_eq
    linear_combination -h1
  have hS'_eq :
      S' = 1 + PowerSeries.C (2 - Polynomial.X) * PowerSeries.X * S' +
        (PowerSeries.C Polynomial.X * PowerSeries.X +
          PowerSeries.C (1 - Polynomial.X) * PowerSeries.X ^ 2) * (S' * S') := by
    have hmul := congr_arg (· * (S' * S')) hB_quad
    simp only [zero_mul] at hmul
    have hC1 : PowerSeries.C (2 - Polynomial.X : R) = 2 - PowerSeries.C Polynomial.X := by
      rw [map_sub, map_ofNat]
    have hC2 : PowerSeries.C (1 - Polynomial.X : R) = 1 - PowerSeries.C Polynomial.X := by
      rw [map_sub, map_one]
    rw [hC1, hC2]
    linear_combination -hmul + ((PowerSeries.X * Bseries * S') + (1 - PowerSeries.X) * S' - 1) * hXB -
      (1 - PowerSeries.C Polynomial.X * PowerSeries.X) * S' * hXB
  -- Now prove Sseries = S' by strong induction on n!
  have hEq : Sseries = S' := by
    apply PowerSeries.ext
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero =>
        have h0 := congr_arg (PowerSeries.coeff 0) hS'_eq
        simp [Sseries, schroderRowPoly_zero] at h0 ⊢
        exact h0.symm
      | succ m =>
        have hS1 := congr_arg (PowerSeries.coeff (m + 1)) Sseries_eq
        have hS2 := congr_arg (PowerSeries.coeff (m + 1)) hS'_eq
        rw [hS1, hS2]
        simp only [add_mul, map_add, PowerSeries.coeff_one, Nat.succ_ne_zero, ↓reduceIte, zero_add]
        have hlin : PowerSeries.coeff (m + 1)
            (PowerSeries.C (2 - Polynomial.X) * PowerSeries.X * Sseries) =
            PowerSeries.coeff (m + 1)
            (PowerSeries.C (2 - Polynomial.X) * PowerSeries.X * S') := by
          rw [mul_assoc, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
            PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul, ih m (by omega)]
        have hq1 : PowerSeries.coeff (m + 1)
            (PowerSeries.C Polynomial.X * PowerSeries.X * (Sseries * Sseries)) =
            PowerSeries.coeff (m + 1)
            (PowerSeries.C Polynomial.X * PowerSeries.X * (S' * S')) := by
          rw [mul_assoc, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
            PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul,
            PowerSeries.coeff_mul, PowerSeries.coeff_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
          congr 1
          apply Finset.sum_congr rfl
          intro j hj
          have hjm : j < m + 1 := Finset.mem_range.mp hj
          rw [ih j hjm, ih (m - j) (by omega)]
        have hq2 : PowerSeries.coeff (m + 1)
            (PowerSeries.C (1 - Polynomial.X) * PowerSeries.X ^ 2 * (Sseries * Sseries)) =
            PowerSeries.coeff (m + 1)
            (PowerSeries.C (1 - Polynomial.X) * PowerSeries.X ^ 2 * (S' * S')) := by
          rw [mul_assoc, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
            pow_two, mul_assoc, mul_assoc, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul]
          cases m with
          | zero => simp
          | succ m' =>
            rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul,
              PowerSeries.coeff_mul, PowerSeries.coeff_mul,
              Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
              Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
            congr 1
            apply Finset.sum_congr rfl
            intro j hj
            have hjm : j < m' + 1 := Finset.mem_range.mp hj
            rw [ih j (by omega), ih (m' - j) (by omega)]
        rw [hlin, hq1, hq2]
  rw [hEq]
  exact hS'_mul

private noncomputable def G0 : PS := 1 + PowerSeries.X * Sseries

private noncomputable def Gseries (k : ℕ) : PS := G0 * Bseries ^ k

private noncomputable def R' (n k : ℕ) : R :=
  if k ≤ n then PowerSeries.coeff (n - k) (Gseries k) else 0

private lemma G0_recur : G0 = 1 + PowerSeries.X * (G0 + PowerSeries.X * Bseries * G0) → True :=
  fun _ => trivial

private lemma G0_eq_sum : (1 - PowerSeries.X * Bseries) * G0 = 1 - PowerSeries.X * Bseries + PowerSeries.X * G0 := by
  have h1 := one_sub_X_sub_XB_mul_S
  dsimp only [G0]
  linear_combination PowerSeries.X * h1

private lemma Gseries_step (k : ℕ) :
    Gseries (k + 1) - PowerSeries.X * Gseries (k + 2) =
      Gseries k + PowerSeries.C Polynomial.X * PowerSeries.X * Gseries (k + 1) := by
  dsimp only [Gseries]
  have hB := Bseries_eq
  have hpow : Bseries ^ (k + 2) = Bseries ^ k * (Bseries * Bseries) := by ring
  have hpow1 : Bseries ^ (k + 1) = Bseries ^ k * Bseries := by ring
  rw [hpow, hpow1]
  linear_combination G0 * Bseries ^ k * hB

private lemma R'_diag (n : ℕ) : R' n n = 1 := by
  simp only [R', le_refl, ↓reduceIte, Nat.sub_self, Gseries, G0, map_mul, map_pow,
    PowerSeries.coeff_zero_eq_constantCoeff, map_add, map_one, PowerSeries.constantCoeff_X,
    zero_mul, add_zero, Bseries, PowerSeries.constantCoeff_mk, narayanaSeq, one_pow, mul_one]

private lemma R'_zero_succ (m : ℕ) :
    R' (m + 1) 0 = ∑ j ∈ Finset.range (m + 1), R' m j := by
  -- From (1 - X*B)*G0 = 1 - X*B + X*G0, we get:
  -- G0 - 1 = X * G0 / (1 - X*B), i.e., (1 - X*B) * (G0 - 1) = X * G0!
  -- Actually, prove directly: coeff (m+1) G0 = ∑_{j=0..m} coeff (m-j) (G0 * B^j)
  -- via telescoping (1 - X*B) * ∑_{j=0..m} X^j * G0 * B^j = G0 - X^(m+1) * G0 * B^(m+1)!
  have htele :
      (1 - PowerSeries.X * Bseries) *
        (∑ j ∈ Finset.range (m + 1), PowerSeries.X ^ j * Gseries j) =
      G0 - PowerSeries.X ^ (m + 1) * Gseries (m + 1) := by
    induction m with
    | zero =>
      simp only [Nat.zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, one_mul, Gseries,
        pow_one]
      ring
    | succ m ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      dsimp only [Gseries]
      ring
  -- Also (1 - X*B) * (G0 - 1) = X * G0!
  have hG0 : (1 - PowerSeries.X * Bseries) * (G0 - 1) = PowerSeries.X * G0 := by
    linear_combination G0_eq_sum
  -- Multiply htele by X: (1 - X*B) * X * ∑ ... = X * G0 - X^(m+2) * G_{m+1}
  -- So (1 - X*B) * (G0 - 1 - X * ∑ ...) = X^(m+2) * G_{m+1}!
  have hdiff :
      (1 - PowerSeries.X * Bseries) *
        (G0 - 1 - PowerSeries.X * ∑ j ∈ Finset.range (m + 1), PowerSeries.X ^ j * Gseries j) =
      PowerSeries.X ^ (m + 2) * Gseries (m + 1) := by
    linear_combination hG0 - PowerSeries.X * htele
  -- Since (1 - X*B) has constant coeff 1, coeff k of (G0 - 1 - X*∑) is 0 for all k <= m + 1!
  have hzero : ∀ k ≤ m + 1,
      PowerSeries.coeff k
        (G0 - 1 - PowerSeries.X * ∑ j ∈ Finset.range (m + 1), PowerSeries.X ^ j * Gseries j) = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      have hc := congr_arg (PowerSeries.coeff k) hdiff
      have hrhs : PowerSeries.coeff k (PowerSeries.X ^ (m + 2) * Gseries (m + 1)) = 0 := by
        rw [PowerSeries.coeff_X_pow_mul']
        simp [show ¬(m + 2 ≤ k) by omega]
      rw [hrhs] at hc
      rw [sub_mul, one_mul, map_sub] at hc
      have hterm : PowerSeries.coeff k
          (PowerSeries.X * Bseries *
            (G0 - 1 - PowerSeries.X * ∑ j ∈ Finset.range (m + 1), PowerSeries.X ^ j * Gseries j)) = 0 := by
        rw [mul_assoc]
        cases k with
        | zero => simp
        | succ k' =>
          rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
          apply Finset.sum_eq_zero
          intro j hj
          have hjk : j < k' + 1 := Finset.mem_range.mp hj
          rw [ih (k' - j) (by omega) (by omega), mul_zero]
      rw [hterm, sub_zero] at hc
      exact hc
  have hm1 := hzero (m + 1) (le_refl _)
  simp only [map_sub, PowerSeries.coeff_one, Nat.succ_ne_zero, ↓reduceIte, sub_zero,
    PowerSeries.coeff_succ_X_mul, map_sum, sub_eq_zero] at hm1
  simp only [R', Nat.zero_le, ↓reduceIte, Nat.sub_zero, Gseries, pow_zero, mul_one]
  rw [hm1]
  apply Finset.sum_congr rfl
  intro j hj
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  simp only [hjm, ↓reduceIte, PowerSeries.coeff_X_pow_mul', Gseries]

private lemma R'_step (m k : ℕ) (hk1 : 1 ≤ k) (hkm : k ≤ m) :
    R' (m + 1) k - R' (m + 1) (k + 1) =
      R' m (k - 1) + Polynomial.X * R' m k := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hc := congr_arg (PowerSeries.coeff (m - k')) (Gseries_step k')
  simp only [map_sub, map_add] at hc
  rw [mul_assoc, PowerSeries.coeff_C_mul] at hc
  obtain ⟨d, hd⟩ : ∃ d, m - k' = d + 1 := ⟨m - k' - 1, by omega⟩
  rw [hd, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul] at hc
  simp only [R', show k' + 1 ≤ m + 1 by omega, show k' + 1 + 1 ≤ m + 1 by omega,
    show k' ≤ m by omega, show k' + 1 ≤ m by omega, ↓reduceIte,
    show m + 1 - (k' + 1) = d + 1 by omega,
    show m + 1 - (k' + 1 + 1) = d by omega,
    show k' + 1 - 1 = k' by omega,
    show m - k' = d + 1 by omega,
    show m - (k' + 1) = d by omega]
  exact hc

private lemma R'_inner (m k : ℕ) (hk1 : 1 ≤ k) (hkm : k ≤ m) :
    R' (m + 1) k =
      R' m (k - 1) +
        (Polynomial.X + 1) * (R' (m + 1) 0 - ∑ j ∈ Finset.range k, R' m j) := by
  -- Induction downward from k = m to k = 1!
  have hsum_tail : R' (m + 1) 0 - ∑ j ∈ Finset.range k, R' m j =
      ∑ j ∈ Finset.Ico k (m + 1), R' m j := by
    rw [R'_zero_succ m]
    have hsplit : ∑ j ∈ Finset.range (m + 1), R' m j =
        ∑ j ∈ Finset.range k, R' m j + ∑ j ∈ Finset.Ico k (m + 1), R' m j := by
      rw [← Finset.sum_union]
      · congr 1; ext j; simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]; omega
      · rw [Finset.disjoint_left]; intro j h1 h2
        simp only [Finset.mem_range, Finset.mem_Ico] at h1 h2; omega
    linear_combination hsplit
  rw [hsum_tail]
  -- Prove by induction on d = m - k
  have aux : ∀ d : ℕ, ∀ k : ℕ, 1 ≤ k → k + d = m →
      R' (m + 1) k = R' m (k - 1) + (Polynomial.X + 1) * ∑ j ∈ Finset.Ico k (m + 1), R' m j := by
    intro d
    induction d with
    | zero =>
      intro k hk1 hkm'
      have hk_eq : k = m := by omega
      rw [hk_eq]
      have hstep := R'_step m m (by omega) (le_refl m)
      rw [R'_diag (m + 1), R'_diag m] at hstep
      have hIco : Finset.Ico m (m + 1) = {m} := by
        ext j; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
      rw [hIco, Finset.sum_singleton, R'_diag m]
      linear_combination hstep
    | succ d ih =>
      intro k hk1 hkm'
      have hstep := R'_step m k hk1 (by omega)
      have hnext := ih (k + 1) (by omega) (by omega)
      have hIco : ∑ j ∈ Finset.Ico k (m + 1), R' m j =
          R' m k + ∑ j ∈ Finset.Ico (k + 1) (m + 1), R' m j := by
        rw [← Finset.sum_Ico_consecutive (f := fun j => R' m j) (show k ≤ k + 1 by omega)
          (show k + 1 ≤ m + 1 by omega)]
        have h1 : Finset.Ico k (k + 1) = {k} := by
          ext j; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
        rw [h1, Finset.sum_singleton]
      rw [hIco]
      simp only [Nat.add_sub_cancel] at hnext
      linear_combination hstep + hnext
  exact aux (m - k) k hk1 (by omega)

private lemma kurkovR_eq_R' : ∀ n k : ℕ, kurkovR n k = R' n k := by
  intro n
  induction n with
  | zero =>
    intro k
    rw [kurkovR]
    by_cases h0 : k = 0
    · subst h0; simp [R'_diag]
    · simp [h0, R', show ¬(k ≤ 0) by omega]
  | succ m ih =>
    have h0 : kurkovR (m + 1) 0 = R' (m + 1) 0 := by
      rw [kurkovR]
      simp only [Nat.zero_ne_add_one, ↓reduceIte, R'_zero_succ]
      apply Finset.sum_congr rfl
      intro j _
      exact ih j
    intro k
    by_cases hkn : k = m + 1
    · subst hkn; rw [kurkovR]; simp [R'_diag]
    · by_cases hk0 : k = 0
      · subst hk0; exact h0
      · by_cases hklt : k < m + 1
        · rw [kurkovR]
          simp only [hkn, hk0, hklt, ↓reduceIte, h0, ih (k - 1)]
          have hsum : ∑ j ∈ Finset.range k, kurkovR m j = ∑ j ∈ Finset.range k, R' m j :=
            Finset.sum_congr rfl fun j _ => ih j
          rw [hsum]
          exact (R'_inner m k (by omega) (by omega)).symm
        · rw [kurkovR]
          simp [hkn, hk0, hklt, R', show ¬(k ≤ m + 1) by omega]

private theorem main_proved :
    ∀ n : ℕ, schroderRowPoly n = kurkovR (n + 1) 0 := by
  intro n
  rw [kurkovR_eq_R']
  simp only [R', Nat.zero_le, ↓reduceIte, Nat.sub_zero, Gseries, pow_zero, mul_one, G0,
    map_add, PowerSeries.coeff_one, Nat.succ_ne_zero, zero_add, PowerSeries.coeff_succ_X_mul,
    Sseries, PowerSeries.coeff_mk]

end OMA.P_oeis_a101282

theorem OMA.solution : type_of% @OMA.S_oeis_a101282.main :=
  OMA.P_oeis_a101282.main_proved
