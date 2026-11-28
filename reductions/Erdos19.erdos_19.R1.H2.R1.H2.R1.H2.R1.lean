import OMAReductions.R_Erdos19_erdos_19_R1_H2_R1_H2_R1

/-!
# Reduction of `Erdos19.erdos_19.R1.H2.R1.H2.R1.H2` (dual sign-domain stars & 5-edge augmentation)

From the zero-mass linear dependence `g` supported on `univ.image L` (`∑ g = 0`, `g|_U = 0`),
we prove unconditionally:

1. **Five-edge augmenting path** (`E19DualStar.augment5`): any disjoint pair `(L i, L j)` whose
   mates `(R i, R j)` are disjoint from distinct unmatched supports `x, y ∈ U` augments the
   matching from `m` to `m + 1`.
2. **Dual sign-domain star extraction** (`E19DualStar.sign_domain_star`): both the positive sign
   domain `P = {i : 0 < g (L i)}` and the negative sign domain `Q = {i : g (L i) < 0}` are
   disjoint, satisfy `2 * (r - 1) ≤ |P|` and `2 * (r - 1) ≤ |Q|`, and contain maximizers `i₀ ∈ P`
   and `j₀ ∈ Q` whose disjointness stars `S_P ⊆ P` and `S_Q ⊆ Q` each have size at least `r ≥ 3`.
3. **Star synchronization & cross-star exclusion** (`E19DualStar.star_sync`): eliminating all
   5-edge augmenting paths forces either a dead mate `R i` meeting every `x ∈ U` (paired with a
   disjoint partner `L j` in the same sign domain), OR dual synchronized stars `(S_P, x_P)` and
   `(S_Q, x_Q)` where every mate in `S_P` (resp. `S_Q`) is disjoint from `U` uniquely at `x_P`
   (resp. `x_Q`), the mates within each star are pairwise intersecting, and if `x_P ≠ x_Q` then
   every left support in `S_P` intersects every left support in `S_Q`.

Splits `H2` cleanly into `H1` (dead mate in `P` or `Q`) and `H2` (dual synchronized stars).
-/

section

open Finset
open scoped Classical

namespace E19DualStar

/-- Five-edge alternating path augmentation from `x ∈ U` through `(R i, L i)` and `(L j, R j)` to `y ∈ U`. -/
theorem augment5 {V : Type*} [DecidableEq V] (K : Finset (Finset V)) {m : ℕ}
    (L R : Fin m → Finset V) (lK : ∀ k, L k ∈ K) (rK : ∀ k, R k ∈ K)
    (il : Function.Injective L) (ir : Function.Injective R)
    (apart : ∀ a b, L a ≠ R b) (matched : ∀ k, Disjoint (L k) (R k))
    (i j : Fin m) (ij : i ≠ j) (x y : Finset V) (xK : x ∈ K) (yK : y ∈ K)
    (xy : x ≠ y) (xl : ∀ k, x ≠ L k) (xr : ∀ k, x ≠ R k)
    (yl : ∀ k, y ≠ L k) (yr : ∀ k, y ≠ R k)
    (first : Disjoint x (R i)) (middle : Disjoint (L i) (L j)) (last : Disjoint y (R j)) :
    ∃ l r : Fin (m + 1) → Finset V, (∀ k, l k ∈ K) ∧ (∀ k, r k ∈ K) ∧
      Function.Injective l ∧ Function.Injective r ∧ (∀ a b, l a ≠ r b) ∧
      ∀ k, Disjoint (l k) (r k) := by
  let g (k : Fin m) := if k = i then x else if k = j then y else L k
  have gi : Function.Injective g := by
    intro a b h
    dsimp [g] at h
    split_ifs at h <;> grind
  have fresh (k : Fin m) : L i ≠ g k ∧ L j ≠ g k := by
    dsimp [g]
    split_ifs <;> grind
  have home (k : Fin m) : g k ∈ K := by dsimp [g]; split_ifs <;> grind
  have sep (a b : Fin m) : g a ≠ R b := by dsimp [g]; split_ifs <;> grind
  have good (k : Fin m) : Disjoint (g k) (R k) := by dsimp [g]; split_ifs <;> grind
  refine ⟨Fin.cons (L i) g, Fin.cons (L j) R, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Fin.cases (lK i) home
  · exact Fin.cases (lK j) rK
  · intro a b
    refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b <;>
      simp [Fin.cons_zero, Fin.cons_succ, gi.eq_iff, (fresh _).1, Ne.symm (fresh _).1]
  · intro a b
    refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b <;>
      simp [Fin.cons_zero, Fin.cons_succ, ir.eq_iff, apart, fun k => Ne.symm (apart j k)]
  · intro a b
    refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b <;>
      simp [Fin.cons_zero, Fin.cons_succ, il.ne ij, apart, fun k => Ne.symm (fresh k).2, sep]
  · exact Fin.cases middle good

/-- No three pairwise disjoint members of `K` implies any two members disjoint from a common third intersect. -/
lemma not_disjoint_of_common_disj {n : ℕ} {K : Finset (Finset (Fin n))}
    (hsize : ∀ A ∈ K, 1 ≤ A.card)
    (noThree : ¬ ∃ T ⊆ K, T.card = 3 ∧ ∀ A ∈ T, ∀ B ∈ T, A ≠ B → Disjoint A B)
    {X A B : Finset (Fin n)} (hX : X ∈ K) (hA : A ∈ K) (hB : B ∈ K)
    (hXA : Disjoint X A) (hXB : Disjoint X B) : ¬ Disjoint A B := by
  intro hAB
  have hne_self : ∀ C ∈ K, ¬ Disjoint C C := fun C hC hd => by
    have he : C = ∅ := disjoint_self.mp hd
    have h1 := hsize C hC
    rw [he, Finset.card_empty] at h1
    omega
  have hXAne : X ≠ A := fun h => hne_self X hX (h ▸ hXA)
  have hXBne : X ≠ B := fun h => hne_self X hX (h ▸ hXB)
  have hABne : A ≠ B := fun h => hne_self A hA (h ▸ hAB)
  apply noThree
  refine ⟨{X, A, B}, ?_, ?_, ?_⟩
  · intro Z hZ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hZ
    rcases hZ with rfl | rfl | rfl <;> assumption
  · rw [Finset.card_insert_of_notMem (by simp [hXAne, hXBne]),
        Finset.card_insert_of_notMem (by simp [hABne]), Finset.card_singleton]
  · intro Y hY Z hZ hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hY hZ
    rcases hY with rfl | rfl | rfl <;> rcases hZ with rfl | rfl | rfl <;>
      first | exact (hne rfl).elim | exact hXA | exact hXA.symm | exact hXB | exact hXB.symm | exact hAB | exact hAB.symm

/-- From a zero-sum row-equation vector `f : Fin m → ℝ`, extract a positive sign domain `P` of size
at least `2 * (r - 1)` and a maximizer `i₀ ∈ P` whose disjointness star `S ⊆ P` has size at least `r`. -/
theorem sign_domain_star {n r m : ℕ} (hr : 3 ≤ r) (K : Finset (Finset (Fin n)))
    (L : Fin m → Finset (Fin n)) (hL : ∀ i, L i ∈ K)
    (hsize : ∀ A ∈ K, r ≤ A.card)
    (noThree : ¬ ∃ T ⊆ K, T.card = 3 ∧ ∀ A ∈ T, ∀ B ∈ T, A ≠ B → Disjoint A B)
    (f : Fin m → ℝ) (hnz : ∃ i, f i ≠ 0) (hsum0 : ∑ i, f i = 0)
    (hrow : ∀ i : Fin m, ((L i).card - 1 : ℝ) * f i = ∑ j ∈ Finset.univ.filter (fun j => Disjoint (L i) (L j)), f j) :
    let P := Finset.univ.filter (fun i : Fin m => 0 < f i)
    2 * (r - 1) ≤ P.card ∧
    ∃ (S : Finset (Fin m)) (i₀ : Fin m),
      i₀ ∈ S ∧ S ⊆ P ∧ r ≤ S.card ∧ ∀ a ∈ S, a ≠ i₀ → Disjoint (L i₀) (L a) := by
  intro P
  have hPne : P.Nonempty := by
    by_contra h
    have hall : ∀ i, f i ≤ 0 := fun i => by
      by_contra hpos; push Not at hpos
      exact h ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos⟩⟩
    obtain ⟨i, hi⟩ := hnz
    have hlt : f i < 0 := lt_of_le_of_ne (hall i) hi
    have hle : ∑ j ∈ Finset.univ.erase i, f j ≤ 0 := Finset.sum_nonpos fun j _ => hall j
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hsum0
    linarith
  have htri : ∀ i ∈ P, ∀ j ∈ P, ∀ k ∈ P, Disjoint (L i) (L j) → Disjoint (L i) (L k) → ¬ Disjoint (L j) (L k) :=
    fun i _ j _ k _ hij hik =>
      not_disjoint_of_common_disj (fun A hA => by have := hsize A hA; omega) noThree (hL i) (hL j) (hL k) hij hik
  have hProw : ∀ i ∈ P, (0 : ℝ) + ((r - 1 : ℕ) : ℝ) * f i ≤ ∑ j ∈ P.filter (fun j => Disjoint (L i) (L j)), f j := by
    intro i hi
    have hfi : 0 < f i := (Finset.mem_filter.mp hi).2
    have hri : ((r - 1 : ℕ) : ℝ) ≤ (L i).card - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
      have : (r : ℝ) ≤ (L i).card := by exact_mod_cast hsize (L i) (hL i)
      linarith
    have h1 : ((r - 1 : ℕ) : ℝ) * f i ≤ ((L i).card - 1 : ℝ) * f i :=
      mul_le_mul_of_nonneg_right hri hfi.le
    have h2 : ∑ j ∈ Finset.univ.filter (fun j => Disjoint (L i) (L j)), f j ≤
        ∑ j ∈ P.filter (fun j => Disjoint (L i) (L j)), f j := by
      have hcap := Finset.sum_le_sum (s := Finset.univ.filter (fun j => Disjoint (L i) (L j)))
        (fun j _ => show f j ≤ if 0 < f j then f j else 0 by split_ifs <;> linarith)
      rw [← Finset.sum_filter] at hcap
      have heq : (Finset.univ.filter (fun j => Disjoint (L i) (L j))).filter (fun j => 0 < f j) =
          P.filter (fun j => Disjoint (L i) (L j)) := by
        ext j; simp [P, and_comm]
      rwa [heq] at hcap
    linarith [hrow i]
  have hPcard : 2 * (r - 1) ≤ P.card := by
    have hb := (E19Signs.sign_count P (fun i j => Disjoint (L i) (L j)) htri f
      (fun i hi => (Finset.mem_filter.mp hi).2) hPne ((r - 1 : ℕ) : ℝ) 0
      (by exact_mod_cast (by omega : 0 < r - 1)) le_rfl (by intro i hi; convert hProw i hi)).1
    exact_mod_cast hb
  obtain ⟨i₀, hi₀P, hmax⟩ := Finset.exists_max_image P f hPne
  have hfi₀ : 0 < f i₀ := (Finset.mem_filter.mp hi₀P).2
  let N := P.filter (fun j => Disjoint (L i₀) (L j))
  have hNcard : r - 1 ≤ N.card := by
    have hlow := hProw i₀ hi₀P
    have hup : ∑ j ∈ N, f j ≤ (N.card : ℝ) * f i₀ := by
      calc ∑ j ∈ N, f j ≤ ∑ _j ∈ N, f i₀ := Finset.sum_le_sum fun j hj => hmax j (Finset.mem_filter.mp hj).1
        _ = (N.card : ℝ) * f i₀ := by rw [Finset.sum_const, nsmul_eq_mul]
    have hle : ((r - 1 : ℕ) : ℝ) * f i₀ ≤ (N.card : ℝ) * f i₀ := by linarith
    have hle' : ((r - 1 : ℕ) : ℝ) ≤ (N.card : ℝ) := le_of_mul_le_mul_right hle hfi₀
    exact_mod_cast hle'
  have hi₀_notN : i₀ ∉ N := by
    intro hm
    have hd := (Finset.mem_filter.mp hm).2
    have he : L i₀ = ∅ := disjoint_self.mp hd
    have h1 := hsize (L i₀) (hL i₀)
    rw [he, Finset.card_empty] at h1
    omega
  refine ⟨hPcard, insert i₀ N, i₀, Finset.mem_insert_self _ _, ?_, ?_, ?_⟩
  · exact Finset.insert_subset hi₀P (Finset.filter_subset _ _)
  · rw [Finset.card_insert_of_notMem hi₀_notN]; omega
  · intro a ha hne
    exact (Finset.mem_filter.mp ((Finset.mem_insert.mp ha).resolve_left hne)).2

/-- On any star `(S, c)` of size `≥ 2` (`∀ a ∈ S, a ≠ c → Disjoint (L c) (L a)`), either a 5-edge
augmenting path exists, OR some mate `R a` (`a ∈ S`) meets all of `U`, OR all mates in `S` share
the exact same unique disjoint unmatched support `x ∈ U` and are pairwise intersecting. -/
theorem star_sync {n : ℕ} (K U : Finset (Finset (Fin n))) {m : ℕ}
    (L R : Fin m → Finset (Fin n)) (hL : ∀ i, L i ∈ K) (hR : ∀ i, R i ∈ K)
    (injL : Function.Injective L) (injR : Function.Injective R)
    (apart : ∀ i j, L i ≠ R j) (matched : ∀ i, Disjoint (L i) (R i))
    (subU : U ⊆ K) (disU : ∀ i, L i ∉ U) (disR : ∀ i, R i ∉ U)
    (hsize : ∀ A ∈ K, 1 ≤ A.card)
    (noThree : ¬ ∃ T ⊆ K, T.card = 3 ∧ ∀ A ∈ T, ∀ B ∈ T, A ≠ B → Disjoint A B)
    (S : Finset (Fin m)) (c : Fin m) (hcS : c ∈ S) (hS2 : 2 ≤ S.card)
    (hstar : ∀ a ∈ S, a ≠ c → Disjoint (L c) (L a)) :
    (∃ l r' : Fin (m + 1) → Finset (Fin n), (∀ i, l i ∈ K) ∧ (∀ i, r' i ∈ K) ∧
      Function.Injective l ∧ Function.Injective r' ∧ (∀ i j, l i ≠ r' j) ∧ ∀ i, Disjoint (l i) (r' i)) ∨
    (∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ Disjoint (L a) (L b) ∧ ∀ x ∈ U, ¬ Disjoint x (R a)) ∨
    (∃ x ∈ U, (∀ a ∈ S, ∀ y ∈ U, Disjoint y (R a) ↔ y = x) ∧
      ∀ a ∈ S, ∀ b ∈ S, ¬ Disjoint (R a) (R b)) := by
  by_cases hdead : ∃ a ∈ S, ∀ x ∈ U, ¬ Disjoint x (R a)
  · obtain ⟨a, haS, hadead⟩ := hdead
    right; left
    by_cases hac : a = c
    · subst a
      have hpos : 0 < (S.erase c).card := by rw [Finset.card_erase_of_mem hcS]; omega
      obtain ⟨b, hb⟩ := Finset.card_pos.mp hpos
      obtain ⟨hbc, hbS⟩ := Finset.mem_erase.mp hb
      exact ⟨c, hcS, b, hbS, hbc.symm, hstar b hbS hbc, hadead⟩
    · exact ⟨a, haS, c, hcS, hac, (hstar a haS hac).symm, hadead⟩
  · push Not at hdead
    obtain ⟨x, hxU, hxRc⟩ := hdead c hcS
    by_cases hother : ∃ a ∈ S, a ≠ c ∧ ∃ y ∈ U, y ≠ x ∧ Disjoint y (R a)
    · obtain ⟨a, haS, hac, y, hyU, hyx, hyRa⟩ := hother
      left
      exact augment5 K L R hL hR injL injR apart matched c a hac.symm x y
        (subU hxU) (subU hyU) hyx.symm
        (fun k he => disU k (he ▸ hxU)) (fun k he => disR k (he ▸ hxU))
        (fun k he => disU k (he ▸ hyU)) (fun k he => disR k (he ▸ hyU))
        hxRc (hstar a haS hac) hyRa
    · push Not at hother
      have hother_x : ∀ a ∈ S, a ≠ c → Disjoint x (R a) := by
        intro a haS hac
        obtain ⟨y, hyU, hyRa⟩ := hdead a haS
        have hyx : y = x := by
          by_contra hne; exact hother a haS hac y hyU hne hyRa
        exact hyx ▸ hyRa
      by_cases hc2 : ∃ y ∈ U, y ≠ x ∧ Disjoint y (R c)
      · obtain ⟨y, hyU, hyx, hyRc⟩ := hc2
        have hpos : 0 < (S.erase c).card := by rw [Finset.card_erase_of_mem hcS]; omega
        obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
        obtain ⟨hac, haS⟩ := Finset.mem_erase.mp ha
        left
        exact augment5 K L R hL hR injL injR apart matched c a hac.symm y x
          (subU hyU) (subU hxU) hyx
          (fun k he => disU k (he ▸ hyU)) (fun k he => disR k (he ▸ hyU))
          (fun k he => disU k (he ▸ hxU)) (fun k he => disR k (he ▸ hxU))
          hyRc (hstar a haS hac) (hother_x a haS hac)
      · push Not at hc2
        right; right
        have hsync : ∀ a ∈ S, ∀ y ∈ U, Disjoint y (R a) ↔ y = x := by
          intro a haS y hyU
          constructor
          · intro hyRa
            by_cases hac : a = c
            · subst a; by_contra hne; exact hc2 y hyU hne hyRa
            · by_contra hne; exact hother a haS hac y hyU hne hyRa
          · rintro rfl
            by_cases hac : a = c
            · subst a; exact hxRc
            · exact hother_x a haS hac
        refine ⟨x, hxU, hsync, fun a haS b hbS => ?_⟩
        exact not_disjoint_of_common_disj hsize noThree (subU hxU) (hR a) (hR b)
          ((hsync a haS x hxU).mpr rfl) ((hsync b hbS x hxU).mpr rfl)

end E19DualStar

end

namespace OMA.R_Erdos19_erdos_19_R1_H2_R1_H2_R1_H2_R1

open Finset
open scoped Classical

/-- H1: Dead mate inside a disjointness star of size `≥ r` in one of the sign domains. -/
def H1 : Prop := ∀ (n r : ℕ) (K : Finset (Finset (Fin n))), 3 ≤ r → r * r + r - 1 ≤ n →
    n ≤ r * ((n - r) / (r - 1)) → (∃ T ∈ K, T.card = r) → (∀ A ∈ K, r ≤ A.card) →
    (∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).card ≤ 1) →
    (∀ T ∈ K, n ≤ ((K.erase T).filter fun A => (T ∩ A).Nonempty).card) →
    3 ≤ (K.filter fun A => 3 ≤ A.card).card →
    (¬ ∃ e : Fin n ≃ Fin n, ∀ A ∈ K.image (Finset.map e.toEmbedding),
      3 ≤ A.card → ∃ l r : Fin n, A = Finset.Icc l r) →
    (¬ ∃ L R : Finset (Finset (Fin n)), L ∪ R = K ∧ Disjoint L R ∧
      (∀ A ∈ L, ∀ B ∈ L, A ≠ B → (A ∩ B).Nonempty) ∧ (∀ A ∈ R, ∀ B ∈ R, A ≠ B → (A ∩ B).Nonempty)) →
    (¬ ∃ T ⊆ K, T.card = 3 ∧ ∀ A ∈ T, ∀ B ∈ T, A ≠ B → Disjoint A B) →
    ∀ (m : ℕ) (L R : Fin m → Finset (Fin n)) (U : Finset (Finset (Fin n))),
    (∀ i, L i ∈ K) → (∀ i, R i ∈ K) → Function.Injective L → Function.Injective R →
    (∀ i j, L i ≠ R j) → (∀ i, Disjoint (L i) (R i)) → U ⊆ K →
    (∀ A ∈ U, ∀ B ∈ U, ¬ Disjoint A B) → (∀ i, ∀ A ∈ U, ¬ Disjoint (L i) A) →
    (∀ i, L i ∉ U) → (∀ i, R i ∉ U) → K.card = U.card + 2 * m → (n < U.card + m) → (4 * (r - 1) ≤ m) →
    (∃ g : (U ∪ univ.image L : Finset _) → ℝ, (∃ A, g A ≠ 0) ∧ (∑ A, g A) = 0 ∧
      (∀ A, A.val ∈ U → g A = 0) ∧ ∀ i : Fin n, ∑ B, g B * (if i ∈ B.val then 1 else 0) = 0) →
    (∃ (S : Finset (Fin m)) (i j : Fin m), r ≤ S.card ∧ i ∈ S ∧ j ∈ S ∧ i ≠ j ∧
      Disjoint (L i) (L j) ∧ ∀ x ∈ U, ¬ Disjoint x (R i)) →
    ∃ l r' : Fin (m + 1) → Finset (Fin n), (∀ i, l i ∈ K) ∧ (∀ i, r' i ∈ K) ∧
      Function.Injective l ∧ Function.Injective r' ∧ (∀ i j, l i ≠ r' j) ∧ ∀ i, Disjoint (l i) (r' i)

/-- H2: Dual disjoint synchronized stars `(S_P, x_P)` and `(S_Q, x_Q)` of size `≥ r` with cross-star
intersection whenever `x_P ≠ x_Q`. -/
def H2 : Prop := ∀ (n r : ℕ) (K : Finset (Finset (Fin n))), 3 ≤ r → r * r + r - 1 ≤ n →
    n ≤ r * ((n - r) / (r - 1)) → (∃ T ∈ K, T.card = r) → (∀ A ∈ K, r ≤ A.card) →
    (∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).card ≤ 1) →
    (∀ T ∈ K, n ≤ ((K.erase T).filter fun A => (T ∩ A).Nonempty).card) →
    3 ≤ (K.filter fun A => 3 ≤ A.card).card →
    (¬ ∃ e : Fin n ≃ Fin n, ∀ A ∈ K.image (Finset.map e.toEmbedding),
      3 ≤ A.card → ∃ l r : Fin n, A = Finset.Icc l r) →
    (¬ ∃ L R : Finset (Finset (Fin n)), L ∪ R = K ∧ Disjoint L R ∧
      (∀ A ∈ L, ∀ B ∈ L, A ≠ B → (A ∩ B).Nonempty) ∧ (∀ A ∈ R, ∀ B ∈ R, A ≠ B → (A ∩ B).Nonempty)) →
    (¬ ∃ T ⊆ K, T.card = 3 ∧ ∀ A ∈ T, ∀ B ∈ T, A ≠ B → Disjoint A B) →
    ∀ (m : ℕ) (L R : Fin m → Finset (Fin n)) (U : Finset (Finset (Fin n))),
    (∀ i, L i ∈ K) → (∀ i, R i ∈ K) → Function.Injective L → Function.Injective R →
    (∀ i j, L i ≠ R j) → (∀ i, Disjoint (L i) (R i)) → U ⊆ K →
    (∀ A ∈ U, ∀ B ∈ U, ¬ Disjoint A B) → (∀ i, ∀ A ∈ U, ¬ Disjoint (L i) A) →
    (∀ i, L i ∉ U) → (∀ i, R i ∉ U) → K.card = U.card + 2 * m → (n < U.card + m) → (4 * (r - 1) ≤ m) →
    (∃ g : (U ∪ univ.image L : Finset _) → ℝ, (∃ A, g A ≠ 0) ∧ (∑ A, g A) = 0 ∧
      (∀ A, A.val ∈ U → g A = 0) ∧ ∀ i : Fin n, ∑ B, g B * (if i ∈ B.val then 1 else 0) = 0) →
    (∃ (SP SQ : Finset (Fin m)) (i₀ j₀ : Fin m) (xP xQ : Finset (Fin n)),
      Disjoint SP SQ ∧ i₀ ∈ SP ∧ j₀ ∈ SQ ∧ r ≤ SP.card ∧ r ≤ SQ.card ∧
      (∀ a ∈ SP, a ≠ i₀ → Disjoint (L i₀) (L a)) ∧ (∀ b ∈ SQ, b ≠ j₀ → Disjoint (L j₀) (L b)) ∧
      xP ∈ U ∧ xQ ∈ U ∧ (∀ a ∈ SP, ∀ y ∈ U, Disjoint y (R a) ↔ y = xP) ∧
      (∀ b ∈ SQ, ∀ y ∈ U, Disjoint y (R b) ↔ y = xQ) ∧
      (xP ≠ xQ → ∀ a ∈ SP, ∀ b ∈ SQ, ¬ Disjoint (L a) (L b))) →
    ∃ l r' : Fin (m + 1) → Finset (Fin n), (∀ i, l i ∈ K) ∧ (∀ i, r' i ∈ K) ∧
      Function.Injective l ∧ Function.Injective r' ∧ (∀ i j, l i ≠ r' j) ∧ ∀ i, Disjoint (l i) (r' i)

theorem main : H1 → H2 → OMA.R_Erdos19_erdos_19_R1_H2_R1_H2_R1.H2 := by
  intro h1 h2 n r K hr gap pack witness size linear degree large disorder notSplit noThree
    m L R U hL hR injL injR apart matched subU umeet lmeet disU disR count big band dep
  obtain ⟨g, hgnz, hgsum, hgU, hgcols⟩ := dep
  let Sset := U ∪ univ.image L
  have hSsub : Sset ⊆ K := Finset.union_subset subU fun A hA => by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hA; exact hL i
  have hmemL : ∀ i : Fin m, L i ∈ Sset := fun i =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem L (Finset.mem_univ i))
  let f : Fin m → ℝ := fun i => g ⟨L i, hmemL i⟩
  have hsum_f : ∑ i : Fin m, f i = 0 := by
    have hdisj : Disjoint U (univ.image L) := Finset.disjoint_left.mpr fun A hAU hAL => by
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hAL; exact disU i hAU
    have hsplit : ∑ B : Sset, g B =
        (∑ B ∈ Finset.univ.filter (fun B : Sset => B.val ∈ U), g B) +
        (∑ B ∈ Finset.univ.filter (fun B : Sset => B.val ∉ U), g B) :=
      (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    have hU0 : ∑ B ∈ Finset.univ.filter (fun B : Sset => B.val ∈ U), g B = 0 :=
      Finset.sum_eq_zero fun B hB => hgU B (Finset.mem_filter.mp hB).2
    have hLsum : ∑ B ∈ Finset.univ.filter (fun B : Sset => B.val ∉ U), g B = ∑ i : Fin m, f i := by
      refine (Finset.sum_nbij (fun i : Fin m => (⟨L i, hmemL i⟩ : Sset)) ?_ ?_ ?_ ?_).symm
      · intro i _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, disU i⟩
      · intro i₁ _ i₂ _ h; exact injL (congrArg (fun z : Sset => z.1) h)
      · intro B hB
        have hBU := (Finset.mem_filter.mp hB).2
        have hBL : B.1 ∈ univ.image L := (Finset.mem_union.mp B.2).resolve_left hBU
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hBL
        exact ⟨i, Finset.mem_univ _, Subtype.ext hi⟩
      · intro i _; rfl
    linarith
  have hnz_f : ∃ i : Fin m, f i ≠ 0 := by
    obtain ⟨A, hA⟩ := hgnz
    have hAnU : A.1 ∉ U := fun hU => hA (hgU A hU)
    have hAL : A.1 ∈ univ.image L := (Finset.mem_union.mp A.2).resolve_left hAnU
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hAL
    exact ⟨i, by convert hA using 1; exact congrArg g (Subtype.ext hi)⟩
  have hrow_f : ∀ i : Fin m, ((L i).card - 1 : ℝ) * f i =
      ∑ j ∈ Finset.univ.filter (fun j => Disjoint (L i) (L j)), f j := by
    intro i
    have hinc := E19Signs.incidence_rows Sset
      (fun A hA B hB => linear A (hSsub hA) B (hSsub hB))
      (fun A hA => by have := size A (hSsub hA); omega) g hgcols ⟨L i, hmemL i⟩
    rw [hgsum, zero_add] at hinc
    rw [hinc]
    refine (Finset.sum_nbij (fun j : Fin m => (⟨L j, hmemL j⟩ : Sset)) ?_ ?_ ?_ ?_).symm
    · intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
    · intro j₁ _ j₂ _ h; exact injL (congrArg (fun z : Sset => z.1) h)
    · intro B hB
      have hdis := (Finset.mem_filter.mp hB).2
      have hBnU : B.1 ∉ U := fun hU => lmeet i B.1 hU hdis
      have hBL : B.1 ∈ univ.image L := (Finset.mem_union.mp B.2).resolve_left hBnU
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hBL
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj ▸ hdis⟩, Subtype.ext hj⟩
    · intro j _; rfl
  -- Extract P-star and Q-star
  let P := Finset.univ.filter (fun i : Fin m => 0 < f i)
  let Q := Finset.univ.filter (fun i : Fin m => 0 < -f i)
  have hPQdisj : Disjoint P Q := Finset.disjoint_left.mpr fun i hP hQ => by
    have hp := (Finset.mem_filter.mp hP).2
    have hq := (Finset.mem_filter.mp hQ).2
    linarith
  obtain ⟨hPcard, S_P, i₀, hi₀SP, hSPsub, hSPcard, hSPstar⟩ :=
    E19DualStar.sign_domain_star hr K L hL size noThree f hnz_f hsum_f hrow_f
  obtain ⟨hQcard, S_Q, j₀, hj₀SQ, hSQsub, hSQcard, hSQstar⟩ :=
    E19DualStar.sign_domain_star hr K L hL size noThree (fun i => -f i)
      (by obtain ⟨i, hi⟩ := hnz_f; exact ⟨i, neg_ne_zero.mpr hi⟩)
      (by simp [Finset.sum_neg_distrib, hsum_f])
      (fun i => by simp only [mul_neg, Finset.sum_neg_distrib]; linarith [hrow_f i])
  have hsize1 : ∀ A ∈ K, 1 ≤ A.card := fun A hA => by have := size A hA; omega
  -- Apply star synchronization to S_P and S_Q
  rcases E19DualStar.star_sync K U L R hL hR injL injR apart matched subU disU disR hsize1 noThree
      S_P i₀ hi₀SP (by omega) hSPstar with haug | ⟨a, haS, b, hbS, hab, hLab, hadead⟩ | ⟨x_P, hxPU, hPsync, _⟩
  · exact haug
  · exact h1 n r K hr gap pack witness size linear degree large disorder notSplit noThree
      m L R U hL hR injL injR apart matched subU umeet lmeet disU disR count big band
      ⟨g, hgnz, hgsum, hgU, hgcols⟩
      ⟨S_P, a, b, hSPcard, haS, hbS, hab, hLab, hadead⟩
  · rcases E19DualStar.star_sync K U L R hL hR injL injR apart matched subU disU disR hsize1 noThree
        S_Q j₀ hj₀SQ (by omega) hSQstar with haug | ⟨a, haS, b, hbS, hab, hLab, hadead⟩ | ⟨x_Q, hxQU, hQsync, _⟩
    · exact haug
    · exact h1 n r K hr gap pack witness size linear degree large disorder notSplit noThree
        m L R U hL hR injL injR apart matched subU umeet lmeet disU disR count big band
        ⟨g, hgnz, hgsum, hgU, hgcols⟩
        ⟨S_Q, a, b, hSQcard, haS, hbS, hab, hLab, hadead⟩
    · -- Check cross-star 5-edge augmentation when x_P ≠ x_Q
      by_cases hcross : x_P ≠ x_Q ∧ ∃ a ∈ S_P, ∃ b ∈ S_Q, Disjoint (L a) (L b)
      · obtain ⟨hxne, a, haS, b, hbS, hLab⟩ := hcross
        have hab : a ≠ b := fun h =>
          Finset.disjoint_left.mp hPQdisj (hSPsub haS) (h ▸ hSQsub hbS)
        exact E19DualStar.augment5 K L R hL hR injL injR apart matched a b hab x_P x_Q
          (subU hxPU) (subU hxQU) hxne
          (fun k he => disU k (he ▸ hxPU)) (fun k he => disR k (he ▸ hxPU))
          (fun k he => disU k (he ▸ hxQU)) (fun k he => disR k (he ▸ hxQU))
          ((hPsync a haS x_P hxPU).mpr rfl) hLab ((hQsync b hbS x_Q hxQU).mpr rfl)
      · have hnoCross : x_P ≠ x_Q → ∀ a ∈ S_P, ∀ b ∈ S_Q, ¬ Disjoint (L a) (L b) := by
          intro hxne a haS b hbS hLab
          exact hcross ⟨hxne, a, haS, b, hbS, hLab⟩
        have hSPQdisj : Disjoint S_P S_Q := Finset.disjoint_left.mpr fun z hzP hzQ =>
          Finset.disjoint_left.mp hPQdisj (hSPsub hzP) (hSQsub hzQ)
        exact h2 n r K hr gap pack witness size linear degree large disorder notSplit noThree
          m L R U hL hR injL injR apart matched subU umeet lmeet disU disR count big band
          ⟨g, hgnz, hgsum, hgU, hgcols⟩
          ⟨S_P, S_Q, i₀, j₀, x_P, x_Q, hSPQdisj, hi₀SP, hj₀SQ,
            hSPcard, hSQcard, hSPstar, hSQstar, hxPU, hxQU, hPsync, hQsync, hnoCross⟩

end OMA.R_Erdos19_erdos_19_R1_H2_R1_H2_R1_H2_R1
