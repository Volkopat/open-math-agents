import OMAReductions.R_Erdos107_erdos_107_R1_H1_R1_H2_R1
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Embedding
import Mathlib.Order.Fin.Basic

/-!
A reduction of the finite H2 in the seventeen-label branch of Erdős 107.
The two hypotheses concern only the sixteen labels after the anchor.
The positive five-set case closes by adjoining the anchor. In the remaining
cases a six-gon is encoded by two increasing chains with shared endpoints.
The proof uses only the signs of consecutive triples and packet consistency.
-/

namespace OMA.R_Erdos107_erdos_107_R1_H1_R1_H2_R1_H2_R2

/-- Equal turns at the ends of a packet force the middle turns. -/
private theorem packet_middle {n : ℕ} {g : Fin n → Fin n → Fin n → Bool}
    (packet : ∀ a b c d, a < b → b < c → c < d →
        (g a b c = g a b d ∧ g a b d = g a c d) ∨
        (g a b c = g a b d ∧ g a c d = g b c d) ∨
        (g a b d = g a c d ∧ g a c d = g b c d)) {a b c d : Fin n} {t : Bool}
    (ab : a < b) (bc : b < c) (cd : c < d) (left : g a b c = t) (right : g b c d = t) :
    g a b d = t ∧ g a c d = t := by
  rcases packet a b c d ab bc cd with h | h | h <;> grind

/-- In a finite increasing chain, consecutive triples determine all triples.
Split a nonconsecutive triple at an intermediate label. Both shorter intervals
have the chain sign, so the four-label packet forces the original triple. -/
private theorem chain_triple {n : ℕ} {g : Fin n → Fin n → Fin n → Bool}
    (packet : ∀ a b c d, a < b → b < c → c < d →
        (g a b c = g a b d ∧ g a b d = g a c d) ∨
        (g a b c = g a b d ∧ g a c d = g b c d) ∨
        (g a b d = g a c d ∧ g a c d = g b c d)) {S : Finset (Fin n)} {t : Bool}
    (chain : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a < b → b < c →
        (∀ x ∈ S, a < x → x < c → x = b) → g a b c = t)
    (a b c : Fin n) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (ab : a < b) (bc : b < c) : g a b c = t := by
  classical
  by_cases consecutive : ∀ x ∈ S, a < x → x < c → x = b
  · exact chain a ha b hb c hc ab bc consecutive
  · push Not at consecutive
    obtain ⟨x, hx, ax, xc, ne⟩ := consecutive
    rcases lt_or_gt_of_ne ne with xb | bx
    · exact (packet_middle packet ax xb bc
        (chain_triple packet chain a x b ha hx hb ax xb)
        (chain_triple packet chain x b c hx hb hc xb bc)).2
    · exact (packet_middle packet ab bx xc
        (chain_triple packet chain a b x ha hb hx ab bx)
        (chain_triple packet chain b x c hb hx hc bx xc)).1
termination_by c.val - a.val
decreasing_by all_goals omega

/-- On a boundary, the signs of triples touching an endpoint are determined
by the side of the middle label, even when the other label is on the opposite side. -/
private theorem endpoint_signs {n : ℕ} {g : Fin n → Fin n → Fin n → Bool}
    (packet : ∀ a b c d, a < b → b < c → c < d →
        (g a b c = g a b d ∧ g a b d = g a c d) ∨
        (g a b c = g a b d ∧ g a c d = g b c d) ∨
        (g a b d = g a c d ∧ g a c d = g b c d))
    {S : Finset (Fin n)} {lo hi : Fin n} {side : Fin n → Bool}
    (bd : ∀ t : Bool, ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a < b → b < c →
      (a = lo ∨ a = hi ∨ side a = t) → (b = lo ∨ b = hi ∨ side b = t) →
      (c = lo ∨ c = hi ∨ side c = t) → g a b c = t) (hl : lo ∈ S) (hr : hi ∈ S)
    {x y : Fin n} (hx : x ∈ S) (hy : y ∈ S) (lx : lo < x) (xy : x < y) (yr : y < hi) :
    g lo x y = side x ∧ g x y hi = side y := by
  have left (t) : lo = lo ∨ lo = hi ∨ side lo = t := Or.inl rfl
  have right (t) : hi = lo ∨ hi = hi ∨ side hi = t := Or.inr (Or.inl rfl)
  have own (z) : z = lo ∨ z = hi ∨ side z = side z := Or.inr (Or.inr rfl)
  have xsign := bd _ _ hl _ hx _ hr lx (xy.trans yr) (left _) (own x) (right _)
  have ysign := bd _ _ hl _ hy _ hr (lx.trans xy) yr (left _) (own y) (right _)
  by_cases same : side x = side y
  · exact ⟨bd _ _ hl _ hx _ hy lx xy (left _) (own x) (Or.inr (Or.inr same.symm)),
           bd _ _ hx _ hy _ hr xy yr (Or.inr (Or.inr same)) (own y) (right _)⟩
  · rcases packet lo x y hi lx xy yr with h | h | h <;> grind

/-- Every quadruple through the least boundary vertex has even parity. -/
theorem boundary_even {n : ℕ} {g : Fin n → Fin n → Fin n → Bool}
    (packet : ∀ a b c d, a < b → b < c → c < d →
        (g a b c = g a b d ∧ g a b d = g a c d) ∨
        (g a b c = g a b d ∧ g a c d = g b c d) ∨
        (g a b d = g a c d ∧ g a c d = g b c d))
    {S : Finset (Fin n)} {lo hi : Fin n} {side : Fin n → Bool}
    (bd : ∀ t : Bool, ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a < b → b < c →
      (a = lo ∨ a = hi ∨ side a = t) → (b = lo ∨ b = hi ∨ side b = t) →
      (c = lo ∨ c = hi ∨ side c = t) → g a b c = t) (hl : lo ∈ S) (hr : hi ∈ S)
    {a b c : Fin n} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (la : lo < a) (ab : a < b) (bc : b < c) (cr : c ≤ hi) :
    (((g lo a b).xor (g lo a c)).xor (g lo b c)).xor (g a b c) = false := by
  have first := endpoint_signs packet bd hl hr ha hb la ab (bc.trans_le cr)
  have pairs : g lo a b = g lo a c ∧ g lo b c = g a b c := by
    rcases cr.lt_or_eq with strict | rfl
    · have second := endpoint_signs packet bd hl hr ha hc la (ab.trans bc) strict
      have third := endpoint_signs packet bd hl hr hb hc (la.trans ab) bc strict
      refine ⟨first.1.trans second.1.symm, ?_⟩
      by_cases sameAB : side a = side b
      · by_cases sameBC : side b = side c
        · have same := bd (side b) _ ha _ hb _ hc ab bc
                (Or.inr (Or.inr sameAB)) (Or.inr (Or.inr rfl)) (Or.inr (Or.inr sameBC.symm))
          exact third.1.trans same.symm
        · rcases packet a b c hi ab bc strict with h | h | h <;> grind
      · rcases packet lo a b c la ab bc with h | h | h <;> grind
    · have atHi (x) (hx : x ∈ S) (lx : lo < x) (xr : x < c) : g lo x c = side x :=
        bd _ _ hl _ hx _ hr lx xr (Or.inl rfl) (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl))
      exact ⟨first.1.trans (atHi _ ha la (ab.trans bc)).symm,
        (atHi _ hb (la.trans ab) bc).trans first.2.symm⟩
  simp [pairs.1, pairs.2]

/-- Neither sign occurs on all triples of a five-set. -/
def H1 : Prop :=
  ∀ g : Fin 16 → Fin 16 → Fin 16 → Bool,
  let packet : Prop := ∀ a b c d, a < b → b < c → c < d →
    (g a b c = g a b d ∧ g a b d = g a c d) ∨
    (g a b c = g a b d ∧ g a c d = g b c d) ∨
    (g a b d = g a c d ∧ g a c d = g b c d)
  let five (t : Bool) : Prop := ∃ S : Finset (Fin 16), S.card = 5 ∧
    ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a < b → b < c → g a b c = t
  let chain (S : Finset (Fin 16)) (t : Bool) : Prop :=
    ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a < b → b < c →
      (∀ x ∈ S, a < x → x < c → x = b) → g a b c = t
  packet → ¬ five true → ¬ five false →
  ∃ lo hi : Fin 16, ∃ A B : Finset (Fin 16),
    lo < hi ∧ lo ∈ A ∧ lo ∈ B ∧ hi ∈ A ∧ hi ∈ B ∧
    (∀ x ∈ A ∪ B, lo ≤ x ∧ x ≤ hi) ∧
    chain A false ∧ chain B true ∧ A.card + B.card = 8

/-- A negative five-set exists, and no positive five-set exists. -/
def H2 : Prop :=
  ∀ g : Fin 16 → Fin 16 → Fin 16 → Bool,
  let packet : Prop := ∀ a b c d, a < b → b < c → c < d →
    (g a b c = g a b d ∧ g a b d = g a c d) ∨
    (g a b c = g a b d ∧ g a c d = g b c d) ∨
    (g a b d = g a c d ∧ g a c d = g b c d)
  let five (t : Bool) : Prop := ∃ S : Finset (Fin 16), S.card = 5 ∧
    ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a < b → b < c → g a b c = t
  let chain (S : Finset (Fin 16)) (t : Bool) : Prop :=
    ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a < b → b < c →
      (∀ x ∈ S, a < x → x < c → x = b) → g a b c = t
  packet → ¬ five true → five false →
  ∃ lo hi : Fin 16, ∃ A B : Finset (Fin 16),
    lo < hi ∧ lo ∈ A ∧ lo ∈ B ∧ hi ∈ A ∧ hi ∈ B ∧
    (∀ x ∈ A ∪ B, lo ≤ x ∧ x ≤ hi) ∧
    chain A false ∧ chain B true ∧ A.card + B.card = 8

theorem main : H1 → H2 → OMA.R_Erdos107_erdos_107_R1_H1_R1_H2_R1.H2 := by
  classical
  intro h₁ h₂ g packet anchor
  let tail : Fin 16 → Fin 16 → Fin 16 → Bool := fun a b c => g a.succ b.succ c.succ
  have ordered : ∀ a b c d, a < b → b < c → c < d →
    (tail a b c = tail a b d ∧ tail a b d = tail a c d) ∨
    (tail a b c = tail a b d ∧ tail a c d = tail b c d) ∨
    (tail a b d = tail a c d ∧ tail a c d = tail b c d) := fun a b c d ab bc cd =>
    packet a.succ b.succ c.succ d.succ (Fin.succ_lt_succ_iff.mpr ab)
      (Fin.succ_lt_succ_iff.mpr bc) (Fin.succ_lt_succ_iff.mpr cd)
  let lift := Fin.succEmb 16
  let five (t : Bool) : Prop := ∃ S : Finset (Fin 16), S.card = 5 ∧
    ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a < b → b < c → tail a b c = t
  by_cases positive : five true
  · obtain ⟨T, card, mono⟩ := positive
    have fresh : (0 : Fin 17) ∉ T.map lift := by simp [lift, Finset.mem_map]
    refine ⟨insert 0 (T.map lift), by simp [fresh, card], 0, Finset.mem_insert_self ..,
      fun _ _ => Fin.zero_le _, ?_⟩
    intro a ha b hb c hc za ab bc
    have preimage {x : Fin 17} (hx : x ∈ insert 0 (T.map lift)) (pos : 0 < x) :
        ∃ i ∈ T, lift i = x :=
      Finset.mem_map.mp ((Finset.mem_insert.mp hx).resolve_left pos.ne')
    obtain ⟨i, hi, rfl⟩ := preimage ha za
    obtain ⟨j, hj, rfl⟩ := preimage hb (za.trans ab)
    obtain ⟨k, hk, rfl⟩ := preimage hc ((za.trans ab).trans bc)
    have last : g (lift i) (lift j) (lift k) = true :=
      mono i hi j hj k hk (Fin.succ_lt_succ_iff.mp ab) (Fin.succ_lt_succ_iff.mp bc)
    simp [anchor _ _ za ab, anchor _ _ za (ab.trans bc), anchor _ _ (za.trans ab) bc, last]
  · let chain (S : Finset (Fin 16)) (t : Bool) : Prop :=
      ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a < b → b < c →
        (∀ x ∈ S, a < x → x < c → x = b) → tail a b c = t
    have joined : ∃ lo hi : Fin 16, ∃ A B : Finset (Fin 16),
        lo < hi ∧ lo ∈ A ∧ lo ∈ B ∧ hi ∈ A ∧ hi ∈ B ∧
        (∀ x ∈ A ∪ B, lo ≤ x ∧ x ≤ hi) ∧
        chain A false ∧ chain B true ∧ A.card + B.card = 8 := by
      by_cases negative : five false
      · exact h₂ tail ordered positive negative
      · exact h₁ tail ordered positive negative
    obtain ⟨lo, hi, A, B, lr, la, lb, ra, rb, bounds, neg, pos, total⟩ := joined
    have overlap {x} (xa : x ∈ A) (xb : x ∈ B) : x = lo ∨ x = hi := by
      by_contra! h
      have lx := lt_of_le_of_ne (bounds x (Finset.mem_union_left _ xa)).1 h.1.symm
      have xr := lt_of_le_of_ne (bounds x (Finset.mem_union_left _ xa)).2 h.2
      have zero := chain_triple ordered neg lo x hi la xa ra lx xr
      have one := chain_triple ordered pos lo x hi lb xb rb lx xr
      simp_all
    have inter : A ∩ B = {lo, hi} := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨fun h => overlap h.1 h.2, fun h => h.elim (fun e => e ▸ ⟨la, lb⟩) (fun e => e ▸ ⟨ra, rb⟩)⟩
    have card := Finset.card_union_add_card_inter A B
    rw [inter] at card
    simp [lr.ne] at card
    have six : (A ∪ B).card = 6 := by omega
    let T := A ∪ B
    let side (x : Fin 16) := decide (x ∈ B)
    have hl : lo ∈ T := Finset.mem_union_left _ la
    have hr : hi ∈ T := Finset.mem_union_left _ ra
    have bd : ∀ t : Bool, ∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, a < b → b < c →
        (a = lo ∨ a = hi ∨ side a = t) → (b = lo ∨ b = hi ∨ side b = t) →
        (c = lo ∨ c = hi ∨ side c = t) → tail a b c = t := by
      intro t a ha b hb c hc ab bc sa sb sc
      have inNeg {x} (hx : x ∈ A ∪ B) (onSide : x = lo ∨ x = hi ∨ decide (x ∈ B) = false) : x ∈ A := by
        rcases onSide with rfl | rfl | outside
        · exact la
        · exact ra
        · exact (Finset.mem_union.mp hx).resolve_right (of_decide_eq_false outside)
      have inPos {x} (onSide : x = lo ∨ x = hi ∨ decide (x ∈ B) = true) : x ∈ B := by
        rcases onSide with rfl | rfl | inside
        · exact lb
        · exact rb
        · exact of_decide_eq_true inside
      cases t
      · exact chain_triple ordered neg a b c (inNeg ha sa) (inNeg hb sb) (inNeg hc sc) ab bc
      · exact chain_triple ordered pos a b c (inPos sa) (inPos sb) (inPos sc) ab bc
    refine ⟨T.map lift, by simpa [T] using six, lift lo, Finset.mem_map.mpr ⟨lo, hl, rfl⟩, ?_, ?_⟩
    · intro a ha
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp ha
      exact Fin.succ_le_succ_iff.mpr (bounds x hx).1
    · intro a ha b hb c hc la ab bc
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp ha
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hb
      obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hc
      exact boundary_even ordered bd hl hr hx hy hz (Fin.succ_lt_succ_iff.mp la)
        (Fin.succ_lt_succ_iff.mp ab) (Fin.succ_lt_succ_iff.mp bc) (bounds z hz).2

end OMA.R_Erdos107_erdos_107_R1_H1_R1_H2_R1_H2_R2
