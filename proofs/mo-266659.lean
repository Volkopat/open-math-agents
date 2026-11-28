import OMAStatements.S_mo_266659
import Mathlib

/-!
MathOverflow 266659: the assumption "`pq = 0` iff `qp = 0`" for idempotents forces every idempotent
`e` to be central (apply it to `1 - e` and the idempotent `e + e x (1 - e)`). Then `p ∧ q = pq`
and both sides of the inequality equal `pq + ef`.
-/

namespace OMA.P266659

open OMA.S_mo_266659

variable {R : Type} [Ring R]

lemma corner_zero
    (hsym : ∀ p q : R, IsIdempotentElem p → IsIdempotentElem q → (p * q = 0 ↔ q * p = 0))
    {e : R} (he : IsIdempotentElem e) (x : R) : e * x * (1 - e) = 0 := by
  have he' : e * e = e := he
  set y := e * x * (1 - e) with hy
  have hey : e * y = y := by
    rw [hy, show e * (e * x * (1 - e)) = (e * e) * x * (1 - e) by noncomm_ring, he']
  have hye : y * e = 0 := by
    rw [hy, show e * x * (1 - e) * e = e * x * (e - e * e) by noncomm_ring, he', sub_self,
      mul_zero]
  have hyy : y * y = 0 := by
    rw [show y * y = y * (e * y) by rw [hey], ← mul_assoc, hye, zero_mul]
  have hq : IsIdempotentElem (e + y) := by
    show (e + y) * (e + y) = e + y
    rw [show (e + y) * (e + y) = e * e + e * y + y * e + y * y by noncomm_ring, he', hey, hye,
      hyy]
    abel
  have h0 : (1 - e) * (e + y) = 0 := by
    rw [show (1 - e) * (e + y) = e + y - e * e - e * y by noncomm_ring, he', hey]; abel
  have h1 := (hsym _ _ he.one_sub hq).1 h0
  rw [show (e + y) * (1 - e) = e + y - e * e - y * e by noncomm_ring, he', hye] at h1
  simpa using h1

lemma central
    (hsym : ∀ p q : R, IsIdempotentElem p → IsIdempotentElem q → (p * q = 0 ↔ q * p = 0))
    {e : R} (he : IsIdempotentElem e) (x : R) : e * x = x * e := by
  have h1 := corner_zero hsym he x
  have h2 := corner_zero hsym he.one_sub x
  rw [sub_sub_cancel] at h2
  have a1 : e * x = e * x * e := by
    rw [show e * x * (1 - e) = e * x - e * x * e by noncomm_ring] at h1
    exact sub_eq_zero.1 h1
  have a2 : x * e = e * x * e := by
    rw [show (1 - e) * x * e = x * e - e * x * e by noncomm_ring] at h2
    exact sub_eq_zero.1 h2
  rw [a1, a2]

lemma idem_mul {p q : R} (hp : p * p = p) (hq : q * q = q) (hcq : q * p = p * q) :
    p * q * (p * q) = p * q := by
  calc p * q * (p * q) = p * (q * p) * q := by noncomm_ring
    _ = p * (p * q) * q := by rw [hcq]
    _ = (p * p) * (q * q) := by noncomm_ring
    _ = p * q := by rw [hp, hq]

lemma inf_eq {inf : R → R → R}
    (hinf : ∀ p q : R, IsIdempotentElem p → IsIdempotentElem q →
        IsIdempotentElem (inf p q) ∧ IdemLE (inf p q) p ∧ IdemLE (inf p q) q ∧
          ∀ r : R, IsIdempotentElem r → IdemLE r p → IdemLE r q → IdemLE r (inf p q))
    (hc : ∀ e : R, IsIdempotentElem e → ∀ x : R, e * x = x * e)
    {p q : R} (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) : inf p q = p * q := by
  obtain ⟨-, ⟨hm1, -⟩, ⟨hm2, -⟩, hglb⟩ := hinf p q hp hq
  have hp' : p * p = p := hp
  have hq' : q * q = q := hq
  have hpq : IsIdempotentElem (p * q) := idem_mul hp' hq' (hc q hq p)
  have hle1 : IdemLE (p * q) p := ⟨by rw [mul_assoc, ← hc p hp q, ← mul_assoc, hp'],
    by rw [← mul_assoc, hp']⟩
  have hle2 : IdemLE (p * q) q := ⟨by rw [mul_assoc, hq'],
    by rw [← mul_assoc, hc q hq p, mul_assoc, hq']⟩
  obtain ⟨h1, -⟩ := hglb _ hpq hle1 hle2
  -- `m * (p * q) = m` and `(p * q) * m = p * q`
  calc inf p q = inf p q * p * q := by rw [hm1, hm2]
    _ = inf p q * (p * q) := by rw [mul_assoc]
    _ = p * q * inf p q := (hc _ hpq _).symm
    _ = p * q := h1

theorem solve :
    ∀ (R : Type) [Ring R] (inf sup : R → R → R),
      (∀ p q : R, IsIdempotentElem p → IsIdempotentElem q →
        IsIdempotentElem (inf p q) ∧ IdemLE (inf p q) p ∧ IdemLE (inf p q) q ∧
          ∀ r : R, IsIdempotentElem r → IdemLE r p → IdemLE r q → IdemLE r (inf p q)) →
      (∀ p q : R, IsIdempotentElem p → IsIdempotentElem q →
        IsIdempotentElem (sup p q) ∧ IdemLE p (sup p q) ∧ IdemLE q (sup p q) ∧
          ∀ r : R, IsIdempotentElem r → IdemLE p r → IdemLE q r → IdemLE (sup p q) r) →
      (∀ p q : R, IsIdempotentElem p → IsIdempotentElem q → (p * q = 0 ↔ q * p = 0)) →
      ∀ p q e f : R, IsIdempotentElem p → IsIdempotentElem q → IsIdempotentElem e →
        IsIdempotentElem f → p * e = 0 → p * f = 0 → q * e = 0 → q * f = 0 →
        IdemLE (inf (p + e) (q + f)) (inf p q + inf e f) := by
  intro R _ inf sup hinf _ hsym p q e f hp hq he hf hpe hpf hqe hqf
  have hc : ∀ e : R, IsIdempotentElem e → ∀ x : R, e * x = x * e :=
    fun e he x => central hsym he x
  have hep : e * p = 0 := by rw [← hc p hp e, hpe]
  have hfq : f * q = 0 := by rw [← hc q hq f, hqf]
  have hp' : p * p = p := hp
  have he' : e * e = e := he
  have hq' : q * q = q := hq
  have hf' : f * f = f := hf
  have hpe' : IsIdempotentElem (p + e) := by
    show (p + e) * (p + e) = p + e
    rw [add_mul, mul_add, mul_add, hp', hpe, hep, he']; abel
  have hqf' : IsIdempotentElem (q + f) := by
    show (q + f) * (q + f) = q + f
    rw [add_mul, mul_add, mul_add, hq', hqf, hfq, hf']; abel
  rw [inf_eq hinf hc hpe' hqf', inf_eq hinf hc hp hq, inf_eq hinf hc he hf]
  have heq : e * q = 0 := by rw [← hc q hq e, hqe]
  have hx : (p + e) * (q + f) = p * q + e * f := by
    rw [add_mul, mul_add, mul_add, hpf, heq]; abel
  rw [hx]
  have hpqef : p * q * (e * f) = 0 := by
    rw [mul_assoc, ← mul_assoc q e f, hqe, zero_mul, mul_zero]
  have hefpq : e * f * (p * q) = 0 := by
    rw [mul_assoc, ← mul_assoc f p q, ← hc p hp f, hpf, zero_mul, mul_zero]
  have hpq : p * q * (p * q) = p * q := idem_mul hp' hq' (hc q hq p)
  have hef : e * f * (e * f) = e * f := idem_mul he' hf' (hc f hf e)
  have hid : (p * q + e * f) * (p * q + e * f) = p * q + e * f := by
    rw [add_mul, mul_add, mul_add, hpq, hpqef, hefpq, hef]; abel
  exact ⟨hid, hid⟩

end OMA.P266659

theorem OMA.solution : type_of% @OMA.S_mo_266659.main := OMA.P266659.solve
