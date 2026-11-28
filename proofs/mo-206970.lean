import OMAStatements.S_mo_206970

namespace OMA.SupermodularProduct

open OMA.S_mo_206970

private theorem rectangle (f g : ℝ → ℝ → ℝ) (hmf : NonnegIncr f) (hmg : NonnegIncr g)
    (x x' y y' : ℝ) (hx : x < x') (hy : y < y')
    (hf : f x' y + f x y' ≤ f x' y' + f x y)
    (hg : g x' y + g x y' ≤ g x' y' + g x y) :
    (f x' y * g x' y + f x y' * g x y' ≤ f x' y' * g x' y' + f x y * g x y) ∧
    (f x' y + f x y' < f x' y' + f x y → 0 < g x' y' →
      f x' y * g x' y + f x y' * g x y' < f x' y' * g x' y' + f x y * g x y) := by
  have balance :
      f x' y' * g x' y' + f x y * g x y - (f x' y * g x' y + f x y' * g x y') =
      (f x' y' + f x y - (f x' y + f x y')) * g x' y' +
      f x y * (g x' y' + g x y - (g x' y + g x y')) +
      (f x' y - f x y) * (g x' y' - g x' y) +
      (f x y' - f x y) * (g x' y' - g x y') := by ring
  have cross₁ := mul_nonneg (sub_nonneg.mpr (hmf.2.1 x x' y hx.le))
    (sub_nonneg.mpr (hmg.2.2 x' y y' hy.le))
  have cross₂ := mul_nonneg (sub_nonneg.mpr (hmf.2.2 x y y' hy.le))
    (sub_nonneg.mpr (hmg.2.1 x x' y' hx.le))
  have deltaG := mul_nonneg (hmf.1 x y) (sub_nonneg.mpr hg)
  constructor
  · have deltaF := mul_nonneg (sub_nonneg.mpr hf) (hmg.1 x' y')
    linarith only [balance, deltaF, deltaG, cross₁, cross₂]
  · intro hstrict hpos
    have deltaF := mul_pos (sub_pos.mpr hstrict) hpos
    linarith only [balance, deltaF, deltaG, cross₁, cross₂]

end OMA.SupermodularProduct

theorem OMA.solution : type_of% @OMA.S_mo_206970.main := by
  constructor
  · intro f g hmf hmg hf hg x x' y y' hx hy
    exact (OMA.SupermodularProduct.rectangle f g hmf hmg x x' y y' hx hy
      (hf x x' y y' hx hy) (hg x x' y y' hx hy)).1
  · intro f g hmf hmg hf hg x x' y y' hx hy
    have h₁ := hf x x' y y' hx hy
    have h₂ := hg x x' y y' hx hy
    have hpos : 0 < g x' y' := by
      linarith only [h₂, hmg.2.1 x x' y hx.le, hmg.1 x y']
    exact (OMA.SupermodularProduct.rectangle f g hmf hmg x x' y y' hx hy h₁.le h₂.le).2 h₁ hpos