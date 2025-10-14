import SmaleSpace.Bracket

open scoped Uniformity Topology
open Function Set Filter Metric

namespace SmaleSpace

variable (X : Type*) [MetricSpace X] {U V : Set (X × X)} {a b c o s u x y z : X} {ε : ℝ}

local notation3 "δ₀" => HasRuelleBracket.deltaZero X
local notation3 "δ₁" => deltaOne X

/-- Class registering that a space is endowed with a hyperbolic map, compatible with a given
Ruelle bracket. -/
class HasRuelleBracketWithMap extends HasRuelleBracket X where
  /-- The hyperbolic map. Use as `T` through notation. -/
  mapT : X ≃ X
  unifCont_T : UniformContinuous mapT
  unifCont_Tsymm : UniformContinuous mapT.symm
  /-- The contraction parameter -/
  lambda : ℝ
  lambda_pos : 0 < lambda
  lambda_lt_one : lambda < 1
  T_bracket x y (h : dist x y < δ₀) (h' : dist (mapT x) (mapT y) < δ₀) :
    ⁅mapT x, mapT y⁆ = mapT ⁅x, y⁆
  expansion x y (hxy : y ∈ locUnstable δ₀ x) : dist (mapT.symm x) (mapT.symm y) ≤ lambda * dist x y
  contraction x y (hxy : y ∈ locStable δ₀ x) : dist (mapT x) (mapT y) ≤ lambda * dist x y

local notation3 "T" => HasRuelleBracketWithMap.mapT (X := X)
local notation3 "λ" => HasRuelleBracketWithMap.lambda (X := X)

/-- If `T` is a hyperbolic map on a space `X`, then `T⁻¹` is also hyperbolic (with respect to the
reversed bracket). We register this as a typeclass on the type synonym `invDyn X`. -/
instance [h : HasRuelleBracketWithMap X] : HasRuelleBracketWithMap (invDyn X) where
  mapT := Equiv.symm T
  unifCont_T := h.unifCont_Tsymm
  unifCont_Tsymm := h.unifCont_T
  lambda := h.lambda
  lambda_pos := h.lambda_pos
  lambda_lt_one := h.lambda_lt_one
  T_bracket x y h₁ h₂ := by
    rw [dist_comm] at h₁ h₂
    have W := h.T_bracket _ _ h₂ ?_; swap
    · convert h₁ using 1
      congr
      · apply Equiv.apply_symm_apply
      · apply Equiv.apply_symm_apply
    rw [← Equiv.apply_eq_iff_eq_symm_apply]
    apply W.symm.trans
    congr
    · apply Equiv.apply_symm_apply
    · apply Equiv.apply_symm_apply
  expansion x y hxy := h.contraction (ofInvDyn x) (ofInvDyn y) hxy
  contraction x y hxy := h.expansion (ofInvDyn x) (ofInvDyn y) hxy
