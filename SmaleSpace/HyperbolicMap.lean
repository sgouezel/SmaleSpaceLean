import SmaleSpace.Bracket

open scoped Uniformity Topology
open Function Set Filter Metric

namespace SmaleSpace

variable (X : Type*) [MetricSpace X] {U V : Set (X × X)} {a b c o s u x y z : X} {ε : ℝ}

local notation3 "δ₀" => HasRuelleBracket.deltaZero X
local notation3 "δ₁" => deltaOne X

class HasRuelleBracketWithMap extends HasRuelleBracket X where
  /-- The hyperbolic map -/
  T : X ≃ X
  unifCont_T : UniformContinuous T
  unifCont_Tsymm : UniformContinuous T.symm
  /-- The contraction parameter -/
  lambda : ℝ
  lambda_pos : 0 < lambda
  lambda_lt_one : lambda < 1
  T_bracket x y (h : dist x y < δ₀) (h' : dist (T x) (T y) < δ₀) : ⁅T x, T y⁆ = T ⁅x, y⁆
  expansion x y (hxy : y ∈ locUnstable δ₀ x) : dist (T.symm x) (T.symm y) ≤ lambda * dist x y
  contration x y (hxy : y ∈ locStable δ₀ x) : dist (T x) (T y) ≤ lambda * dist x y
