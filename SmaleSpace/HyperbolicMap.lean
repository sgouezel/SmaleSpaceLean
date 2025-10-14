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

lemma dist_image_iter_le_of_pseudoOrbit
    {Y : Type*} [MetricSpace Y] {f : Y → Y} (hf : UniformContinuous f)
    {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    ∃ ε > 0, ∀ (u : ℕ → Y), (∀ n, dist (f (u n)) (u (n + 1)) < ε) →
      dist (f ^[n] (u 0)) (u n) < δ := by
  induction n generalizing δ with
  | zero =>
    refine ⟨δ, hδ, fun u hu ↦ by simp [hδ]⟩
  | succ n ih =>
    rcases Metric.uniformContinuous_iff.1 hf (δ / 2) (by linarith) with ⟨δ', δ'pos, h'⟩
    rcases ih δ'pos with ⟨ε, εpos, hε⟩
    refine ⟨min ε (δ / 2), by positivity, fun u hu ↦ ?_⟩
    calc
    dist (f^[n + 1] (u 0)) (u (n + 1))
    _ ≤ dist (f (f^[n] (u 0))) (f (u n)) + dist (f (u n)) (u (n + 1)) := by
      rw [iterate_succ_apply']
      apply dist_triangle
    _ < δ / 2 + δ / 2 := by
      gcongr
      · apply h'
        exact hε u (fun m ↦ (hu m).trans_le (min_le_left _ _))
      · exact (hu n).trans_le (min_le_right _ _)
    _ = δ := by linarith

variable [HasRuelleBracketWithMap X] [HasReduceScale X]

lemma future_shadowing_aux (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (x : ℕ → X)
    (hx : ∀ n, dist (T (x n)) (x (n+1)) < ε) (M : ℕ) (hM : 2 * λ ^ M * δ ≤ reduceScale X δ)
    (hε : ∀ (u : ℕ → X), (∀ n, dist (T (u n)) (u (n + 1)) < ε) →
      dist (T ^[M] (u 0)) (u M) < reduceScale X δ / 2) :
    ∃ p ∈ locUnstable ε (x 0), ∀ n, dist (x n) (T ^[n] p) < ε := by
  -- define inductively a sequence by `y₀ = x₀`, and `y_{n+1}` the intersection of `W^u (T^M yₙ)`
  -- and `W^s (x_{M * (n+1)})`.
  let y := Nat.rec (motive := fun n ↦ X) (x 0) (fun n q ↦ ⁅T^[M] q, x (M * (n + 1))⁆)
  have A n : dist (y n) (x (M * n)) < δ := by
    induction n with
    | zero =>
      simp [y, hδ]
    | succ n ih =>
      have : y (n + 1) = ⁅T^[M] (y n), x (M * (n + 1))⁆ := rfl
      rw [this, dist_comm]
      apply dist_bracket_lt_of_lt_reduceScale ?_ (by simp [reduceScale_pos hδ])
      apply (dist_triangle_left _ _ (T^[M] (x (M * n)))).trans_lt
      have A : dist (T^[M] (x (M * n))) (x (M * (n + 1))) < reduceScale X δ / 2 :=
        hε (fun k ↦ x (M * n + k)) (fun k ↦ hx (M * n + k))
      have B : dist (T^[M] (x (M * n))) (T^[M] (y n)) ≤ λ ^ M * δ := sorry
      linarith









lemma future_shadowing (ε : ℝ) (hε : 0 < ε) (x : ℕ → X) (hx : ∀ n, dist (x (n+1)) (T (x n)) ≤ ε) :
    ∃ p ∈ locUnstable ε (x 0), ∀ n, dist (x n) (T ^[n] p) < ε := by
  -- define inductively a sequence by `y₀ = x₀`, and `y_{n+1}` is the intersection of `W^u (T yₙ)`
  -- and `W ^ s (x_{n+1})`.
  let y := Nat.rec (motive := fun n ↦ X) (x 0) (fun n q ↦ ⁅T q, x (n + 1)⁆)
