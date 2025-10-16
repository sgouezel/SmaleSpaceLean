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
  bracket_image {x y : X} (h : dist x y ≤ δ₀) (h' : dist (mapT x) (mapT y) ≤ δ₀) :
    ⁅mapT x, mapT y⁆ = mapT ⁅x, y⁆
  expansion {x y : X} (hxy : y ∈ locUnstable δ₀ x) :
    dist (mapT.symm x) (mapT.symm y) ≤ lambda * dist x y
  contraction {x y : X} (hxy : y ∈ locStable δ₀ x) :
    dist (mapT x) (mapT y) ≤ lambda * dist x y

local notation3 "T.symm" => Equiv.symm (HasRuelleBracketWithMap.mapT (X := X))
local notation3 "T" => HasRuelleBracketWithMap.mapT (X := X)
local notation3 "λ" => HasRuelleBracketWithMap.lambda (X := X)

export HasRuelleBracketWithMap (lambda_pos lambda_lt_one bracket_image expansion contraction)

lemma bracket_image_symm [h : HasRuelleBracketWithMap X] (h : dist x y ≤ δ₀)
    (h' : dist (T.symm x) (T.symm y) ≤ δ₀) :
    ⁅T.symm x, T.symm y⁆ = T.symm ⁅x, y⁆ := by
  rw [← Equiv.apply_eq_iff_eq_symm_apply]
  simpa using (bracket_image h' (by simpa using h)).symm

/-- If `T` is a hyperbolic map on a space `X`, then `T⁻¹` is also hyperbolic (with respect to the
reversed bracket). We register this as a typeclass on the type synonym `invDyn X`. -/
instance [h : HasRuelleBracketWithMap X] : HasRuelleBracketWithMap (invDyn X) where
  mapT := T.symm
  unifCont_T := h.unifCont_Tsymm
  unifCont_Tsymm := h.unifCont_T
  lambda := h.lambda
  lambda_pos := h.lambda_pos
  lambda_lt_one := h.lambda_lt_one
  bracket_image {x y} h₁ h₂ := by rw [dist_comm] at h₁ h₂; exact bracket_image_symm (X := X) h₁ h₂
  expansion hxy := h.contraction hxy
  contraction hxy := h.expansion hxy

class HasReduceScaleWithMap [HasRuelleBracketWithMap X] extends HasReduceScale X where
  dist_image_le {ε : ℝ} {x y : X} (h : dist x y ≤ reduceScale ε) : dist (T x) (T y) ≤ ε
  dist_image_symm_le {ε : ℝ} {x y : X} (h : dist x y ≤ reduceScale ε) :
    dist (T.symm x) (T.symm y) ≤ ε

export HasReduceScaleWithMap (dist_image_le dist_image_symm_le)

instance [HasRuelleBracketWithMap X] [HasReduceScaleWithMap X] :
    HasReduceScaleWithMap (invDyn X) where
  dist_image_le := dist_image_symm_le (X := X)
  dist_image_symm_le := dist_image_le (X := X)

variable {X}
variable [HasRuelleBracketWithMap X]

lemma image_mem_locStable (hε : ε ≤ δ₀) (h : x ∈ locStable ε o) :
    T x ∈ locStable (λ * ε) (T o) := by
  simp only [locStable, mem_setOf_eq]
  have A : dist (T o) (T x) ≤ λ * ε := by
    apply (contraction (locStable_mono hε h)).trans
    gcongr
    · apply lambda_pos.le
    · exact h.1
  refine ⟨A, ?_⟩
  rw [bracket_image]
  · congr 1
    exact h.2
  · rw [dist_comm]
    exact (locStable_mono hε h).1
  · have : 0 ≤ ε := dist_nonneg.trans h.1
    rw [dist_comm]
    apply A.trans (le_trans _ hε)
    have := lambda_lt_one (X := X)
    nlinarith

lemma image_iter_mem_locStable (hε : ε ≤ δ₀) (h : x ∈ locStable ε o) (n : ℕ) :
    T^[n] x ∈ locStable (λ ^ n * ε) (T^[n] o) := by
  induction n with
  | zero =>
    simpa using h
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ_apply', show λ ^ (n + 1) * ε = λ * (λ ^ n * ε) by ring]
    apply image_mem_locStable _ ih
    have : λ ^ n ≤ 1 := pow_le_one₀ lambda_pos.le lambda_lt_one.le
    have : 0 ≤ ε := dist_nonneg.trans h.1
    exact le_trans (by nlinarith) hε

lemma image_mem_locUnstable (hε : ε ≤ δ₀) (h : x ∈ locUnstable ε o) :
    T.symm x ∈ locUnstable (λ * ε) (T.symm o) :=
  image_mem_locStable (X := invDyn X) (by exact hε) h

lemma image_iter_mem_locUnstable (hε : ε ≤ δ₀) (h : x ∈ locUnstable ε o) (n : ℕ) :
    T.symm^[n] x ∈ locUnstable (λ ^ n * ε) (T.symm^[n] o) :=
  image_iter_mem_locStable (X := invDyn X) (by exact hε) h n

lemma locStable_eq_dist_iter_le [HasReduceScale X] (hε : ε ≤ δ₁) :
    locStable ε o = {x | ∀ n, dist (T^[n] o) (T^[n] x) ≤ ε} := by
  have h'ε : ε ≤ δ₀ := hε.trans deltaOne_le_deltaZero
  apply Subset.antisymm
  · intro x hx n
    apply (image_iter_mem_locStable h'ε hx n).1.trans
    have : λ ^ n ≤ 1 := pow_le_one₀ lambda_pos.le lambda_lt_one.le
    have : 0 ≤ ε := dist_nonneg.trans hx.1
    nlinarith
  · intro x hx
    rw [locStable_eq h'ε]
    refine ⟨by simpa using hx 0, ?_⟩
    let y n := ⁅T^[n] o, T^[n] x⁆
    have A n : T (y n) = y (n + 1) := by
      simp only [y, iterate_succ_apply']
      rw [bracket_image]
      · apply (hx n).trans h'ε
      · simp only [← iterate_succ_apply']
        apply (hx (n + 1)).trans h'ε
    have A' n : y n = T^[n] (y 0) := by
      induction n with
      | zero => simp
      | succ n ih => simp only [← A, ih, iterate_succ_apply']
    have B n : y n ∈ locUnstable δ₀ (T^[n] o) := by
      apply bracket_mem_locUnstable
      exact (hx n).trans hε
    have C n : y 0 ∈ locUnstable (λ ^ n * δ₀) o := by
      have L : Function.LeftInverse T.symm^[n] T^[n] := (Equiv.leftInverse_symm T).iterate _
      convert image_iter_mem_locUnstable le_rfl (B n) n
      · rw [L o]
      · rw [A' n, L (y 0)]
    have : dist o (y 0) = 0 := by
      apply le_antisymm ?_ dist_nonneg
      have : Tendsto (fun n ↦ λ ^ n * δ₀) atTop (𝓝 (0 * δ₀)) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one lambda_pos.le lambda_lt_one).mul_const _
      rw [zero_mul] at this
      exact ge_of_tendsto' this (fun n ↦ (C n).1)
    simp only [dist_eq_zero] at this
    exact this.symm

lemma locUnstable_eq_dist_iter_le [HasReduceScale X] (hε : ε ≤ δ₁) :
    locUnstable ε o = {x | ∀ n, dist (T.symm^[n] o) (T.symm^[n] x) ≤ ε} :=
  locStable_eq_dist_iter_le (X := invDyn X) hε

lemma exists_dist_image_iter_le_of_pseudoOrbit
    {Y : Type*} [MetricSpace Y] {f : Y → Y} (hf : UniformContinuous f)
    {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    ∃ ε > 0, ∀ (u : ℕ → Y), (∀ n, dist (f (u n)) (u (n + 1)) ≤ ε) →
      ∀ i ≤ n, dist (f ^[i] (u 0)) (u i) ≤ δ := by
  induction n generalizing δ with
  | zero =>
    refine ⟨δ, hδ, fun u hu ↦ by simp [hδ.le]⟩
  | succ n ih =>
    rcases Metric.uniformContinuous_iff.1 hf (δ / 2) (by linarith) with ⟨δ', δ'pos, h'⟩
    rcases ih (show 0 < min δ (δ' / 2) by positivity) with ⟨ε, εpos, hε⟩
    refine ⟨min ε (δ / 2), by positivity, fun u hu i hi ↦ ?_⟩
    rcases Nat.le_succ_iff.1 hi with h'i | rfl
    · apply (hε u (fun m ↦ ?_) i h'i).trans (min_le_left _ _)
      exact (hu m).trans (min_le_left _ _)
    calc
    dist (f^[n + 1] (u 0)) (u (n + 1))
    _ ≤ dist (f (f^[n] (u 0))) (f (u n)) + dist (f (u n)) (u (n + 1)) := by
      rw [iterate_succ_apply']
      apply dist_triangle
    _ ≤ δ / 2 + δ / 2 := by
      gcongr
      · apply (h' _).le
        suffices dist (f^[n] (u 0)) (u n) ≤ δ' / 2 by linarith
        exact (hε u (fun m ↦ (hu m).trans (min_le_left _ _)) n le_rfl).trans
          (min_le_right _ _)
      · exact (hu n).trans (min_le_right _ _)
    _ = δ := by linarith

variable [HasReduceScale X]

lemma future_shadowing_aux (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (h'δ : δ ≤ δ₀) (x : ℕ → X)
    (hx : ∀ n, dist (T (x n)) (x (n + 1)) ≤ ε) (M : ℕ) (hM : 2 * λ ^ M * δ ≤ reduceScale X δ)
    (hε : ∀ (u : ℕ → X), (∀ n, dist (T (u n)) (u (n + 1)) ≤ ε) →
      ∀ i ≤ M, dist (T^[i] (u 0)) (u i) ≤ reduceScale X δ / 2) :
    ∃ p ∈ locUnstable δ (x 0), ∀ n, dist (x n) (T ^[n] p) < ε := by
  have := lambda_pos (X := X)
  have : λ ^ M ≤ 2⁻¹ := by
    have W := hM.trans reduceScale_le_half_self
    field_simp at W
    linarith
  -- define inductively a sequence by `y₀ = x₀`, and `y_{n+1}` the intersection of `W^u (T^M yₙ)`
  -- and `W^s (x_{M * (n+1)})`.
  let y := Nat.rec (motive := fun n ↦ X) (x 0) (fun n q ↦ ⁅T^[M] q, x (M * (n + 1))⁆)
  have A_aux n (hn : y n ∈ locStable δ (x (M * n))) :
      dist (x (M * (n + 1))) ((⇑T)^[M] (y n)) ≤ reduceScale X δ := by
    apply (dist_triangle_left _ _ (T^[M] (x (M * n)))).trans
    have A : dist (T^[M] (x (M * n))) (x (M * (n + 1))) ≤ reduceScale X δ / 2 :=
      hε (fun k ↦ x (M * n + k)) (fun k ↦ hx (M * n + k)) M le_rfl
    have B : dist (T^[M] (x (M * n))) (T^[M] (y n)) ≤ λ ^ M * δ :=
      (image_iter_mem_locStable h'δ hn M).1
    linarith
  have B n : y n ∈ locStable δ (x (M * n)) := by
    induction n with
    | zero => simp [y, hδ.le, locStable]
    | succ n ih =>
      rw [show y (n + 1) = ⁅T^[M] (y n), x (M * (n + 1))⁆ by rfl]
      exact bracket_mem_locStable (A_aux n ih)
  have A n : dist (x (M * (n + 1))) ((⇑T)^[M] (y n)) ≤ reduceScale X δ :=
    A_aux n (B n)
  have C n : y (n + 1) ∈ locUnstable δ (T^[M] (y n)) := by
    rw [show y (n + 1) = ⁅T^[M] (y n), x (M * (n + 1))⁆ by rfl]
    apply bracket_mem_locUnstable
    rw [dist_comm]
    exact A n
  let z n := T.symm^[M * n] (y n)
  have Z n : z (n + 1) ∈ locUnstable (λ ^ (M * (n + 1)) * δ) (z n) := by
    convert image_iter_mem_locUnstable h'δ (C n) (n := M * (n + 1)) using 2
    have L : Function.LeftInverse T.symm^[M] T^[M] := (Equiv.leftInverse_symm T).iterate _
    rw [mul_add, iterate_add_apply, mul_one, L (y n)]
  have Z' n : z (n + 1) ∈ locUnstable (2⁻¹ ^ (n + 1) * δ) (z n) := by
    apply locUnstable_mono _ (Z n)
    rw [pow_mul]
    gcongr
  sorry

lemma future_shadowing (ε : ℝ) (hε : 0 < ε) (x : ℕ → X)
    (hx : ∀ n, dist (x (n + 1)) (T (x n)) ≤ ε) :
    ∃ p ∈ locUnstable ε (x 0), ∀ n, dist (x n) (T ^[n] p) < ε := by
  sorry

end SmaleSpace
