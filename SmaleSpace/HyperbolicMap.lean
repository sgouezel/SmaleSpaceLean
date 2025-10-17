import SmaleSpace.Bracket

open scoped Uniformity Topology
open Function Set Filter Metric

namespace SmaleSpace

variable (X : Type*) [MetricSpace X] {U V : Set (X × X)} {a b c o s u x y z : X} {ε : ℝ} {n : ℕ}

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

export HasRuelleBracketWithMap (lambda_pos lambda_lt_one bracket_image expansion contraction
  unifCont_T unifCont_Tsymm)

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

variable {X}
variable [HasRuelleBracketWithMap X]

@[fun_prop]
lemma continuous_T : Continuous T := unifCont_T.continuous

@[fun_prop]
lemma continuous_Tsymm : Continuous T.symm := unifCont_Tsymm.continuous

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

lemma image_mem_locUnstable (hε : ε ≤ δ₀) (h : x ∈ locUnstable ε o) :
    T.symm x ∈ locUnstable (λ * ε) (T.symm o) :=
  image_mem_locStable (X := invDyn X) (by exact hε) h

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

lemma image_iter_mem_locUnstable (hε : ε ≤ δ₀) (h : x ∈ locUnstable ε o) (n : ℕ) :
    T.symm^[n] x ∈ locUnstable (λ ^ n * ε) (T.symm^[n] o) :=
  image_iter_mem_locStable (X := invDyn X) (by exact hε) h n

variable [HasReduceScale X]

/-- If two points follow each other during time `n`, then the difference between their unstable
components is exponentially small. -/
lemma mem_locUnstable_lambda_pow_of_forall_dist_le
    (hx : ∀ i ≤ n, dist (T^[i] o) (T^[i] x) ≤ δ₁) :
    ⁅o, x⁆ ∈ locUnstable (λ ^ n * δ₀) o := by
  let y i := ⁅T^[i] o, T^[i] x⁆
  have A i (hi : i < n) : T (y i) = y (i + 1) := by
    simp only [y, iterate_succ_apply']
    rw [bracket_image]
    · apply (hx i hi.le).trans deltaOne_le_deltaZero
    · simp only [← iterate_succ_apply']
      apply (hx (i + 1) (by omega)).trans deltaOne_le_deltaZero
  have A' i (hi : i ≤ n) : y i = T^[i] (y 0) := by
    induction i with
    | zero => simp
    | succ i ih => rw [← A _ (by omega), ih (by omega), iterate_succ_apply']
  have B : y n ∈ locUnstable δ₀ (T^[n] o) := by
    apply bracket_mem_locUnstable
    exact hx n le_rfl
  have : y 0 ∈ locUnstable (λ ^ n * δ₀) o := by
    have L : Function.LeftInverse T.symm^[n] T^[n] := (Equiv.leftInverse_symm T).iterate _
    convert image_iter_mem_locUnstable le_rfl B n
    · rw [L o]
    · rw [A' n le_rfl, L (y 0)]
  exact this

/-- If two points follow each other during time `n` in the past, then the difference between their
stable components is exponentially small. -/
lemma mem_locStable_lambda_pow_of_forall_dist_le
    (hx : ∀ i ≤ n, dist (T.symm^[i] o) (T.symm^[i] x) ≤ δ₁) :
    ⁅x, o⁆ ∈ locStable (λ ^ n * δ₀) o :=
  mem_locUnstable_lambda_pow_of_forall_dist_le (X := invDyn X) hx

/-- The local stable manifold of a point `o` of size `ε` is exactly the set of points that
remain within distance `ε` of the orbit of `o` in the future. -/
lemma locStable_eq_dist_iter_le (hε : ε ≤ δ₁) :
    locStable ε o = {x | ∀ n, dist (T^[n] o) (T^[n] x) ≤ ε} := by
  have h'ε : ε ≤ δ₀ := hε.trans deltaOne_le_deltaZero
  apply Subset.antisymm
  · intro x hx n
    apply (image_iter_mem_locStable h'ε hx n).1.trans
    have : λ ^ n ≤ 1 := pow_le_one₀ lambda_pos.le lambda_lt_one.le
    have : 0 ≤ ε := dist_nonneg.trans hx.1
    nlinarith
  · intro x hx
    rw [locStable_eq (hε.trans deltaOne_le_deltaZero)]
    refine ⟨hx 0, ?_⟩
    have C n : ⁅o, x⁆ ∈ locUnstable (λ ^ n * δ₀) o := by
      apply mem_locUnstable_lambda_pow_of_forall_dist_le (fun i hi ↦ (hx i).trans hε)
    have : dist o ⁅o, x⁆ = 0 := by
      apply le_antisymm ?_ dist_nonneg
      have : Tendsto (fun n ↦ λ ^ n * δ₀) atTop (𝓝 (0 * δ₀)) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one lambda_pos.le lambda_lt_one).mul_const _
      rw [zero_mul] at this
      exact ge_of_tendsto' this (fun n ↦ (C n).1)
    simp only [dist_eq_zero] at this
    exact this.symm

/-- The local unstable manifold of a point `o` of size `ε` is exactly the set of points that
remain within distance `ε` of the orbit of `o` in the past. -/
lemma locUnstable_eq_dist_iter_le (hε : ε ≤ δ₁) :
    locUnstable ε o = {x | ∀ n, dist (T.symm^[n] o) (T.symm^[n] x) ≤ ε} :=
  locStable_eq_dist_iter_le (X := invDyn X) hε

/-- If two points follow each other during time `n`, both in the past and in the future, then they
are exponentially close. -/
lemma expansive_finite_time (h : ∀ i ≤ n, dist (T^[i] x) (T^[i] y) ≤ δ₁)
    (h' : ∀ i ≤ n, dist (T.symm^[i] x) (T.symm^[i] y) ≤ δ₁) :
    dist x y ≤ 2 * λ^n * δ₀ := by
  have : dist x ⁅y, x⁆ ≤ λ ^ n * δ₀ := (mem_locStable_lambda_pow_of_forall_dist_le h').1
  have : dist y ⁅y, x⁆ ≤ λ ^ n * δ₀ := by
    have : ∀ i ≤ n, dist (T^[i] y) (T^[i] x) ≤ δ₁ := by
      intro i hi
      rw [dist_comm]
      exact h i hi
    exact (mem_locUnstable_lambda_pow_of_forall_dist_le this).1
  linarith [dist_triangle_right x y ⁅y, x⁆]

/-- If two points follow each other during time `n`, both in the past and in the future, then they
are exponentially close. -/
lemma expansive_finite_time' (h : ∀ (i : ℤ), i.natAbs ≤ n → dist ((T ^ i) x) ((T ^ i) y) ≤ δ₁) :
    dist x y ≤ 2 * λ^n * δ₀ := by
  apply expansive_finite_time
  · intro i hi
    exact h (i : ℤ) (by omega)
  · intro i hi
    have : T.symm^[i] = ⇑(T ^ (-i : ℤ)) := by
      simp only [Equiv.Perm.iterate_eq_pow, zpow_neg, zpow_natCast, DFunLike.coe_fn_eq]
      rfl
    convert h (-i : ℤ) (by omega)

/-- If two points follow each other, both in the past and in the future, then they coincide. -/
lemma expansive (h : ∀ i, dist (T^[i] x) (T^[i] y) ≤ δ₁)
    (h' : ∀ i, dist (T.symm^[i] x) (T.symm^[i] y) ≤ δ₁) : x = y := by
  apply eq_of_dist_eq_zero
  apply le_antisymm ?_ dist_nonneg
  have : Tendsto (fun n ↦ 2 * λ ^ n * δ₀) atTop (𝓝 (2 * 0 * δ₀)) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one lambda_pos.le lambda_lt_one).const_mul _).mul_const _
  rw [mul_zero, zero_mul] at this
  apply ge_of_tendsto' this (fun n ↦ ?_)
  apply expansive_finite_time (fun i hi ↦ h i) (fun i hi ↦ h' i)

/-- If two points follow each other, both in the past and in the future, then they coincide. -/
lemma expansive' (h : ∀ (i : ℤ), dist ((T ^ i) x) ((T ^ i) y) ≤ δ₁) : x = y := by
  apply expansive (fun i ↦ h i) (fun i ↦ ?_)
  have : T.symm^[i] = ⇑(T ^ (-i : ℤ)) := by
    simp only [Equiv.Perm.iterate_eq_pow, zpow_neg, zpow_natCast, DFunLike.coe_fn_eq]
    rfl
  convert h (-i : ℤ)






/-- Given a positive parameter `δ`, an integer `n` and a uniformly continuous map `f`, one may find
`ε > 0` such that any `ε`-pseudo-orbit does not deviate from a genuine orbit by more than `δ`
during the first `n` iterates. -/
lemma exists_dist_image_iter_le_of_pseudoOrbit
    {Y : Type*} [MetricSpace Y] {f : Y → Y} (hf : UniformContinuous f)
    {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    ∃ ε > 0, ∀ (u : ℕ → Y), (∀ n, dist (f (u n)) (u (n + 1)) ≤ ε) →
      ∀ i ≤ n, dist (f ^[i] (u 0)) (u i) ≤ δ := by
  /- This is a straightforward consequence of uniform continuity (through an induction). -/
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

variable [CompleteSpace X]

--TODO: upstream
attribute [fun_prop] Continuous.iterate

/-- Let `δ > 0`. Let `ε` be small enough compared to `δ`. Then any `ε`-pseudo-orbit in the future
can be `4δ`-shadowed by a genuine orbit, starting from the `δ`-unstable manifold of the initial
point.

We give the conditions on `ε` in explicit form, to make it possible to check them uniformly
over families of maps. First, we fix `M` large enough so that `2 * λ ^ M * δ ≤ reduceScale X δ`.
Then, `ε` should be small enough that an `ε`-pseudo-orbit does not deviate from a genuine orbit
by more than `reduceScale X δ / 2` until time `M`.
-/
lemma future_shadowing_precise
    {ε δ : ℝ} (hδ : 0 < δ) (h''δ : δ ≤ δ₀ / 2) (x : ℕ → X)
    (hx : ∀ n, dist (T (x n)) (x (n + 1)) ≤ ε) {M : ℕ} (hM : 2 * λ ^ M * δ ≤ reduceScale X δ)
    (hε : ∀ (u : ℕ → X), (∀ n, dist (T (u n)) (u (n + 1)) ≤ ε) →
      ∀ i ≤ M, dist (T^[i] (u 0)) (u i) ≤ reduceScale X δ / 2) :
    ∃ p ∈ locUnstable δ (x 0), ∀ n, dist (x n) (T ^[n] p) ≤ 4 * δ := by
  -- Start by recording useful basic facts
  have : Nonempty X := ⟨x 0⟩
  have := lambda_pos (X := X)
  have lambdaM : λ ^ M ≤ 2⁻¹ := by
    have W := hM.trans reduceScale_le_half_self
    field_simp at W
    linarith
  have : M ≠ 0 := by
    intro h
    simp only [h, pow_zero] at lambdaM
    norm_num at lambdaM
  have h'δ : δ ≤ δ₀ := by linarith [deltaZero_pos (X := X)]
  have L n : Function.LeftInverse T.symm^[n] T^[n] := (Equiv.leftInverse_symm T).iterate _
  have L' n : Function.LeftInverse T^[n] T.symm^[n] := (Equiv.leftInverse_symm T.symm).iterate _
  /- define inductively a sequence by `y₀ = x₀`, and `y_{n+1}` the intersection of `W^u (T^M yₙ)`
  and `W^s (x_{M * (n + 1)})`.
  We will prove in the course of the proof that the displacement along the unstable manifold made
  at step `n` when going from `T^M yₙ` to `y_{n+1}` is always by at most `δ`. Pulling back `yₙ` by
  `T^{-n}` inside `W^u (x₀)`, one gets a sequence with jumps bounded by `δ 2^{-n}`, therefore Cauchy
  and converging. By design, its limit will be the desired point.
  -/
  let y := Nat.rec (motive := fun n ↦ X) (x 0) (fun n q ↦ ⁅T^[M] q, x (M * (n + 1))⁆)
  /- First, we will check inductively that `yₙ` is on the `δ`-stable manifold of `x_{M * n}`.
  It follows that its image under `T^M` is even closer to `x_{M * (n + 1)}`, therefore taking the
  bracket one remains within `δ`, completing the induction. -/
  have A_aux n (hn : y n ∈ locStable δ (x (M * n))) :
      dist (x (M * (n + 1))) (T^[M] (y n)) ≤ reduceScale X δ := by
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
  have A n : dist (x (M * (n + 1))) (T^[M] (y n)) ≤ reduceScale X δ :=
    A_aux n (B n)
  have C n : y (n + 1) ∈ locUnstable δ (T^[M] (y n)) := by
    rw [show y (n + 1) = ⁅T^[M] (y n), x (M * (n + 1))⁆ by rfl]
    apply bracket_mem_locUnstable
    rw [dist_comm]
    exact A n
  /- Define a sequence `z_{i, n}` around `x_{M * i}`, as the pullback of `y_{i + n}` from `n` times
  later in the future. We are mostly interested in `z_{0,n}` (which will converge to the desired
  point) but for the estimates we will need to control what happens at an arbitrary `i`. Thanks to
  the contracting properties of `T⁻¹` along unstable manifolds, `n ↦ z_{i,n}` has successive jumps
  of size at most `2^{-(n+1)} δ`, and is therefore converging to a limit `pᵢ` belonging to
  the stable manifold of `yᵢ` of size `δ`. -/
  let z i n := T.symm^[M * n] (y (i + n))
  have Z i n : z i (n + 1) ∈ locUnstable (λ ^ (M * (n + 1)) * δ) (z i n) := by
    convert image_iter_mem_locUnstable h'δ (C (i + n)) (n := M * (n + 1)) using 2
    rw [mul_add, iterate_add_apply, mul_one, L]
  have Z' i n : z i (n + 1) ∈ locUnstable (2⁻¹ ^ (n + 1) * δ) (z i n) := by
    apply locUnstable_mono _ (Z i n)
    rw [pow_mul]
    gcongr
  let p i := limUnder atTop (z i)
  have Lim i : Tendsto (z i) atTop (𝓝 (p i)) := by
    apply tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete ?_)
    apply cauchySeq_of_le_geometric_two (C := δ) (fun n ↦ ?_)
    apply (Z' i n).1.trans_eq
    simp only [inv_pow, pow_succ]
    field_simp
  have I n : T^[M * n] (p 0) = p n := by
    have L1 : Tendsto (fun i ↦ T^[M * n] (z 0 i)) atTop (𝓝 (T^[M * n] (p 0))) := by
      have : ContinuousAt (T^[M * n]) (p 0) := by fun_prop
      exact Tendsto.comp this (Lim 0)
    have L'1 : Tendsto (fun i ↦ T^[M * n] (z 0 (n + i))) atTop (𝓝 (T^[M * n] (p 0))) := by
      simpa [add_comm] using (tendsto_add_atTop_iff_nat n).2 L1
    have L2 : Tendsto (fun i ↦ T^[M * n] (z 0 (n + i))) atTop (𝓝 (p n)) := by
      convert Lim n using 2 with i
      simp only [z]
      rw [mul_add, iterate_add_apply, L', zero_add]
    exact tendsto_nhds_unique L'1 L2
  have H i n : z i n ∈ locUnstable ((1 - 2⁻¹ ^ n) * δ) (y i) := by
    induction n with
    | zero => simp [z]
    | succ n ih =>
      have A : (1 - 2⁻¹ ^ n) * δ + 2⁻¹ ^ (n + 1) * δ = (1 - 2⁻¹ ^ (n + 1)) * δ := by ring
      have W := mem_locUnstable_trans ih (Z' i n)
      rw [A] at W
      apply W
      apply le_trans _ h'δ
      apply mul_le_of_le_one_left hδ.le (by simp)
  have P i : p i ∈ locUnstable δ (y i) := by
    apply IsClosed.mem_of_tendsto (isClosed_locUnstable h'δ) (Lim i)
      (Eventually.of_forall (fun n ↦ ?_))
    apply locUnstable_mono _ (H i n)
    simp [sub_mul, hδ.le]
  /- The point `p₀` will satisfy the conclusion of the lemma. To control the distance between
  `T^n (p₀)` and `xₙ`, we write `n = M a + b`. The points `x_{M a}` and `yₐ` are on the same
  stable manifold of size `δ`, so their images under `T^b` are `δ`-close. Moreover, the image
  `T^b (x_{M a})` is `δ` close to `x_{M a + b}` by the `ε`-pseudoorbit property. It remains
  to see that `T^b yₐ` is `2δ`-close to `T^n p₀` to conclude. At time `(M+1) a`, the corresponding
  points are on a common unstable manifold of size `2δ` by construction (as `y_{a+1}` is on the
  `δ`-unstable manifold of `T^M yₐ` and `p_{a+1}` is on the `δ`-unstable manifold of `y_{a+1}`.)
  Pulling back by `T^{-(M-b)}`, which contracts distances along unstable manifolds, we get the
  desired bound by `2δ`. -/
  refine ⟨p 0, P 0, fun n ↦ ?_⟩
  obtain ⟨a, b, hb, rfl⟩ : ∃ (a b : ℕ), b < M ∧ n = M * a + b :=
    ⟨n / M, n % M, Nat.mod_lt n (by omega), by rw [Nat.div_add_mod]⟩
  have : dist (x (M * a + b)) (T^[M * a + b] (p 0)) ≤ dist (x (M * a + b)) (T^[b] (x (M * a)))
      + dist (T^[b] (x (M * a))) (T^[b] (y a)) + dist (T^[b] (y a)) (T^[M * a + b] (p 0)) :=
    dist_triangle4 _ _ _ _
  have : dist (x (M * a + b)) (T^[b] (x (M * a))) ≤ δ := by
    have : dist (x (M * a + b)) (T^[b] (x (M * a))) ≤ reduceScale X δ / 2 := by
      rw [dist_comm]
      exact hε (fun i ↦ x (M * a + i)) (fun n ↦ hx _) b hb.le
    exact this.trans (by linarith [reduceScale_le_half_self (X := X) (ε := δ)])
  have : dist (T^[b] (x (M * a))) (T^[b] (y a)) ≤ δ := by
    apply (image_iter_mem_locStable h'δ (B a) b).1.trans
    apply mul_le_of_le_one_left hδ.le
    apply pow_le_one₀ lambda_pos.le lambda_lt_one.le
  have : dist (T^[b] (y a)) (T^[M * a + b] (p 0)) ≤ 2 * δ := by
    have E1 : T^[b] (y a) = T.symm^[M-b] (T^[M] (y a)) := by
      have : M = M-b + b := by omega
      nth_rw 2 [this]
      rw [iterate_add_apply, L]
    have E2 : T^[M * a + b] (p 0) = T.symm^[M-b] (p (a + 1)) := by
      have : M * (a + 1) = (M - b) + (M * a + b) := by rw [mul_add]; omega
      rw [← I (a + 1), this, iterate_add_apply _ (M - b), L]
    rw [E1, E2]
    have : p (a + 1) ∈ locUnstable (δ + δ) (T^[M] (y a)) :=
      mem_locUnstable_trans (C a) (P (a + 1)) (by linarith)
    apply (image_iter_mem_locUnstable (by linarith) this (M - b)).1.trans
    apply (mul_le_of_le_one_left (by linarith) _).trans_eq (by ring)
    apply pow_le_one₀ lambda_pos.le lambda_lt_one.le
  linarith

/-- Let `δ > 0`. Let `ε` be small enough compared to `δ`. Then any `ε`-pseudo-orbit
can be `4δ`-shadowed by a genuine orbit.

We give the conditions on `ε` in explicit form, to make it possible to check them uniformly
over families of maps. First, we fix `M` large enough so that `2 * λ ^ M * δ ≤ reduceScale X δ`.
Then, `ε` should be small enough that an `ε`-pseudo-orbit does not deviate from a genuine orbit
by more than `reduceScale X δ / 2` until time `M`.
-/
lemma shadowing_precise
    {ε δ : ℝ} (hδ : 0 < δ) (h''δ : δ ≤ δ₁ / 4) (x : ℤ → X)
    (hx : ∀ n, dist (T (x n)) (x (n + 1)) ≤ ε) {M : ℕ} (hM : 2 * λ ^ M * δ ≤ reduceScale X δ)
    (hε : ∀ (u : ℕ → X), (∀ n, dist (T (u n)) (u (n + 1)) ≤ ε) →
      ∀ i ≤ M, dist (T^[i] (u 0)) (u i) ≤ reduceScale X δ / 2) :
    ∃ p, ∀ n, dist (x n) ((T ^ n) p) ≤ 4 * δ := by
  have h'δ : δ ≤ δ₀ / 2 := by linarith [deltaOne_le_deltaZero (X := X)]
  have A n : ∃ p, (∀ (i : ℕ), dist (x i) (T^[i] p) ≤ 4 * δ)
      ∧ (∀ (i : ℕ), i ≤ n → dist (x (-i)) (T.symm^[i] p) ≤ 4 * δ) := by
    rcases future_shadowing_precise hδ h'δ (ε := ε) (fun i ↦ x (i - n : ℤ))
      (fun i ↦ by convert hx (i - n) using 3; omega) hM hε with ⟨q, -, hq⟩
    refine ⟨T^[n] q, fun i ↦ ?_, fun i hi ↦ ?_⟩
    · rw [← iterate_add_apply]
      convert hq (i + n)
      omega
    · have L : Function.LeftInverse T.symm^[i] T^[i] := (Equiv.leftInverse_symm T).iterate _
      have : n = i + (n - i) := by omega
      rw [this, iterate_add_apply, L]
      convert hq (n - i) using 3
      omega





#exit


lemma shadowing {δ : ℝ} (hδ : 0 < δ) : ∃ ε > 0, ∀ (x : ℤ → X),
    (∀ n, dist (T (x n)) (x (n + 1)) ≤ ε) → ∃ p, ∀ n, dist (x n) ((T ^ n) p) ≤ 4 * δ := by
  let δ' := min δ (δ₀ / 2)
  have : 0 < δ' := by
    simp [δ', hδ]


end SmaleSpace
