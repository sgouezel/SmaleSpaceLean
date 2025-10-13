import Mathlib

/-!
# Ruelle brackets

Convention:

 W^+(o)
  |
  u-----⁅s, u⁆
  |       |
  |       |
  |       |
  |       |
--o-------s-- W^-(o)
  |

The stable manifold is the set of points with `⁅x, o⁆ = x`, or equivalently `⁅o, x⁆ = o`.
The unstable manifold is the set of points with `⁅o, y⁆ = y`, or equivalently `⁅y, o⁆ = o`.
The stable manifold is represented horizontally and the unstable manifold vertically,
so that the notation `⁅s, u⁆` for a point parameterized by its stable and unstable components is
analogous to a coordinate notation `(s, u)`. Generally, if `p` and `q` are thought of as
two-dimensional, then `⁅p, q⁆ = (p.1, q.2)` is the intersection of the vertical line through `p`
and the horizontal line through `q`.
-/

open scoped Uniformity Topology
open Function Set Filter Metric

namespace SmaleSpace

variable (X : Type*) [MetricSpace X] {U V : Set (X × X)} {a b c o s u x y z : X} {ε : ℝ}

/-! ### Spaces with a Ruelle bracket -/

/-- A Ruelle bracket on a space is a bracket operation `⁅x, y⁆` corresponding to taking the local
intersection of the stable manifold of `x` and the unstable manifold of `y`. It is only defined for
`x` close enough to `y`.

For the formalization, we require the bracket to be defined everywhere although we will only use
it close to the diagonal, to avoid dependent type issues. We record its algebraic properties,
together with uniform continuity.

We include in the definition the data of a size `δ₀` below which the bracket is well defined.
We could require only its existence, but including it as data makes it possible to be more explicit
in concrete situations. For instance, in subshifts of finite type, we can take `δ₀ = 1`, meaning
that the bracket is well defined on pairs of points sharing the same symbol at coordinate `0`.
-/
class HasRuelleBracket where
  /-- the bracket itself, denoted `⁅x, y⁆` once the theory is set up -/
  toFun : X → X → X
  /-- the bracket is only well behaved below some size `δ₀ > 0` -/
  deltaZero : ℝ
  deltaZero_pos : 0 < deltaZero
  unifCont : UniformContinuousOn (uncurry toFun) {p | dist p.1 p.2 < deltaZero}
  refl x : toFun x x = x
  bracket_left' : ∀ x y z, dist x y < deltaZero → dist y z < deltaZero →
    toFun (toFun x y) z = toFun x z
  bracket_right' : ∀ x y z, dist x y < deltaZero → dist y z < deltaZero →
    toFun x (toFun y z) = toFun x z

instance [h : HasRuelleBracket X] : Bracket X X where
  bracket := h.toFun

export HasRuelleBracket (deltaZero_pos)

local notation3 "δ₀" => HasRuelleBracket.deltaZero X

variable [HasRuelleBracket X]

lemma uniformContinuousOn_bracket :
    UniformContinuousOn (fun (p : X × X) ↦ ⁅p.1, p.2⁆) {p : X × X | dist p.1 p.2 < δ₀} :=
  HasRuelleBracket.unifCont

lemma continuousOn_bracket :
    ContinuousOn (fun (p : X × X) ↦ ⁅p.1, p.2⁆) {p : X × X | dist p.1 p.2 < δ₀} :=
  (uniformContinuousOn_bracket X).continuousOn

variable {X}

@[simp] lemma bracket_self (x : X) : ⁅x, x⁆ = x :=
  HasRuelleBracket.refl x

lemma bracket_left (h : dist x y < δ₀) (h' : dist y z < δ₀) :
    ⁅⁅x, y⁆, z⁆ = ⁅x, z⁆ :=
  HasRuelleBracket.bracket_left' x y z h h'

lemma bracket_right (h : dist x y < δ₀) (h' : dist y z < δ₀) :
    ⁅x, ⁅y, z⁆⁆ = ⁅x, z⁆ :=
  HasRuelleBracket.bracket_right' x y z h h'

/-- If `a` and `b` are close, then `a` and `⁅a, b⁆` are close. -/
lemma tendsto_bracket_fst : Tendsto (fun (p : X × X) ↦ (p.1, ⁅p.1, p.2⁆)) (𝓤 X) (𝓤 X) := by
  intro V hV
  rcases uniformContinuousOn_bracket X hV with ⟨t₁, h₁, t₂, h₂, hV'⟩
  rcases entourageProd_subset h₁ with ⟨u, hu, u', hu', huu'⟩
  have : {p : X × X | dist p.1 p.2 < δ₀} ∈ 𝓤 X := Metric.dist_mem_uniformity deltaZero_pos
  have : {p : X × X | dist p.1 p.2 < δ₀} ∩ u ∩ u' ∈ 𝓤 X := by grind [Filter.inter_mem]
  apply mem_of_superset this
  rintro ⟨a, b⟩ hab
  have M₁ : ((a, a), (a, b)) ∈ t₁ := huu' (by simp [entourageProd, mem_uniformity_of_eq hu, hab.2])
  have M₂ : ((a, a), (a, b)) ∈ t₂ := by
    simp only [mem_principal] at h₂
    apply h₂
    simp [deltaZero_pos, hab.1.1]
  have : ((a, a), (a, b)) ∈ t₁ ∩ t₂ := ⟨M₁, M₂⟩
  simpa [← hV']

/-- If `a` and `b` are close, then `a` and `⁅a, b⁆` are close. -/
lemma tendsto_bracket_snd : Tendsto (fun (p : X × X) ↦ (p.2, ⁅p.1, p.2⁆)) (𝓤 X) (𝓤 X) :=
  tendsto_id.uniformity_symm.uniformity_trans tendsto_bracket_fst

/-- If three points are close, then the first one is close to the bracket of the other ones.
Version in terms of uniformities. -/
lemma exists_bracket_mem_entourage (hU : U ∈ 𝓤 X) :
    ∃ V ∈ 𝓤 X, (∀ x y, (x, y) ∈ V → (y, x) ∈ V) ∧
      ∀ x y z, (y, x) ∈ V → (x, z) ∈ V → ((x, ⁅y, z⁆) ∈ U ∧ (⁅y, z⁆, x) ∈ U) := by
  rcases comp_symm_of_uniformity hU with ⟨U', U'_mem, U'_symm, hU'⟩
  rcases comp_symm_of_uniformity (tendsto_bracket_fst U'_mem) with ⟨V, V_mem, V_symm, hV⟩
  refine ⟨U' ∩ V, inter_mem U'_mem V_mem, fun x y hxy ↦ ⟨U'_symm hxy.1, V_symm hxy.2⟩ ,
    fun x y z hxy hxz ↦ ?_⟩
  have : (y, ⁅y, z⁆) ∈ U' := by
    have : (y, z) ∈ V ○ V := prodMk_mem_compRel hxy.2 hxz.2
    exact hV this
  exact ⟨hU' (prodMk_mem_compRel (U'_symm hxy.1) this),
    hU' (prodMk_mem_compRel (U'_symm this) hxy.1)⟩

variable (X) in
/-- If three points are close, then the first one is clsoe to the bracket of the other ones.
Version in terms of distances. -/
lemma exists_dist_bracket_lt (hε : 0 < ε) :
    ∃ ε' ∈ Ioc 0 ((min ε δ₀) / 2), ∀ x y z,
      dist x y < ε' → dist x z < ε' → dist (x : X) ⁅y, z⁆ < ε := by
  have := deltaZero_pos (X := X)
  have : {p : X × X | dist p.1 p.2 < ε} ∈ 𝓤 X := Metric.dist_mem_uniformity hε
  rcases exists_bracket_mem_entourage this with ⟨V, hV, -, h'V⟩
  rcases Metric.mem_uniformity_dist.1 hV with ⟨ε', ε'_pos, hε'⟩
  refine ⟨min ε' ((min ε δ₀) / 2), ⟨by positivity, min_le_right _ _⟩ , fun x y z hxy hxz ↦ ?_⟩
  refine (h'V _ _ _ (hε' ?_) (hε' (by grind))).1
  rw [dist_comm]
  grind

/-!
### Reducing scales

Given a small scale `ε`, we define a smaller scale `reduceScale X ε` so that points within the
smaller scale have brackets within distance `ε`. We specialize this to `δ₁ := reduceScale X δ₀`.
-/

variable (X) in
/-- The scale `reduceScale X ε` is small enough compared to `ε` so that points within the
smaller scale have brackets within distance `ε`.-/
noncomputable def reduceScale (ε : ℝ) : ℝ :=
  if hε : 0 < ε then (exists_dist_bracket_lt X hε).choose
  else ε

lemma reduceScale_pos (hε : 0 < ε) : 0 < reduceScale X ε := by
  simp only [reduceScale, hε, ↓reduceDIte]
  exact (exists_dist_bracket_lt X hε).choose_spec.1.1

lemma reduceScale_le_half_self : reduceScale X ε ≤ ε / 2 := by
  by_cases hε : 0 < ε
  · simp only [reduceScale, hε, ↓reduceDIte]
    apply (exists_dist_bracket_lt X hε).choose_spec.1.2.trans
    gcongr
    exact min_le_left _ _
  · simp only [reduceScale, hε, ↓reduceDIte]
    linarith

lemma reduceScale_le_half_deltaZero : reduceScale X ε ≤ δ₀ / 2 := by
  by_cases hε : 0 < ε
  · simp only [reduceScale, hε, ↓reduceDIte]
    apply (exists_dist_bracket_lt X hε).choose_spec.1.2.trans
    gcongr
    exact min_le_right _ _
  · simp only [reduceScale, hε, ↓reduceDIte]
    linarith [deltaZero_pos (X := X)]

lemma reduceScale_le_deltaZero : reduceScale X ε ≤ δ₀ := by
  linarith [reduceScale_le_half_deltaZero (X := X) (ε := ε), deltaZero_pos (X := X)]

lemma dist_bracket_lt_of_lt_reduceScale {x y z : X}
    (hxy : dist x y < reduceScale X ε) (hxz : dist x z < reduceScale X ε) :
    dist x ⁅y, z⁆ < ε := by
  by_cases hε : 0 < ε
  · simp only [reduceScale, hε, ↓reduceDIte] at hxy hxz
    exact (exists_dist_bracket_lt X hε).choose_spec.2 x y z hxy hxz
  · simp [reduceScale, hε] at hxy
    linarith [dist_nonneg (x := x) (y := y)]

variable (X) in
/-- A fixed size, sufficiently smaller than `δ₀` to ensure that brackets of points within `δ₁`
remain within `δ₀`. -/
noncomputable def deltaOne : ℝ := reduceScale X δ₀

local notation3 "δ₁" => deltaOne X

lemma deltaOne_pos : 0 < δ₁ := reduceScale_pos deltaZero_pos

lemma deltaOne_le_half_deltaZero : δ₁ ≤ δ₀ / 2 := reduceScale_le_half_deltaZero

lemma deltaOne_le_deltaZero : δ₁ ≤ δ₀ := by
  linarith [deltaOne_le_half_deltaZero (X := X), deltaZero_pos (X := X)]

lemma dist_bracket_lt_deltaZero {x y z : X} (hxy : dist x y < δ₁) (hxz : dist x z < δ₁) :
    dist x ⁅y, z⁆ < δ₀ := dist_bracket_lt_of_lt_reduceScale hxy hxz

/-!
### Local stable and unstable manifolds, local parametrization with product coordinates
-/

/-- The local stable manifold of `o` inside an entourage `U`, defined as the set of points `s` which
are `U`-close to `o` and satisfy `⁅s, o⁆ = s`.
Equivalently, these are the points with `⁅o, s⁆ = o`, see `locStable_eq`. -/
def locStable (ε : ℝ) (o : X) : Set X := {s | dist o s < ε ∧ ⁅s, o⁆ = s}

/-- The local unstable manifold of `o` inside an entourage `U`, defined as the set of points `u`
which are `U`-close to `o` and satisfy `⁅o, u⁆ = u`.
Equivalently, these are the points with `⁅u, o⁆ = o`, see `locUnstable_eq`. -/
def locUnstable (ε : ℝ) (o : X) : Set X := {u | dist o u < ε ∧ ⁅o, u⁆ = u}

lemma mem_of_mem_locStable (hs : s ∈ locStable ε o) : dist o s < ε := hs.1

lemma bracket_eq_of_mem_locStable (hs : s ∈ locStable ε o) : ⁅s, o⁆ = s := hs.2

lemma locStable_eq (hε : ε ≤ δ₀) : locStable ε o = {s | dist o s < ε ∧ ⁅o, s⁆ = o} := by
  ext s
  have : dist o s = dist s o := PseudoMetricSpace.dist_comm o s
  simp only [locStable, mem_setOf_eq, and_congr_right_iff]
  intro h
  refine ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩
  · rw [← h', bracket_right, bracket_self] <;> linarith
  · rw [← h', bracket_right, bracket_self] <;> linarith

lemma mem_of_mem_locUnstable (hu : u ∈ locUnstable ε o) : dist o u < ε := hu.1

lemma bracket_eq_of_mem_locUnstable (hu : u ∈ locUnstable ε o) : ⁅o, u⁆ = u := hu.2

lemma locUnstable_eq (hε : ε ≤ δ₀) : locUnstable ε o = {u | dist o u < ε ∧ ⁅u, o⁆ = o} := by
  ext u
  have : dist o u = dist u o := PseudoMetricSpace.dist_comm o u
  simp only [locUnstable, mem_setOf_eq, and_congr_right_iff]
  intro h
  refine ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩
  · rw [← h', bracket_left, bracket_self] <;> linarith
  · rw [← h', bracket_left, bracket_self] <;> linarith

/-- For small enough `ε`, one can parametrize a neighborhood of any point `o` by
taking the bracket of points on its stable and unstable manifolds of size `ε`.

The fact that the target of this parametrization is indeed a neighborhood of `o` (of
fixed size `reduceScale X ε`) is given in `ball_reduceScale_subset_target_localProduct`.
-/
@[simps!]
def localProductEquiv (hε : ε ≤ δ₁) (o : X) : PartialEquiv (X × X) X where
  toFun p := ⁅p.1, p.2⁆
  invFun z := (⁅z, o⁆, ⁅o, z⁆)
  source := (locStable ε o) ×ˢ (locUnstable ε o)
  target := {y | dist o y < δ₀ ∧ dist o ⁅o, y⁆ < ε ∧ dist o ⁅y, o⁆ < ε}
  map_source' := by
    rintro ⟨s, u⟩ ⟨hs, hu⟩
    have h's : dist o s < ε := mem_of_mem_locStable hs
    have h'u : dist o u < ε := mem_of_mem_locUnstable hu
    have : dist s u < δ₀ := by
      linarith [dist_triangle_left s u o, deltaOne_le_half_deltaZero (X := X)]
    have := deltaOne_le_deltaZero (X := X)
    simp only [mem_setOf_eq]
    refine ⟨?_, ?_, ?_⟩
    · exact dist_bracket_lt_deltaZero (by linarith) (by linarith)
    · rwa [bracket_right, bracket_eq_of_mem_locUnstable hu] <;> linarith
    · rwa [bracket_left, bracket_eq_of_mem_locStable hs]
      · linarith
      · rw [dist_comm]
        linarith
  map_target' := by
    rintro x ⟨hx_main, hx, h'x⟩
    simp only [locStable, locUnstable, mem_prod, mem_setOf_eq, h'x, true_and, hx]
    rw [bracket_left, bracket_right] <;> simp [deltaZero_pos, dist_comm, hx_main]
  left_inv' := by
    rintro ⟨s, u⟩ ⟨hs, hu⟩
    have h's : dist o s < ε := mem_of_mem_locStable hs
    have h'u : dist o u < ε := mem_of_mem_locUnstable hu
    have : dist s u < δ₀ := by
      linarith [dist_triangle_left s u o, deltaOne_le_half_deltaZero (X := X)]
    have := deltaOne_le_deltaZero (X := X)
    simp only [Prod.mk.injEq]
    constructor
    · rw [bracket_left]
      · exact bracket_eq_of_mem_locStable hs
      · linarith
      · rw [dist_comm]
        linarith
    · rw [bracket_right]
      · exact bracket_eq_of_mem_locUnstable hu
      · linarith
      · linarith
  right_inv' := by
    intro x ⟨hx, h'x, h''x⟩
    simp only
    rw [bracket_left, bracket_right, bracket_self]
    · rwa [dist_comm]
    · exact hx
    · rwa [dist_comm]
    · linarith [deltaOne_le_deltaZero (X := X)]

lemma continuousOn_localProductEquiv (hε : ε ≤ δ₁) :
    ContinuousOn (localProductEquiv hε o) (localProductEquiv hε o).source := by
  apply (continuousOn_bracket X).mono
  rintro ⟨s, u⟩ ⟨⟨hs, h's⟩, ⟨hu, h'u⟩⟩
  simp only [mem_setOf_eq] at hs hu ⊢
  linarith [dist_triangle_left s u o, deltaOne_le_half_deltaZero (X := X)]

lemma continuousOn_symm_localProductEquiv (hε : ε ≤ δ₁) :
    ContinuousOn (localProductEquiv hε o).symm (localProductEquiv hε o).target := by
  apply ContinuousOn.prodMk
  · apply (continuousOn_bracket X).comp (Continuous.prodMk_left o).continuousOn
    intro x ⟨hxo, hx, h'x⟩
    simpa [dist_comm] using hxo
  · apply (continuousOn_bracket X).comp (Continuous.prodMk_right o).continuousOn
    intro x ⟨hxo, hx, h'x⟩
    exact hxo

/-- Given a small enough entourage `U`, the ball around `o` for the smaller
entourage `bracketRoot U` is covered by the local product parametrization coming from `U`.-/
lemma ball_reduceScale_subset_target_localProductEquiv (hε : ε ≤ δ₁) :
    ball o (reduceScale X ε) ⊆ (localProductEquiv hε o).target := by
  by_cases hε : 0 < ε; swap
  · simp only [reduceScale, hε, ↓reduceDIte, localProductEquiv_target]
    rw [Metric.ball_eq_empty.2 (by linarith)]
    simp
  intro y (hy : dist y o < reduceScale X ε)
  rw [dist_comm] at hy
  simp only [localProductEquiv_target, mem_setOf_eq]
  refine ⟨?_, ?_, ?_⟩
  · exact hy.trans_le reduceScale_le_deltaZero
  · apply dist_bracket_lt_of_lt_reduceScale _ hy
    simp [reduceScale_pos hε]
  · apply dist_bracket_lt_of_lt_reduceScale hy
    simp [reduceScale_pos hε]

lemma target_localProductEquiv_mem_nhds (hε : ε ≤ δ₁) (h'ε : 0 < ε) :
    (localProductEquiv hε o).target ∈ 𝓝 o := by
  apply mem_of_superset _ (ball_reduceScale_subset_target_localProductEquiv hε)
  exact ball_mem_nhds _ (reduceScale_pos h'ε)

end SmaleSpace
