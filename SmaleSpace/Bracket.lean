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

section

-- PRed to mathlib in UniformSpace.Basic, remove when upstreamed

variable {α β γ : Type*} [UniformSpace α] [UniformSpace β] [UniformSpace γ] {f : α → β} {g : β → γ}
  {s t : Set α}

lemma UniformContinuous.uniformContinuousOn
    (hf : UniformContinuous f)  : UniformContinuousOn f s :=
  tendsto_inf_left hf

lemma UniformContinuousOn.mono (hf : UniformContinuousOn f s) (ht : t ⊆ s) :
    UniformContinuousOn f t :=
  Tendsto.mono_left hf (inf_le_inf le_rfl (by simp [ht]))

lemma UniformContinuous.swap : UniformContinuous (Prod.swap : α × β → β × α) :=
  uniformContinuous_snd.prodMk uniformContinuous_fst

lemma UniformContinuousOn.comp
    {t : Set β} (hg : UniformContinuousOn g t)
    (hf : UniformContinuousOn f s) (hst : MapsTo f s t) : UniformContinuousOn (g ∘ f) s := by
  change Tendsto ((fun x ↦ (g x.1, g x.2)) ∘ (fun x ↦ (f x.1, f x.2))) (𝓤 α ⊓ 𝓟 (s ×ˢ s)) (𝓤 γ)
  apply Tendsto.comp hg
  refine tendsto_inf.2 ⟨hf, tendsto_inf_right ?_⟩
  simp only [tendsto_principal, mem_prod, eventually_principal, and_imp, Prod.forall]
  exact fun a b ha hb ↦ ⟨hst ha, hst hb⟩

lemma UniformContinuous.comp_uniformContinuousOn
    (hg : UniformContinuous g) (hf : UniformContinuousOn f s) : UniformContinuousOn (g ∘ f) s :=
  (hg.uniformContinuousOn (s := univ)).comp hf (mapsTo_univ _ _)

end

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
/-- In a space with a Ruelle bracket, we introduce a function `reduceScale` associating to `ε`
a smaller scale so that points within the smaller scale have brackets within distance `ε`.
Such a function always exists (by continuity) but instead we provide it as data:
having a control of this function over a whole family of systems is important when proving
structural stability, so we can not just rely on choice to get it.
To get one such arbitrary function, one can use `hasReduceScaleDefault`. -/
class HasReduceScale where
  /-- The scale `reduceScale X ε` is small enough compared to `ε` so that points within the
  smaller scale have brackets within distance `ε`.-/
  reduceScale (ε : ℝ) : ℝ
  reduceScale_pos {ε : ℝ} (hε : 0 < ε) : 0 < reduceScale ε
  reduceScale_le_half_self {ε : ℝ} : reduceScale ε ≤ ε / 2
  reduceScale_le_half_deltaZero {ε : ℝ}: reduceScale ε ≤ δ₀ / 2
  dist_bracket_lt_of_lt_reduceScale {ε : ℝ} {x y z : X}
    (hxy : dist x y < reduceScale ε) (hxz : dist x z < reduceScale ε) :
    dist x ⁅y, z⁆ < ε

/-- A possible construction of an arbitrary reducing scale function, based on
continuity and choice. -/
noncomputable def hasReduceScaleDefault : HasReduceScale X where
  reduceScale (ε : ℝ) : ℝ :=
    if hε : 0 < ε then (exists_dist_bracket_lt X hε).choose
    else ε
  reduceScale_pos hε := by
    simp only [hε, ↓reduceDIte]
    exact (exists_dist_bracket_lt X hε).choose_spec.1.1
  reduceScale_le_half_self {ε} := by
    by_cases hε : 0 < ε
    · simp only [hε, ↓reduceDIte]
      apply (exists_dist_bracket_lt X hε).choose_spec.1.2.trans
      gcongr
      exact min_le_left _ _
    · simp only [hε, ↓reduceDIte]
      linarith
  reduceScale_le_half_deltaZero {ε} := by
    by_cases hε : 0 < ε
    · simp only [hε, ↓reduceDIte]
      apply (exists_dist_bracket_lt X hε).choose_spec.1.2.trans
      gcongr
      exact min_le_right _ _
    · simp only [hε, ↓reduceDIte]
      linarith [deltaZero_pos (X := X)]
  dist_bracket_lt_of_lt_reduceScale {ε x y z} hxy hxz := by
    by_cases hε : 0 < ε
    · simp only [hε, ↓reduceDIte] at hxy hxz
      exact (exists_dist_bracket_lt X hε).choose_spec.2 x y z hxy hxz
    · simp [hε] at hxy
      linarith [dist_nonneg (x := x) (y := y)]

export HasReduceScale (reduceScale reduceScale_pos reduceScale_le_half_self
  reduceScale_le_half_deltaZero dist_bracket_lt_of_lt_reduceScale)

section

variable [HasReduceScale X]

lemma reduceScale_le_deltaZero : reduceScale X ε ≤ δ₀ := by
  linarith [reduceScale_le_half_deltaZero (X := X) (ε := ε), deltaZero_pos (X := X)]

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

end

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

lemma bracket_mem_locStable [HasReduceScale X] (hx : dist o x < reduceScale X ε) :
    ⁅x, o⁆ ∈ locStable ε o := by
  refine ⟨?_, ?_⟩
  · apply dist_bracket_lt_of_lt_reduceScale hx
    simp only [dist_self]
    apply lt_of_le_of_lt (by positivity) hx
  · rw [bracket_left]
    · rw [dist_comm]
      apply hx.trans_le reduceScale_le_deltaZero
    · simp [deltaZero_pos]

lemma locStable_mono {ε ε' : ℝ} (h : ε ≤ ε') : locStable ε o ⊆ locStable ε' o := by
  simp only [locStable, setOf_subset_setOf, and_imp]
  grind

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

lemma bracket_mem_locUnstable [HasReduceScale X] (hx : dist o x < reduceScale X ε) :
    ⁅o, x⁆ ∈ locUnstable ε o := by
  refine ⟨?_, ?_⟩
  · apply dist_bracket_lt_of_lt_reduceScale _ hx
    simp only [dist_self]
    apply lt_of_le_of_lt (by positivity) hx
  · rw [bracket_right]
    · simp [deltaZero_pos]
    · apply hx.trans_le reduceScale_le_deltaZero

lemma locUnstable_mono {ε ε' : ℝ} (h : ε ≤ ε') : locUnstable ε o ⊆ locUnstable ε' o := by
  simp only [locUnstable, setOf_subset_setOf, and_imp]
  grind

variable [HasReduceScale X]
local notation3 "δ₁" => deltaOne X

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
  · rw [Metric.ball_eq_empty.2]
    · simp
    apply reduceScale_le_half_self.trans
    linarith
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

/-!
### Reversing stable and unstable direction

It is often convenient to prove something for the unstable direction, and then deduce it for the
stable one, or conversely. For this, we endow the type copy `Xᵒᵖ` with the reverse bracket and
the reverse dynamics.
-/

def invDyn (X : Type*) : Type _ := X

def ofInvDyn {X : Type*} (x : invDyn X) : X := x

def toInvDyn {X : Type*} (x : X) : invDyn X := x

instance : MetricSpace (invDyn X) := inferInstanceAs (MetricSpace X)

instance : HasRuelleBracket (invDyn X) where
  toFun x y := toInvDyn ⁅ofInvDyn y, ofInvDyn x⁆
  deltaZero := δ₀
  deltaZero_pos := deltaZero_pos
  unifCont := by
    have A : MapsTo (fun (p : X × X) ↦ p.swap)
        {p | dist p.1 p.2 < δ₀} {p | dist p.1 p.2 < δ₀} := by simp [MapsTo, dist_comm]
    have B : UniformContinuousOn (fun (p : X × X) ↦ Prod.swap p) {p | dist p.1 p.2 < δ₀} :=
      UniformContinuous.swap.uniformContinuousOn
    exact (uniformContinuousOn_bracket X).comp B A
  refl o := by simp [toInvDyn, ofInvDyn]
  bracket_left' x y z hxy hyz := by
    apply bracket_right (X := X)
    · rw [dist_comm]
      exact hyz
    · rw [dist_comm]
      exact hxy
  bracket_right' x y z hxy hyz := by
    apply bracket_left (X := X)
    · rw [dist_comm]
      exact hyz
    · rw [dist_comm]
      exact hxy

instance : HasReduceScale (invDyn X) where
  reduceScale := reduceScale X
  reduceScale_pos := reduceScale_pos (X := X)
  reduceScale_le_half_self := reduceScale_le_half_self (X := X)
  reduceScale_le_half_deltaZero := reduceScale_le_half_deltaZero (X := X)
  dist_bracket_lt_of_lt_reduceScale hxy hxz :=
    dist_bracket_lt_of_lt_reduceScale (X := X) hxz hxy

end SmaleSpace
