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

This file is an experiment to implement Ruelle bracket in terms of uniformities. This works quite
well, but for subsequent results this is not enough (convergence of geometric series is key for
the shadowing lemma, and not really natural to express with uniformities). So we've switched
to a design based on distances, and only keep this file for the record.
-/

open scoped Uniformity Topology
open Function Set Filter SetRel

namespace SmaleSpaceUniformityExperiment

variable (X : Type*) [UniformSpace X] {U V : Set (X × X)} {a b c o s u x y z : X}

/-! ### Spaces with a Ruelle bracket -/

/-- A Ruelle bracket on a space is a bracket operation `⁅x, y⁆` corresponding to taking the local
intersection of the stable manifold of `x` and the unstable manifold of `y`. It is only defined for
`x` close enough to `y`.

For the formalization, we require the bracket to be defined everywhere although we will only use
it close to the diagonal, to avoid dependent type issues. We record its algebraic properties,
together with uniform continuity.

We include in the definition the data of an entourage where the bracket is well-defined. We could
require only its existence, but including it as data makes it possible to be more explicit in
concrete situations. For instance, in subshifts of finite type, we can take for `mainEnt` the
set of pairs of points sharing the same symbol at coordinate `0`.
-/
class HasRuelleBracket where
  /-- the bracket itself, denoted `⁅x, y⁆` once the theory is set up -/
  toFun : X → X → X
  /-- An entourage on which the bracket is uniformly continuous and involutive -/
  mainEnt : Set (X × X)
  mainEnt_mem : mainEnt ∈ 𝓤 X
  mainEnt_symm {x y : X} (h : (x, y) ∈ mainEnt) : (y, x) ∈ mainEnt
  unifCont : UniformContinuousOn (uncurry toFun) mainEnt
  refl x : toFun x x = x
  bracket_left' : ∀ x y z, (x, y) ∈ mainEnt → (y, z) ∈ mainEnt →
    toFun (toFun x y) z = toFun x z
  bracket_right' : ∀ x y z, (x, y) ∈ mainEnt → (y, z) ∈ mainEnt →
    toFun x (toFun y z) = toFun x z

instance [h : HasRuelleBracket X] : Bracket X X where
  bracket := h.toFun

export HasRuelleBracket (mainEnt mainEnt_mem mainEnt_symm)

variable [HasRuelleBracket X]

lemma uniformContinuousOn_bracket : UniformContinuousOn (fun (p : X × X) ↦ ⁅p.1, p.2⁆) mainEnt :=
  HasRuelleBracket.unifCont

lemma continuousOn_bracket : ContinuousOn (fun (p : X × X) ↦ ⁅p.1, p.2⁆) mainEnt :=
  (uniformContinuousOn_bracket X).continuousOn

variable {X}

@[simp] lemma bracket_self (x : X) : ⁅x, x⁆ = x :=
  HasRuelleBracket.refl x

@[simp] lemma prodMk_self_mem_mainEnt (x : X) : (x, x) ∈ mainEnt :=
  mem_uniformity_of_eq mainEnt_mem rfl

lemma bracket_left (h : (x, y) ∈ mainEnt) (h' : (y, z) ∈ mainEnt) :
    ⁅⁅x, y⁆, z⁆ = ⁅x, z⁆ :=
  HasRuelleBracket.bracket_left' x y z h h'

lemma bracket_right (h : (x, y) ∈ mainEnt) (h' : (y, z) ∈ mainEnt) :
    ⁅x, ⁅y, z⁆⁆ = ⁅x, z⁆ :=
  HasRuelleBracket.bracket_right' x y z h h'

/-- If `a` and `b` are close, then `a` and `⁅a, b⁆` are close. -/
lemma tendsto_bracket_fst : Tendsto (fun (p : X × X) ↦ (p.1, ⁅p.1, p.2⁆)) (𝓤 X) (𝓤 X) := by
  intro V hV
  rcases uniformContinuousOn_bracket X hV with ⟨t₁, h₁, t₂, h₂, hV'⟩
  rcases entourageProd_subset h₁ with ⟨u, hu, u', hu', huu'⟩
  have : mainEnt ∩ u ∩ u' ∈ 𝓤 X := by grind [Filter.inter_mem, mainEnt_mem]
  apply mem_of_superset this
  rintro ⟨a, b⟩ hab
  have M₁ : ((a, a), (a, b)) ∈ t₁ := huu' (by simp [entourageProd, mem_uniformity_of_eq hu, hab.2])
  have M₂ : ((a, a), (a, b)) ∈ t₂ := by
    simp only [mem_principal] at h₂
    apply h₂
    simp [mem_uniformity_of_eq mainEnt_mem, hab.1.1]
  have : ((a, a), (a, b)) ∈ t₁ ∩ t₂ := ⟨M₁, M₂⟩
  simpa [← hV']

/-- If `a` and `b` are close, then `a` and `⁅a, b⁆` are close. -/
lemma tendsto_bracket_snd : Tendsto (fun (p : X × X) ↦ (p.2, ⁅p.1, p.2⁆)) (𝓤 X) (𝓤 X) :=
  tendsto_id.uniformity_symm.uniformity_trans tendsto_bracket_fst

/-- If three points are close, then the first one is close to the bracket of the other ones. -/
lemma exists_bracket_mem (hU : U ∈ 𝓤 X) :
    ∃ V ∈ 𝓤 X, (∀ x y, (x, y) ∈ V → (y, x) ∈ V) ∧
      ∀ x y z, (y, x) ∈ V → (x, z) ∈ V → ((x, ⁅y, z⁆) ∈ U ∧ (⁅y, z⁆, x) ∈ U) := by
  rcases comp_symm_of_uniformity hU with ⟨U', U'_mem, U'_symm, hU'⟩
  rcases comp_symm_of_uniformity (tendsto_bracket_fst U'_mem) with ⟨V, V_mem, V_symm, hV⟩
  refine ⟨U' ∩ V, inter_mem U'_mem V_mem, fun x y hxy ↦ ⟨U'_symm hxy.1, V_symm hxy.2⟩ ,
    fun x y z hxy hxz ↦ ?_⟩
  have : (y, ⁅y, z⁆) ∈ U' := by
    have : (y, z) ∈ V ○ V := prodMk_mem_comp hxy.2 hxz.2
    exact hV this
  exact ⟨hU' (prodMk_mem_comp (U'_symm hxy.1) this),
    hU' (prodMk_mem_comp (U'_symm this) hxy.1)⟩

/-!
### Reducing entourages

Given an entourage `U`, we construct a smaller entourage `bracketRoot U` such that composing points
in `bracketRoot U` or taking their brackets, one remains in `U`.
-/

open scoped Classical in
/-- Given an entourage `U`, the entourage `bracketRoot U` is smaller, designed so that the Ruelle
bracket of points inside it remain in `U`. Iterate this construction if you need stability
of longer brackets. -/
def bracketRoot (U : Set (X × X)) : Set (X × X) :=
  if hU : U ∈ 𝓤 X then
    (comp_symm_of_uniformity (exists_bracket_mem hU).choose_spec.1).choose
  else ∅

lemma bracketRoot_symm (h : (a, b) ∈ bracketRoot U) : (b, a) ∈ bracketRoot U := by
  by_cases hU : U ∈ 𝓤 X; swap
  · simp [bracketRoot, hU] at h
  simp only [bracketRoot, hU, ↓reduceDIte] at h ⊢
  exact (comp_symm_of_uniformity (exists_bracket_mem hU).choose_spec.1).choose_spec.2.1 h

lemma bracketRoot_mem_unif (hU : U ∈ 𝓤 X) : bracketRoot U ∈ 𝓤 X := by
  simp only [bracketRoot, hU, ↓reduceDIte]
  exact (comp_symm_of_uniformity (exists_bracket_mem hU).choose_spec.1).choose_spec.1

lemma bracket_right_mem_of_mem_bracketRoot
    (h : (a, b) ∈ bracketRoot U) (h' : (b, c) ∈ bracketRoot U) : (b, ⁅a, c⁆) ∈ U := by
  by_cases hU : U ∈ 𝓤 X; swap
  · simp [bracketRoot, hU] at h
  let U' := (exists_bracket_mem hU).choose
  have I : bracketRoot U ⊆ U' := by
    have : bracketRoot U ○ bracketRoot U ⊆ U' := by
      simp only [bracketRoot, hU, ↓reduceDIte]
      exact (comp_symm_of_uniformity (exists_bracket_mem hU).choose_spec.1).choose_spec.2.2
    exact (subset_comp_self_of_mem_uniformity (bracketRoot_mem_unif hU)).trans this
  exact ((exists_bracket_mem hU).choose_spec.2.2 _ _ _ (I h) (I h')).1

lemma bracket_left_mem_of_mem_bracketRoot
    (h : (a, b) ∈ bracketRoot U) (h' : (b, c) ∈ bracketRoot U) : (⁅a, c⁆, b) ∈ U := by
  by_cases hU : U ∈ 𝓤 X; swap
  · simp [bracketRoot, hU] at h
  let U' := (exists_bracket_mem hU).choose
  have I : bracketRoot U ⊆ U' := by
    have : bracketRoot U ○ bracketRoot U ⊆ U' := by
      simp only [bracketRoot, hU, ↓reduceDIte]
      exact (comp_symm_of_uniformity (exists_bracket_mem hU).choose_spec.1).choose_spec.2.2
    exact (subset_comp_self_of_mem_uniformity (bracketRoot_mem_unif hU)).trans this
  exact ((exists_bracket_mem hU).choose_spec.2.2 _ _ _ (I h) (I h')).2

lemma bracketRoot_subset_self : bracketRoot U ⊆ U := by
  rintro ⟨a, b⟩ hab
  simpa using bracket_right_mem_of_mem_bracketRoot (bracketRoot_symm hab) hab

lemma comp_mem_of_mem_bracketRoot
    (h : (a, b) ∈ bracketRoot U) (h' : (b, c) ∈ bracketRoot U) : (a, c) ∈ U := by
  by_cases hU : U ∈ 𝓤 X; swap
  · simp [bracketRoot, hU] at h
  let U' := (exists_bracket_mem hU).choose
  have hU'U : U' ⊆ U := by
    rintro ⟨x, y⟩ hxy
    have hyx : (y, x) ∈ U' := (exists_bracket_mem hU).choose_spec.2.1 _ _ hxy
    simpa using ((exists_bracket_mem hU).choose_spec.2.2 _ _ _ hyx hxy).1
  simp only [bracketRoot, hU, ↓reduceDIte] at h h'
  have := (comp_symm_of_uniformity (exists_bracket_mem hU).choose_spec.1).choose_spec.2.2
  apply this.trans hU'U (prodMk_mem_comp h h')

/-!
### Small enough entourages

Stable and unstable manifolds are only local objects. We parametrize them using an entourage `U`.
These constructions only work well if `U` is small enough. We record in this section smallness
conditions that are suitable for the task. They are explicit enough that, in the case of subshifts
of finite type, pairs of points with matching zeroth coordinate form a small enough entourage --
which is important since in this specific example we really want to have explicit and rather large
local stable and unstable manifolds.
-/

/-- An entourage is *small enough* it it is contained in the main entourage where the bracket is
well behaved, and the bracket of points also remains in the main entourage. -/
structure SmallEnough (U : Set (X × X)) : Prop where
  subset_mainEnt : U ⊆ mainEnt
  comp_subset_mainEnt : U ○ U ⊆ mainEnt
  bracket_mem {x y z : X} (h : (y, x) ∈ U) (h' : (x, z) ∈ U) : (x, ⁅y, z⁆) ∈ mainEnt

lemma SmallEnough.mono (hU : SmallEnough U) (h : V ⊆ U) : SmallEnough V where
  subset_mainEnt := h.trans hU.subset_mainEnt
  comp_subset_mainEnt := (comp_subset_comp h h).trans hU.comp_subset_mainEnt
  bracket_mem hyx hxz := hU.bracket_mem (h hyx) (h hxz)

/-- Every set contained in a small entourage is small enough. -/
lemma eventually_smallEnough : ∀ᶠ U in (𝓤 X).smallSets, SmallEnough U := by
  rw [eventually_smallSets]
  rcases comp_symm_of_uniformity (mainEnt_mem (X := X)) with ⟨U, U_mem, U_symm, hU⟩
  rcases exists_bracket_mem mainEnt_mem (X := X) with ⟨V, V_mem, V_symm, hV⟩
  refine ⟨U ∩ V, inter_mem U_mem V_mem, fun t ht ↦ ⟨by grind [subset_comp_self_of_mem_uniformity],
    ?_, by grind⟩⟩
  have : t ⊆ U := by grind
  exact (comp_subset_comp this this).trans hU

/-!
### Local stable and unstable manifolds, local parametrization with product coordinates
-/

/-- The local stable manifold of `o` inside an entourage `U`, defined as the set of points `s` which
are `U`-close to `o` and satisfy `⁅s, o⁆ = s`.
Equivalently, these are the points with `⁅o, s⁆ = o`, see `locStable_eq`. -/
def locStable (U : Set (X × X)) (o : X) : Set X := {s | (s, o) ∈ U ∧ ⁅s, o⁆ = s}

/-- The local unstable manifold of `o` inside an entourage `U`, defined as the set of points `u`
which are `U`-close to `o` and satisfy `⁅o, u⁆ = u`.
Equivalently, these are the points with `⁅u, o⁆ = o`, see `locUnstable_eq`. -/
def locUnstable (U : Set (X × X)) (o : X) : Set X := {u | (o, u) ∈ U ∧ ⁅o, u⁆ = u}

lemma mem_of_mem_locStable (hs : s ∈ locStable U o) : (s, o) ∈ U := hs.1

lemma bracket_eq_of_mem_locStable (hs : s ∈ locStable U o) : ⁅s, o⁆ = s := hs.2

lemma locStable_eq (hU : SmallEnough U) : locStable U o = {s | (s, o) ∈ U ∧ ⁅o, s⁆ = o} := by
  ext s
  simp only [locStable, mem_setOf_eq, and_congr_right_iff]
  intro h
  refine ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩
  · rw [← h', bracket_right, bracket_self]
    · exact mainEnt_symm (hU.subset_mainEnt h)
    · exact hU.subset_mainEnt h
  · rw [← h', bracket_right, bracket_self]
    · exact hU.subset_mainEnt h
    · exact mainEnt_symm (hU.subset_mainEnt h)

lemma mem_of_mem_locUnstable (hu : u ∈ locUnstable U o) : (o, u) ∈ U := hu.1

lemma bracket_eq_of_mem_locUnstable (hu : u ∈ locUnstable U o) : ⁅o, u⁆ = u := hu.2

lemma locUnstable_eq (hU : SmallEnough U) : locUnstable U o = {u | (o, u) ∈ U ∧ ⁅u, o⁆ = o} := by
  ext u
  simp only [locUnstable, mem_setOf_eq, and_congr_right_iff]
  intro h
  refine ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩
  · rw [← h', bracket_left, bracket_self]
    · exact hU.subset_mainEnt h
    · exact mainEnt_symm (hU.subset_mainEnt h)
  · rw [← h', bracket_left, bracket_self]
    · exact mainEnt_symm (hU.subset_mainEnt h)
    · exact hU.subset_mainEnt h

/-- If an entourage is small enough, then one can parametrize a neighborhood of any point `o` by
taking the bracket of points on its stable and unstable manifolds.

The fact that the target of this parametrization is indeed a neighborhood of `o` (of fixed size)
is given in `SmallEnough.bracketRoot_subset_target_localProduct`.
-/
@[simps!]
def SmallEnough.localProductEquiv (hU : SmallEnough U) (o : X) : PartialEquiv (X × X) X where
  toFun p := ⁅p.1, p.2⁆
  invFun z := (⁅z, o⁆, ⁅o, z⁆)
  source := (locStable U o) ×ˢ (locUnstable U o)
  target := {y | (o, y) ∈ mainEnt ∧ (o, ⁅o, y⁆) ∈ U ∧ (⁅y, o⁆, o) ∈ U}
  map_source' := by
    rintro ⟨s, u⟩ ⟨hs, hu⟩
    have h's : (s, o) ∈ U := mem_of_mem_locStable hs
    have h'u : (o, u) ∈ U := mem_of_mem_locUnstable hu
    simp only [mem_setOf_eq]
    refine ⟨?_, ?_, ?_⟩
    · apply hU.bracket_mem h's h'u
    · rwa [bracket_right, bracket_eq_of_mem_locUnstable hu]
      · apply mainEnt_symm
        exact hU.subset_mainEnt h's
      · exact hU.comp_subset_mainEnt (prodMk_mem_comp h's h'u)
    · rwa [bracket_left, bracket_eq_of_mem_locStable hs]
      · exact hU.comp_subset_mainEnt (prodMk_mem_comp h's h'u)
      · apply mainEnt_symm
        exact hU.subset_mainEnt h'u
  map_target' := by
    rintro x ⟨hx_main, hx, h'x⟩
    simp [locStable, locUnstable, bracket_left, bracket_right, hx_main, mainEnt_symm hx_main,
      hx, h'x]
  left_inv' := by
    rintro ⟨s, u⟩ ⟨hs, hu⟩
    have h's : (s, o) ∈ U := mem_of_mem_locStable hs
    have h'u : (o, u) ∈ U := mem_of_mem_locUnstable hu
    simp only [Prod.mk.injEq]
    constructor
    · rw [bracket_left]
      · exact bracket_eq_of_mem_locStable hs
      · apply hU.comp_subset_mainEnt (prodMk_mem_comp h's h'u)
      · apply mainEnt_symm
        apply hU.subset_mainEnt h'u
    · rw [bracket_right]
      · exact bracket_eq_of_mem_locUnstable hu
      · apply mainEnt_symm
        apply hU.subset_mainEnt h's
      · apply hU.comp_subset_mainEnt (prodMk_mem_comp h's h'u)
  right_inv' := by
    intro x ⟨hx, h'x, h''x⟩
    simp only
    rw [bracket_left, bracket_right, bracket_self]
    · exact mainEnt_symm hx
    · exact hx
    · exact mainEnt_symm hx
    · exact hU.subset_mainEnt h'x

lemma SmallEnough.continuousOn_localProductEquiv (hU : SmallEnough U) :
    ContinuousOn (hU.localProductEquiv o) (hU.localProductEquiv o).source := by
  apply (continuousOn_bracket X).mono
  rintro ⟨s, u⟩ ⟨⟨hs, h's⟩, ⟨hu, h'u⟩⟩
  exact hU.comp_subset_mainEnt (prodMk_mem_comp hs hu)

lemma SmallEnough.continuousOn_symm_localProductEquiv (hU : SmallEnough U) :
    ContinuousOn (hU.localProductEquiv o).symm (hU.localProductEquiv o).target := by
  change ContinuousOn (fun z ↦ (⁅z, o⁆, ⁅o, z⁆))
    {y | (o, y) ∈ mainEnt ∧ (o, ⁅o, y⁆) ∈ U ∧ (⁅y, o⁆, o) ∈ U}
  apply ContinuousOn.prodMk
  · apply (continuousOn_bracket X).comp (Continuous.prodMk_left o).continuousOn
    intro x ⟨hxo, hx, h'x⟩
    exact mainEnt_symm hxo
  · apply (continuousOn_bracket X).comp (Continuous.prodMk_right o).continuousOn
    intro x ⟨hxo, hx, h'x⟩
    exact hxo

/-- Given a small enough entourage `U`, the ball around `o` for the smaller
entourage `bracketRoot U` is covered by the local product parametrization coming from `U`. -/
lemma SmallEnough.bracketRoot_subset_target_localProductEquiv (hU : SmallEnough U) :
    UniformSpace.ball o (bracketRoot U) ⊆ (hU.localProductEquiv o).target := by
  by_cases h'U : U ∈ 𝓤 X; swap
  · simp [bracketRoot, h'U, UniformSpace.ball]
  intro y (hy : (o, y) ∈ bracketRoot U)
  simp only [localProductEquiv_target, mem_setOf_eq]
  have hoo : (o, o) ∈ bracketRoot U := mem_uniformity_of_eq (bracketRoot_mem_unif h'U) rfl
  refine ⟨?_, ?_, ?_⟩
  · apply hU.subset_mainEnt
    exact bracketRoot_subset_self hy
  · exact bracket_right_mem_of_mem_bracketRoot hoo hy
  · exact bracket_left_mem_of_mem_bracketRoot (bracketRoot_symm hy) hoo

lemma SmallEnough.target_localProductEquiv_mem_nhds (hU : SmallEnough U) (h : U ∈ 𝓤 X) :
    (hU.localProductEquiv o).target ∈ 𝓝 o := by
  apply Filter.mem_of_superset _ hU.bracketRoot_subset_target_localProductEquiv
  exact UniformSpace.ball_mem_nhds o (bracketRoot_mem_unif h)

end SmaleSpaceUniformityExperiment
