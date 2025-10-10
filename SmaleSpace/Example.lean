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
 o-------s-- W^-(o)

The stable manifold is those points with `⁅x, o⁆ = x`. The unstable manifold is those points with
`⁅o, y⁆ = y`. The stable manifold is represented horizontally and the unstable manifold vertically,
so that the notation `⁅s, u⁆` for a point parameterized by its stable and unstable components is
analogous to a coordinate notation `(s, u)`.

-/


open scoped Uniformity
open Function Set Filter


namespace SmaleSpace

variable (X : Type*) [UniformSpace X]

structure ruelleBracket where

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
  mainEnt_symm {x y} (h : (x, y) ∈ mainEnt) : (y, x) ∈ mainEnt
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

variable {X}

@[simp] lemma bracket_self (x : X) : ⁅x, x⁆ = x :=
  HasRuelleBracket.refl x

@[simp] lemma prodMk_self_mem_mainEnt (x : X) : (x, x) ∈ mainEnt :=
  mem_uniformity_of_eq mainEnt_mem rfl

lemma bracket_left {x y z : X} (h : (x, y) ∈ mainEnt) (h' : (y, z) ∈ mainEnt) :
    ⁅⁅x, y⁆, z⁆ = ⁅x, z⁆ :=
  HasRuelleBracket.bracket_left' x y z h h'

lemma bracket_right {x y z : X} (h : (x, y) ∈ mainEnt) (h' : (y, z) ∈ mainEnt) :
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
lemma exists_bracket_mem {U : Set (X × X)} (hU : U ∈ 𝓤 X) :
    ∃ V ∈ 𝓤 X, (∀ x y, (x, y) ∈ V → (y, x) ∈ V) ∧
      ∀ x y z, (y, x) ∈ V → (x, z) ∈ V → (x, ⁅y, z⁆) ∈ U := by
  rcases comp_symm_of_uniformity hU with ⟨U', U'_mem, U'_symm, hU'⟩
  rcases comp_symm_of_uniformity (tendsto_bracket_fst U'_mem) with ⟨V, V_mem, V_symm, hV⟩
  refine ⟨U' ∩ V, inter_mem U'_mem V_mem, fun x y hxy ↦ ⟨U'_symm hxy.1, V_symm hxy.2⟩ ,
    fun x y z hxy hxz ↦ ?_⟩
  have : (y, ⁅y, z⁆) ∈ U' := by
    have : (y, z) ∈ V ○ V := prodMk_mem_compRel hxy.2 hxz.2
    exact hV this
  exact hU' (prodMk_mem_compRel (U'_symm hxy.1) this)

/-
open scoped Classical in
/-- Given an entourage `U`, the entourage `myRoot U` is smaller, designed so that the Ruelle
bracket of points inside it remain in `U`. Iterate this construction if you need stability
of longer brackets. -/
def myRoot (U : Set (X × X)) : Set (X × X) :=
  if hU : U ∈ 𝓤 X then
    (comp_symm_of_uniformity
      (inter_mem hU (inter_mem (tendsto_bracket_fst hU) (tendsto_bracket_snd hU)))).choose
  else univ

lemma myRoot_symm {a b : X} {U : Set (X × X)} (h : (a, b) ∈ myRoot U) : (b, a) ∈ myRoot U := by
  by_cases hU : U ∈ 𝓤 X; swap
  · simp [myRoot, hU]
  simp only [myRoot, hU, ↓reduceDIte] at h ⊢
  exact (comp_symm_of_uniformity (inter_mem hU (inter_mem (tendsto_bracket_fst hU)
    (tendsto_bracket_snd hU)))).choose_spec.2.1 h

lemma myRoot_mem {U : Set (X × X)} : myRoot U ∈ 𝓤 X := by
  by_cases hU : U ∈ 𝓤 X; swap
  · simp [myRoot, hU]
  simp only [myRoot, hU, ↓reduceDIte]
  exact (comp_symm_of_uniformity (inter_mem hU (inter_mem (tendsto_bracket_fst hU)
    (tendsto_bracket_snd hU)))).choose_spec.1

lemma myRoot_subset {U : Set (X × X)} (hU : U ∈ 𝓤 X) : myRoot U ⊆ U := by
  simp only [myRoot, hU, ↓reduceDIte]
  have := (comp_symm_of_uniformity (inter_mem hU (inter_mem (tendsto_bracket_fst hU)
    (tendsto_bracket_snd hU)))).choose_spec.2.2
  apply (subset_comp_self_of_mem_uniformity _).trans (by grind)
  exact (comp_symm_of_uniformity (inter_mem hU (inter_mem (tendsto_bracket_fst hU)
    (tendsto_bracket_snd hU)))).choose_spec.1

lemma myRoot_comp {U : Set (X × X)} (hU : U ∈ 𝓤 X) {a b c : X}
    (h : (a, b) ∈ myRoot U) (h' : (b, c) ∈ myRoot U) : (a, c) ∈ U := by
  simp only [myRoot, hU, ↓reduceDIte] at h h'
  have := (comp_symm_of_uniformity (inter_mem hU (inter_mem (tendsto_bracket_fst hU)
    (tendsto_bracket_snd hU)))).choose_spec.2.2
  apply this.trans (by grind)
  exact prodMk_mem_compRel h h'

lemma myRoot_bracket {U : Set (X × X)} (hU : U ∈ 𝓤 X) {a b c : X}
    (h : (a, b) ∈ myRoot U) (h' : (b, c) ∈ myRoot U) : (a, ⁅a, c⁆) ∈ U := by
  sorry
-/


/-- The local stable manifold of `o` inside an entourage `U`, defined as the set of points `s` which
are `U`-close to `o` and satisfy `⁅s, o⁆ = s`. -/
def locStable (U : Set (X × X)) (o : X) : Set X := {s | (s, o) ∈ U ∧ ⁅s, o⁆ = s}

/-- The local unstable manifold of `o` inside an entourage `U`, defined as the set of points `u`
which are `U`-close to `o` and satisfy `⁅o, u⁆ = u`. -/
def locUnstable (U : Set (X × X)) (o : X) : Set X := {u | (o, u) ∈ U ∧ ⁅o, u⁆ = u}

lemma mem_of_mem_locStable {U : Set (X × X)} {o s : X} (hs : s ∈ locStable U o) : (s, o) ∈ U := hs.1

lemma bracket_eq_of_mem_locStable {U : Set (X × X)} {o s : X} (hs : s ∈ locStable U o) :
    ⁅s, o⁆ = s := hs.2

lemma mem_of_mem_locUnstable {U : Set (X × X)} {o u : X} (hu : u ∈ locUnstable U o) : (o, u) ∈ U :=
  hu.1

lemma bracket_eq_of_mem_locUnstable {U : Set (X × X)} {o u : X} (hu : u ∈ locUnstable U o) :
    ⁅o, u⁆ = u := hu.2

structure SmallEnough (U : Set (X × X)) : Prop where
  mem_unif : U ∈ 𝓤 X
  comp_subset_mainEnt : U ○ U ⊆ mainEnt
  bracket_mem {x y z} (h : (y, x) ∈ U) (h' : (x, z) ∈ U) : (x, ⁅y, z⁆) ∈ mainEnt

lemma SmallEnough.subset_mainEnt {U : Set (X × X)} (hU : SmallEnough U) : U ⊆ mainEnt :=
  (subset_comp_self_of_mem_uniformity hU.mem_unif).trans hU.comp_subset_mainEnt

lemma eventually_smallEnough : ∀ᶠ U in (𝓤 X).smallSets, SmallEnough U := by
  rw [eventually_smallSets]


#exit

def SmallEnough.foo {U : Set (X × X)} (hU : SmallEnough U) (o : X) : PartialEquiv (X × X) X where
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
      · exact hU.comp_subset_mainEnt (prodMk_mem_compRel h's h'u)
    · rwa [bracket_left, bracket_eq_of_mem_locStable hs]
      · exact hU.comp_subset_mainEnt (prodMk_mem_compRel h's h'u)
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
      · apply hU.comp_subset_mainEnt (prodMk_mem_compRel h's h'u)
      · apply mainEnt_symm
        apply hU.subset_mainEnt h'u
    · rw [bracket_right]
      · exact bracket_eq_of_mem_locUnstable hu
      · apply mainEnt_symm
        apply hU.subset_mainEnt h's
      · apply hU.comp_subset_mainEnt (prodMk_mem_compRel h's h'u)
  right_inv' := by
    intro x ⟨hx, h'x, h''x⟩
    simp only
    rw [bracket_left, bracket_right, bracket_self]
    · exact mainEnt_symm hx
    · exact hx
    · exact mainEnt_symm hx
    · exact hU.subset_mainEnt h'x
