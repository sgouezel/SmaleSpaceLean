import Mathlib

/-!
# Ruelle brackets

Convention:

W^-(o)
 |
 s-----⁅s, u⁆
 |       |
 |       |
 |       |
 |       |
 o-------u-- W^+(o)

The stable manifold is those points with `⁅x, o⁆ = x`. The unstable manifold is those points with
`⁅o, y⁆ = y`.

-/


open scoped Uniformity
open Function Set Filter


namespace SmaleSpace

variable (X : Type*) [UniformSpace X]

/-- A Ruelle bracket on a space is a bracket operation `⁅x, y⁆` corresponding to taking the local
intersection of the stable manifold of `x` and the unstable manifold of `y`. It is only defined for
`x` close enough to `y`.

For the formalization, we require the bracket to be defined everywhere although we will only use
it close to the diagonal, to avoid dependent type issues. We record its algebraic properties,
together with uniform continuity. -/
structure ruelleBracket where
  /-- the bracket itself, denoted `⁅x, y⁆` once the theory is set up -/
  toFun : X → X → X
  unifCont : ∃ U ∈ 𝓤 X, UniformContinuousOn (uncurry toFun) U
  refl x : toFun x x = x
  comp_left : ∀ᶠ p in (𝓤 X) ×ˢ (𝓤 X), p.1.2 = p.2.1 →
    toFun (toFun p.1.1 p.1.2) p.2.2 = toFun p.1.1 p.2.2
  comp_right : ∀ᶠ p in (𝓤 X) ×ˢ (𝓤 X), p.1.2 = p.2.1 →
    toFun p.1.1 (toFun p.2.1 p.2.2) = toFun p.1.1 p.2.2

/-- Typeclass recording that a type `X` is endowed with a canonical Ruelle bracket. Useful to make
notation available. -/
class HasRuelleBracket where
  /-- The bracket in a space with a Ruelle bracket. -/
  bracket : ruelleBracket X

instance [h : HasRuelleBracket X] : Bracket X X where
  bracket := h.bracket.toFun

variable [HasRuelleBracket X]

lemma uniformContinuousOn_bracket : ∃ U ∈ 𝓤 X, UniformContinuousOn (fun p ↦ ⁅p.1, p.2⁆) U :=
  HasRuelleBracket.bracket.unifCont

variable {X} in
@[simp] lemma bracket_self (x : X) : ⁅x, x⁆ = x :=
  HasRuelleBracket.bracket.refl x

lemma bracket_left' : ∀ᶠ p in (𝓤 X) ×ˢ (𝓤 X), p.1.2 = p.2.1 →
    ⁅⁅p.1.1, p.1.2⁆, p.2.2⁆ = ⁅p.1.1, p.2.2⁆ :=
  HasRuelleBracket.bracket.comp_left

lemma bracket_left :
    ∀ᶠ U in (𝓤 X).smallSets, ∀ x y z, (x, y) ∈ U → (y, z) ∈ U → ⁅⁅x, y⁆, z⁆ = ⁅x, z⁆ := by
  have W := bracket_left' X
  simp only [Filter.Eventually, Filter.mem_prod_iff] at W
  rcases W with ⟨U₁, h₁, U₂, h₂, hU⟩
  rw [eventually_smallSets]
  refine ⟨U₁ ∩ U₂, Filter.inter_mem h₁ h₂, fun U hU x y z hxy hyz ↦ ?_⟩
  have : ((x, y), (y, z)) ∈ U₁ ×ˢ U₂ := by grind
  grind

lemma bracket_right' : ∀ᶠ p in (𝓤 X) ×ˢ (𝓤 X), p.1.2 = p.2.1 →
    ⁅p.1.1, ⁅p.2.1, p.2.2⁆⁆ = ⁅p.1.1, p.2.2⁆ :=
  HasRuelleBracket.bracket.comp_right

lemma bracket_right :
    ∀ᶠ U in (𝓤 X).smallSets, ∀ x y z, (x, y) ∈ U → (y, z) ∈ U → ⁅x, ⁅y, z⁆⁆ = ⁅x, z⁆ := by
  have W := bracket_right' X
  simp only [Filter.Eventually, Filter.mem_prod_iff] at W
  rcases W with ⟨U₁, h₁, U₂, h₂, hU⟩
  rw [eventually_smallSets]
  refine ⟨U₁ ∩ U₂, Filter.inter_mem h₁ h₂, fun U hU x y z hxy hyz ↦ ?_⟩
  have : ((x, y), (y, z)) ∈ U₁ ×ˢ U₂ := by grind
  grind

/-- If `a` and `b` are close, then `a` and `⁅a, b⁆` are close. -/
lemma tendsto_bracket_fst : Tendsto (fun (p : X × X) ↦ (p.1, ⁅p.1, p.2⁆)) (𝓤 X) (𝓤 X) := by
  rcases uniformContinuousOn_bracket X with ⟨U, U_mem, hU⟩
  intro V hV
  rcases hU hV with ⟨t₁, h₁, t₂, h₂, hV'⟩
  rcases entourageProd_subset h₁ with ⟨u, hu, u', hu', huu'⟩
  have : U ∩ u ∩ u' ∈ 𝓤 X := by grind [Filter.inter_mem]
  apply mem_of_superset this
  rintro ⟨a, b⟩ hab
  have M₁ : ((a, a), (a, b)) ∈ t₁ := huu' (by simp [entourageProd, mem_uniformity_of_eq hu, hab.2])
  have M₂ : ((a, a), (a, b)) ∈ t₂ := by
    simp only [mem_principal] at h₂
    apply h₂
    simp [mem_uniformity_of_eq U_mem, hab.1.1]
  have : ((a, a), (a, b)) ∈ t₁ ∩ t₂ := ⟨M₁, M₂⟩
  simpa [← hV']

/-- If `a` and `b` are close, then `a` and `⁅a, b⁆` are close. -/
lemma tendsto_bracket_snd : Tendsto (fun (p : X × X) ↦ (p.2, ⁅p.1, p.2⁆)) (𝓤 X) (𝓤 X) :=
  tendsto_id.uniformity_symm.uniformity_trans (tendsto_bracket_fst X)

variable {X}

/-- A symmetric entourage of the diagonal on which the Ruelle bracket satisfies the identities
`⁅⁅x, y⁆, z⁆ = ⁅x, z⁆` and `⁅x, ⁅y, z⁆⁆ = ⁅x, z⁆`. -/
def myU : Set (X × X) :=
  symmetrizeRel ((bracket_left X).and (bracket_right X)).exists_mem_of_smallSets.choose

@[simp] lemma myU_mem_uniformity : myU ∈ 𝓤 X := by
  apply symmetrize_mem_uniformity
  exact ((bracket_left X).and (bracket_right X)).exists_mem_of_smallSets.choose_spec.1

lemma myU_symm {a b : X} (h : (a, b) ∈ myU) : (b, a) ∈ myU := by
  rwa [IsSymmetricRel.mk_mem_comm]
  exact symmetric_symmetrizeRel _

lemma myU_prop_left {x y z : X} (h : (x, y) ∈ myU) (h' : (y, z) ∈ myU) : ⁅⁅x, y⁆, z⁆ = ⁅x, z⁆ :=
  ((bracket_left X).and (bracket_right X)).exists_mem_of_smallSets.choose_spec.2.1 _ _ _
    (symmetrizeRel_subset_self _ h) (symmetrizeRel_subset_self _ h')

lemma myU_prop_right {x y z : X} (h : (x, y) ∈ myU) (h' : (y, z) ∈ myU) : ⁅x, ⁅y, z⁆⁆ = ⁅x, z⁆ :=
  ((bracket_left X).and (bracket_right X)).exists_mem_of_smallSets.choose_spec.2.2 _ _ _
    (symmetrizeRel_subset_self _ h) (symmetrizeRel_subset_self _ h')

open scoped Classical in
/-- Given an entourage `U`, the entourage `myRoot U` is smaller, designed so that the Ruelle
bracket of points inside it remain in `U`. Iterate this construction if you need stability
of longer brackets. -/
def myRoot (U : Set (X × X)) : Set (X × X) :=
  if hU : U ∈ 𝓤 X then
    (comp_symm_of_uniformity
      (inter_mem hU (inter_mem (tendsto_bracket_fst X hU) (tendsto_bracket_snd X hU)))).choose
  else univ

lemma myRoot_symm {a b : X} {U : Set (X × X)} (h : (a, b) ∈ myRoot U) : (b, a) ∈ myRoot U := by
  by_cases hU : U ∈ 𝓤 X; swap
  · simp [myRoot, hU]
  simp only [myRoot, hU, ↓reduceDIte] at h ⊢
  exact (comp_symm_of_uniformity (inter_mem hU (inter_mem (tendsto_bracket_fst X hU)
    (tendsto_bracket_snd X hU)))).choose_spec.2.1 h

lemma myRoot_mem {U : Set (X × X)} : myRoot U ∈ 𝓤 X := by
  by_cases hU : U ∈ 𝓤 X; swap
  · simp [myRoot, hU]
  simp only [myRoot, hU, ↓reduceDIte]
  exact (comp_symm_of_uniformity (inter_mem hU (inter_mem (tendsto_bracket_fst X hU)
    (tendsto_bracket_snd X hU)))).choose_spec.1

lemma myRoot_subset {U : Set (X × X)} (hU : U ∈ 𝓤 X) : myRoot U ⊆ U := by
  simp only [myRoot, hU, ↓reduceDIte]
  have := (comp_symm_of_uniformity (inter_mem hU (inter_mem (tendsto_bracket_fst X hU)
    (tendsto_bracket_snd X hU)))).choose_spec.2.2
  apply (subset_comp_self_of_mem_uniformity _).trans (by grind)
  exact (comp_symm_of_uniformity (inter_mem hU (inter_mem (tendsto_bracket_fst X hU)
    (tendsto_bracket_snd X hU)))).choose_spec.1

lemma myRoot_comp {U : Set (X × X)} (hU : U ∈ 𝓤 X) {a b c : X}
    (h : (a, b) ∈ myRoot U) (h' : (b, c) ∈ myRoot U) : (a, c) ∈ U := by
  simp only [myRoot, hU, ↓reduceDIte] at h h'
  have := (comp_symm_of_uniformity (inter_mem hU (inter_mem (tendsto_bracket_fst X hU)
    (tendsto_bracket_snd X hU)))).choose_spec.2.2
  apply this.trans (by grind)
  exact prodMk_mem_compRel h h'

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


def foo (U : Set (X × X)) (o : X) (hU : U ⊆ myRoot myU) : PartialEquiv (X × X) X where
  toFun p := ⁅p.1, p.2⁆
  invFun z := (⁅z, o⁆, ⁅o, z⁆)
  source := (locStable U o) ×ˢ (locUnstable U o)
  target := (fun p ↦ ⁅p.1, p.2⁆) '' ((locStable U o) ×ˢ (locUnstable U o))
  map_source' := sorry
  map_target' := sorry
  left_inv' := by
    rintro ⟨s, u⟩ ⟨hs, hu⟩
    have h's : (s, o) ∈ U := mem_of_mem_locStable hs
    have h'u : (o, u) ∈ U := mem_of_mem_locUnstable hu
    simp only [Prod.mk.injEq]
    constructor
    · rw [myU_prop_left]
      · exact bracket_eq_of_mem_locStable hs
      · apply myRoot_comp myU_mem_uniformity (hU h's) (hU h'u)
      · apply myU_symm
        apply myRoot_subset myU_mem_uniformity (hU h'u)
    · rw [myU_prop_right]
      · exact bracket_eq_of_mem_locUnstable hu
      · apply myU_symm
        apply myRoot_subset myU_mem_uniformity (hU h's)
      · apply myRoot_comp myU_mem_uniformity (hU h's) (hU h'u)
  right_inv' := by
    rintro x ⟨⟨s, u⟩, ⟨hs, hu⟩, rfl⟩
    simp only
    have h's : (s, o) ∈ U := mem_of_mem_locStable hs
    have h'u : (o, u) ∈ U := mem_of_mem_locUnstable hu
    rw [myU_prop_left (z := o), myU_prop_right (x := o), bracket_eq_of_mem_locStable hs,
      bracket_eq_of_mem_locUnstable hu]
    · apply myU_symm
      apply myRoot_subset myU_mem_uniformity (hU h's)
    · apply myRoot_comp myU_mem_uniformity (hU h's) (hU h'u)
    · apply myRoot_comp myU_mem_uniformity (hU h's) (hU h'u)
    · apply myU_symm
      apply myRoot_subset myU_mem_uniformity (hU h'u)










#exit


lemma inj : ∃ U ∈ 𝓤 X, ∀ x, InjOn (fun p ↦ ⁅p.1, p.2⁆) ((locStable U x) ×ˢ (locUnstable U x)) := by




-- ⁅p.1, ⁅p.2, q.2⁆⁆ :=
