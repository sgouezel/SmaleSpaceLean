import Mathlib

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
  -- the bracket itself, denoted `⁅x, y⁆` once the theory is set up
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
  b : ruelleBracket X

instance [h : HasRuelleBracket X] : Bracket X X where
  bracket := h.b.toFun

variable [HasRuelleBracket X]

lemma uniformContinuousOn_bracket : ∃ U ∈ 𝓤 X, UniformContinuousOn (fun p ↦ ⁅p.1, p.2⁆) U :=
  HasRuelleBracket.b.unifCont

variable {X} in
@[simp] lemma bracket_self (x : X) : ⁅x, x⁆ = x :=
  HasRuelleBracket.b.refl x

lemma bracket_left' : ∀ᶠ p in (𝓤 X) ×ˢ (𝓤 X), p.1.2 = p.2.1 →
    ⁅⁅p.1.1, p.1.2⁆, p.2.2⁆ = ⁅p.1.1, p.2.2⁆ :=
  HasRuelleBracket.b.comp_left

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
  HasRuelleBracket.b.comp_right

lemma bracket_right :
    ∀ᶠ U in (𝓤 X).smallSets, ∀ x y z, (x, y) ∈ U → (y, z) ∈ U → ⁅x, ⁅y, z⁆⁆ = ⁅x, z⁆ := by
  have W := bracket_right' X
  simp only [Filter.Eventually, Filter.mem_prod_iff] at W
  rcases W with ⟨U₁, h₁, U₂, h₂, hU⟩
  rw [eventually_smallSets]
  refine ⟨U₁ ∩ U₂, Filter.inter_mem h₁ h₂, fun U hU x y z hxy hyz ↦ ?_⟩
  have : ((x, y), (y, z)) ∈ U₁ ×ˢ U₂ := by grind
  grind

lemma exists_local : Tendsto (fun (p : X × X) ↦ (p.1, ⁅p.1, p.2⁆)) (𝓤 X) (𝓤 X) := by
  rcases uniformContinuousOn_bracket X with ⟨U, U_mem, hU⟩
  intro V hV
  have : (U ∩ V) ×ˢ (U ∩ V) ∈ 𝓤 (X × X) ⊓ 𝓟 (U ×ˢ U) := by
    apply Filter.mem_inf_of_inter (s := V ×ˢ V) (t := U ×ˢ U)
    rw [uniformity_prod]
    simp
  simp




#exit

def smallEnoughEnt : Set (X × X) := (bracket_left X).choose ∩ (bracket_right X).choose


variable {X}

/-- The local stable manifold of `x` inside an entourage `U`, defined as the set of points `y` which
are `U`-close to `x` and satisfy `⁅y, x⁆ = y`. -/
def locStable (U : Set (X × X)) (x : X) : Set X := {y | (y, x) ∈ U ∧ ⁅y, x⁆ = y}

/-- The local stable manifold of `x` inside an entourage `U`, defined as the set of points `y` which
are `U`-close to `x` and satisfy `⁅x, y⁆ = y`. -/
def locUnstable (U : Set (X × X)) (x : X) : Set X := {y | (x, y) ∈ U ∧ ⁅x, y⁆ = y}


lemma inj : ∃ U ∈ 𝓤 X, ∀ x, InjOn (fun p ↦ ⁅p.1, p.2⁆) ((locStable U x) ×ˢ (locUnstable U x)) := by




-- ⁅p.1, ⁅p.2, q.2⁆⁆ :=
