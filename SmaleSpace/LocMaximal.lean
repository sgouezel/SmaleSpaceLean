import Mathlib

open scoped Uniformity Topology
open Function Set Filter Metric

variable {X : Type*} [MetricSpace X] {T' : X → X} {T : X ≃ X}
  {U V : Set (X × X)} {a b c o s u x y z : X} {ε ε' δ : ℝ} {n : ℕ}

def locStable (T : X → X) (ε : ℝ) (o : X) : Set X :=
  {y | (∀ n, dist (T^[n] o) (T^[n] y) ≤ ε) ∧
    Tendsto (fun n ↦ dist (T^[n] o) (T^[n] y)) atTop (𝓝 0)}

def locUnstable (T : X ≃ X) (ε : ℝ) (o : X) : Set X :=
  locStable T.symm ε o

lemma dist_le_of_mem_locStable (hs : s ∈ locStable T' ε o) : dist o s ≤ ε := by
  simpa using hs.1 0

lemma dist_le_of_mem_locUnstable (hu : u ∈ locUnstable T ε o) : dist o u ≤ ε :=
  dist_le_of_mem_locStable hu

lemma mem_locStable_symm (hx : x ∈ locStable T' ε o) : o ∈ locStable T' ε x := by
  simpa [locStable, dist_comm] using hx

lemma mem_locUnstable_symm (hx : x ∈ locUnstable T ε o) : o ∈ locUnstable T ε x :=
  mem_locStable_symm hx

lemma mem_locStable_iff_symm : x ∈ locStable T' ε o ↔ o ∈ locStable T' ε x :=
  ⟨fun h ↦ mem_locStable_symm h, fun h ↦ mem_locStable_symm h⟩

lemma mem_locUnstable_iff_symm : x ∈ locUnstable T ε o ↔ o ∈ locUnstable T ε x :=
  mem_locStable_iff_symm

lemma locStable_mono (h : ε ≤ ε') : locStable T' ε o ⊆ locStable T' ε' o := by
  simp only [locStable, setOf_subset_setOf, and_imp]
  grind

lemma locUnstable_mono (h : ε ≤ ε') : locUnstable T ε o ⊆ locUnstable T ε' o :=
  locStable_mono h

@[simp] lemma locStable_zero : locStable T' 0 o = {o} := by
  apply Subset.antisymm (fun y hy ↦ ?_) (fun y hy ↦ ?_)
  · simp [locStable, dist_le_zero, mem_setOf_eq] at hy
    simpa using (hy.1 0).symm
  · simp only [mem_singleton_iff] at hy
    simp [locStable, hy]

@[simp] lemma locUnstable_zero : locUnstable T 0 o = {o} :=
  locStable_zero

lemma self_mem_locStable (hε : 0 ≤ ε) : o ∈ locStable T' ε o := by
  simp [locStable, hε]

lemma self_mem_locUnstable (hε : 0 ≤ ε) : o ∈ locUnstable T ε o :=
  self_mem_locStable hε

lemma locStable_eq_empty_of_neg (hε : ε < 0) : locStable T' ε o = ∅ := by
  ext x
  simp only [locStable, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
  intro h
  linarith [h 0, dist_nonneg (x := T'^[0] o) (y := T'^[0] x)]

lemma locUnstable_eq_empty_of_neg (hε : ε < 0) : locUnstable T ε o = ∅ :=
  locStable_eq_empty_of_neg hε

lemma nonempty_locStable_iff : (locStable T' ε o).Nonempty ↔ 0 ≤ ε := by
  rcases lt_or_ge ε 0 with hε | hε
  · simp [locStable_eq_empty_of_neg, hε]
  · simp only [hε, iff_true]
    exact ⟨o, self_mem_locStable hε⟩

lemma nonempty_locUnstable_iff : (locUnstable T ε o).Nonempty ↔ 0 ≤ ε :=
  nonempty_locStable_iff

lemma mem_locStable_trans (hx : x ∈ locStable T' ε o) (hy : y ∈ locStable T' ε' x) :
    y ∈ locStable T' (ε + ε') o := by
  refine ⟨fun n ↦ ?_, ?_⟩
  · linarith [dist_triangle (T'^[n] o) (T'^[n] x) (T'^[n] y), hx.1 n, hy.1 n]
  · exact squeeze_zero (fun n ↦ dist_nonneg) (fun n ↦ dist_triangle _ _ _)
      (by simpa using hx.2.add hy.2)

lemma mem_locUnstable_trans (hx : x ∈ locUnstable T ε o) (hy : y ∈ locUnstable T ε' x) :
    y ∈ locUnstable T (ε + ε') o :=
  mem_locStable_trans hx hy

lemma image_mem_locStable (hx : x ∈ locStable T' ε o) : T' x ∈ locStable T' ε (T' o) := by
  refine ⟨fun n ↦ ?_, ?_⟩
  · simp_rw [← iterate_succ_apply]
    apply hx.1
  · simp_rw [← iterate_succ_apply]
    exact hx.2.comp (tendsto_add_atTop_nat 1)

lemma image_mem_locUntable (hx : x ∈ locUnstable T ε o) : T.symm x ∈ locUnstable T ε (T.symm o) :=
  image_mem_locStable hx

lemma iterate_mem_locStable (hx : x ∈ locStable T' ε o) : T'^[n] x ∈ locStable T' ε (T'^[n] o) := by
  induction n with
  | zero => simpa using hx
  | succ n ih => simpa [iterate_succ_apply'] using image_mem_locStable ih

lemma iterate_mem_locUnstable (hx : x ∈ locUnstable T ε o) :
    T.symm^[n] x ∈ locUnstable T ε (T.symm^[n] o) :=
  iterate_mem_locStable hx

/-- Structure registering that a set `A` is hyperbolic locally maximal for an invertible map `T`.
We have two parameters `δ₀` and `δ₁` in the definition. The first one is such that the map
is uniformly contracting by `ρ` on stable manifolds of size `δ₀`, and similarly for unstable
manifolds. The second one is such that, if two points of `A` are within distance `δ₁`, then their
stable and unstable manifolds of size `δ₀` intersect at exactly one point. As this intersection
plays a prominent role in the theory, we include it as data in the definition, the
function `bracket` (sometimes called the Ruelle bracket).
-/
structure IsLocallyMaxHyperbolicSet (T : X ≃ X) (A : Set X) (δ₀ δ₁ : ℝ) (ρ : ℝ) where
  isClosed_A : IsClosed A
  uniformContinuous_T : UniformContinuous T
  uniformContinuous_Tsymm : UniformContinuous T.symm
  rho_pos : 0 < ρ
  rho_lt_one : ρ < 1
  deltaOne_pos : 0 < δ₁
  deltaOne_le_half_deltaZero : δ₁ ≤ δ₀ / 2
  contraction {a x y : X} (ha : a ∈ A) (hx : x ∈ locStable T δ₀ a) (hy : y ∈ locStable T δ₀ a) :
    dist (T x) (T y) ≤ ρ * dist x y
  expansion {a x y : X} (ha : a ∈ A) (hx : x ∈ locUnstable T δ₀ a) (hy : y ∈ locUnstable T δ₀ a) :
    dist (T.symm x) (T.symm y) ≤ ρ * dist x y
  bracket : X → X → X
  bracket_eq_inter {x y : X} (hx : x ∈ A) (hy : y ∈ A) (h : dist x y ≤ δ₁) :
    locStable T δ₀ x ∩ locUnstable T δ₀ y = {bracket x y}
  uniformContinuousOn_bracket :
    UniformContinuousOn (uncurry bracket) {p : X × X | dist p.1 p.2 ≤ δ₀}
  bracket_mem {x y : X} (hx : x ∈ A) (hy : y ∈ A) : bracket x y ∈ A
  bracket_self {x : X} : bracket x x = x
  mapsTo_T : MapsTo T A A
  mapsTo_Tsymm : MapsTo T.symm A A

namespace IsLocallyMaxHyperbolicSet

/- The standing assumption in this section is that `A` is a locally maximal hyperbolic set for `T`.
This assumption, called `hT`, will be used in all theorems. To apply such a theorem `foo`, we will
call it using dot notation as `hT.foo`. In this way, we never have to write the longish
`IsLocallyMaxHyperbolicSet` with all its parameters.
-/

variable {A : Set X} {δ₀ δ₁ ρ : ℝ} (hT : IsLocallyMaxHyperbolicSet T A δ₀ δ₁ ρ)
include hT

protected def symm : IsLocallyMaxHyperbolicSet T.symm A δ₀ δ₁ ρ where
  isClosed_A := hT.isClosed_A
  uniformContinuous_T := hT.uniformContinuous_Tsymm
  uniformContinuous_Tsymm := hT.uniformContinuous_T
  rho_pos := hT.rho_pos
  rho_lt_one := hT.rho_lt_one
  deltaOne_pos := hT.deltaOne_pos
  deltaOne_le_half_deltaZero := hT.deltaOne_le_half_deltaZero
  contraction := hT.expansion
  expansion := hT.contraction
  bracket x y := hT.bracket y x
  bracket_eq_inter hx hy h := by
    rw [inter_comm]
    rw [dist_comm] at h
    exact hT.bracket_eq_inter hy hx h
  bracket_mem hx hy := hT.bracket_mem hy hx
  bracket_self := hT.bracket_self
  uniformContinuousOn_bracket := by
    have A : UniformContinuousOn (fun (p : X × X) ↦ Prod.swap p) {p | dist p.1 p.2 ≤ δ₀} :=
      uniformContinuous_swap.uniformContinuousOn
    have B : MapsTo (fun (p : X × X) ↦ p.swap)
      {p | dist p.1 p.2 ≤ δ₀} {p | dist p.1 p.2 ≤ δ₀} := by simp [MapsTo, dist_comm]
    exact hT.uniformContinuousOn_bracket.comp A B
  mapsTo_T := hT.mapsTo_Tsymm
  mapsTo_Tsymm := hT.mapsTo_T

lemma deltaZero_pos : 0 < δ₀ := by linarith [hT.deltaOne_pos, hT.deltaOne_le_half_deltaZero]

lemma deltaOne_le_deltaZero : δ₁ ≤ δ₀ := by
  linarith [hT.deltaOne_pos, hT.deltaOne_le_half_deltaZero]

lemma continuous_T : Continuous T := hT.uniformContinuous_T.continuous

lemma continuous_Tsymm : Continuous T.symm := hT.uniformContinuous_Tsymm.continuous

lemma dist_iterate_le (hx : x ∈ locStable T δ₀ o) (hy : y ∈ locStable T δ₀ o) :
    dist (T^[n] x) (T^[n] y) ≤ ρ ^ n * dist x y := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [iterate_succ_apply']



#exit

lemma image_mem_locStable_mul (hε : ε ≤ δ₀) (hx : x ∈ locStable T ε o) :
    T x ∈ locStable T (ρ * ε) (T o) := by
  refine ⟨fun n ↦ ?_, ?_⟩
  · have := image_mem_locStable hx
    simp_rw [← iterate_succ_apply]
    apply hx.1
  · simp_rw [← iterate_succ_apply]
    exact hx.2.comp (tendsto_add_atTop_nat 1)




#exit

lemma isClosed_locStable (hε : ε ≤ δ₁) (ho : o ∈ A) :
    IsClosed (locStable T ε o) := by
  /- the condition that `dist (T^n x) (T^n o) ≤ ε` is clearly closed
  To show that `dist (T^n x) (T^n o)` tends to zero when `x` belongs to the closure, it suffices
  to prove that `dist (T^n x) (T^n o) ≤ ρ^n dist x y` as the latter tends to zero. For this,
  notice that this condition is closed, and holds on `locStable T ε o` by `hT.contraction`. -/
  refine isClosed_of_closure_subset (fun x hx ↦ ?_)
  have A n : dist (T^[n] o) (T^[n] x) ≤ ρ ^ n * ε := by
    have := mem_closure_iff_clusterPt.1 hx
    simp only [ClusterPt] at this
    have : Tendsto (fun y ↦ dist (T^[n] o) (T^[n] y)) (𝓝 x ⊓ 𝓟 (locStable (⇑T) ε o))
        (𝓝 (dist (T^[n] o) (T^[n] x))) := by
      apply Tendsto.dist tendsto_const_nhds
      apply Tendsto.mono_left (x := 𝓝 x) ?_ (by simp)
      exact (hT.continuous_T.iterate n).tendsto x
    apply le_of_tendsto this
    rw [eventually_inf_principal]
    filter_upwards [] with y hy

end IsLocallyMaxHyperbolicSet
