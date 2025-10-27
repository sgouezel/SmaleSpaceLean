import Mathlib

open scoped Uniformity Topology
open Function Set Filter Metric

/- TODO: PR to Topology.MetricSpace.Pseudo.Defs next to uniformContinuous_iff -/
theorem Metric.uniformContinuous_iff_le
    {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β] {f : α → β} :
    UniformContinuous f ↔ ∀ ε > 0, ∃ δ > 0, ∀ ⦃a b : α⦄, dist a b ≤ δ → dist (f a) (f b) ≤ ε :=
  uniformity_basis_dist_le.uniformContinuous_iff uniformity_basis_dist_le

/- TODO: PR to Topology.UniformSpace.Basic -/
theorem UniformContinuousOn.congr
    {α β : Type*} [UniformSpace α] [UniformSpace β] {f g : α → β} {s : Set α}
    (hf : UniformContinuousOn f s) (h : EqOn f g s) :
    UniformContinuousOn g s := by
  apply hf.congr'
  apply EventuallyEq.filter_mono _ inf_le_right
  filter_upwards [mem_principal_self _] with ⟨a, b⟩ ⟨ha, hb⟩ using by simp [h ha, h hb]

variable {X : Type*} [MetricSpace X] {T' : X → X} {T : X ≃ X} {A B : Set X}
  {U V : Set (X × X)} {a b c o s u x y z : X} {ε ε' δ : ℝ} {n : ℕ}

/-- The local stable manifold of a map `T`, of size `ε`, around a point `o`. This is the set of
points `y` whose orbit remains within `ε` of the orbit of `o`, and the two orbits tend to each
other asymptotically. -/
def locStable (T : X → X) (ε : ℝ) (o : X) : Set X :=
  {y | (∀ n, dist (T^[n] o) (T^[n] y) ≤ ε) ∧
    Tendsto (fun n ↦ dist (T^[n] o) (T^[n] y)) atTop (𝓝 0)}

/-- The local stable manifold of a map `T`, of size `ε`, around a point `o`. This is the set of
points `y` whose orbit in the past remains within `ε` of the orbit of `o`, and the two orbits tend
to each other asymptotically. Defined only when `T` is invertible. -/
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

lemma image_mem_locUnstable (hx : x ∈ locUnstable T ε o) : T.symm x ∈ locUnstable T ε (T.symm o) :=
  image_mem_locStable hx

lemma iterate_mem_locStable (hx : x ∈ locStable T' ε o) (n : ℕ) :
    T'^[n] x ∈ locStable T' ε (T'^[n] o) := by
  induction n with
  | zero => simpa using hx
  | succ n ih => simpa [iterate_succ_apply'] using image_mem_locStable ih

lemma iterate_symm_mem_locUnstable (hx : x ∈ locUnstable T ε o) (n : ℕ) :
    T.symm^[n] x ∈ locUnstable T ε (T.symm^[n] o) :=
  iterate_mem_locStable hx n

/-- Structure registering that a set `A` is hyperbolic locally maximal for an invertible map `T`.
The definition features two numbers `δ₀`and `ρ`. The first one is such that the map
is uniformly contracting by `ρ` on stable manifolds of size `δ₀`, and similarly for unstable
manifolds. Moreover, if two points of `A` are close enough, then their
stable and unstable manifolds of size `δ₀` intersect at exactly one point. As this intersection
plays a prominent role in the theory, we include it as data in the definition, the
function `bracket` (sometimes called the Ruelle bracket).
-/
structure IsLocallyMaxHyperbolicSet (T : X ≃ X) (A : Set X) where
  isClosed : IsClosed A
  uniformContinuous : UniformContinuous T
  uniformContinuous_symm : UniformContinuous T.symm
  /-- The contraction parameter along stable and unstable manifolds -/
  rho : ℝ
  rho_pos : 0 < rho
  rho_lt_one : rho < 1
  /-- The size below which the dynamics is well behaved -/
  deltaZero : ℝ
  deltaZero_pos : 0 < deltaZero
  contraction {o x y : X} (ho : o ∈ A)
    (hx : x ∈ locStable T deltaZero o) (hy : y ∈ locStable T deltaZero o) :
    dist (T x) (T y) ≤ rho * dist x y
  expansion {o x y : X} (ho : o ∈ A)
    (hx : x ∈ locUnstable T deltaZero o) (hy : y ∈ locUnstable T deltaZero o) :
    dist (T.symm x) (T.symm y) ≤ rho * dist x y
  /-- The Ruelle bracket of the hyperbolic map. Denoted as `⁅x, y⁆`. This is the intersection of the
  local unstable manifold of `x` and the local stable manifold of `y`. -/
  bracket : X → X → X
  uniformContinuousOn_bracket :
    UniformContinuousOn (uncurry bracket) {p : X × X | dist p.1 p.2 ≤ deltaZero ∧ p ∈ A ×ˢ A}
  bracket_mem {x y : X} (hx : x ∈ A) (hy : y ∈ A) : bracket x y ∈ A
  bracket_self {x : X} : bracket x x = x
  exists_bracket_eq_inter : ∃ δ > 0, ∀ {x y : X} (_hx : x ∈ A) (_hy : y ∈ A) (_h : dist x y ≤ δ),
    {bracket x y} = locUnstable T deltaZero x ∩ locStable T deltaZero y
  mapsTo : MapsTo T A A
  mapsTo_symm : MapsTo T.symm A A

attribute [simp] IsLocallyMaxHyperbolicSet.bracket_self

namespace IsLocallyMaxHyperbolicSet

/- The standing assumption in this section is that `A` is a locally maximal hyperbolic set for `T`.
This assumption, called `hT`, will be used in all theorems. To apply such a theorem `foo`, we will
call it using dot notation as `hT.foo`. In this way, we never have to write the longish
`IsLocallyMaxHyperbolicSet` with all its parameters.
-/

variable (hT : IsLocallyMaxHyperbolicSet T A)
include hT

local notation3 "δ₀" => hT.deltaZero
local notation3 "ρ" => hT.rho
local notation3 "⁅" x ", " y "⁆" => hT.bracket x y

/-- A locally maximal hyperbolic set for `T` is also locally maximal hyperbolic for `T⁻¹`. -/
protected def symm : IsLocallyMaxHyperbolicSet T.symm A where
  isClosed := hT.isClosed
  uniformContinuous := hT.uniformContinuous_symm
  uniformContinuous_symm := hT.uniformContinuous
  rho := hT.rho
  rho_pos := hT.rho_pos
  rho_lt_one := hT.rho_lt_one
  deltaZero := hT.deltaZero
  deltaZero_pos := hT.deltaZero_pos
  contraction := hT.expansion
  expansion := hT.contraction
  bracket x y := hT.bracket y x
  bracket_mem hx hy := hT.bracket_mem hy hx
  bracket_self := hT.bracket_self
  uniformContinuousOn_bracket := by
    have I : UniformContinuousOn (fun (p : X × X) ↦ Prod.swap p)
      {p | dist p.1 p.2 ≤ δ₀ ∧ p ∈ A ×ˢ A} := uniformContinuous_swap.uniformContinuousOn
    have J : MapsTo (fun (p : X × X) ↦ p.swap)
        {p | dist p.1 p.2 ≤ δ₀ ∧ p ∈ A ×ˢ A} {p | dist p.1 p.2 ≤ δ₀ ∧ p ∈ A ×ˢ A} := by
      simp +contextual [MapsTo, dist_comm]
    exact hT.uniformContinuousOn_bracket.comp I J
  mapsTo := hT.mapsTo_symm
  mapsTo_symm := hT.mapsTo
  exists_bracket_eq_inter := by
    rcases hT.exists_bracket_eq_inter with ⟨δ, δpos, hδ⟩
    refine ⟨δ, δpos, fun {x y} hx hy h ↦ ?_⟩
    rw [inter_comm]
    rw [dist_comm] at h
    exact hδ hy hx h

lemma continuous : Continuous T := hT.uniformContinuous.continuous

lemma continuous_symm : Continuous T.symm := hT.uniformContinuous_symm.continuous

lemma dist_iterate_le (ho : o ∈ A)
    (hx : x ∈ locStable T δ₀ o) (hy : y ∈ locStable T δ₀ o) (n : ℕ) :
    dist (T^[n] x) (T^[n] y) ≤ ρ ^ n * dist x y := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [iterate_succ_apply', pow_succ', mul_assoc]
    apply (hT.contraction (hT.mapsTo.iterate _ ho) (iterate_mem_locStable hx _)
      (iterate_mem_locStable hy _)).trans
    gcongr
    exact hT.rho_pos.le

lemma dist_iterate_symm_le (ho : o ∈ A)
    (hx : x ∈ locUnstable T δ₀ o) (hy : y ∈ locUnstable T δ₀ o) (n : ℕ) :
    dist (T.symm^[n] x) (T.symm^[n] y) ≤ ρ ^ n * dist x y :=
  hT.symm.dist_iterate_le ho hx hy n

lemma image_mem_locStable_mul (ho : o ∈ A) (hε : ε ≤ δ₀) (hx : x ∈ locStable T ε o) :
    T x ∈ locStable T (ρ * ε) (T o) := by
  refine ⟨fun n ↦ ?_, ?_⟩
  · have := image_mem_locStable hx
    simp_rw [← iterate_succ_apply]
    apply (hT.dist_iterate_le ho _ _ _).trans
    · gcongr
      · exact hT.rho_pos.le
      · exact pow_le_of_le_one hT.rho_pos.le hT.rho_lt_one.le (by omega)
      · exact hx.1 0
    · exact self_mem_locStable hT.deltaZero_pos.le
    · exact locStable_mono hε hx
  · simp_rw [← iterate_succ_apply]
    exact hx.2.comp (tendsto_add_atTop_nat 1)

lemma image_symm_mem_locUnstable_mul (ho : o ∈ A) (hε : ε ≤ δ₀) (hx : x ∈ locUnstable T ε o) :
    T.symm x ∈ locUnstable T (ρ * ε) (T.symm o) :=
  hT.symm.image_mem_locStable_mul ho hε hx

lemma iterate_mem_locStable_mul (ho : o ∈ A) (hε : ε ≤ δ₀) (hx : x ∈ locStable T ε o) (n : ℕ) :
    T^[n] x ∈ locStable T (ρ ^ n * ε) (T^[n] o) := by
  induction n with
  | zero => simp [hx]
  | succ n ih =>
    simp_rw [iterate_succ_apply', pow_succ', mul_assoc]
    apply hT.image_mem_locStable_mul (hT.mapsTo.iterate _ ho) _ ih
    apply le_trans _ hε
    apply mul_le_of_le_one_left (nonempty_locStable_iff.1 ⟨x, hx⟩)
    exact pow_le_one₀ hT.rho_pos.le hT.rho_lt_one.le

lemma iterate_symm_mem_locUnstable_mul
    (ho : o ∈ A) (hε : ε ≤ δ₀) (hx : x ∈ locUnstable T ε o) (n : ℕ) :
    T.symm^[n] x ∈ locUnstable T (ρ ^ n * ε) (T.symm^[n] o) :=
  hT.symm.iterate_mem_locStable_mul ho hε hx n

lemma dist_iterate_le_mul_of_mem_locStable
    (ho : o ∈ A) (hε : ε ≤ δ₀) (hx : x ∈ locStable T ε o) (n : ℕ) :
    dist (T^[n] o) (T^[n] x) ≤ ρ ^ n * ε :=
  (hT.iterate_mem_locStable_mul ho hε hx (n := n)).1 0

lemma dist_iterate_symm_le_mul_of_mem_locUnstable
    (ho : o ∈ A) (hε : ε ≤ δ₀) (hx : x ∈ locUnstable T ε o) (n : ℕ) :
    dist (T.symm^[n] o) (T.symm^[n] x) ≤ ρ ^ n * ε :=
  hT.symm.dist_iterate_le_mul_of_mem_locStable ho hε hx n

lemma mem_locStable_iff_dist_iterate_le_mul (ho : o ∈ A) (hε : ε ≤ δ₀) :
    x ∈ locStable T ε o ↔ (∀ n, dist (T^[n] o) (T^[n] x) ≤ ρ ^ n * ε) := by
  refine ⟨fun hx n ↦ hT.dist_iterate_le_mul_of_mem_locStable ho hε hx n, fun hx ↦ ⟨fun n ↦ ?_, ?_⟩⟩
  · apply (hx n).trans
    have E : 0 ≤ ε := le_trans dist_nonneg (by simpa using (hx 0))
    apply mul_le_of_le_one_left E
    exact pow_le_one₀ hT.rho_pos.le hT.rho_lt_one.le
  · have : Tendsto (fun n ↦ ρ ^ n * ε) atTop (𝓝 (0 * ε)) := by
      apply Tendsto.mul_const
      exact tendsto_pow_atTop_nhds_zero_of_lt_one hT.rho_pos.le hT.rho_lt_one
    rw [zero_mul] at this
    exact squeeze_zero (fun n ↦ dist_nonneg) hx this

lemma mem_locUnstable_iff_dist_symm_iterate_le_mul (ho : o ∈ A) (hε : ε ≤ δ₀) :
    x ∈ locUnstable T ε o ↔ (∀ n, dist (T.symm^[n] o) (T.symm^[n] x) ≤ ρ ^ n * ε) :=
  hT.symm.mem_locStable_iff_dist_iterate_le_mul ho hε

lemma mem_locStable_of_mem_locStable_of_dist_le (ho : o ∈ A) (hε : ε ≤ δ₀)
    (hx : x ∈ locStable T ε o) (h'x : dist o x ≤ ε') : x ∈ locStable T ε' o := by
  rcases le_total ε ε' with h | h
  · exact locStable_mono h hx
  apply (hT.mem_locStable_iff_dist_iterate_le_mul ho (h.trans hε)).2 (fun n ↦ ?_)
  apply (hT.dist_iterate_le ho (x := o) (self_mem_locStable hT.deltaZero_pos.le)
    (locStable_mono hε hx) n).trans
  gcongr
  apply pow_nonneg hT.rho_pos.le

lemma mem_locUnstable_of_mem_locUnstable_of_dist_le (ho : o ∈ A) (hε : ε ≤ δ₀)
    (hx : x ∈ locUnstable T ε o) (h'x : dist o x ≤ ε') : x ∈ locUnstable T ε' o :=
  hT.symm.mem_locStable_of_mem_locStable_of_dist_le ho hε hx h'x

lemma isClosed_locStable (ho : o ∈ A) (hε : ε ≤ δ₀) : IsClosed (locStable T ε o) := by
  have : locStable T ε o = ⋂ n, {x | dist (T^[n] o) (T^[n] x) ≤ ρ ^ n * ε} := by
    ext; simp [hT.mem_locStable_iff_dist_iterate_le_mul ho hε ]
  rw [this]
  have : Continuous T := hT.continuous
  exact isClosed_iInter (fun n ↦ isClosed_le (by fun_prop) continuous_const)

lemma isClosed_locUnstable (ho : o ∈ A) (hε : ε ≤ δ₀) : IsClosed (locUnstable T ε o) :=
  hT.symm.isClosed_locStable ho hε

/-- If `a` and `b` are close and belong to `A`, then `a` and `⁅a, b⁆` are close. -/
lemma tendsto_bracket_fst :
    Tendsto (fun (p : X × X) ↦ (p.1, ⁅p.1, p.2⁆)) (𝓤 X ⊓ 𝓟 (A ×ˢ A)) (𝓤 X) := by
  intro V hV
  rcases hT.uniformContinuousOn_bracket hV with ⟨t₁, h₁, t₂, h₂, hV'⟩
  rcases entourageProd_subset h₁ with ⟨u, hu, u', hu', huu'⟩
  have : {p : X × X | dist p.1 p.2 < δ₀} ∈ 𝓤 X := Metric.dist_mem_uniformity hT.deltaZero_pos
  have : ({p : X × X | dist p.1 p.2 < δ₀} ∩ u ∩ u') ∩ (A ×ˢ A) ∈ 𝓤 X ⊓ 𝓟 (A ×ˢ A) :=
    inter_mem_inf (by grind [Filter.inter_mem]) (mem_principal_self _)
  apply mem_of_superset this
  rintro ⟨a, b⟩ hab
  have M₁ : ((a, a), (a, b)) ∈ t₁ :=
    huu' (by simp [entourageProd, mem_uniformity_of_eq hu, hab.1.2])
  have M₂ : ((a, a), (a, b)) ∈ t₂ := by
    simp only [mem_principal] at h₂
    apply h₂
    simp only [mem_inter_iff, mem_setOf_eq, mem_prod] at hab
    simp [hT.deltaZero_pos.le, hab.1.1.1.le, hab.2]
  have : ((a, a), (a, b)) ∈ t₁ ∩ t₂ := ⟨M₁, M₂⟩
  simpa [← hV']

/-- If `a` and `b` are close and belong to `A`, then `a` and `⁅a, b⁆` are close. -/
lemma tendsto_bracket_snd :
    Tendsto (fun (p : X × X) ↦ (p.2, ⁅p.1, p.2⁆)) (𝓤 X ⊓ 𝓟 (A ×ˢ A)) (𝓤 X) :=
  (tendsto_id.uniformity_symm.mono_left inf_le_left).uniformity_trans hT.tendsto_bracket_fst

/-- If three points are close, then the first one is close to the bracket of the other ones.
Version in terms of uniformities. -/
lemma exists_bracket_mem_entourage (hU : U ∈ 𝓤 X) :
    ∃ V ∈ 𝓤 X, (∀ x y, (x, y) ∈ V → (y, x) ∈ V) ∧
      ∀ x y z, y ∈ A → z ∈ A → (y, x) ∈ V → (x, z) ∈ V →
      ((x, ⁅y, z⁆) ∈ U ∧ (⁅y, z⁆, x) ∈ U) := by
  rcases comp_symm_of_uniformity hU with ⟨U', U'_mem, U'_symm, hU'⟩
  rcases mem_inf_iff.1 (hT.tendsto_bracket_fst U'_mem) with ⟨t₁, ht₁, t₂, ht₂, ht⟩
  rcases comp_symm_of_uniformity ht₁ with ⟨V, V_mem, V_symm, hV⟩
  refine ⟨U' ∩ V, inter_mem U'_mem V_mem, fun x y hxy ↦ ⟨U'_symm hxy.1, V_symm hxy.2⟩ ,
    fun x y z hy hz hxy hxz ↦ ?_⟩
  have : (y, ⁅y, z⁆) ∈ U' := by
    have : (y, z) ∈ t₁ ∩ t₂ := by
      simp only [mem_principal] at ht₂
      have : (y, z) ∈ V ○ V := prodMk_mem_compRel hxy.2 hxz.2
      exact ⟨hV this, ht₂ ⟨hy, hz⟩⟩
    rw [← ht] at this
    exact this
  exact ⟨hU' (prodMk_mem_compRel (U'_symm hxy.1) this),
    hU' (prodMk_mem_compRel (U'_symm this) hxy.1)⟩

/-- If three points are close, then the first one is close to the bracket of the other ones.
Version in terms of distances. -/
lemma exists_dist_bracket_lt (ε : ℝ) (hε : 0 < ε) :
    ∃ ε' ∈ Ioc 0 ((min ε δ₀) / 2), ∀ x y z, y ∈ A → z ∈ A →
      dist x y ≤ ε' → dist x z ≤ ε' → dist x ⁅y, z⁆ ≤ ε := by
  have := hT.deltaZero_pos
  have : {p : X × X | dist p.1 p.2 < ε} ∈ 𝓤 X := Metric.dist_mem_uniformity hε
  rcases hT.exists_bracket_mem_entourage this with ⟨V, hV, -, h'V⟩
  rcases Metric.mem_uniformity_dist.1 hV with ⟨ε', ε'_pos, hε'⟩
  refine ⟨min (ε' / 2) ((min ε δ₀) / 2), ⟨by positivity, min_le_right _ _⟩ ,
    fun x y z hy hz hxy hxz ↦ ?_⟩
  refine (h'V _ _ _ hy hz (hε' ?_) (hε' ?_)).1.le
  · rw [dist_comm]
    exact (hxy.trans (min_le_left _ _)).trans_lt (by linarith)
  · exact (hxz.trans (min_le_left _ _)).trans_lt (by linarith)

/-- In a locally maximal hyperbolic set, to any scale `δ` we can associate a smaller scale such that
points within the small scale have brackets and images which are controlled within the initial
scale. We register the convenient properties of such a scale reducing function in the
structure `ReduceScaleStruct`. Many fine properties of hyperbolic maps can be expressed in terms
of such a function (for instance the constants in the shadowing lemma).
Any locally maximal hyperbolic set admits a scale-reducing function, see `reduceScaleStructDefault`.
-/
structure ReduceScaleStruct where
  /-- A smaller scale such that, if two points are within the smaller scale, then their brackets
  and their images under `T` are within the initial scale. -/
  reduceScale (ε : ℝ) : ℝ
  reduceScale_mono : Monotone reduceScale
  reduceScale_pos {ε : ℝ} (hε : 0 < ε) : 0 < reduceScale ε
  reduceScale_le_half_self {ε : ℝ} : reduceScale ε ≤ ε / 2
  reduceScale_le_half_deltaZero {ε : ℝ} : reduceScale ε ≤ δ₀ / 2
  dist_bracket_le_of_le_reduceScale {ε : ℝ} {x y z : X} (hy : y ∈ A) (hz : z ∈ A)
    (hxy : dist x y ≤ reduceScale ε) (hxz : dist x z ≤ reduceScale ε) :
    dist x ⁅y, z⁆ ≤ ε
  bracket_eq_inter {x y : X} (hx : x ∈ A) (hy : y ∈ A) (h : dist x y ≤ reduceScale δ₀) :
    {⁅x, y⁆} = locUnstable T δ₀ x ∩ locStable T δ₀ y
  dist_image_le {ε : ℝ} (hε : ε ≤ δ₀) {x y : X} (h : dist x y ≤ reduceScale ε) :
    dist (T x) (T y) ≤ ε
  dist_image_symm_le {ε : ℝ} (hε : ε ≤ δ₀) {x y : X} (h : dist x y ≤ reduceScale ε) :
    dist (T.symm x) (T.symm y) ≤ ε

omit hT in
variable (T A) in
/-- Structure registering that a set `A` is hyperbolic locally maximal for an invertible map `T`.
The definition features two numbers `δ₀`and `ρ`. The first one is such that the map
is uniformly contracting by `ρ` on stable manifolds of size `δ₀`, and similarly for unstable
manifolds. Moreover, if two points of `A` are close enough, then their
stable and unstable manifolds of size `δ₀` intersect at exactly one point. As this intersection
plays a prominent role in the theory, we include it as data in the definition, the
function `bracket` (sometimes called the Ruelle bracket).

In this extended structure (compared to `IsLocallyMaxHyperbolicSet`), we also include a function
`reduceScale` such that, if two points are within the smaller scale, then their brackets
and their images under `T` are within the initial scale. This function is useful for stating
technical estimates. Such a function always exists in a locally maximal hyperbolic set, see
`IsLocallyMaxHyperbolicSet.extendDefault`.
-/

structure _root_.IsExtLocallyMaxHyperbolicSet extends IsLocallyMaxHyperbolicSet T A where
  /-- A smaller scale such that, if two points are within the smaller scale, then their brackets
  and their images under `T` are within the initial scale. -/
  reduceScale (ε : ℝ) : ℝ
  reduceScale_mono : Monotone reduceScale
  reduceScale_pos {ε : ℝ} (hε : 0 < ε) : 0 < reduceScale ε
  reduceScale_le_half_self {ε : ℝ} : reduceScale ε ≤ ε / 2
  reduceScale_le_half_deltaZero {ε : ℝ} : reduceScale ε ≤ deltaZero / 2
  dist_bracket_le_of_le_reduceScale {ε : ℝ} {x y z : X} (hy : y ∈ A) (hz : z ∈ A)
    (hxy : dist x y ≤ reduceScale ε) (hxz : dist x z ≤ reduceScale ε) :
    dist x (bracket y z) ≤ ε
  bracket_eq_inter {x y : X} (hx : x ∈ A) (hy : y ∈ A) (h : dist x y ≤ reduceScale deltaZero) :
    {bracket x y} = locUnstable T deltaZero x ∩ locStable T deltaZero y
  dist_image_le {ε : ℝ} (hε : ε ≤ deltaZero) {x y : X} (h : dist x y ≤ reduceScale ε) :
    dist (T x) (T y) ≤ ε
  dist_image_symm_le {ε : ℝ} (hε : ε ≤ deltaZero) {x y : X} (h : dist x y ≤ reduceScale ε) :
    dist (T.symm x) (T.symm y) ≤ ε

/-- Given a locally maximal hyperbolic set, and a compatible scale-reducing function, construct
the associated extended locally maximal hyperbolic set. -/
def extend_of_reduceScaleStruct (hR : hT.ReduceScaleStruct) : IsExtLocallyMaxHyperbolicSet T A where
  __ := hT
  __ := hR

/- The `omit` is nonsense, but otherwise the `irreducible_def` makes something weird. -/
omit [MetricSpace X] hT in
/-- Any locally maximal hyperbolic set admits a scale-reducing function. -/
noncomputable irreducible_def reduceScaleStructDefault : hT.ReduceScaleStruct := by
  have I (ε : ℝ) (hε : 0 < ε) : ∃ δ ∈ Ioc 0 ((min ε δ₀) / 2),
      (∀ x y z, y ∈ A → z ∈ A → dist x y ≤ δ → dist x z ≤ δ → dist x ⁅y, z⁆ ≤ ε)
      ∧ (∀ x y, dist x y ≤ δ → dist (T x) (T y) ≤ ε)
      ∧ (∀ x y, dist x y ≤ δ → dist (T.symm x) (T.symm y) ≤ ε) := by
    rcases Metric.uniformContinuous_iff_le.1 hT.uniformContinuous ε hε with ⟨t, tpos, ht⟩
    rcases Metric.uniformContinuous_iff_le.1 hT.uniformContinuous_symm ε hε with ⟨t', t'pos, ht'⟩
    rcases hT.exists_dist_bracket_lt ε hε with ⟨t'', t''pos, ht''⟩
    exact ⟨min t (min t' t''), by grind⟩
  choose! f1 hf1 h'f1 h''f1 h'''f1 using I
  have B (t : ℝ) (ht : 0 < t) : BddAbove (range (fun (x : Ioc 0 t) ↦ f1 x / 2)) := by
    refine ⟨t / 2 / 2, ?_⟩
    simp only [upperBounds, mem_range, Subtype.exists, mem_Ioc, exists_prop,
      forall_exists_index, and_imp, mem_setOf_eq]
    rintro a x hx h'x rfl
    gcongr
    apply (hf1 x hx).2.trans
    gcongr
    apply (min_le_left _ _).trans h'x
  let f2 (ε : ℝ) := ⨆ (t : Ioc 0 ε), f1 t / 2
  have If2 (ε : ℝ) (hε : 0 < ε) : f1 ε / 2 ≤ f2 ε := by
    let a : Ioc 0 ε := ⟨ε, hε, le_rfl⟩
    change f1 a / 2 ≤ f2 ε
    exact le_ciSup (f := fun (t : Ioc 0 ε) ↦ f1 t / 2) (B ε hε) a
  have f2_pos (ε : ℝ) (hε : 0 < ε) : 0 < f2 ε := by linarith [If2 ε hε, (hf1 ε hε).1]
  choose δ₁ δ₁_pos hδ₁ using hT.exists_bracket_eq_inter
  let reduceScale (ε : ℝ) := if ε ≤ 0 then ε / 2 else min (f2 ε) δ₁
  have reduceScale_mono : Monotone reduceScale := by
    intro x y hxy
    by_cases hy : y ≤ 0
    · have : x ≤ 0 := by linarith
      simp only [this, ↓reduceIte, hy, reduceScale]
      linarith
    by_cases hx : x ≤ 0
    · have : x / 2 ≤ δ₁ := by linarith
      simp only [hx, ↓reduceIte, hy, le_inf_iff, this, and_true, ge_iff_le, reduceScale]
      linarith [f2_pos y (by linarith)]
    simp only [hx, ↓reduceIte, hy, le_inf_iff, inf_le_iff, and_true, reduceScale, or_true, le_rfl]
    left
    have : Nonempty (Ioc 0 x) := ⟨⟨x, ⟨by linarith, le_rfl⟩⟩⟩
    apply ciSup_le (f := fun (t : Ioc 0 x) ↦ f1 t / 2)
    intro a
    let a' : Ioc 0 y := ⟨a, a.2.1, a.2.2.trans hxy⟩
    change f1 a' / 2 ≤ f2 y
    apply le_ciSup (f := fun (t : Ioc 0 y) ↦ f1 t / 2) (B y (by linarith))
  have reduceScale_pos {ε : ℝ} (hε : 0 < ε) : 0 < reduceScale ε := by
    have : ¬(ε ≤ 0) := by linarith
    simp [reduceScale, this, δ₁_pos, f2_pos ε hε]
  have reduceScale_le {ε : ℝ} : reduceScale ε ≤ min ε δ₀ / 2 := by
    by_cases hε : ε ≤ 0
    · simp only [hε, ↓reduceIte, reduceScale]
      gcongr
      simp only [le_inf_iff, le_refl, true_and]
      linarith [hT.deltaZero_pos]
    simp only [hε, ↓reduceIte, inf_le_iff, reduceScale]
    left
    have : Nonempty (Ioc 0 ε) := ⟨⟨ε, ⟨by linarith, le_rfl⟩⟩⟩
    apply ciSup_le (f := fun (t : Ioc 0 ε) ↦ f1 t / 2) (fun x ↦ ?_)
    simp only
    gcongr
    apply (hf1 x x.2.1).2.trans
    apply (half_le_self (le_min x.2.1.le hT.deltaZero_pos.le)).trans
    gcongr
    exact x.2.2
  have reduceScale_le_half_self {ε : ℝ} : reduceScale ε ≤ ε / 2 := by
    apply reduceScale_le.trans
    gcongr
    exact min_le_left _ _
  have reduceScale_le_half_deltaZero {ε : ℝ} : reduceScale ε ≤ δ₀ / 2 := by
    apply reduceScale_le.trans
    gcongr
    exact min_le_right _ _
  have dist_bracket_le_of_le_reduceScale {ε : ℝ} {x y z : X} (hy : y ∈ A) (hz : z ∈ A)
      (hxy : dist x y ≤ reduceScale ε) (hxz : dist x z ≤ reduceScale ε) :
      dist x ⁅y, z⁆ ≤ ε := by
    rcases le_or_gt ε 0 with hε | hε
    · have I : x = y := by rw [← dist_le_zero]; linarith [reduceScale_le_half_self (ε := ε)]
      have J : x = z := by rw [← dist_le_zero]; linarith [reduceScale_le_half_self (ε := ε)]
      simp only [← I, ← J, bracket_self, dist_self, ge_iff_le]
      linarith [dist_nonneg (x := x) (y := y), reduceScale_le_half_self (ε := ε)]
    obtain ⟨⟨i, i_pos, i_le⟩, hi⟩ : ∃ (i : Ioc 0 ε), reduceScale ε / 2 < f1 i / 2 := by
      have I : reduceScale ε / 2 < reduceScale ε := by linarith [reduceScale_pos hε]
      have J : reduceScale ε / 2 < ⨆ (t : Ioc 0 ε), f1 t / 2 := by
        apply I.trans_le
        have : ¬(ε ≤ 0) := by linarith
        simp [reduceScale, this, f2]
      have : Nonempty (Ioc 0 ε) := ⟨⟨ε, ⟨by linarith, le_rfl⟩⟩⟩
      exact exists_lt_of_lt_ciSup (f := fun (t : Ioc 0 ε) ↦ f1 t / 2) J
    apply le_trans _ i_le
    exact h'f1 _ i_pos _ _ _ hy hz (hxy.trans (by linarith)) (hxz.trans (by linarith))
  have bracket_eq_inter {x y : X} (hx : x ∈ A) (hy : y ∈ A) (h : dist x y ≤ reduceScale δ₀) :
      {⁅x, y⁆} = locUnstable T δ₀ x ∩ locStable T δ₀ y := by
    apply hδ₁ hx hy
    exact h.trans (by simp [reduceScale, not_le_of_gt hT.deltaZero_pos])
  have dist_image_le {ε : ℝ} (hε : ε ≤ δ₀) {x y : X} (h : dist x y ≤ reduceScale ε) :
      dist (T x) (T y) ≤ ε := by
    rcases le_or_gt ε 0 with hε | hε
    · have I : x = y := by rw [← dist_le_zero]; linarith [reduceScale_le_half_self (ε := ε)]
      simp only [← I, dist_self]
      linarith [dist_nonneg (x := x) (y := y), reduceScale_le_half_self (ε := ε)]
    obtain ⟨⟨i, i_pos, i_le⟩, hi⟩ : ∃ (i : Ioc 0 ε), reduceScale ε / 2 < f1 i / 2 := by
      have I : reduceScale ε / 2 < reduceScale ε := by linarith [reduceScale_pos hε]
      have J : reduceScale ε / 2 < ⨆ (t : Ioc 0 ε), f1 t / 2 := by
        apply I.trans_le
        have : ¬(ε ≤ 0) := by linarith
        simp [reduceScale, this, f2]
      have : Nonempty (Ioc 0 ε) := ⟨⟨ε, ⟨by linarith, le_rfl⟩⟩⟩
      exact exists_lt_of_lt_ciSup (f := fun (t : Ioc 0 ε) ↦ f1 t / 2) J
    apply le_trans _ i_le
    apply h''f1 i i_pos _ _ (h.trans (by linarith))
  have dist_image_symm_le {ε : ℝ} (hε : ε ≤ δ₀) {x y : X} (h : dist x y ≤ reduceScale ε) :
      dist (T.symm x) (T.symm y) ≤ ε := by
    rcases le_or_gt ε 0 with hε | hε
    · have I : x = y := by rw [← dist_le_zero]; linarith [reduceScale_le_half_self (ε := ε)]
      simp only [← I, dist_self]
      linarith [dist_nonneg (x := x) (y := y), reduceScale_le_half_self (ε := ε)]
    obtain ⟨⟨i, i_pos, i_le⟩, hi⟩ : ∃ (i : Ioc 0 ε), reduceScale ε / 2 < f1 i / 2 := by
      have I : reduceScale ε / 2 < reduceScale ε := by linarith [reduceScale_pos hε]
      have J : reduceScale ε / 2 < ⨆ (t : Ioc 0 ε), f1 t / 2 := by
        apply I.trans_le
        have : ¬(ε ≤ 0) := by linarith
        simp [reduceScale, this, f2]
      have : Nonempty (Ioc 0 ε) := ⟨⟨ε, ⟨by linarith, le_rfl⟩⟩⟩
      exact exists_lt_of_lt_ciSup (f := fun (t : Ioc 0 ε) ↦ f1 t / 2) J
    apply le_trans _ i_le
    apply h'''f1 i i_pos _ _ (h.trans (by linarith))
  exact
  { reduceScale := reduceScale
    reduceScale_mono := reduceScale_mono
    reduceScale_pos := reduceScale_pos
    reduceScale_le_half_self := reduceScale_le_half_self
    reduceScale_le_half_deltaZero := reduceScale_le_half_deltaZero
    dist_bracket_le_of_le_reduceScale := dist_bracket_le_of_le_reduceScale
    bracket_eq_inter := bracket_eq_inter
    dist_image_le := dist_image_le
    dist_image_symm_le := dist_image_symm_le }

/-- Endowing a locally maximal hyperbolic set with some (arbitrary) good scale-reduction
function. -/
noncomputable def extend : IsExtLocallyMaxHyperbolicSet T A :=
  hT.extend_of_reduceScaleStruct hT.reduceScaleStructDefault

end IsLocallyMaxHyperbolicSet

namespace IsExtLocallyMaxHyperbolicSet

variable {A : Set X} (hT : IsExtLocallyMaxHyperbolicSet T A)
include hT

local notation3 "δ₀" => hT.deltaZero
local notation3 "ρ" => hT.rho
local notation3 "⁅" x ", " y "⁆" => hT.bracket x y
local notation3 "δ₁" => hT.reduceScale δ₀
local notation3 "δ₂" => hT.reduceScale δ₁

/-- A locally maximal hyperbolic set for `T` is also locally maximal hyperbolic for `T⁻¹`. -/
protected def symm : IsExtLocallyMaxHyperbolicSet T.symm A where
  __ := hT.toIsLocallyMaxHyperbolicSet.symm
  reduceScale := hT.reduceScale
  reduceScale_mono := hT.reduceScale_mono
  reduceScale_pos := hT.reduceScale_pos
  reduceScale_le_half_self := hT.reduceScale_le_half_self
  reduceScale_le_half_deltaZero := hT.reduceScale_le_half_deltaZero
  dist_bracket_le_of_le_reduceScale hy hz hxy hxz :=
    hT.dist_bracket_le_of_le_reduceScale hz hy hxz hxy
  bracket_eq_inter hx hy h := by
    rw [inter_comm]
    rw [dist_comm] at h
    exact hT.bracket_eq_inter hy hx h
  dist_image_le := hT.dist_image_symm_le
  dist_image_symm_le := hT.dist_image_le

lemma reduceScale_le_self (hε : 0 ≤ ε) : hT.reduceScale ε ≤ ε :=
  hT.reduceScale_le_half_self.trans (by linarith)

lemma deltaOne_le_half_deltaZero : δ₁ ≤ δ₀ / 2 := hT.reduceScale_le_half_deltaZero

lemma deltaOne_le_deltaZero : δ₁ ≤ δ₀ :=
  hT.reduceScale_le_self hT.deltaZero_pos.le

lemma deltaOne_pos : 0 < δ₁ := hT.reduceScale_pos hT.deltaZero_pos

lemma deltaTwo_pos : 0 < δ₂ := hT.reduceScale_pos hT.deltaOne_pos

lemma deltaTwo_le_deltaOne : δ₂ ≤ δ₁ :=
  hT.reduceScale_le_self hT.deltaOne_pos.le

lemma bracket_mem_locStable
    (hx : x ∈ A) (hy : y ∈ A) (h : dist x y ≤ hT.reduceScale ε) (hε : ε ≤ δ₀) :
    ⁅x, y⁆ ∈ locStable T ε y := by
  apply hT.mem_locStable_of_mem_locStable_of_dist_le hy le_rfl
  · suffices {⁅x, y⁆} ⊆ locStable T δ₀ y by simpa
    rw [hT.bracket_eq_inter hx hy]
    · exact inter_subset_right
    · apply h.trans
      apply hT.reduceScale_mono hε
  · apply hT.dist_bracket_le_of_le_reduceScale hx hy (by simpa [dist_comm] using h)
    exact le_trans (by simp) h

lemma bracket_mem_locUnstable
    (hx : x ∈ A) (hy : y ∈ A) (h : dist x y ≤ hT.reduceScale ε) (hε : ε ≤ δ₀) :
    ⁅x, y⁆ ∈ locUnstable T ε x :=
  hT.symm.bracket_mem_locStable hy hx (by simpa [dist_comm] using h) hε

lemma bracket_eq_inter_of_le
    (hx : x ∈ A) (hy : y ∈ A) (h : dist x y ≤ hT.reduceScale ε) (hε : ε ≤ δ₀) :
    {⁅x, y⁆} = locUnstable T ε x ∩ locStable T ε y := by
  apply Subset.antisymm
  · simp [hT.bracket_mem_locStable hx hy h hε, hT.bracket_mem_locUnstable hx hy h hε]
  rw [hT.bracket_eq_inter hx hy (h.trans (hT.reduceScale_mono hε))]
  exact inter_subset_inter (locUnstable_mono hε) (locStable_mono hε)

lemma image_mem_locUnstable (hε : ε ≤ δ₀) (hx : x ∈ locUnstable T (hT.reduceScale ε) o) :
    T x ∈ locUnstable T ε (T o) := by
  refine ⟨fun n ↦ ?_, ?_⟩
  · cases n with
    | zero =>
      simp only [iterate_zero, id_eq]
      exact hT.dist_image_le hε (hx.1 0)
    | succ n =>
      simp only [iterate_succ_apply, Equiv.symm_apply_apply]
      apply (hx.1 n).trans
      apply hT.reduceScale_le_self
      linarith [(nonempty_locUnstable_iff.1 ⟨x, hx⟩).trans hT.reduceScale_le_half_self]
  · rw [← tendsto_add_atTop_iff_nat 1]
    simp only [iterate_succ_apply, Equiv.symm_apply_apply]
    exact hx.2

lemma image_symm_mem_locStable (hε : ε ≤ δ₀) (hx : x ∈ locStable T (hT.reduceScale ε) o) :
    T.symm x ∈ locStable T ε (T.symm o) :=
  hT.symm.image_mem_locUnstable hε hx

lemma image_bracket (hx : x ∈ A) (hy : y ∈ A) (h : dist x y ≤ δ₂) : T ⁅x, y⁆ = ⁅T x, T y⁆ := by
  have h' : dist (T x) (T y) ≤ δ₁ := by
    apply hT.dist_image_le hT.deltaOne_le_deltaZero h
  suffices T ⁅x, y⁆ ∈ locUnstable T δ₀ (T x) ∩ locStable T δ₀ (T y) by
    simpa [← hT.bracket_eq_inter (hT.mapsTo hx) (hT.mapsTo hy) h'] using this
  refine ⟨?_, ?_⟩
  · apply hT.image_mem_locUnstable le_rfl
    exact hT.bracket_mem_locUnstable hx hy h hT.deltaOne_le_deltaZero
  · apply image_mem_locStable
    apply hT.bracket_mem_locStable hx hy ?_ le_rfl
    exact h.trans (hT.reduceScale_le_self hT.deltaOne_pos.le)

lemma image_symm_bracket (hx : x ∈ A) (hy : y ∈ A) (h : dist x y ≤ δ₂) :
    T.symm ⁅x, y⁆ = ⁅T.symm x, T.symm y⁆ :=
  hT.symm.image_bracket hy hx (by simpa [dist_comm] using h)

/-- If two points follow each other during time `n`, then the difference between their unstable
components is exponentially small. -/
lemma mem_locUnstable_mul_of_forall_dist_le (ho : o ∈ A) (hx : x ∈ A)
    (h'x : ∀ i ≤ n, dist (T^[i] o) (T^[i] x) ≤ δ₂) :
    ⁅o, x⁆ ∈ locUnstable T (ρ ^ n * δ₁) o := by
  let y i := ⁅T^[i] o, T^[i] x⁆
  have B i (hi : i < n) : T (y i) = y (i + 1) := by
    simp only [y, iterate_succ_apply']
    rw [hT.image_bracket (hT.mapsTo.iterate _ ho) (hT.mapsTo.iterate _ hx)]
    exact h'x _ hi.le
  have B' i (hi : i ≤ n) : y i = T^[i] (y 0) := by
    induction i with
    | zero => simp
    | succ i ih => rw [← B _ (by omega), ih (by omega), iterate_succ_apply']
  have C : y n ∈ locUnstable T δ₁ (T^[n] o) := by
    apply hT.bracket_mem_locUnstable (hT.mapsTo.iterate _ ho) (hT.mapsTo.iterate _ hx) _
      hT.deltaOne_le_deltaZero
    exact h'x n le_rfl
  have : y 0 ∈ locUnstable T (ρ ^ n * δ₁) o := by
    have L : Function.LeftInverse T.symm^[n] T^[n] := (Equiv.leftInverse_symm T).iterate _
    convert hT.iterate_symm_mem_locUnstable_mul (hT.mapsTo.iterate _ ho)
      hT.deltaOne_le_deltaZero C n
    · rw [L o]
    · rw [B' n le_rfl, L (y 0)]
  exact this

/-- If two points follow each other during time `n` in the past, then the difference between their
stable components is exponentially small. -/
lemma mem_locStable_mul_of_forall_dist_le (ho : o ∈ A) (hx : x ∈ A)
    (h'x : ∀ i ≤ n, dist (T.symm^[i] o) (T.symm^[i] x) ≤ δ₂) :
    ⁅x, o⁆ ∈ locStable T (ρ ^ n * δ₁) o :=
  hT.symm.mem_locUnstable_mul_of_forall_dist_le ho hx h'x

/-- If two points follow each other during time `n`, both in the past and in the future, then they
are exponentially close. -/
lemma expansive_finite_time (hx : x ∈ A) (hy : y ∈ A) (h : ∀ i ≤ n, dist (T^[i] x) (T^[i] y) ≤ δ₂)
    (h' : ∀ i ≤ n, dist (T.symm^[i] x) (T.symm^[i] y) ≤ δ₂) :
    dist x y ≤ ρ ^ n * (2 * δ₁) := by
  have : dist x ⁅y, x⁆ ≤ ρ ^ n * δ₁ := (hT.mem_locStable_mul_of_forall_dist_le hx hy h').1 0
  have : dist y ⁅y, x⁆ ≤ ρ ^ n * δ₁ := by
    have : ∀ i ≤ n, dist (T^[i] y) (T^[i] x) ≤ δ₂ := by
      intro i hi
      rw [dist_comm]
      exact h i hi
    exact (hT.mem_locUnstable_mul_of_forall_dist_le hy hx this).1 0
  linarith [dist_triangle_right x y ⁅y, x⁆]

/-- If two points follow each other during time `n`, both in the past and in the future, then they
are exponentially close. -/
lemma expansive_finite_time' (hx : x ∈ A) (hy : y ∈ A)
    (h : ∀ (i : ℤ), i.natAbs ≤ n → dist ((T ^ i) x) ((T ^ i) y) ≤ δ₂) :
    dist x y ≤ ρ^n * (2 * δ₁) := by
  apply hT.expansive_finite_time hx hy
  · intro i hi
    exact h (i : ℤ) (by omega)
  · intro i hi
    have : T.symm^[i] = ⇑(T ^ (-i : ℤ)) := by
      simp only [Equiv.Perm.iterate_eq_pow, zpow_neg, zpow_natCast, DFunLike.coe_fn_eq]
      rfl
    convert h (-i : ℤ) (by omega)

/-- If two points follow each other, both in the past and in the future, then they coincide. -/
lemma expansive (hx : x ∈ A) (hy : y ∈ A) (h : ∀ i, dist (T^[i] x) (T^[i] y) ≤ δ₂)
    (h' : ∀ i, dist (T.symm^[i] x) (T.symm^[i] y) ≤ δ₂) : x = y := by
  apply eq_of_dist_eq_zero
  apply le_antisymm ?_ dist_nonneg
  have : Tendsto (fun n ↦ ρ ^ n * (2 * δ₁)) atTop (𝓝 (0 * (2 * δ₁))) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hT.rho_pos.le hT.rho_lt_one).mul_const _)
  rw [zero_mul] at this
  apply ge_of_tendsto' this (fun n ↦ ?_)
  apply hT.expansive_finite_time hx hy (fun i hi ↦ h i) (fun i hi ↦ h' i)

/-- If two points follow each other, both in the past and in the future, then they coincide. -/
lemma expansive' (hx : x ∈ A) (hy : y ∈ A)
    (h : ∀ (i : ℤ), dist ((T ^ i) x) ((T ^ i) y) ≤ δ₂) : x = y := by
  apply hT.expansive hx hy (fun i ↦ h i) (fun i ↦ ?_)
  have : T.symm^[i] = ⇑(T ^ (-i : ℤ)) := by
    simp only [Equiv.Perm.iterate_eq_pow, zpow_neg, zpow_natCast, DFunLike.coe_fn_eq]
    rfl
  convert h (-i : ℤ)

omit hT in
lemma bracket_eq_bracket
    (hA : IsExtLocallyMaxHyperbolicSet T A) (hB : IsExtLocallyMaxHyperbolicSet T B)
    {x y : X} (hx : x ∈ A ∩ B) (hy : y ∈ A ∩ B)
    (h : dist x y ≤ min (hA.reduceScale (min hA.deltaZero hB.deltaZero))
      (hB.reduceScale (min hA.deltaZero hB.deltaZero))) :
    hA.bracket x y = hB.bracket x y := by
  suffices ({hA.bracket x y} : Set X) = {hB.bracket x y} by simpa
  rw [hA.bracket_eq_inter_of_le hx.1 hy.1 (ε := min hA.deltaZero hB.deltaZero),
    hB.bracket_eq_inter_of_le hx.2 hy.2 (ε := min hA.deltaZero hB.deltaZero)] <;>
  grind only [= min_def, = mem_inter_iff, cases Or]

omit hT in
/-- The intersection of two locally maximal hyperbolic sets is again locally maximal hyperbolic.
Version given here assuming that the two initial sets are endowed with a scale-reducing function.
See `IsLocallyMaxHyperbolicSet.inter` for the version without this assumption. -/
protected noncomputable def inter
    (hA : IsExtLocallyMaxHyperbolicSet T A) (hB : IsExtLocallyMaxHyperbolicSet T B) :
    IsLocallyMaxHyperbolicSet T (A ∩ B) where
  isClosed := hA.isClosed.inter hB.isClosed
  uniformContinuous := hA.uniformContinuous
  uniformContinuous_symm := hA.uniformContinuous_symm
  rho := hA.rho
  rho_pos := hA.rho_pos
  rho_lt_one := hA.rho_lt_one
  deltaZero := min (hA.reduceScale (min hA.deltaZero hB.deltaZero))
    (hB.reduceScale (min hA.deltaZero hB.deltaZero))
  deltaZero_pos := by
    apply lt_min
    · apply hA.reduceScale_pos (lt_min hA.deltaZero_pos hB.deltaZero_pos)
    · apply hB.reduceScale_pos (lt_min hA.deltaZero_pos hB.deltaZero_pos)
  contraction {o x y} ho hx hy := by
    apply hA.contraction ho.1 (locStable_mono ?_ hx) (locStable_mono ?_ hy)
    · apply (min_le_left _ _).trans
      apply (hA.reduceScale_le_self _).trans (min_le_left _ _)
      exact le_min hA.deltaZero_pos.le hB.deltaZero_pos.le
    · apply (min_le_left _ _).trans
      apply (hA.reduceScale_le_self _).trans (min_le_left _ _)
      exact le_min hA.deltaZero_pos.le hB.deltaZero_pos.le
  expansion {o x y} ho hx hy := by
    apply hA.expansion ho.1 (locStable_mono ?_ hx) (locStable_mono ?_ hy)
    · apply (min_le_left _ _).trans
      apply (hA.reduceScale_le_self _).trans (min_le_left _ _)
      exact le_min hA.deltaZero_pos.le hB.deltaZero_pos.le
    · apply (min_le_left _ _).trans
      apply (hA.reduceScale_le_self _).trans (min_le_left _ _)
      exact le_min hA.deltaZero_pos.le hB.deltaZero_pos.le
  mapsTo := (hA.mapsTo.mono inter_subset_left Subset.rfl).inter
    (hB.mapsTo.mono inter_subset_right Subset.rfl)
  mapsTo_symm := (hA.mapsTo_symm.mono inter_subset_left Subset.rfl).inter
    (hB.mapsTo_symm.mono inter_subset_right Subset.rfl)
  bracket x y := if dist x y ≤ min (hA.reduceScale (min hA.deltaZero hB.deltaZero))
    (hB.reduceScale (min hA.deltaZero hB.deltaZero)) then hA.bracket x y else x
  bracket_mem {x y} hx hy := by
    split_ifs with h
    · refine ⟨hA.bracket_mem hx.1 hy.1, ?_⟩
      convert hB.bracket_mem hx.2 hy.2 using 1
      exact bracket_eq_bracket hA hB hx hy h
    · exact hx
  bracket_self := by simp
  uniformContinuousOn_bracket := by
    apply (hA.uniformContinuousOn_bracket.mono ?_).congr
    · intro p hp
      simp only [mem_prod, mem_inter_iff, mem_setOf_eq] at hp
      simp [hp.1, uncurry]
    simp +contextual only [le_inf_iff, mem_prod, mem_inter_iff, setOf_subset_setOf, and_self,
      and_true, and_imp, Prod.forall]
    rintro a b h - - - - -
    apply h.trans
    apply (hA.reduceScale_le_self _).trans (min_le_left _ _)
    exact le_min hA.deltaZero_pos.le hB.deltaZero_pos.le
  exists_bracket_eq_inter := by
    have I : 0 < min (hA.reduceScale (min hA.deltaZero hB.deltaZero))
        (hB.reduceScale (min hA.deltaZero hB.deltaZero)) := by
      apply lt_min
      · apply hA.reduceScale_pos (lt_min hA.deltaZero_pos hB.deltaZero_pos)
      · apply hB.reduceScale_pos (lt_min hA.deltaZero_pos hB.deltaZero_pos)
    refine ⟨hA.reduceScale (min (hA.reduceScale (min hA.deltaZero hB.deltaZero))
      (hB.reduceScale (min hA.deltaZero hB.deltaZero))), hA.reduceScale_pos I, ?_⟩
    intro x y hx hy hxy
    have : dist x y ≤ min (hA.reduceScale (min hA.deltaZero hB.deltaZero))
        (hB.reduceScale (min hA.deltaZero hB.deltaZero)) :=
      hxy.trans (hA.reduceScale_le_self I.le)
    simp only [this, ↓reduceIte]
    apply hA.bracket_eq_inter_of_le hx.1 hy.1 hxy ?_
    apply (min_le_left _ _).trans
    apply (hA.reduceScale_le_self _).trans (min_le_left _ _)
    exact le_min hA.deltaZero_pos.le hB.deltaZero_pos.le

variable [CompleteSpace X]

/-- Let `δ > 0`. Let `ε` be small enough compared to `δ`. Then any `ε`-pseudo-orbit in the future
can be `4δ`-shadowed by a genuine orbit, starting from the `δ`-unstable manifold of the initial
point.

We give the conditions on `ε` in explicit form, to make it possible to check them uniformly
over families of maps. First, we fix `M` large enough so that `2 * ρ ^ M * δ ≤ hT.reduceScale δ`.
Then, `ε` should be small enough that an `ε`-pseudo-orbit does not deviate from a genuine orbit
by more than `hT.reduceScale δ / 2` until time `M`.
-/
lemma future_shadowing_precise
    (hδ : 0 < δ) (h''δ : δ ≤ δ₀ / 2) (x : ℕ → X)
    (hx : ∀ n, dist (T (x n)) (x (n + 1)) ≤ ε) (h'x : ∀ n, x n ∈ A)
    {M : ℕ} (hM : 2 * ρ ^ M * δ ≤ hT.reduceScale δ)
    (hε : ∀ (u : ℕ → X), (∀ n, dist (T (u n)) (u (n + 1)) ≤ ε) →
      ∀ i ≤ M, dist (T^[i] (u 0)) (u i) ≤ hT.reduceScale δ / 2) :
    ∃ p ∈ locUnstable T δ (x 0) ∩ A, ∀ n, dist (x n) (T ^[n] p) ≤ 4 * δ := by
  -- Start by recording useful basic facts
  have : Nonempty X := ⟨x 0⟩
  have := hT.rho_pos
  have := hT.continuous
  have rhoM : ρ ^ M ≤ 2⁻¹ := by
    have W := hM.trans hT.reduceScale_le_half_self
    field_simp at W
    linarith
  have : M ≠ 0 := by
    intro h
    simp only [h, pow_zero] at rhoM
    norm_num at rhoM
  have h'δ : δ ≤ δ₀ := by linarith [hT.deltaZero_pos]
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
  have A_aux n (hn : y n ∈ locStable T δ (x (M * n))) :
      dist (x (M * (n + 1))) (T^[M] (y n)) ≤ hT.reduceScale δ := by
    apply (dist_triangle_left _ _ (T^[M] (x (M * n)))).trans
    have : dist (T^[M] (x (M * n))) (x (M * (n + 1))) ≤ hT.reduceScale δ / 2 :=
      hε (fun k ↦ x (M * n + k)) (fun k ↦ hx (M * n + k)) M le_rfl
    have : dist (T^[M] (x (M * n))) (T^[M] (y n)) ≤ ρ ^ M * δ :=
      hT.dist_iterate_le_mul_of_mem_locStable (h'x _) h'δ hn M
    linarith
  have B n : y n ∈ locStable T δ (x (M * n)) ∩ A := by
    induction n with
    | zero => simp [y, hδ.le, locStable, h'x 0]
    | succ n ih =>
      rw [show y (n + 1) = ⁅T^[M] (y n), x (M * (n + 1))⁆ by rfl]
      refine ⟨?_, hT.bracket_mem (hT.mapsTo.iterate _ ih.2) (h'x _)⟩
      apply hT.bracket_mem_locStable (hT.mapsTo.iterate _ ih.2) (h'x _) _ h'δ
      rw [dist_comm]
      apply A_aux _ ih.1
  have A' n : dist (x (M * (n + 1))) (T^[M] (y n)) ≤ hT.reduceScale δ :=
    A_aux n (B n).1
  have C n : y (n + 1) ∈ locUnstable T δ (T^[M] (y n)) := by
    rw [show y (n + 1) = ⁅T^[M] (y n), x (M * (n + 1))⁆ by rfl]
    apply hT.bracket_mem_locUnstable (hT.mapsTo.iterate _ (B n).2) (h'x _) _ h'δ
    rw [dist_comm]
    exact A' n
  /- Define a sequence `z_{i, n}` around `x_{M * i}`, as the pullback of `y_{i + n}` from `n` times
  later in the future. We are mostly interested in `z_{0,n}` (which will converge to the desired
  point) but for the estimates we will need to control what happens at an arbitrary `i`. Thanks to
  the contracting properties of `T⁻¹` along unstable manifolds, `n ↦ z_{i,n}` has successive jumps
  of size at most `2^{-(n+1)} δ`, and is therefore converging to a limit `pᵢ` belonging to
  the stable manifold of `yᵢ` of size `δ`. -/
  let z i n := T.symm^[M * n] (y (i + n))
  have Z i n : z i (n + 1) ∈ locUnstable T (ρ ^ (M * (n + 1)) * δ) (z i n) := by
    convert hT.iterate_symm_mem_locUnstable_mul (hT.mapsTo.iterate _ (B _).2) h'δ (C (i + n))
      (n := M * (n + 1)) using 2
    rw [mul_add, iterate_add_apply, mul_one, L]
  have Z' i n : z i (n + 1) ∈ locUnstable T (2⁻¹ ^ (n + 1) * δ) (z i n) := by
    apply locUnstable_mono _ (Z i n)
    rw [pow_mul]
    gcongr
  let p i := limUnder atTop (z i)
  have Lim i : Tendsto (z i) atTop (𝓝 (p i)) := by
    apply tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete ?_)
    apply cauchySeq_of_le_geometric_two (C := δ) (fun n ↦ ?_)
    apply ((Z' i n).1 0).trans_eq
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
  have H i n : z i n ∈ locUnstable T ((1 - 2⁻¹ ^ n) * δ) (y i) := by
    induction n with
    | zero => simp [z]
    | succ n ih =>
      have I : (1 - 2⁻¹ ^ n) * δ + 2⁻¹ ^ (n + 1) * δ = (1 - 2⁻¹ ^ (n + 1)) * δ := by ring
      have := mem_locUnstable_trans ih (Z' i n)
      rwa [I] at this
  have P i : p i ∈ locUnstable T δ (y i) ∩ A := by
    refine IsClosed.mem_of_tendsto ((hT.isClosed_locUnstable (B _).2 h'δ).inter hT.isClosed) (Lim i)
      (Eventually.of_forall (fun n ↦ ⟨?_, ?_⟩))
    · apply locUnstable_mono _ (H i n)
      simp [sub_mul, hδ.le]
    · apply hT.mapsTo_symm.iterate
      exact (B _).2
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
    have : dist (x (M * a + b)) (T^[b] (x (M * a))) ≤ hT.reduceScale δ / 2 := by
      rw [dist_comm]
      exact hε (fun i ↦ x (M * a + i)) (fun n ↦ hx _) b hb.le
    exact this.trans (by linarith [hT.reduceScale_le_half_self (ε := δ)])
  have : dist (T^[b] (x (M * a))) (T^[b] (y a)) ≤ δ := (iterate_mem_locStable (B _).1 _).1 0
  have : dist (T^[b] (y a)) (T^[M * a + b] (p 0)) ≤ 2 * δ := by
    have E1 : T^[b] (y a) = T.symm^[M-b] (T^[M] (y a)) := by
      have : M = M-b + b := by omega
      nth_rw 2 [this]
      rw [iterate_add_apply, L]
    have E2 : T^[M * a + b] (p 0) = T.symm^[M-b] (p (a + 1)) := by
      have : M * (a + 1) = (M - b) + (M * a + b) := by rw [mul_add]; omega
      rw [← I (a + 1), this, iterate_add_apply _ (M - b), L]
    rw [E1, E2]
    have : p (a + 1) ∈ locUnstable T (δ + δ) (T^[M] (y a)) :=
      mem_locUnstable_trans (C a) (P (a + 1)).1
    apply ((iterate_symm_mem_locUnstable this (M - b)).1 0).trans_eq (by ring)
  linarith

/-- Consider a locally maximal hyperbolic set. Let `δ > 0`. Let `ε` be small enough compared
to `δ`. Then any `ε`-pseudo-orbit can be `4δ`-shadowed by a genuine orbit.

We give the conditions on `ε` in explicit form, to make it possible to check them uniformly
over families of maps. First, we fix `M` large enough so that `2 * ρ ^ M * δ ≤ hT.reduceScale δ`.
Then, `ε` should be small enough that an `ε`-pseudo-orbit does not deviate from a genuine orbit
by more than `hT.reduceScale δ / 2` until time `M`.
-/
lemma shadowing_precise
    (hδ : 0 < δ) (h'δ : δ ≤ δ₂ / 8) (x : ℤ → X)
    (hx : ∀ n, dist (T (x n)) (x (n + 1)) ≤ ε) (h'x : ∀ n, x n ∈ A)
    {M : ℕ} (hM : 2 * ρ ^ M * δ ≤ hT.reduceScale δ)
    (hε : ∀ (u : ℕ → X), (∀ n, dist (T (u n)) (u (n + 1)) ≤ ε) →
      ∀ i ≤ M, dist (T^[i] (u 0)) (u i) ≤ hT.reduceScale δ / 2) :
    ∃ p ∈ A, ∀ (n : ℕ), dist (x n) (T^[n] p) ≤ 4 * δ ∧ dist (x (-n)) (T.symm^[n] p) ≤ 4 * δ := by
  have h'δ : δ ≤ δ₀ / 2 := by linarith [hT.deltaTwo_le_deltaOne, hT.deltaOne_le_deltaZero]
  have E n : ∃ p ∈ A, (∀ (i : ℕ), dist (x i) (T^[i] p) ≤ 4 * δ)
      ∧ (∀ (i : ℕ), i ≤ n → dist (x (-i)) (T.symm^[i] p) ≤ 4 * δ) := by
    rcases hT.future_shadowing_precise hδ h'δ (ε := ε) (fun i ↦ x (i - n : ℤ))
      (fun i ↦ by convert hx (i - n) using 3; omega) (fun i ↦ h'x _) hM hε with ⟨q, h'q, hq⟩
    refine ⟨T^[n] q, hT.mapsTo.iterate _ h'q.2, fun i ↦ ?_, fun i hi ↦ ?_⟩
    · rw [← iterate_add_apply]
      convert hq (i + n)
      omega
    · have L : Function.LeftInverse T.symm^[i] T^[i] := (Equiv.leftInverse_symm T).iterate _
      have : n = i + (n - i) := by omega
      rw [this, iterate_add_apply, L]
      convert hq (n - i) using 3
      omega
  choose p hpA hp h'p using E
  have B n : dist (p n) (p (n + 1)) ≤ ρ ^ n * (2 * δ₁) := by
    apply hT.expansive_finite_time (hpA _) (hpA _) (fun i hi ↦ ?_) (fun i hi ↦ ?_)
    · apply (dist_triangle_left _ _ (x i)).trans
      linarith [hp n i, hp (n + 1) i]
    · apply (dist_triangle_left _ _ (x (-i))).trans
      linarith [h'p n i hi , h'p (n + 1) i (by omega)]
  have : CauchySeq p := by
    apply cauchySeq_of_le_geometric (ρ) (2 * δ₁) hT.rho_lt_one (fun n ↦ ?_)
    exact (B n).trans_eq (by ring)
  obtain ⟨q, hq⟩ : ∃ q, Tendsto p atTop (𝓝 q) := cauchy_iff_exists_le_nhds.mp this
  refine ⟨q, ?_, fun n ↦ ⟨?_, ?_⟩⟩
  · exact IsClosed.mem_of_tendsto hT.isClosed hq (Eventually.of_forall hpA)
  · have := hT.continuous
    have : ContinuousAt (T^[n]) q := by fun_prop
    have := Tendsto.dist (tendsto_const_nhds (x := x n)) (Tendsto.comp this hq)
    exact le_of_tendsto' this (fun i ↦ hp _ _)
  · have := hT.continuous_symm
    have : ContinuousAt (T.symm^[n]) q := by fun_prop
    have := Tendsto.dist (tendsto_const_nhds (x := x (-n))) (Tendsto.comp this hq)
    apply le_of_tendsto this
    filter_upwards [Ici_mem_atTop n] with i hi using h'p _ _ hi

/-- Consider a locally maximal hyperbolic set. Let `δ > 0`. Let `ε` be small enough compared
to `δ`. Then any `ε`-pseudo-orbit can be `4δ`-shadowed by a genuine orbit.

We give the conditions on `ε` in explicit form, to make it possible to check them uniformly
over families of maps. First, we fix `M` large enough so that `2 * ρ ^ M * δ ≤ hT.reduceScale δ`.
Then, `ε` should be small enough that an `ε`-pseudo-orbit does not deviate from a genuine orbit
by more than `hT.reduceScale δ / 2` until time `M`.
-/
lemma shadowing_precise'
    (hδ : 0 < δ) (h''δ : δ ≤ δ₂ / 8) (x : ℤ → X)
    (hx : ∀ n, dist (T (x n)) (x (n + 1)) ≤ ε) (h'x : ∀ n, x n ∈ A)
    {M : ℕ} (hM : 2 * ρ ^ M * δ ≤ hT.reduceScale δ)
    (hε : ∀ (u : ℕ → X), (∀ n, dist (T (u n)) (u (n + 1)) ≤ ε) →
      ∀ i ≤ M, dist (T^[i] (u 0)) (u i) ≤ hT.reduceScale δ / 2) :
    ∃ p ∈ A, ∀ (n : ℤ), dist (x n) ((T ^ n) p) ≤ 4 * δ := by
  rcases hT.shadowing_precise hδ h''δ x hx h'x hM hε with ⟨p, hpA, hp⟩
  refine ⟨p, hpA, fun n ↦ ?_⟩
  rcases Int.natAbs_eq n with hn | hn <;> set i := n.natAbs <;> rw [hn]
  · apply (hp i).1
  · convert (hp i).2
    simp only [Equiv.Perm.iterate_eq_pow, zpow_neg, zpow_natCast, DFunLike.coe_fn_eq]
    rfl

end IsExtLocallyMaxHyperbolicSet

/-- Given a positive parameter `δ`, an integer `n` and a uniformly continuous map `f`, one may find
`ε > 0` such that any `ε`-pseudo-orbit does not deviate from a genuine orbit by more than `δ`
during the first `n` iterates. -/
lemma exists_dist_iterate_le_of_pseudoOrbit
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

namespace IsLocallyMaxHyperbolicSet

/-- Consider a locally maximal hyperbolic set. Let `δ > 0`. If `ε` is small enough, then
any `ε`-pseudo-orbit can be `δ`-shadowed by a genuine orbit.

The statement is given here as an existential statement. For explicit sufficient conditions on `ε`,
see `shadowing_precise'` (from which this one is derived). -/
theorem shadowing [CompleteSpace X] (hT : IsLocallyMaxHyperbolicSet T A) (hδ : 0 < δ) :
    ∃ ε > 0, ∀ (x : ℤ → X), (∀ n, dist (T (x n)) (x (n + 1)) ≤ ε) → (∀ n, x n ∈ A) →
      ∃ p ∈ A, ∀ n, dist (x n) ((T ^ n) p) ≤ δ := by
  let hT' := hT.extend
  let δ₂ := hT'.reduceScale (hT'.reduceScale hT'.deltaZero)
  let ρ := hT'.rho
  let δ' := min (δ / 4) (δ₂ / 8)
  have : δ' ≤ δ / 4 := min_le_left _ _
  have δ'_pos : 0 < δ' := by simpa [δ', hδ] using hT'.deltaTwo_pos
  obtain ⟨M, hM⟩ : ∃ M, 2 * ρ ^ M * δ' < hT'.reduceScale δ' := by
    have : Tendsto (fun n ↦ 2 * ρ ^ n * δ') atTop (𝓝 (2 * 0 * δ')) :=
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hT.rho_pos.le hT.rho_lt_one).const_mul _).mul_const _
    rw [mul_zero, zero_mul] at this
    exact ((tendsto_order.1 this).2 _ (hT'.reduceScale_pos δ'_pos)).exists
  obtain ⟨ε, εpos, hε⟩ : ∃ ε > 0, ∀ (u : ℕ → X), (∀ n, dist (T (u n)) (u (n + 1)) ≤ ε) →
      ∀ i ≤ M, dist (T^[i] (u 0)) (u i) ≤ hT'.reduceScale δ' / 2 := by
    apply exists_dist_iterate_le_of_pseudoOrbit hT.uniformContinuous
    linarith [hT'.reduceScale_pos δ'_pos]
  refine ⟨ε, εpos, fun x hx h'x ↦ ?_⟩
  rcases hT'.shadowing_precise' δ'_pos (min_le_right _ _) x hx h'x hM.le hε with ⟨p, hpA, hp⟩
  exact ⟨p, hpA, fun n ↦ (hp n).trans (by linarith)⟩

/-- The intersection of two locally maximal hyperbolic sets is again locally maximal hyperbolic. -/
protected noncomputable def inter
    (hA : IsLocallyMaxHyperbolicSet T A) (hB : IsLocallyMaxHyperbolicSet T B) :
    IsLocallyMaxHyperbolicSet T (A ∩ B) :=
  hA.extend.inter hB.extend

end IsLocallyMaxHyperbolicSet
