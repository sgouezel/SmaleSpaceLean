/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Topological study of spaces `Π (n : ℤ), E n`

This is a copy of pârt of the mathlib file `PiNat.lean`, with indexing by `ℤ` instead of `ℕ`.

When `E n` are topological spaces, the space `Π (n : ℤ), E n` is naturally a topological space
(with the product topology). When `E n` are uniform spaces, it also inherits a uniform structure.
However, it does not inherit a canonical metric space structure of the `E n`. Nevertheless, one
can put a noncanonical metric space structure (or rather, several of them). This is done in this
file.

## Main definitions and results

One can define a combinatorial distance on `Π (n : ℤ), E n`, as follows:

* `PiInt.cylinder x n` is the set of points `y` with `x i = y i` for `-n < i < n`.
* `PiInt.firstDiff x y` is the first index at which `x i ≠ y i` or `x (-i) ≠ y (-i)`.
* `PiInt.dist x y` is equal to `(1/2) ^ (firstDiff x y)`. It defines a distance
  on `Π (n : ℕ), E n`, compatible with the topology when the `E n` have the discrete topology.
* `PiInt.metricSpace`: the metric space structure, given by this distance. Not registered as an
  instance. This space is a complete metric space.
* `PiInt.metricSpaceOfDiscreteUniformity`: the same metric space structure, but adjusting the
  uniformity defeqness when the `E n` already have the discrete uniformity. Not registered as an
  instance
-/

noncomputable section

open Topology TopologicalSpace Set Metric Filter Function

attribute [local simp] pow_le_pow_iff_right₀ one_lt_two inv_le_inv₀ zero_le_two zero_lt_two

variable {E : ℤ → Type*}

namespace PiInt

/-! ### The firstDiff function -/

open Classical in
/-- In a product space `Π n, E n`, then `firstDiff x y` is the first index at which `x` and `y`
differ. If `x = y`, then by convention we set `firstDiff x x = 0`. -/
irreducible_def firstDiff (x y : Π n, E n) : ℕ :=
  if h : ∃ (i : ℕ), x i ≠ y i ∨ x (-i) ≠ y (-i) then Nat.find h else 0

theorem apply_firstDiff_ne_or {x y : Π n, E n} (h : x ≠ y) :
    x (firstDiff x y) ≠ y (firstDiff x y) ∨ x (-firstDiff x y) ≠ y (-firstDiff x y) := by
  have h' : ∃ (i : ℕ), x i ≠ y i ∨ x (-i) ≠ y (-i) := by
    contrapose! h
    ext j
    rcases Int.eq_nat_or_neg j with ⟨w, rfl | rfl⟩ <;> grind
  rw [firstDiff_def, dif_pos h']
  classical
  apply Nat.find_spec h'

theorem apply_nat_eq_of_lt_firstDiff {x y : Π n, E n} {n : ℕ} (hn : n < firstDiff x y) :
    x n = y n := by
  classical
  rw [firstDiff_def] at hn
  split_ifs at hn with h
  · have := Nat.find_min h hn
    grind
  · exact (not_lt_zero' hn).elim

theorem apply_neg_eq_of_lt_firstDiff {x y : Π n, E n} {n : ℕ} (hn : n < firstDiff x y) :
    x (-n) = y (-n) := by
  classical
  rw [firstDiff_def] at hn
  split_ifs at hn with h
  · have := Nat.find_min h hn
    grind
  · exact (not_lt_zero' hn).elim

theorem apply_eq {x y : Π n, E n} {i : ℤ} (h : (-firstDiff x y : ℤ) < i) (h' : i < firstDiff x y) :
    x i = y i := by
  rcases Int.eq_nat_or_neg i with ⟨w, rfl | rfl⟩
  · apply apply_nat_eq_of_lt_firstDiff (by grind)
  · apply apply_neg_eq_of_lt_firstDiff (by grind)

theorem firstDiff_comm (x y : Π n, E n) : firstDiff x y = firstDiff y x := by
  classical
  simp only [firstDiff_def, ne_comm]

theorem min_firstDiff_le (x y z : Π n, E n) (h : x ≠ z) :
    min (firstDiff x y) (firstDiff y z) ≤ firstDiff x z := by
  by_contra! H
  rw [lt_min_iff] at H
  rcases apply_firstDiff_ne_or h with h' | h'
  · apply h'
    calc
    x (firstDiff x z) = y (firstDiff x z) := apply_nat_eq_of_lt_firstDiff H.1
    _ = z (firstDiff x z) := apply_nat_eq_of_lt_firstDiff H.2
  · apply h'
    calc
    x (-firstDiff x z) = y (-firstDiff x z) := apply_neg_eq_of_lt_firstDiff H.1
    _ = z (-firstDiff x z) := apply_neg_eq_of_lt_firstDiff H.2

/-! ### Cylinders -/

/-- In a product space `Π n, E n`, the cylinder set of length `n` around `x`, denoted
`cylinder x n`, is the set of sequences `y` that coincide with `x` on the first `n` symbols, i.e.,
such that `y i = x i` for all `i < n`.
-/
def cylinder (x : Π n, E n) (n : ℕ) : Set (Π n, E n) :=
  { y | ∀ i, (-n : ℤ) < i → i < n → y i = x i }

theorem cylinder_eq_pi (x : Π n, E n) (n : ℕ) :
    cylinder x n = Set.pi (Finset.Ioo (-n : ℤ) n : Set ℤ) fun i : ℤ => {x i} := by
  ext y
  simp [cylinder]

@[simp]
theorem cylinder_zero (x : Π n, E n) : cylinder x 0 = univ := by
  simp [cylinder_eq_pi]

theorem cylinder_anti (x : Π n, E n) {m n : ℕ} (h : m ≤ n) : cylinder x n ⊆ cylinder x m :=
  fun _y hy i hi h'i ↦ hy i (by grind) (by grind)

@[simp]
theorem mem_cylinder_iff {x y : Π n, E n} {n : ℕ} :
    y ∈ cylinder x n ↔ ∀ i, (-n : ℤ) < i → i < n → y i = x i :=
  Iff.rfl

theorem self_mem_cylinder (x : Π n, E n) (n : ℕ) : x ∈ cylinder x n := by simp

theorem mem_cylinder_iff_eq {x y : Π n, E n} {n : ℕ} :
    y ∈ cylinder x n ↔ cylinder y n = cylinder x n := by
  constructor
  · intro hy
    apply Subset.antisymm
    · intro z hz i hi h'i
      rw [← hy i hi h'i]
      exact hz i hi h'i
    · intro z hz i hi h'i
      rw [hy i hi h'i]
      exact hz i hi h'i
  · intro h
    rw [← h]
    exact self_mem_cylinder _ _

theorem mem_cylinder_comm (x y : Π n, E n) (n : ℕ) : y ∈ cylinder x n ↔ x ∈ cylinder y n := by
  simp [eq_comm]

theorem mem_cylinder_iff_le_firstDiff {x y : Π n, E n} (hne : x ≠ y) (i : ℕ) :
    x ∈ cylinder y i ↔ i ≤ firstDiff x y := by
  constructor
  · intro h
    by_contra!
    rcases apply_firstDiff_ne_or hne with h' | h' <;>
    apply h' (h _ (by grind) (by grind))
  · intro hi j hj h'j
    exact apply_eq (by grind) (by grind)

theorem mem_cylinder_firstDiff (x y : Π n, E n) : x ∈ cylinder y (firstDiff x y) := fun _i hi h'i =>
  apply_eq hi h'i

theorem cylinder_eq_cylinder_of_le_firstDiff (x y : Π n, E n) {n : ℕ} (hn : n ≤ firstDiff x y) :
    cylinder x n = cylinder y n := by
  rw [← mem_cylinder_iff_eq]
  intro i hi h'i
  exact apply_eq (by grind) (by grind)

theorem update_mem_cylinder (x : Π n, E n) (n : ℕ) (y : E n) : update x n y ∈ cylinder x n :=
  mem_cylinder_iff.2 fun i hi h'i => by simp [h'i.ne]

/-!
### A distance function on `Π n, E n`

We define a distance function on `Π n, E n`, given by `dist x y = (1/2)^n` where `n` is the first
index at which `x` and `y` differ. When each `E n` has the discrete topology, this distance will
define the right topology on the product space. We do not record a global `Dist` instance nor
a `MetricSpace` instance, as other distances may be used on these spaces, but we register them as
local instances in this section.
-/

open Classical in
/-- The distance function on a product space `Π n, E n`, given by `dist x y = (1/2)^n` where `n` is
the first index at which `x` and `y` differ. -/
protected def dist : Dist (Π n, E n) :=
  ⟨fun x y => if x ≠ y then (2⁻¹ : ℝ) ^ firstDiff x y else 0⟩

attribute [local instance] PiInt.dist

theorem dist_eq_of_ne {x y : Π n, E n} (h : x ≠ y) : dist x y = (2⁻¹ : ℝ) ^ firstDiff x y := by
  simp [dist, h]

protected theorem dist_self (x : Π n, E n) : dist x x = 0 := by simp [dist]

protected theorem dist_comm (x y : Π n, E n) : dist x y = dist y x := by
  classical
  simp [dist, @eq_comm _ x y, firstDiff_comm]

protected theorem dist_nonneg (x y : Π n, E n) : 0 ≤ dist x y := by
  rcases eq_or_ne x y with (rfl | h)
  · simp [dist]
  · simp [dist, h]

theorem dist_triangle_nonarch (x y z : Π n, E n) : dist x z ≤ max (dist x y) (dist y z) := by
  rcases eq_or_ne x z with (rfl | hxz)
  · simp [PiInt.dist_self x, PiInt.dist_nonneg]
  rcases eq_or_ne x y with (rfl | hxy)
  · simp
  rcases eq_or_ne y z with (rfl | hyz)
  · simp
  simp only [dist_eq_of_ne, hxz, hxy, hyz, inv_le_inv₀, inv_pow, zero_lt_two, Ne,
    not_false_iff, le_max_iff, pow_le_pow_iff_right₀, one_lt_two, pow_pos,
    min_le_iff.1 (min_firstDiff_le x y z hxz)]

protected theorem dist_triangle (x y z : Π n, E n) : dist x z ≤ dist x y + dist y z :=
  calc
    dist x z ≤ max (dist x y) (dist y z) := dist_triangle_nonarch x y z
    _ ≤ dist x y + dist y z := max_le_add_of_nonneg (PiInt.dist_nonneg _ _) (PiInt.dist_nonneg _ _)

protected theorem eq_of_dist_eq_zero (x y : Π n, E n) (hxy : dist x y = 0) : x = y := by
  rcases eq_or_ne x y with (rfl | h); · rfl
  simp [dist_eq_of_ne h] at hxy

theorem mem_cylinder_iff_dist_le {x y : Π n, E n} {n : ℕ} :
    y ∈ cylinder x n ↔ dist y x ≤ 2⁻¹ ^ n := by
  rcases eq_or_ne y x with (rfl | hne)
  · simp [PiInt.dist_self]
  suffices (∀ i : ℤ, (-n : ℤ) < i → i < n → y i = x i) ↔ n ≤ firstDiff y x by
    simpa [dist_eq_of_ne hne]
  constructor
  · intro hy
    by_contra! H
    rcases apply_firstDiff_ne_or hne with h' | h' <;>
    exact h' (hy _ (by grind) (by grind))
  · intro h i hi h'i
    exact apply_eq (by grind) (by grind)

theorem mem_cylinder_succ_iff_dist_lt {x y : Π n, E n} {n : ℕ} :
    y ∈ cylinder x (n + 1) ↔ dist y x < 2⁻¹ ^ n := by
  rcases eq_or_ne y x with (rfl | hne)
  · simp [PiInt.dist_self]
  suffices (∀ i : ℤ, (-(n + 1) : ℤ) < i → i < n + 1 → y i = x i) ↔ n < firstDiff y x by
    simp only [neg_add_rev, Int.reduceNeg, add_neg_lt_iff_lt_add, mem_cylinder_iff, Nat.cast_add,
      Nat.cast_one, dist_eq_of_ne hne, inv_pow] at this ⊢
    simp only [this]
    rw [inv_lt_inv₀ (by positivity) (by positivity), pow_lt_pow_iff_right₀ one_lt_two]
  constructor
  · intro hy
    by_contra! H
    rcases apply_firstDiff_ne_or hne with h' | h' <;>
    exact h' (hy _ (by grind) (by grind))
  · intro h i hi h'i
    exact apply_eq (by grind) (by grind)

theorem apply_eq_of_dist_lt {x y : Π n, E n} {n : ℕ} (h : dist x y < 2⁻¹ ^ n) {i : ℤ}
    (hi : (-n : ℤ) ≤ i) (h'i : i ≤ n) : x i = y i :=
  mem_cylinder_succ_iff_dist_lt.2 h i (by grind) (by grind)

lemma dist_le_iff {x y : Π n, E n} {s : ℝ} (hs : 0 ≤ s) :
    (dist x y ≤ s) ↔ (∀ (n : ℕ), s < (2 ⁻¹) ^ n → dist x y < 2⁻¹ ^ n) := by
  refine ⟨fun h n hs ↦ by order, fun h ↦ ?_⟩
  rcases eq_or_ne x y with rfl | hxy
  · simp [hs, PiInt.dist_self]
  rw [dist_eq_of_ne hxy] at h ⊢
  contrapose! h
  exact ⟨firstDiff x y, h, le_rfl⟩

/-- A function to a pseudo-metric-space is `1`-Lipschitz if and only if points in the same cylinder
of length `n` are sent to points within distance `(1/2)^n`.
Not expressed using `LipschitzWith` as we don't have a metric space structure -/
theorem lipschitz_with_one_iff_forall_dist_image_le_of_mem_cylinder {α : Type*}
    [PseudoMetricSpace α] {f : (Π n, E n) → α} :
    (∀ x y : Π n, E n, dist (f x) (f y) ≤ dist x y) ↔
      ∀ x y n, y ∈ cylinder x n → dist (f x) (f y) ≤ 2⁻¹ ^ n := by
  constructor
  · intro H x y n hxy
    apply (H x y).trans
    rw [PiInt.dist_comm]
    exact mem_cylinder_iff_dist_le.1 hxy
  · intro H x y
    rcases eq_or_ne x y with (rfl | hne)
    · simp [PiInt.dist_nonneg]
    rw [dist_eq_of_ne hne]
    apply H x y (firstDiff x y)
    rw [firstDiff_comm]
    exact mem_cylinder_firstDiff _ _

variable (E)
variable [∀ n, TopologicalSpace (E n)] [∀ n, DiscreteTopology (E n)]

theorem isOpen_cylinder (x : Π n, E n) (n : ℕ) : IsOpen (cylinder x n) := by
  rw [PiInt.cylinder_eq_pi]
  exact isOpen_set_pi (Finset.finite_toSet _) fun a _ => isOpen_discrete _

theorem isTopologicalBasis_cylinders :
    IsTopologicalBasis {s : Set (Π n, E n) | ∃ (x : Π n, E n) (n : ℕ), s = cylinder x n} := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · rintro u ⟨x, n, rfl⟩
    apply isOpen_cylinder
  · intro x u hx u_open
    obtain ⟨v, ⟨U, F, -, rfl⟩, xU, Uu⟩ :
        ∃ v ∈ { S : Set (∀ i : ℤ, E i) | ∃ (U : ∀ i : ℤ, Set (E i)) (F : Finset ℤ),
          (∀ i : ℤ, i ∈ F → U i ∈ { s : Set (E i) | IsOpen s }) ∧ S = (F : Set ℤ).pi U },
        x ∈ v ∧ v ⊆ u :=
      (isTopologicalBasis_pi fun n : ℤ => isTopologicalBasis_opens).exists_subset_of_mem_open hx
        u_open
    rcases Finset.bddAbove (F.image Int.natAbs) with ⟨n, hn⟩
    refine ⟨cylinder x (n + 1), ⟨x, n + 1, rfl⟩, self_mem_cylinder _ _, Subset.trans ?_ Uu⟩
    intro y hy
    suffices ∀ i : ℤ, i ∈ F → y i ∈ U i by simpa
    intro i hi
    have : y i = x i := by
      have := hn (Finset.mem_image_of_mem Int.natAbs hi)
      apply mem_cylinder_iff.1 hy i (by grind) (by grind)
    rw [this]
    simp only [Set.mem_pi, Finset.mem_coe] at xU
    exact xU i hi

variable {E}

theorem isOpen_iff_dist (s : Set (Π n, E n)) :
    IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, dist x y < ε → y ∈ s := by
  constructor
  · intro hs x hx
    obtain ⟨v, ⟨y, n, rfl⟩, h'x, h's⟩ :
        ∃ v ∈ { s | ∃ (x : ∀ n : ℤ, E n) (n : ℕ), s = cylinder x n }, x ∈ v ∧ v ⊆ s :=
      (isTopologicalBasis_cylinders E).exists_subset_of_mem_open hx hs
    rw [← mem_cylinder_iff_eq.1 h'x] at h's
    refine
      ⟨(2⁻¹ : ℝ) ^ n, by simp, fun y hy => h's
        fun i hi h'i => (apply_eq_of_dist_lt hy hi.le h'i.le).symm⟩
  · intro h
    refine (isTopologicalBasis_cylinders E).isOpen_iff.2 fun x hx => ?_
    rcases h x hx with ⟨ε, εpos, hε⟩
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (2⁻¹ : ℝ) ^ n < ε := exists_pow_lt_of_lt_one εpos (by norm_num)
    refine ⟨cylinder x n, ⟨x, n, rfl⟩, self_mem_cylinder x n, fun y hy => hε y ?_⟩
    rw [PiInt.dist_comm]
    exact (mem_cylinder_iff_dist_le.1 hy).trans_lt hn

/-- Metric space structure on `Π (n : ℤ), E n` when the spaces `E n` have the discrete topology,
where the distance is given by `dist x y = (1/2)^n`, where `n` is the smallest index where `x` and
`y` differ. Not registered as a global instance by default.
Warning: this definition makes sure that the topology is defeq to the original product topology,
but it does not take care of a possible uniformity. If the `E n` have a uniform structure, then
there will be two non-defeq uniform structures on `Π n, E n`, the product one and the one coming
from the metric structure. In this case, use `metricSpaceOfDiscreteUniformity` instead. -/
protected def metricSpace : MetricSpace (Π n, E n) :=
  MetricSpace.ofDistTopology dist PiInt.dist_self PiInt.dist_comm PiInt.dist_triangle
    isOpen_iff_dist PiInt.eq_of_dist_eq_zero

/-- Metric space structure on `Π (n : ℤ), E n` when the spaces `E n` have the discrete uniformity,
where the distance is given by `dist x y = (1/2)^n`, where `n` is the smallest index where `x` and
`y` differ. Not registered as a global instance by default. -/
protected def metricSpaceOfDiscreteUniformity {E : ℤ → Type*} [∀ n, UniformSpace (E n)]
    (h : ∀ n, uniformity (E n) = 𝓟 SetRel.id) : MetricSpace (Π n, E n) :=
  haveI : ∀ n, DiscreteTopology (E n) := fun n => discreteTopology_of_discrete_uniformity (h n)
  { dist_triangle := PiInt.dist_triangle
    dist_comm := PiInt.dist_comm
    dist_self := PiInt.dist_self
    eq_of_dist_eq_zero := PiInt.eq_of_dist_eq_zero _ _
    toUniformSpace := Pi.uniformSpace _
    uniformity_dist := by
      simp only [Pi.uniformity, h, SetRel.id, comap_principal, preimage_setOf_eq]
      apply le_antisymm
      · simp only [le_iInf_iff, le_principal_iff]
        intro ε εpos
        obtain ⟨n, hn⟩ : ∃ n, (2⁻¹ : ℝ) ^ n < ε := exists_pow_lt_of_lt_one εpos (by norm_num)
        apply
          @mem_iInf_of_iInter _ _ _ _ _ (Finset.Ioo (-n : ℤ) n).finite_toSet fun i =>
            { p : (Π n : ℤ, E n) × (Π n : ℤ, E n) | p.fst i = p.snd i }
        · simp only [mem_principal, setOf_subset_setOf, imp_self, imp_true_iff]
        · rintro ⟨x, y⟩ hxy
          simp only [SetLike.coe_sort_coe, mem_iInter, mem_setOf_eq, Subtype.forall, Finset.mem_Ioo,
            and_imp] at hxy
          apply lt_of_le_of_lt _ hn
          rw [← mem_cylinder_iff_dist_le, mem_cylinder_iff]
          exact hxy
      · simp only [le_iInf_iff, le_principal_iff]
        intro n
        refine mem_iInf_of_mem (2⁻¹ ^ n.natAbs : ℝ) ?_
        refine mem_iInf_of_mem (by positivity) ?_
        simp only [mem_principal, setOf_subset_setOf, Prod.forall]
        intro x y hxy
        exact apply_eq_of_dist_lt hxy (by grind) (by grind) }

/- Not suitable for mathlib, but good for the project -/
attribute [instance] PiInt.metricSpace

protected theorem completeSpace : CompleteSpace (Π n, E n) := by
  refine Metric.complete_of_convergent_controlled_sequences (fun n => 2⁻¹ ^ n) (by simp) ?_
  intro u hu
  refine ⟨fun n => u n.natAbs n, tendsto_pi_nhds.2 fun i => ?_⟩
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.Ici_mem_atTop i.natAbs] with n hn
  apply apply_eq_of_dist_lt (hu i.natAbs _ n le_rfl hn) (by grind) (by grind)

end PiInt
