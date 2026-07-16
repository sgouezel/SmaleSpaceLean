/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import SmaleSpace.Shadowing
import SmaleSpace.NonWandering

/-! # The spectral decomposition of a hyperbolic dynamical system -/

open scoped Uniformity Topology
open Function Set Filter Metric SetRel

/-- In a locally maximal hyperbolic set, periodic points are dense in
-- the nonwandering set. -/
theorem nonWanderingSetWithin_eq_closure_periodicPts_inter
    {X : Type*} [MetricSpace X] [CompleteSpace X] {T : X ≃ X} {A : Set X}
    (hT : IsLocallyMaxHyperbolicSet T A) :
    nonWanderingSetWithin T A = closure (periodicPts T ∩ A) := by
  apply Subset.antisymm ?_ closure_periodicPts_inter_subset_nonWanderingSetWithin
  -- fix some nonwandering point `x` in `A`
  intro x hx
  -- we need to find a periodic point in `A` close to `x`, say `δ`-close.
  apply Metric.mem_closure_iff.2 (fun δ δpos ↦ ?_)
  -- the closing lemma gives some `ε` such that, if two points are `ε`-close, then one can
  -- close the orbit making an error at most `δ / 2`.
  rcases hT.closing (half_pos δpos) with ⟨ε, εpos, hε⟩
  let ε' := min (ε / 2) (δ / 4)
  have : ball x ε' ∈ 𝓝 x := ball_mem_nhds _ (by positivity)
  -- as `x` is non-wandering, we may find `y` very close to `x` that comes back very close to `x`
  obtain ⟨y, ⟨yA, yx⟩, n, n_pos, hn⟩ : ∃ y ∈ A ∩ ball x ε', ∃ n > 0, T^[n] y ∈ ball x ε' :=
    hx _ this
  -- by construction, `y` comes back close to itself
  have I : dist (T^[n] y) y < ε := calc
    _ ≤ dist (T^[n] y) x + dist y x := dist_triangle_right _ _ _
    _ < ε' + ε' := by gcongr; exacts [hn, yx]
    _ ≤ ε / 2 + ε / 2 := by gcongr <;> apply min_le_left
    _ = ε := by ring
  -- by the closing lemma, we get a periodic point close to `y`
  obtain ⟨z, zA, yz, hz⟩ : ∃ z ∈ A, dist y z ≤ δ / 2 ∧ T^[n] z = z := hε _ _ yA I.le
  -- this periodic point is also `δ`-close to `x`, by construction
  refine ⟨z, ⟨⟨n, n_pos, hz⟩, zA⟩, ?_⟩
  calc dist x z
  _ ≤ dist y x + dist y z := dist_triangle_left _ _ _
  _ ≤ ε' + δ / 2 := by gcongr; apply le_of_lt yx
  _ ≤ δ / 4 + δ / 2 := by gcongr; apply min_le_right
  _ < δ := by linarith
