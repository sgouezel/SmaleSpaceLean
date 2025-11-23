import SmaleSpace.Shadowing
import SmaleSpace.NonWandering

open scoped Uniformity Topology
open Function Set Filter Metric SetRel

variable {X : Type*} [MetricSpace X] {T' : X → X} {T : X ≃ X} {A B : Set X}
  {U V : Set (X × X)} {a b c o s u x y z : X} {ε ε' δ : ℝ} {n : ℕ}
  [CompleteSpace X]

namespace IsLocallyMaxHyperbolicSet

variable (hT : IsLocallyMaxHyperbolicSet T A)
include hT

local notation3 "δ₀" => hT.deltaZero
local notation3 "C₀" => hT.C0
local notation3 "ρ" => hT.rho
local notation3 "⁅" x ", " y "⁆" => hT.bracket x y

/-- In a locally maximal hyperbolic set, periodic points are dense in the nonwandering set. -/
theorem nonWanderingSetWithin_eq_closure_periodicPts_inter :
    nonWanderingSetWithin T A = closure (periodicPts T ∩ A) := by
  apply Subset.antisymm ?_ closure_periodicPts_inter_subset_nonWanderingSetWithin
  intro x hx
  apply Metric.mem_closure_iff.2 (fun δ δpos ↦ ?_)
  rcases hT.closing (half_pos δpos) with ⟨ε, εpos, hε⟩
  let ε' := min (ε / 2) (δ / 4)
  have : ball x ε' ∈ 𝓝 x := ball_mem_nhds _ (by positivity)
  obtain ⟨y, ⟨yA, yx⟩, n, n_pos, hn⟩ : ∃ y ∈ A ∩ ball x ε', ∃ n > 0, (⇑T)^[n] y ∈ ball x ε' :=
    hx _ this
  have I : dist (T^[n] y) y < ε := calc
    _ ≤ dist (T^[n] y) x + dist y x := dist_triangle_right _ _ _
    _ < ε' + ε' := by gcongr; exacts [hn, yx]
    _ ≤ ε / 2 + ε / 2 := by gcongr <;> apply min_le_left
    _ = ε := by ring
  obtain ⟨z, zA, yz, hz⟩ : ∃ z ∈ A, dist y z ≤ δ / 2 ∧ T^[n] z = z := hε _ _ yA I.le
  refine ⟨z, ⟨⟨n, n_pos, hz⟩, zA⟩, ?_⟩
  calc dist x z
  _ ≤ dist y x + dist y z := dist_triangle_left _ _ _
  _ ≤ ε' + δ / 2 := by gcongr; apply le_of_lt yx
  _ ≤ δ / 4 + δ / 2 := by gcongr; apply min_le_right
  _ < δ := by linarith

end IsLocallyMaxHyperbolicSet
