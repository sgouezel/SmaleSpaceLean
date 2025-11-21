import Mathlib

open scoped Topology
open Function

variable {X : Type*} [TopologicalSpace X]

def nonWanderingSetWithin (T : X → X) (A : Set X) : Set X :=
  {x | ∀ U ∈ 𝓝 x, ∃ y ∈ A ∩ U, ∃ n > 0, T ^[n] y ∈ U}

lemma nonWanderingSetWithin_subset_closure (T : X → X) (A : Set X) :
    nonWanderingSetWithin T A ⊆ closure A := by
  intro x hx
  apply mem_closure_iff_nhds.2 (fun U hU ↦ ?_)
  rw [Set.inter_comm]
  rcases hx U hU with ⟨y, y_mem, -⟩
  exact ⟨y, y_mem⟩

lemma nonWanderingSetWithin_mono {T : X → X} {A B : Set X} (h : A ⊆ B) :
    nonWanderingSetWithin T A ⊆ nonWanderingSetWithin T B := by
  simp only [nonWanderingSetWithin]
  grind

lemma isClosed_nonWanderingSetWithin (T : X → X) (A : Set X) :
    IsClosed (nonWanderingSetWithin T A) := sorry

lemma periodicPts_subset_nonWanderingSetWithin (T : X → X) (A : Set X) :
    periodicPts T ∩ A ⊆ nonWanderingSetWithin T A := sorry
