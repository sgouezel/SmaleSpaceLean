import Mathlib

open scoped Topology
open Function Set Filter

variable {X : Type*} [TopologicalSpace X]

def nonWanderingSetWithin (T : X → X) (A : Set X) : Set X :=
  {x | ∀ U ∈ 𝓝 x, ∃ y ∈ A ∩ U, ∃ n > 0, T ^[n] y ∈ U}

variable {T : X → X} {A B : Set X} {x : X}

lemma nonWanderingSetWithin_subset_closure :
    nonWanderingSetWithin T A ⊆ closure A := by
  intro x hx
  apply mem_closure_iff_nhds.2 (fun U hU ↦ ?_)
  rw [Set.inter_comm]
  rcases hx U hU with ⟨y, y_mem, -⟩
  exact ⟨y, y_mem⟩

lemma nonWanderingSetWithin_mono (h : A ⊆ B) :
    nonWanderingSetWithin T A ⊆ nonWanderingSetWithin T B := by
  simp only [nonWanderingSetWithin]
  grind

@[simp]
lemma nonWonderingSetWithin_empty : nonWanderingSetWithin T ∅ = ∅ := by
  ext x
  simp only [nonWanderingSetWithin, Set.empty_inter, Set.mem_empty_iff_false, gt_iff_lt, false_and,
    exists_false, imp_false, Set.mem_setOf_eq, iff_false, not_forall, not_not]
  exact ⟨univ, by simp⟩

lemma isClosed_nonWanderingSetWithin (T : X → X) (A : Set X) :
    IsClosed (nonWanderingSetWithin T A) := by
  apply isClosed_iff_nhds.2 (fun x hx ↦ ?_)
  intro U hU
  rcases hx _ (eventually_mem_nhds_iff.2 hU) with ⟨y, hy⟩
  simp only [nonWanderingSetWithin, Set.mem_inter_iff, gt_iff_lt, Set.mem_setOf_eq] at hy
  grind

lemma periodicPts_subset_nonWanderingSetWithin :
    periodicPts T ∩ A ⊆ nonWanderingSetWithin T A := by
  rintro x ⟨⟨n, npos, hn⟩, hA⟩ U hU
  refine ⟨x, ⟨hA, mem_of_mem_nhds hU⟩, n, npos, ?_⟩
  simp only [IsPeriodicPt, IsFixedPt] at hn
  rw [hn]
  exact mem_of_mem_nhds hU

lemma mem_nonWanderingSetWithin_iff_frequently_atTop (hT : Continuous T) :
    x ∈ nonWanderingSetWithin T A ↔ ∀ U ∈ 𝓝 x, ∃ᶠ n in atTop, ∃ y ∈ A ∩ U, T ^[n] y ∈ U := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩; swap
  · intro U hU
    have W := h U hU
    rcases frequently_atTop.1 (h U hU) 1 with ⟨n, hn, y, y_mem, hy⟩
    grind
  intro U hU
  apply frequently_atTop.2 (fun N ↦ ?_)
  by_cases hx : ∃ n > 0, T ^[n] x = x
  · rcases hx with ⟨n, n_pos, hn⟩
    refine ⟨N * n, le_mul_of_one_le_right (by simp) (by grind), ?_⟩
    have : U ∩ T^[N * n] ⁻¹' U ∈ 𝓝 x := by
      apply inter_mem hU
      apply ContinuousAt.preimage_mem_nhds (by fun_prop)
      have : T ^[N * n] x = x := by
        have : IsPeriodicPt T n x := hn
        exact this.const_mul N
      rwa [this]
    rcases h _ this with ⟨y, y_mem, -⟩
    grind
  push_neg at hx
