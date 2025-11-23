import Mathlib

open scoped Topology
open Function Set Filter

variable {X : Type*} [TopologicalSpace X]

/-- The non-wandering set of a map `T`, within a subset `A`, is the set of points `x` for which one
can point a nearby point `y` returning close to `x`, and moreover `y` belongs to `A`.
The most classical notion is when `A = univ`, where the corresponding set is just called
the non-wandering set of `T`. The relative notion is useful in hyperbolic dynamics. -/
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

lemma isClosed_nonWanderingSetWithin :
    IsClosed (nonWanderingSetWithin T A) := by
  apply isClosed_iff_nhds.2 (fun x hx ↦ ?_)
  intro U hU
  rcases hx _ (eventually_mem_nhds_iff.2 hU) with ⟨y, hy⟩
  simp only [nonWanderingSetWithin, Set.mem_inter_iff, gt_iff_lt, Set.mem_setOf_eq] at hy
  grind

lemma periodicPts_inter_subset_nonWanderingSetWithin :
    periodicPts T ∩ A ⊆ nonWanderingSetWithin T A := by
  rintro x ⟨⟨n, npos, hn⟩, hA⟩ U hU
  refine ⟨x, ⟨hA, mem_of_mem_nhds hU⟩, n, npos, ?_⟩
  simp only [IsPeriodicPt, IsFixedPt] at hn
  rw [hn]
  exact mem_of_mem_nhds hU

lemma closure_periodicPts_inter_subset_nonWanderingSetWithin :
    closure (periodicPts T ∩ A) ⊆ nonWanderingSetWithin T A := by
  rw [← isClosed_nonWanderingSetWithin.closure_eq]
  exact closure_mono periodicPts_inter_subset_nonWanderingSetWithin

/-- If a point is nonwandering, one can find nearby points that return arbitrarily close in
arbitrarily large times. -/
lemma mem_nonWanderingSetWithin_iff_frequently_atTop [T2Space X] (hT : Continuous T) :
    x ∈ nonWanderingSetWithin T A ↔ ∀ U ∈ 𝓝 x, ∃ᶠ n in atTop, ∃ y ∈ A ∩ U, T ^[n] y ∈ U := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩; swap
  · intro U hU
    have W := h U hU
    rcases frequently_atTop.1 (h U hU) 1 with ⟨n, hn, y, y_mem, hy⟩
    grind
  /- For the nontrivial direction, we consider separately the cases where `x` is periodic or not.
  When `x` is periodic of period `n`, then `T^{Nn} x = x` so a nearby point in `A` comes back close
  to `x` at time `Nn` by continuity. -/
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
  /- Assume now that `x` is not periodic. Considering neighborhoods separating `x` and `T^n x`,
  we construct a neighborhood `U'` of `x` which does not return to itself during the first `N`
  iterates. Then any point in `U'` returning close to `x` has to do so in more than `N` iterates. -/
  push_neg at hx
  have A (n : ℕ) (hn : 0 < n) : ∃ V W, V ∈ 𝓝 x ∧ W ∈ 𝓝 (T^[n] x) ∧ Disjoint V W :=
    t2_separation_nhds (hx n hn).symm
  choose! V W hV hW hVW using A
  let U' := U ∩ (⋂ i ∈ Icc 1 N, V i) ∩ (⋂ i ∈ Icc 1 N, T^[i] ⁻¹' W i)
  have U'_mem : U' ∈ 𝓝 x := by
    apply inter_mem (inter_mem hU ?_) ?_
    · apply (biInter_mem (finite_Icc 1 N)).2 (fun n hn ↦ hV _ hn.1)
    · apply (biInter_mem (finite_Icc 1 N)).2 (fun n hn ↦ ?_)
      exact ContinuousAt.preimage_mem_nhds (by fun_prop) (hW _ hn.1)
  obtain ⟨y, ⟨yA, yU'⟩, n, n_pos, hn⟩ : ∃ y ∈ A ∩ U', ∃ n > 0, T^[n] y ∈ U' := h U' U'_mem
  refine ⟨n, ?_, y, ⟨yA, yU'.1.1⟩, hn.1.1⟩
  by_contra!
  have I : T^[n] y ∈ V n := by
    suffices U' ⊆ V n from this hn
    apply inter_subset_left.trans
    apply inter_subset_right.trans
    exact biInter_subset_of_mem (by grind)
  have J : T^[n] y ∈ W n := by
    suffices U' ⊆ T^[n]⁻¹' W n from this yU'
    apply inter_subset_right.trans
    exact biInter_subset_of_mem (by grind)
  exact disjoint_left.1 (hVW n (by grind)) I J

lemma mapsTo_nonWanderingSetWithin (hT : Continuous T) (h : MapsTo T A A) :
    MapsTo T (nonWanderingSetWithin T A) (nonWanderingSetWithin T A) := by
  intro x hx U hU
  have hxU : T⁻¹' U ∈ 𝓝 x := hT.continuousAt.preimage_mem_nhds hU
  obtain ⟨y, ⟨yA, yU⟩, n, n_pos, hn⟩ : ∃ y ∈ A ∩ T ⁻¹' U, ∃ n > 0, T^[n] y ∈ T ⁻¹' U := hx _ hxU
  refine ⟨T y, ⟨h yA, yU⟩, n, n_pos, ?_⟩
  rwa [← iterate_succ_apply, iterate_succ_apply']
