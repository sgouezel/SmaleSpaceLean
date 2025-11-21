/-
This file was edited by Aristotle.

Lean Toolchain version: leanprover/lean4:v4.20.0-rc5
Mathlib version: d62eab0cc36ea522904895389c301cf8d844fd69 (May 9, 2025)

The following was proved by Aristotle:

- lemma nonWanderingSetWithin_subset_closure (T : X → X) (A : Set X) :
    nonWanderingSetWithin T A ⊆ closure A

- lemma nonWanderingSetWithin_mono {T : X → X} {A B : Set X} (h : A ⊆ B) :
    nonWanderingSetWithin T A ⊆ nonWanderingSetWithin T B

- lemma isClosed_nonWanderingSetWithin (T : X → X) (A : Set X) :
    IsClosed (nonWanderingSetWithin T A)

- lemma periodicPts_subset_nonWanderingSetWithin (T : X → X) (A : Set X) :
    periodicPts T ∩ A ⊆ nonWanderingSetWithin T A
-/

import Mathlib


open scoped Topology

open Function

variable {X : Type*} [TopologicalSpace X]

def nonWanderingSetWithin (T : X → X) (A : Set X) : Set X :=
  {x | ∀ U ∈ 𝓝 x, ∃ y ∈ A ∩ U, ∃ n > 0, T ^[n] y ∈ U}


lemma isClosed_nonWanderingSetWithin (T : X → X) (A : Set X) :
    IsClosed (nonWanderingSetWithin T A) := by
      -- To prove that the non-wandering set is closed, we show that its complement is open.
      have h_compl_open : IsOpen {x | ∃ U ∈ 𝓝 x, ∀ y ∈ A ∩ U, ∀ n > 0, T^[n] y ∉ U} := by
        refine' isOpen_iff_mem_nhds.2 fun x hx => _;
        -- Since $U$ is a neighborhood of $x$, there exists an open set $V$ containing $x$ such that $V \subseteq U$.
        obtain ⟨V, hV_open, hV_subset⟩ : ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ hx.choose := by
          exact Exists.imp ( by tauto ) ( mem_nhds_iff.mp hx.choose_spec.1 );
        filter_upwards [ IsOpen.mem_nhds hV_open hV_subset.1 ] with y hy;
        exact ⟨ V, IsOpen.mem_nhds hV_open hy, fun z hz hz' n hn hz'' => hx.choose_spec.2 z hz ( hV_subset.2 hz' ) n hn ( hV_subset.2 hz'' ) ⟩;
      convert h_compl_open.isClosed_compl using 1
      ext x
      simp only [nonWanderingSetWithin, Set.mem_setOf_eq]
      grind

lemma periodicPts_subset_nonWanderingSetWithin (T : X → X) (A : Set X) :
    periodicPts T ∩ A ⊆ nonWanderingSetWithin T A := by
      -- If $x$ is a periodic point of $T$ and $x \in A$, then for any neighborhood $U$ of $x$, we can choose $y = x$ and $n$ such that $T^n(x) = x \in U$.
      intro x hx
      obtain ⟨hx_periodic, hx_A⟩ := hx
      have h_periodic : ∃ n > 0, T^[n] x = x := by
        -- By definition of Function.periodicPts, there exists some n > 0 such that T^[n] x = x.
        apply hx_periodic;
      -- Since $x$ is a periodic point and $x \in A$, for any neighborhood $U$ of $x$, we can choose $y = x$ and $n$ such that $T^n(x) = x \in U$.
      intro U hU
      obtain ⟨n, hn_pos, hn_periodic⟩ := h_periodic
      use x, by
        -- Since $x \in A$ and $x \in U$, we have $x \in A \cap U$.
        simp [hx_A, mem_of_mem_nhds hU], n, hn_pos, by
        -- Since $T^[n] x = x$ and $x \in U$, we have $T^[n] x \in U$.
        rw [hn_periodic]
        exact mem_of_mem_nhds hU
