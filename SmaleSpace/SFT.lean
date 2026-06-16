/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import SmaleSpace.LocMaximal
import SmaleSpace.PiInt

/-! # Subshifts of finite type
-/

namespace SymbolicDynamics

open PiInt Set Filter Set
open scoped Topology

variable {𝓐 : Type*} -- the alphabet


/-!
# Hyperbolic structure on the full shift
-/

open scoped Classical in
/-- The bracket for the shift, where `⁅x, y⁆` coincides with `x` on negative coordinates and `y` on
positive coordinates. This gluing only makes sense if `x 0 = y 0`, notably in subshifts of finite
type. If `x 0 ≠ y 0`, we set `⁅x, y⁆ = x` as a junk value. -/
noncomputable def shiftBracket (x y : ℤ → 𝓐) (n : ℤ) : 𝓐 :=
  if x 0 = y 0 then (if n ≤ 0 then x n else y n)
  else x n

/-- The left shift on sequences indexed by `ℤ`, as an equivalence. -/
@[simps] def shift : (ℤ → 𝓐) ≃ (ℤ → 𝓐) where
  toFun x n := x (n + 1)
  invFun x n := x (n - 1)
  left_inv x := by ext; grind
  right_inv x := by ext; grind

@[simp] lemma iterate_shift_apply (x : ℤ → 𝓐) (i : ℕ) (j : ℤ) :
    shift^[i] x j = x (j + i) := by
  induction i generalizing j with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp_apply, Nat.cast_add, Nat.cast_one]
    change (shift^[n] x) (j + 1) = _
    rw [ih]
    grind

@[simp] lemma iterate_shift_symm_apply (x : ℤ → 𝓐) (i : ℕ) (j : ℤ) :
    shift.symm^[i] x j = x (j - i) := by
  induction i generalizing j with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp_apply, Nat.cast_add, Nat.cast_one]
    change (shift.symm^[n] x) (j - 1) = _
    rw [ih]
    grind

variable [TopologicalSpace 𝓐] [DiscreteTopology 𝓐]

lemma lipschitzWith_shiftBracket :
    LipschitzWith 1 (fun (p : (ℤ → 𝓐) × (ℤ → 𝓐)) ↦ shiftBracket p.1 p.2) := by
  apply LipschitzWith.of_dist_le_mul
  rintro ⟨x, y⟩ ⟨x', y'⟩
  simp only [NNReal.coe_one, one_mul, Prod.dist_eq]
  rw [dist_le_iff (le_trans (dist_nonneg)  (le_max_left _ _))]
  intro n hn
  simp only [← mem_cylinder_succ_iff_dist_lt, sup_lt_iff] at hn ⊢
  intro i hi h'i
  by_cases hineg : i ≤ 0
  · simp only [shiftBracket, hineg, ↓reduceIte, ite_self]
    exact hn.1 i hi h'i
  by_cases h0 : x 0 = y 0
  · have : x' 0 = y' 0 := by rwa [← hn.1 0, ← hn.2 0] <;> grind
    simp only [shiftBracket, h0, ↓reduceIte, hineg, this]
    exact hn.2 i hi h'i
  have : x' 0 ≠ y' 0 := by rwa [← hn.1 0, ← hn.2 0] <;> grind
  simp only [shiftBracket, h0, ↓reduceIte, this]
  exact hn.1 i hi h'i

lemma lipschitzWith_shift : LipschitzWith 2 (shift : (ℤ → 𝓐) → (ℤ → 𝓐)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_le_iff (by positivity)]
  intro n hn
  replace hn : dist x y < 2⁻¹ ^ (n + 1) := by
    rwa [pow_add, pow_one, ← div_eq_mul_inv, lt_div_iff₀ zero_lt_two, mul_comm]
  rw [← mem_cylinder_succ_iff_dist_lt] at hn ⊢
  intro i hi h'i
  exact hn _ (by grind) (by grind)

lemma lipschitzWith_shift_symm : LipschitzWith 2 (shift.symm : (ℤ → 𝓐) → (ℤ → 𝓐)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_le_iff (by positivity)]
  intro n hn
  replace hn : dist x y < 2⁻¹ ^ (n + 1) := by
    rwa [pow_add, pow_one, ← div_eq_mul_inv, lt_div_iff₀ zero_lt_two, mul_comm]
  rw [← mem_cylinder_succ_iff_dist_lt] at hn ⊢
  intro i hi h'i
  exact hn _ (by grind) (by grind)

lemma dist_shift_le {x y : ℤ → 𝓐} (h : ∀ i ≥ 0, x i = y i) :
    dist (shift x) (shift y) ≤ 2⁻¹ * dist x y := by
  rw [dist_le_iff (by positivity)]
  intro n hn
  cases n with
  | zero =>
    rw [← mem_cylinder_succ_iff_dist_lt]
    intro i hi h'i
    exact h _ (by omega)
  | succ n =>
    replace hn : dist x y < 2⁻¹ ^ n := by
      rwa [pow_succ', mul_lt_mul_iff_right₀ (by norm_num)] at hn
    rw [← mem_cylinder_succ_iff_dist_lt] at hn ⊢
    intro i hi h'i
    simp only [shift, Equiv.coe_fn_mk]
    rcases lt_or_ge (i + 1) 0 with h''i | h''i
    · apply hn _ (by omega) (by omega)
    · apply h _ h''i

lemma dist_iterate_shift_le {x y : ℤ → 𝓐} (h : ∀ i ≥ 0, x i = y i) {n : ℕ} :
    dist (shift^[n] x) (shift^[n] y) ≤ 2⁻¹ ^ n * dist x y := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp_apply]
    apply (dist_shift_le _).trans
    · rw [pow_succ', mul_assoc]
      gcongr
    · intro i hi
      simp only [iterate_shift_apply]
      apply h
      omega

lemma locStable_shift_pow {x : ℤ → 𝓐} {n : ℕ} (hn : n ≠ 0) :
    locStable shift (2⁻¹ ^ n) x = {y | ∀ i > (-n : ℤ), x i = y i} := by
  apply Subset.antisymm
  · intro y hy i hi
    rcases le_or_gt i 0 with h'i | h'i
    · have : dist x y ≤ 2⁻¹ ^ n := hy.1 0
      rw [← mem_cylinder_iff_dist_le] at this
      apply this i (by omega) (by omega)
    · lift i to ℕ using by omega
      have : dist (shift^[i] x) (shift^[i] y) ≤ 2⁻¹ ^ n := hy.1 i
      rw [← mem_cylinder_iff_dist_le] at this
      convert this 0 (by omega) (by omega) using 1 <;>
      simp
  · intro y hy
    refine ⟨fun i ↦ ?_, ?_⟩
    · rw [← mem_cylinder_iff_dist_le, mem_cylinder_iff]
      intro j hj h'j
      simp only [iterate_shift_apply]
      apply hy
      omega
    · have : Tendsto (fun n ↦ (2⁻¹ ^ n : ℝ) * dist x y) atTop (𝓝 (0 * dist x y)) := by
        apply Tendsto.mul_const
        exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      rw [zero_mul] at this
      apply squeeze_zero (fun n ↦ by positivity) (fun n ↦ ?_) this
      exact dist_iterate_shift_le (fun i hi ↦ hy _ (by omega))

lemma locStable_shift {x : ℤ → 𝓐} :
    locStable shift 2⁻¹ x = {y | ∀ i ≥ 0, x i = y i} := by
  rw [show (2⁻¹ : ℝ) = 2⁻¹ ^ 1 by simp, locStable_shift_pow one_ne_zero]
  rfl

lemma dist_shift_symm_le {x y : ℤ → 𝓐} (h : ∀ i ≤ 0, x i = y i) :
    dist (shift.symm x) (shift.symm y) ≤ 2⁻¹ * dist x y := by
  rw [dist_le_iff (by positivity)]
  intro n hn
  cases n with
  | zero =>
    rw [← mem_cylinder_succ_iff_dist_lt]
    intro i hi h'i
    exact h _ (by omega)
  | succ n =>
    replace hn : dist x y < 2⁻¹ ^ n := by
      rwa [pow_succ', mul_lt_mul_iff_right₀ (by norm_num)] at hn
    rw [← mem_cylinder_succ_iff_dist_lt] at hn ⊢
    intro i hi h'i
    simp only [shift, Equiv.coe_fn_symm_mk]
    rcases lt_or_ge 0 (i - 1) with h''i | h''i
    · apply hn _ (by omega) (by omega)
    · apply h _ h''i

lemma dist_iterate_shift_symm_le {x y : ℤ → 𝓐} (h : ∀ i ≤ 0, x i = y i) {n : ℕ} :
    dist (shift.symm^[n] x) (shift.symm^[n] y) ≤ 2⁻¹ ^ n * dist x y := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp_apply]
    apply (dist_shift_symm_le _).trans
    · rw [pow_succ', mul_assoc]
      gcongr
    · intro i hi
      simp only [iterate_shift_symm_apply]
      apply h
      omega

lemma locUnstable_shift_pow {x : ℤ → 𝓐} {n : ℕ} (hn : n ≠ 0) :
    locUnstable shift (2⁻¹ ^ n) x = {y | ∀ i < (n : ℤ), x i = y i} := by
  apply Subset.antisymm
  · intro y hy i hi
    rcases le_or_gt 0 i with h'i | h'i
    · have : dist x y ≤ 2⁻¹ ^ n := hy.1 0
      rw [← mem_cylinder_iff_dist_le] at this
      apply this i (by omega) (by omega)
    · obtain ⟨j, rfl⟩ : ∃ (j : ℕ), i = -j := ⟨i.natAbs, by omega⟩
      have : dist (shift.symm^[j] x) (shift.symm^[j] y) ≤ 2⁻¹ ^ n := hy.1 j
      rw [← mem_cylinder_iff_dist_le] at this
      convert this 0 (by omega) (by omega) using 1 <;>
      simp
  · intro y hy
    refine ⟨fun i ↦ ?_, ?_⟩
    · rw [← mem_cylinder_iff_dist_le, mem_cylinder_iff]
      intro j hj h'j
      simp only [iterate_shift_symm_apply]
      apply hy
      omega
    · have : Tendsto (fun n ↦ (2⁻¹ ^ n : ℝ) * dist x y) atTop (𝓝 (0 * dist x y)) := by
        apply Tendsto.mul_const
        exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      rw [zero_mul] at this
      apply squeeze_zero (fun n ↦ by positivity) (fun n ↦ ?_) this
      exact dist_iterate_shift_symm_le (fun i hi ↦ hy _ (by omega))

lemma locUnstable_shift {x : ℤ → 𝓐} :
    locUnstable shift 2⁻¹ x = {y | ∀ i ≤ 0, x i = y i} := by
  rw [show (2⁻¹ : ℝ) = 2⁻¹ ^ 1 by simp, locUnstable_shift_pow one_ne_zero]
  grind

lemma shiftBracket_eq_locUnstable_inter_locStable {x y : ℤ → 𝓐} (h : dist x y ≤ 2⁻¹) :
    {shiftBracket x y} = locUnstable shift 2⁻¹ x ∩ locStable shift 2⁻¹ y := by
  have A : x 0 = y 0 := by
    rw [show (2⁻¹ : ℝ) = 2⁻¹ ^ 1 by simp, ← mem_cylinder_iff_dist_le] at h
    exact h _ (by norm_num) (by norm_num)
  rw [locStable_shift, locUnstable_shift]
  apply Subset.antisymm
  · simp only [ge_iff_le, subset_inter_iff, singleton_subset_iff, mem_setOf_eq, shiftBracket, A,
      ↓reduceIte, left_eq_ite_iff, not_le, right_eq_ite_iff]
    grind
  · simp only [ge_iff_le, subset_singleton_iff, mem_inter_iff, mem_setOf_eq, and_imp]
    intro z hz h'z
    ext i
    simp only [shiftBracket, A, ↓reduceIte]
    grind

/-- The full shift is a hyperbolic map. -/
@[simps!] noncomputable def isLocallyMaxHyperbolicSetShift :
    IsLocallyMaxHyperbolicSet (shift : (ℤ → 𝓐) ≃ (ℤ → 𝓐)) univ where
  rho := 2⁻¹
  deltaZero := 2⁻¹
  bracket := shiftBracket
  isClosed := isClosed_univ
  uniformContinuous := lipschitzWith_shift.uniformContinuous
  uniformContinuous_symm := lipschitzWith_shift_symm.uniformContinuous
  uniformContinuousOn_bracket := lipschitzWith_shiftBracket.uniformContinuous.uniformContinuousOn
  rho_pos := by norm_num
  rho_lt_one := by norm_num
  deltaZero_pos := by norm_num
  C0 := 1
  one_le_C0 := le_rfl
  dist_iterate_le ho hx hy n := by
    simpa using dist_iterate_shift_le (fun i hi ↦ by grind [locStable_shift])
  dist_iterate_symm_le ho hx hy n := by
    simpa using dist_iterate_shift_symm_le (fun i hi ↦ by grind [locUnstable_shift])
  bracket_mem hx hy := mem_univ _
  bracket_self {x} := by ext; simp [shiftBracket]
  mapsTo := mapsTo_univ _ _
  mapsTo_symm := mapsTo_univ _ _
  exists_bracket_eq_inter :=
    ⟨2⁻¹, by norm_num, fun {x y} hx hy h ↦ shiftBracket_eq_locUnstable_inter_locStable h⟩

/-!
# Subshifts of finite type

For a finite alphabet `𝓐`, and a subset `G` of `𝓐×𝓐`, consider the set of
sequences `x : ℤ → 𝓐` with `(x n, x (n+1)) ∈ G` for all `n`. It is endowed with the product
topology. We think of `G` as the edges of a directed graph with vertex set `𝓐`, so `SFT G` consists
in bi-infinite paths in this graph.
-/
/-- The subshift of finite type associated to an incidence matrix `G`. -/
def SFT (G : Set (𝓐 × 𝓐)) : Set (ℤ → 𝓐) := {x : ℤ → 𝓐 | ∀ n, (x n, x (n + 1)) ∈ G}

variable {G : Set (𝓐 × 𝓐)}

/-- A subshift of finite type is a locally maximal hyperbolic set. -/
noncomputable def isLocallyMaxHyperbolicSetSFT :
    IsLocallyMaxHyperbolicSet shift (SFT G) := by
  apply isLocallyMaxHyperbolicSetShift.mono _ (subset_univ _)
  · suffices IsClosed (⋂ n, {x : ℤ → 𝓐 | (x n, x (n + 1)) ∈ G}) by
      convert! this
      ext x
      simp [SFT]
    exact isClosed_iInter (fun n ↦ (isClosed_discrete G).preimage (by fun_prop))
  · intro x hx n
    simpa using hx (n + 1)
  · intro x hx n
    simpa using hx (n - 1)
  · intro x y hx hy n
    simp only [isLocallyMaxHyperbolicSetShift_bracket, shiftBracket]
    by_cases h : x 0 = y 0; swap
    · simpa [h] using hx n
    simp only [h, ↓reduceIte]
    rcases lt_trichotomy n 0 with hn | rfl | hn
    · convert hx n <;> grind
    · simpa [h] using hy 0
    · convert hy n <;> grind

end SymbolicDynamics
