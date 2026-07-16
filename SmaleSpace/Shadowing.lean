/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import SmaleSpace.LocMaximal

/-! # The shadowing and closing lemmas for hyperbolic dynamics -/

open scoped Uniformity Topology
open Function Set Filter Metric SetRel

variable {X : Type*} [MetricSpace X] {T' : X → X} {T : X ≃ X} {A B : Set X}
  {U V : Set (X × X)} {a b c o s u x y z : X} {ε ε' δ : ℝ} {n : ℕ}
  [CompleteSpace X]

namespace IsExtLocallyMaxHyperbolicSet

variable {A : Set X} (hT : IsExtLocallyMaxHyperbolicSet T A)
include hT

local notation3 "δ₀" => hT.deltaZero
local notation3 "C₀" => hT.C0
local notation3 "ρ" => hT.rho
local notation3 "⁅" x ", " y "⁆" => hT.bracket x y
local notation3 "δ₁" => hT.reduceScale δ₀
local notation3 "δ₂" => hT.reduceScale δ₁

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
    {M : ℕ} (hM : 2 * C₀ * ρ ^ M * δ ≤ hT.reduceScale δ)
    (hε : ∀ (u : ℕ → X), (∀ n, dist (T (u n)) (u (n + 1)) ≤ ε) →
      ∀ i ≤ M, dist (T^[i] (u 0)) (u i) ≤ hT.reduceScale δ / 2) :
    ∃ p ∈ locUnstable T δ (x 0) ∩ A, ∀ n, dist (x n) (T ^[n] p) ≤ 4 * δ := by
  -- Start by recording useful basic facts
  have : Nonempty X := ⟨x 0⟩
  have := hT.one_le_C0
  have : 0 ≤ C₀ := by linarith
  have := hT.rho_pos
  have := hT.continuous
  have rhoM : C₀ * ρ ^ M ≤ 2⁻¹ := by
    have W := hM.trans hT.reduceScale_le_half_self
    field_simp at W
    linarith
  have : M ≠ 0 := by
    intro h
    simp only [h, pow_zero] at rhoM
    norm_num at rhoM
    linarith
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
    have : dist (T^[M] (x (M * n))) (T^[M] (y n)) ≤ C₀ * ρ ^ M * δ :=
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
  have Z i n : z i (n + 1) ∈ locUnstable T (C₀ * ρ ^ (M * (n + 1)) * δ) (z i n) := by
    convert! hT.iterate_symm_mem_locUnstable_mul (hT.mapsTo.iterate _ (B _).2) h'δ (C (i + n))
      (n := M * (n + 1)) using 2
    rw [mul_add, iterate_add_apply, mul_one, L]
  have Z' i n : z i (n + 1) ∈ locUnstable T (2⁻¹ ^ (n + 1) * δ) (z i n) := by
    apply locUnstable_mono _ (Z i n)
    rw [pow_mul]
    gcongr
    calc C₀ * (ρ ^ M) ^ (n + 1)
    _ ≤ C₀ ^ (n + 1) * (ρ ^ M) ^ (n + 1) := by
      gcongr; exact le_self_pow₀ hT.one_le_C0 (by grind)
    _ = (C₀ * ρ ^ M) ^ (n + 1) := by ring
    _ ≤ 2⁻¹ ^ (n + 1) := by gcongr
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
    {M : ℕ} (hM : 2 * C₀ * ρ ^ M * δ ≤ hT.reduceScale δ)
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
  have B n : dist (p n) (p (n + 1)) ≤ C₀ * ρ ^ n * (2 * δ₁) := by
    apply hT.expansive_finite_time (hpA _) (hpA _) (fun i hi ↦ ?_) (fun i hi ↦ ?_)
    · apply (dist_triangle_left _ _ (x i)).trans
      linarith [hp n i, hp (n + 1) i]
    · apply (dist_triangle_left _ _ (x (-i))).trans
      linarith [h'p n i hi , h'p (n + 1) i (by omega)]
  have : CauchySeq p := by
    apply cauchySeq_of_le_geometric (ρ) (C₀ * 2 * δ₁) hT.rho_lt_one (fun n ↦ ?_)
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
    {M : ℕ} (hM : 2 * C₀ * ρ ^ M * δ ≤ hT.reduceScale δ)
    (hε : ∀ (u : ℕ → X), (∀ n, dist (T (u n)) (u (n + 1)) ≤ ε) →
      ∀ i ≤ M, dist (T^[i] (u 0)) (u i) ≤ hT.reduceScale δ / 2) :
    ∃ p ∈ A, ∀ (n : ℤ), dist (x n) ((T ^ n) p) ≤ 4 * δ := by
  rcases hT.shadowing_precise hδ h''δ x hx h'x hM hε with ⟨p, hpA, hp⟩
  refine ⟨p, hpA, fun n ↦ ?_⟩
  rcases Int.natAbs_eq n with hn | hn <;> set i := n.natAbs <;> rw [hn]
  · apply (hp i).1
  · convert (hp i).2
    simp only [Equiv.Perm.iterate_eq_pow, zpow_neg, zpow_natCast]
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
theorem shadowing (hT : IsLocallyMaxHyperbolicSet T A) (hδ : 0 < δ) :
    ∃ ε > 0, ∀ (x : ℤ → X), (∀ n, dist (T (x n)) (x (n + 1)) ≤ ε) → (∀ n, x n ∈ A) →
      ∃ p ∈ A, ∀ n, dist (x n) ((T ^ n) p) ≤ δ := by
  let hT' := hT.extend
  let δ₂ := hT'.reduceScale (hT'.reduceScale hT'.deltaZero)
  let ρ := hT'.rho
  let δ' := min (δ / 4) (δ₂ / 8)
  have : δ' ≤ δ / 4 := min_le_left _ _
  have δ'_pos : 0 < δ' := by simpa [δ', hδ] using hT'.deltaTwo_pos
  obtain ⟨M, hM⟩ : ∃ M, 2 * hT'.C0 * ρ ^ M * δ' < hT'.reduceScale δ' := by
    have : Tendsto (fun n ↦ 2 * hT'.C0 * ρ ^ n * δ') atTop (𝓝 (2 * hT'.C0 * 0 * δ')) :=
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

/-- If an orbit comes back close enough to its starting point, then it is close to a
periodic orbit. -/
theorem closing (hT : IsLocallyMaxHyperbolicSet T A) (hδ : 0 < δ) :
    ∃ ε > 0, ∀ (x : X) (n : ℕ), x ∈ A → dist (T^[n] x) x ≤ ε →
      ∃ y ∈ A, dist x y ≤ δ ∧ T^[n] y = y := by
  /- Form a pseudo-orbit `..., x, T x, ..., T^{n-1} x, x, T x, ...`. If `T ^ n x` is close to `x`,
  this is indeed a pseudo-orbit, shadowed by a (unique) genuine orbit. As the pseudo-orbit is
  periodic, the genuine orbit also is, by uniqueness. -/
  rcases hT.expansive with ⟨δ₁, δ₁_pos, hδ₁⟩
  let δ' := min δ (δ₁ / 2)
  have δ'_pos : 0 < δ' := by positivity
  rcases hT.shadowing δ'_pos with ⟨ε, ε_pos, hε⟩
  refine ⟨ε, ε_pos, fun x n hx h'x ↦ ?_⟩
  rcases eq_or_ne n 0 with rfl | hn
  · exact ⟨x, hx, by simp [hδ.le], by simp⟩
  let u (k : ℤ) := T^[(k % n).toNat] x
  have D (k : ℤ) : dist (T (u k)) (u (k + 1)) ≤ ε := by
    rcases eq_or_ne n 1 with rfl | h'n
    · simpa [u] using h'x
    have one_mod : (1 : ℤ) % n = 1 := Int.emod_eq_of_lt zero_le_one (by omega)
    by_cases h : k % n = n - 1
    · have : (k + 1) % n = 0 := by rw [Int.add_emod, h, one_mod]; simp
      simp only [this, Int.pred_toNat, Int.toNat_natCast, h, Int.toNat_zero, ge_iff_le, u,
        ← iterate_succ_apply' T]
      convert! h'x
      omega
    · have I : 0 ≤ k % n := Int.emod_nonneg k (by omega)
      have : (k + 1) % n = k % n + 1 := by
        rw [Int.add_emod, one_mod]
        apply Int.emod_eq_of_lt (by positivity)
        have : k % n < n := Int.emod_lt_of_pos _ (by omega)
        omega
      simp only [this, Int.toNat_add I zero_le_one, Int.toNat_one, u, iterate_succ_apply',
        dist_self, ε_pos.le]
  obtain ⟨y, yA, hy⟩ : ∃ y ∈ A, ∀ (n : ℤ), dist (u n) ((T ^ n) y) ≤ δ' :=
    hε u D (fun n ↦ hT.mapsTo.iterate _ hx)
  refine ⟨y, yA, (hy 0).trans (min_le_left _ _), ?_⟩
  apply hδ₁ _ (hT.mapsTo.iterate _ yA) _ yA (fun k ↦ ?_)
  calc dist ((T ^ k) (T^[n] y)) ((T ^ k) y)
  _ = dist ((T ^ (k + n)) y) ((T ^ k) y) := by
    simp only [zpow_add, zpow_natCast, Equiv.Perm.coe_mul, comp_apply]; rfl
  _ ≤ dist (u k) ((T ^ (k + n)) y) + dist (u k) ((T ^ k) y) := dist_triangle_left _ _ _
  _ = dist (u (k + n)) ((T ^ (k + n)) y) + dist (u k) ((T ^ k) y) := by simp [u]
  _ ≤ δ₁ / 2 + δ₁ / 2 := by gcongr <;> exact (hy _).trans (min_le_right _ _)
  _ = δ₁ := by ring

end IsLocallyMaxHyperbolicSet
