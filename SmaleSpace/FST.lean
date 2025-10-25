import SmaleSpace.Obsolete.Bracket
import SmaleSpace.Obsolete.HyperbolicMap

namespace SFT

variable {𝓐 : Type*} -- the alphabet

/-!
# Subshifts of finite type

For a finite alphabet `𝓐`, and a subset `G` of `𝓐×𝓐`, consider the subtype of maps `x : ℤ → 𝓐`
with `(x n,x (n+1)) ∈ G` for all `n`. It is endowed with the product topology. We think of `G`
as the edges of a directed graph with vertex set `𝓐`, so `FST G` consists in bi-infinite
paths in this graph.
-/

/-- The subshift of finite type associated to an incidence matrix `G`. -/
def FST (G : Set (𝓐 × 𝓐)) := { x : ℤ → 𝓐 // ∀ n, (x n, x (n+1)) ∈ G }

variable {G : Set (𝓐 × 𝓐)}
-- DecidableEq needed, otherwise "if x = y" doesn't compile

instance : CoeFun (FST G) (fun _ => ℤ → 𝓐) where
  coe f := f.val

/-- The largest `n` such that `x` and `y` coincide at all their coordinates bounded by `n` in
absolute value. -/
noncomputable def common_match (x y : ℤ → 𝓐) := sSup { n : ℕ | ∀ k, -(n:ℤ) ≤ k → k ≤ n → x k = y k }

open scoped Classical in
noncomputable instance : MetricSpace (FST G) where
  dist := fun x y ↦ if x = y then 0 else 2^(-(common_match x y):ℝ)
  dist_self := sorry
  dist_comm := sorry
  dist_triangle := sorry
  edist_dist := sorry
  uniformity_dist := sorry
  cobounded_sets := sorry
  eq_of_dist_eq_zero := sorry

open scoped Classical in
noncomputable instance : SmaleSpace.HasRuelleBracketWithMap (FST G) where
  toFun := fun x y ↦ if x 0 = y 0 then ⟨fun n ↦ if n<0 then x n else y n,sorry⟩ else x
  deltaZero := 1/2
  deltaZero_pos := by bound
  unifCont := sorry
  refl := by
    intro x
    simp only [↓reduceIte, ite_self, Subtype.coe_eta]
  bracket_left' := sorry
  bracket_right' := sorry
  mapT := ⟨fun x ↦ ⟨fun n ↦ x (n+1),sorry⟩,fun x ↦ ⟨fun n ↦ x (n-1),sorry⟩,sorry,sorry⟩
  unifCont_T := sorry
  unifCont_Tsymm := sorry
  lambda := 1/2
  lambda_pos := by bound
  lambda_lt_one := by bound
  bracket_image := sorry
  expansion := sorry
  contraction := sorry

end SFT
