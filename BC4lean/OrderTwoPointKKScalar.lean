import BC4lean.OrderTwoPointKKSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # The order-two point split with scalar source

`orderTwoPointKKSplit`: for `Nat.card Γ = 2` acting on a one-point space `X`,
`KK^Γ_p(C₀(X), ℂ) ≃+ KK_p(ℂ, ℂ) × KK_p(ℂ, ℂ)`, where the right side is KK over the trivial group with
trivial actions. It is `orderTwoKKParitySplit` (the `±1` eigen parts of the non-identity element)
followed by pullback along `pointCZeroEquiv : ℂ ≃⋆ₐ C₀(X)` in each factor.
-/

noncomputable section
universe uΓ uA uB uC u
namespace BC4lean.KKTheory

open GroupUniverseParityGroup GroupUniverseParityFunctoriality

section Point

open UnitPointCutoff
open scoped ZeroAtInfty ComplexOrder

variable {Γ : Type uΓ} [Group Γ] (X : Type) [TopologicalSpace X] [Subsingleton X] [MulAction Γ X]
  [ContinuousConstSMul Γ X]

variable (h2 : Nat.card Γ = 2)

/-- For a group `Γ` of order two acting on a point, `KK^Γ_p(C₀(pt), ℂ) ≅ KK_p(ℂ, ℂ) ⊕ KK_p(ℂ, ℂ)`:
split into the `±1` eigen parts (`orderTwoKKParitySplit`), then pull back along `ℂ ≅ C₀(pt)`. -/
def orderTwoPointKKSplit (x : X) (p : Bool) :
    letI := cZero_separableSpace_of_subsingleton X x
    KKParityGroup.{uΓ, 0, 0, u} p (CZero.action Γ (X := X))
        (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) ≃+
      KKParityGroup.{0, 0, 0, u} p (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
          (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ) ×
        KKParityGroup.{0, 0, 0, u} p (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
          (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ) :=
  letI := cZero_separableSpace_of_subsingleton X x
  let e := sourcePullbackEquiv.{0, 0, 0, 0, u}
    (α := (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ))
    (β := (CStarAlgebraAction.trivial : CStarAlgebraAction Unit C₀(X, ℂ)))
    (γ := (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)) p
    (pointCZeroEquiv X x) (fun _ _ => by simp [CStarAlgebraAction.trivial])
  (orderTwoKKParitySplit h2 p).trans (e.prodCongr e)

end Point

end BC4lean.KKTheory
