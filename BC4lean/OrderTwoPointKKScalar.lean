import BC4lean.OrderTwoPointKKSplit
import BC4lean.GroupUniverseParityFunctoriality
import BC4lean.UnitPointCutoff

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # The order-two point split with scalar source

`sourcePullbackEquiv` turns an equivariant `*`-isomorphism `e : A ≃⋆ₐ B` into an additive equivalence
`KK^Γ_p(B, C) ≃+ KK^Γ_p(A, C)` (pullback along `e`, inverse pullback along `e.symm`; uses
`sourcePullback_comp` and `sourcePullback_id`).

`orderTwoPointKKSplit`: for `Nat.card Γ = 2` acting on a one-point space `X`,
`KK^Γ_p(C₀(X), ℂ) ≃+ KK_p(ℂ, ℂ) × KK_p(ℂ, ℂ)`, where the right side is KK over the trivial group with
trivial actions. It is `orderTwoKKParitySplit` (the `±1` eigen parts of the non-identity element)
followed by pullback along `pointCZeroEquiv : ℂ ≃⋆ₐ C₀(X)` in each factor.
-/

noncomputable section
universe uΓ uA uB uC u
namespace BC4lean.KKTheory

open GroupUniverseParityGroup GroupUniverseParityFunctoriality

section Equiv
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {C : Type uC} [Group Γ] [Countable Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  [TopologicalSpace.SeparableSpace C]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}

omit [PartialOrder A] [StarOrderedRing A] in
theorem sourcePullback_congr (p : Bool) {f f' : A →⋆ₙₐ[ℂ] B} (h : f = f')
    (hact : ∀ k a, f (α.automorphism k a) = β.automorphism k (f a))
    (hact' : ∀ k a, f' (α.automorphism k a) = β.automorphism k (f' a))
    (x : KKParityGroup.{uΓ,uB,uC,max u (max uA (max uB uC))} p β γ) :
    sourcePullback.{uΓ,uA,uB,uC,u} p f hact x = sourcePullback.{uΓ,uA,uB,uC,u} p f' hact' x := by
  subst h; rfl

/-- An equivariant `*`-isomorphism of sources gives an additive equivalence of KK groups. -/
def sourcePullbackEquiv (p : Bool) (e : A ≃⋆ₐ[ℂ] B)
    (hact : ∀ k a, e (α.automorphism k a) = β.automorphism k (e a)) :
    KKParityGroup.{uΓ,uB,uC,max u (max uA (max uB uC))} p β γ ≃+
      KKParityGroup.{uΓ,uA,uC,max u (max uA (max uB uC))} p α γ where
  toFun := sourcePullback.{uΓ,uA,uB,uC,max u (max uA uB)} p (e : A →⋆ₙₐ[ℂ] B) hact
  invFun := sourcePullback.{uΓ,uB,uA,uC,max u (max uA uB)} p (e.symm : B →⋆ₙₐ[ℂ] A) fun k b => by
    apply EquivLike.injective e
    change e (e.symm _) = e (α.automorphism k (e.symm b))
    rw [hact, e.apply_symm_apply, e.apply_symm_apply]
  left_inv x := by
    refine (sourcePullback_comp.{uΓ,uB,uA,uB,uC,max u uA} p (e.symm : B →⋆ₙₐ[ℂ] A)
      (e : A →⋆ₙₐ[ℂ] B) _ hact x).trans ?_
    refine (sourcePullback_congr.{uΓ,uB,uB,uC,max u uA} p (f' := NonUnitalStarAlgHom.id ℂ B)
      (by ext b; exact e.apply_symm_apply b) _ (fun _ _ => rfl) x).trans ?_
    exact sourcePullback_id.{uΓ,uB,uC,max u uA} p x
  right_inv x := by
    refine (sourcePullback_comp.{uΓ,uA,uB,uA,uC,max u uB} p (e : A →⋆ₙₐ[ℂ] B)
      (e.symm : B →⋆ₙₐ[ℂ] A) hact _ x).trans ?_
    refine (sourcePullback_congr.{uΓ,uA,uA,uC,max u uB} p (f' := NonUnitalStarAlgHom.id ℂ A)
      (by ext a; exact e.symm_apply_apply a) _ (fun _ _ => rfl) x).trans ?_
    exact sourcePullback_id.{uΓ,uA,uC,max u uB} p x
  map_add' := sourcePullback_add.{uΓ,uA,uB,uC,max u (max uA uB)} p _ hact

end Equiv

section Point

open UnitPointCutoff
open scoped ZeroAtInfty ComplexOrder

variable {Γ : Type uΓ} [Group Γ] (X : Type) [TopologicalSpace X] [Subsingleton X] [MulAction Γ X]
  [ContinuousConstSMul Γ X]

/-- `C₀` of a one-point space is separable: it is the image of `ℂ` under `pointCZeroEquiv`. -/
theorem cZero_separableSpace_of_subsingleton (x : X) : TopologicalSpace.SeparableSpace C₀(X, ℂ) :=
  (pointCZeroEquiv X x).surjective.denseRange.separableSpace
    (LinearMap.continuous_of_finiteDimensional (LinearMap.mk ⟨pointCZeroEquiv X x,
      map_add (pointCZeroEquiv X x)⟩ (map_smul (pointCZeroEquiv X x)) : ℂ →ₗ[ℂ] C₀(X, ℂ)))

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
