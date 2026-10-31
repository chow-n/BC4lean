import BC4lean.GreenJulgPointLeft
import BC4lean.FiniteGroupPointCalibration
import BC4lean.ReducedScalarKKComparison
import BC4lean.BaumConnesProperty
import BC4lean.NonunitalOperatorK
import BC4lean.GroupUniverseParityUnits

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # The Baum–Connes property for every finite group

Let `Γ` be a finite group with the discrete topology, `Cr = ℂ ⋊_r Γ`, and let
`Ψ_p : KK^Γ_p(C₀(pt), ℂ) → KK_p(ℂ, Cr)` be descent followed by the cutoff product
(`GreenJulgPoint.pointGreenJulgHom`). Julg's inverse `L_p y = ev^*(infl y · [ℓ²Γ])`
(`GreenJulgCorrespondence.greenJulgInverse`) satisfies

* `Ψ_p ∘ L_p = id` (`pointGreenJulgHom_greenJulgInverse`, in `GreenJulgPoint`), and
* `L_p ∘ Ψ_p = id` (`greenJulgInverse_pointGreenJulgHom`, in `GreenJulgPointLeft`),

in both parities. This file assembles these into the point Green–Julg isomorphism
`greenJulgPointEquiv` and deduces the coefficient-free reduced Baum–Connes property for every finite
group (`baumConnesProperty_of_finite`).

The deduction is a reduction proved once for all finite groups. By
`reducedAssemblyHom_finitePoint_formula`, the canonical reduced assembly map factors as
`μ_p = κ_p ∘ Ψ_p ∘ φ_p`, where `φ_p` is the additive equivalence of the topological side with the
point model (`finiteTopologicalPointSpaceEquiv`) and `κ_p : KK_p(ℂ, Cr) → K_p(C*_r Γ)` is the
analytic comparison (`Assembly.reducedScalarKKToAnalyticHom`). The comparison `κ_p` is bijective for
every countable group (`reducedScalarKKToAnalyticHom_bijective`): it is a composite of additive
equivalences and of `K_p` of the `*`-isomorphism `ℂ ⋊_r Γ ≅ C*_r Γ`. So `μ_p` is bijective as soon
as `Ψ_p` is. -/

noncomputable section

/-! ## `K_p` of a `*`-isomorphism -/

namespace BC4lean.OperatorKTheory

/-- `operatorK0Map` along a `*`-isomorphism is bijective. -/
theorem operatorK0Map_bijective {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (e : A ≃⋆ₐ[ℂ] B) : Function.Bijective (operatorK0Map e.toNonUnitalStarAlgHom) := by
  have h1 : e.symm.toNonUnitalStarAlgHom.comp e.toNonUnitalStarAlgHom = NonUnitalStarAlgHom.id ℂ A := by
    ext a; exact e.symm_apply_apply a
  have h2 : e.toNonUnitalStarAlgHom.comp e.symm.toNonUnitalStarAlgHom = NonUnitalStarAlgHom.id ℂ B := by
    ext a; exact e.apply_symm_apply a
  refine ⟨Function.LeftInverse.injective (g := operatorK0Map e.symm.toNonUnitalStarAlgHom) ?_,
    Function.RightInverse.surjective (g := operatorK0Map e.symm.toNonUnitalStarAlgHom) ?_⟩
  · intro x
    rw [← AddMonoidHom.comp_apply, ← operatorK0Map_comp, h1, operatorK0Map_id]; rfl
  · intro x
    rw [← AddMonoidHom.comp_apply, ← operatorK0Map_comp, h2, operatorK0Map_id]; rfl

/-- `operatorK1Map` along a `*`-isomorphism is bijective. -/
theorem operatorK1Map_bijective {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (e : A ≃⋆ₐ[ℂ] B) : Function.Bijective (operatorK1Map e.toNonUnitalStarAlgHom) := by
  have h1 : e.symm.toNonUnitalStarAlgHom.comp e.toNonUnitalStarAlgHom = NonUnitalStarAlgHom.id ℂ A := by
    ext a; exact e.symm_apply_apply a
  have h2 : e.toNonUnitalStarAlgHom.comp e.symm.toNonUnitalStarAlgHom = NonUnitalStarAlgHom.id ℂ B := by
    ext a; exact e.apply_symm_apply a
  refine ⟨Function.LeftInverse.injective (g := operatorK1Map e.symm.toNonUnitalStarAlgHom) ?_,
    Function.RightInverse.surjective (g := operatorK1Map e.symm.toNonUnitalStarAlgHom) ?_⟩
  · intro x
    rw [← AddMonoidHom.comp_apply, ← operatorK1Map_comp, h1, operatorK1Map_id]; rfl
  · intro x
    rw [← AddMonoidHom.comp_apply, ← operatorK1Map_comp, h2, operatorK1Map_id]; rfl

end BC4lean.OperatorKTheory

/-! ## The point Green–Julg isomorphism -/

namespace BC4lean.KKTheory.GreenJulgPoint
open BC4lean.Chapter8Examples KKTheory.GroupUniverseParityGroup KKTheory.GreenJulgCorrespondence
open scoped ZeroAtInfty ComplexOrder KasparovDescent

variable (Γ : Type) [Group Γ] [Countable Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [Finite Γ]

/-- `Ψ_p` is bijective in both parities. -/
theorem pointGreenJulgHom_bijective (p : Bool) : Function.Bijective (pointGreenJulgHom Γ p) :=
  ⟨pointGreenJulgHom_injective Γ p, pointGreenJulgHom_surjective Γ p⟩

/-- **The point Green–Julg isomorphism** `KK^Γ_p(C₀(pt), ℂ) ≃+ KK_p(ℂ, ℂ ⋊_r Γ)` for a finite
group `Γ`, in both parities: the map is `Ψ_p` (descent, then the cutoff product) and the inverse is
Julg's `L_p y = ev^*(infl y · [ℓ²Γ])`. -/
def greenJulgPointEquiv (p : Bool) :
    KKParityGroup.{0, 0, 0, 0} p (CZero.action Γ (X := FiniteGroupPoint.{0}))
        (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) ≃+
      KKParityGroup.{0, 0, 0, 0} p (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ) (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (Cr Γ))
    where
  toFun := pointGreenJulgHom Γ p
  invFun := greenJulgInverse Γ p
  left_inv := greenJulgInverse_pointGreenJulgHom Γ p
  right_inv := pointGreenJulgHom_greenJulgInverse Γ p
  map_add' := (pointGreenJulgHom Γ p).map_add

@[simp]
theorem greenJulgPointEquiv_apply (p : Bool)
    (x : KKParityGroup.{0, 0, 0, 0} p (CZero.action Γ (X := FiniteGroupPoint.{0}))
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)) :
    greenJulgPointEquiv Γ p x = pointGreenJulgHom Γ p x := rfl

@[simp]
theorem greenJulgPointEquiv_symm_apply (p : Bool)
    (y : KKParityGroup.{0, 0, 0, 0} p (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (Cr Γ))) :
    (greenJulgPointEquiv Γ p).symm y = greenJulgInverse Γ p y := rfl

end BC4lean.KKTheory.GreenJulgPoint

/-! ## The reduction and the theorem -/

namespace BC4lean.Chapter8Examples
open KKTheory OperatorKTheory KKTheory.GroupUniverseParityGroup KKTheory.GreenJulgPoint
open scoped ZeroAtInfty ComplexOrder KasparovDescent

section Comparison
variable (Γ : Type) [Group Γ] [Countable Γ]

/-- The analytic comparison `KK_p(ℂ, ℂ ⋊_r Γ) → K_p(C*_r Γ)` is bijective for every countable
group: it is a composite of additive equivalences and of `K_p` of a `*`-isomorphism. -/
theorem reducedScalarKKToAnalyticHom_bijective (p : Bool) :
    Function.Bijective (Assembly.reducedScalarKKToAnalyticHom.{0, 0} Γ p) := by
  let : PartialOrder (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrderedRing _
  cases p
  · exact (operatorK0UnitalEquiv (ReducedGroupCStar Γ)).bijective.comp
      ((operatorK0Map_bijective (reducedCrossedScalarProductEquiv (Γ := Γ))).comp
        scalarKKOperatorK0AddEquiv.bijective)
  · exact (operatorK1UnitalEquiv (ReducedGroupCStar Γ)).bijective.comp
      ((operatorK1Map_bijective (reducedCrossedScalarProductEquiv (Γ := Γ))).comp
        oddKKOperatorK1AllModuleUniversesAddEquiv.bijective)

end Comparison

section Finite
variable (Γ : Type) [Group Γ] [Countable Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [Finite Γ]

/-- **Reduction.** For a finite group, bijectivity of the point Green–Julg map in both parities
gives the coefficient-free reduced Baum–Connes property. -/
theorem baumConnesProperty_of_pointGreenJulg_bijective
    (h : ∀ p, Function.Bijective (pointGreenJulgHom Γ p)) : Assembly.BaumConnesProperty Γ := by
  intro p
  have hformula : (Assembly.reducedAssemblyHom Γ p :
      TopologicalKHomology.topologicalGroup p Γ → Assembly.analyticGroup Γ p) =
      (Assembly.reducedScalarKKToAnalyticHom Γ p) ∘ (pointGreenJulgHom Γ p) ∘
        (finiteTopologicalPointSpaceEquiv Γ p) :=
    funext (reducedAssemblyHom_finitePoint_formula Γ p)
  rw [hformula]
  exact (reducedScalarKKToAnalyticHom_bijective Γ p).comp
    ((h p).comp (finiteTopologicalPointSpaceEquiv Γ p).bijective)

/-- The reduced assembly map of a finite group as an explicit additive equivalence: the point model,
then the point Green–Julg isomorphism, then the analytic comparison. -/
def finiteAssemblyAddEquiv (p : Bool) :
    TopologicalKHomology.topologicalGroup p Γ ≃+ Assembly.analyticGroup Γ p :=
  (finiteTopologicalPointSpaceEquiv Γ p).trans ((greenJulgPointEquiv Γ p).trans
    (AddEquiv.ofBijective (Assembly.reducedScalarKKToAnalyticHom Γ p)
      (reducedScalarKKToAnalyticHom_bijective Γ p)))

/-- The reduced assembly map of a finite group is `finiteAssemblyAddEquiv`. -/
theorem reducedAssemblyHom_finite_eq (p : Bool) (x : TopologicalKHomology.topologicalGroup p Γ) :
    Assembly.reducedAssemblyHom Γ p x = finiteAssemblyAddEquiv Γ p x :=
  reducedAssemblyHom_finitePoint_formula Γ p x

end Finite

/-- **Baum–Connes for finite groups.** Every finite group, with the discrete topology, has the
coefficient-free reduced Baum–Connes property: the canonical reduced assembly map from the
topological side `TopologicalKHomology.topologicalGroup p Γ` to `K_p(C*_r Γ)` is bijective in both
parities.

The order-two theorems (`baumConnesProperty_of_card_two`, `baumConnesProperty_zmod_two`) and the
finite abelian one (`baumConnesProperty_of_finite_commGroup`) are special cases. They keep their
direct proofs, which do not depend on the Green–Julg isomorphism and also give the explicit
coordinates of `K₀(C*_r Γ)`. -/
theorem baumConnesProperty_of_finite (Γ : Type) [Group Γ] [Finite Γ] [Countable Γ]
    [TopologicalSpace Γ] [DiscreteTopology Γ] : Assembly.BaumConnesProperty Γ :=
  baumConnesProperty_of_pointGreenJulg_bijective Γ (pointGreenJulgHom_bijective Γ)

end BC4lean.Chapter8Examples
