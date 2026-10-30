import BC4lean.ScalarUnitProjection
import BC4lean.ScalarKasparovK0IndexUniverse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # The scalar identity class in every module universe

`ScalarUnitProjection.scalarKKOperatorK0AddEquiv_identity` computes the
scalar index of the identity class of `ℂ` in module universe `0`. The same
holds in every module universe `v`: the identity class in universe `v` is the
universe change (`GroupShrinkEvenBridge.addEquivalence`) of the identity
class in universe `0`, because on graded classes the universe change `shrink`
agrees with `ulift`, and the scalar index is invariant under universe change
(`scalarKKOperatorK0Index_universe`).
-/

noncomputable section
universe uΓ uA uB uE v
namespace BC4lean.KKTheory

namespace GradedKasparovHomotopyClass
variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
  {δA : CStarGrading A} {δB : CStarGrading B}

/-- On graded classes, changing the module universe by `Shrink` and by
`ULift` agree: both cycles are isomorphic to the original one. -/
theorem shrink_eq_ulift (x : GradedKasparovHomotopyClass.{uΓ, uA, uB, uE} α β δA δB) :
    shrink.{uΓ, uA, uB, uE, max uE v} x = ulift.{uΓ, uA, uB, uE, v} x := by
  refine Quotient.inductionOn x ?_
  intro c
  exact mk_eq_of_iso (c.cycle.shrinkIso.symm.trans c.cycle.uliftIso)

end GradedKasparovHomotopyClass

namespace ScalarUnitProjection
open BC4lean.OperatorKTheory
open scoped ComplexOrder

/-- The identity class of `ℂ` in module universe `v` is the universe change of
the identity class in module universe `0`. -/
theorem identity_universe :
    GroupUniverseParityUnits.identity.{0,0,v} scalarIdentityAction =
      GroupShrinkEvenBridge.addEquivalence.{0,0,0,0,v}
        (GroupUniverseParityUnits.identity.{0,0,0} scalarIdentityAction) := by
  unfold GroupUniverseParityUnits.identity
  rw [GradedKasparovHomotopyClass.ulift_eq_self]
  unfold GroupShrinkEvenBridge.addEquivalence GroupUniverseEvenBridge.evenClass
  rw [AddEquiv.trans_apply, AddEquiv.trans_apply, AddEquiv.symm_apply_apply,
    GradedKasparovHomotopyClass.shrinkAddEquiv_apply,
    GradedKasparovHomotopyClass.shrink_eq_ulift]

/-- `scalarKKOperatorK0AddEquiv_identity` in every module universe. -/
theorem scalarKKOperatorK0AddEquiv_identity_universe :
    scalarKKOperatorK0AddEquiv.{0,v}
      (GroupUniverseParityUnits.identity.{0,0,v} scalarIdentityAction) =
        nonunitalProjectionK0 (1 : ℂ) (by
          apply isStarProjection_iff'.mpr
          exact ⟨one_mul 1, star_one _⟩) := by
  rw [identity_universe, ← scalarKKOperatorK0AddEquiv_identity]
  simp only [scalarKKOperatorK0AddEquiv_apply]
  exact scalarKKOperatorK0Index_universe.{0,0,v} (B := ℂ) _

end ScalarUnitProjection
end BC4lean.KKTheory
