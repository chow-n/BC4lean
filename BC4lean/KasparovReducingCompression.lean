import BC4lean.ProjectionHilbertModule
import BC4lean.ProjectionHilbertModuleSplit
import BC4lean.KasparovDirectSumIso
import BC4lean.KasparovHomotopyGroup
import BC4lean.OddKasparovDirectSumIso
import BC4lean.OddKasparovHomotopyGroup

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Compression of a Kasparov cycle to a reducing projection

A star projection `P` on the module of a cycle is reducing when it commutes exactly with the
operator, with the representation, with the grading and with the group action. Then the cycle
restricts to the closed range of `P`; the restriction to `P` and the restriction to `1 - P` sum
to the original cycle up to isomorphism, so the class is the sum of the two classes. The same
holds for odd (ungraded) cycles, without the grading condition. All cycle
conditions of a restriction come from those of the original cycle by compressing with the
adjointable inclusion and corestriction. -/

noncomputable section
universe uΓ uA uB uE
namespace BC4lean.KKTheory

variable {B : Type uB} {E : Type uE}
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

/-! ## Compressing operators -/

/-- The compression `P T P` of an operator, as an operator on the range of `P`. -/
def projectionCompress (P : AdjointableMap B E E) (hP : IsStarProjection P)
    (T : AdjointableMap B E E) :
    AdjointableMap B (ProjectionModule P) (ProjectionModule P) :=
  ((projectionCorestrict P hP).comp T).comp (projectionInclusion P hP)

section Compress

omit [StarOrderedRing B] [CompleteSpace E]

variable (P : AdjointableMap B E E) (hP : IsStarProjection P)

theorem projectionCompress_coe (T : AdjointableMap B E E) (x : ProjectionModule P) :
    (projectionCompress P hP T x : E) = P (T (x : E)) := rfl

/-- On an operator commuting with `P` the compression is the restriction. -/
theorem projectionCompress_coe_of_commute {T : AdjointableMap B E E} (hT : Commute P T)
    (x : ProjectionModule P) : (projectionCompress P hP T x : E) = T (x : E) := by
  have h := congrArg (fun S : AdjointableMap B E E => S (x : E)) hT.eq
  change P (T (x : E)) = T (P (x : E)) at h
  rw [projectionCompress_coe, h, x.property]

theorem projectionCompress_mul (S : AdjointableMap B E E) {T : AdjointableMap B E E}
    (hT : Commute P T) :
    projectionCompress P hP (S * T) = projectionCompress P hP S * projectionCompress P hP T := by
  ext x
  change P (S (T (x : E))) = P (S (projectionCompress P hP T x : E))
  rw [projectionCompress_coe_of_commute P hP hT]

theorem projectionCompress_add (S T : AdjointableMap B E E) :
    projectionCompress P hP (S + T) = projectionCompress P hP S + projectionCompress P hP T := by
  ext x
  simp only [projectionCompress_coe, AdjointableMap.coe_add_apply, Submodule.coe_add, map_add]

theorem projectionCompress_sub (S T : AdjointableMap B E E) :
    projectionCompress P hP (S - T) = projectionCompress P hP S - projectionCompress P hP T := by
  ext x
  simp only [projectionCompress_coe, AdjointableMap.coe_sub_apply, Submodule.coe_sub, map_sub]

theorem projectionCompress_smul (z : ℂ) (T : AdjointableMap B E E) :
    projectionCompress P hP (z • T) = z • projectionCompress P hP T := by
  ext x
  simp only [projectionCompress_coe, AdjointableMap.coe_smul_apply, Submodule.coe_smul, map_smul]

theorem projectionCompress_zero : projectionCompress P hP 0 = 0 := by
  ext x
  simp only [projectionCompress_coe, AdjointableMap.coe_zero_apply, Submodule.coe_zero, map_zero]

theorem projectionCompress_one : projectionCompress P hP 1 = 1 := by
  ext x
  exact x.property

theorem star_projectionCompress (T : AdjointableMap B E E) :
    star (projectionCompress P hP T) = projectionCompress P hP (star T) := by
  ext x
  rfl

end Compress

omit [CompleteSpace E] in
theorem IsModuleCompact.projectionCompress (P : AdjointableMap B E E) (hP : IsStarProjection P)
    {T : AdjointableMap B E E} (hT : IsModuleCompact T) :
    IsModuleCompact (projectionCompress P hP T) :=
  (hT.comp_left (projectionCorestrict P hP)).comp_right (projectionInclusion P hP)

/-! ## Reducing projections of a cycle -/

variable {Γ : Type uΓ} {A : Type uA} [Group Γ] [NonUnitalCStarAlgebra A]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

namespace EquivariantHilbertModule

variable (U : EquivariantHilbertModule β E) (P : AdjointableMap B E E)
  (hU : ∀ g x, P (U.action g x) = U.action g (P x))

/-- A projection commuting with the action carries the restricted action on its range. -/
def restrictAction (g : Γ) : ProjectionModule P ≃ₗᵢ[ℂ] ProjectionModule P where
  toLinearEquiv :=
    { toFun := fun x => ⟨U.action g (x : E), by
        change P (U.action g (x : E)) = U.action g (x : E)
        rw [hU, x.property]⟩
      invFun := fun x => ⟨U.action g⁻¹ (x : E), by
        change P (U.action g⁻¹ (x : E)) = U.action g⁻¹ (x : E)
        rw [hU, x.property]⟩
      left_inv := fun x => Subtype.ext (U.inv_apply_apply g (x : E))
      right_inv := fun x => Subtype.ext (U.apply_inv_apply g (x : E))
      map_add' := fun x y => Subtype.ext ((U.action g).map_add (x : E) (y : E))
      map_smul' := fun z x => Subtype.ext ((U.action g).map_smul z (x : E)) }
  norm_map' x := (U.action g).norm_map (x : E)

/-- The restriction of an equivariant module to the range of an invariant projection. -/
def restrict : EquivariantHilbertModule β (ProjectionModule P) where
  action :=
    { toFun := U.restrictAction P hU
      map_one' := by
        ext x
        exact U.one_apply (x : E)
      map_mul' := fun g h => by
        ext x
        exact U.mul_apply g h (x : E) }
  inner_action g x y := U.inner_action g (x : E) (y : E)

omit [StarOrderedRing B] [CompleteSpace E] in
@[simp] theorem restrict_coe (g : Γ) (x : ProjectionModule P) :
    ((U.restrict P hU).action g x : E) = U.action g (x : E) := rfl

end EquivariantHilbertModule

namespace GradedHilbertModule

variable (γ : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) E)
  (P : AdjointableMap B E E) (hγ : ∀ x, P (γ.grading x) = γ.grading (P x))

/-- The restriction of a grading to the range of an even projection. -/
def restrict : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) (ProjectionModule P) where
  grading :=
    { toLinearEquiv :=
        { toFun := fun x => ⟨γ.grading (x : E), by
            change P (γ.grading (x : E)) = γ.grading (x : E)
            rw [hγ, x.property]⟩
          invFun := fun x => ⟨γ.grading (x : E), by
            change P (γ.grading (x : E)) = γ.grading (x : E)
            rw [hγ, x.property]⟩
          left_inv := fun x => Subtype.ext (γ.involutive (x : E))
          right_inv := fun x => Subtype.ext (γ.involutive (x : E))
          map_add' := fun x y => Subtype.ext (γ.grading.map_add (x : E) (y : E))
          map_smul' := fun z x => Subtype.ext (γ.grading.map_smul z (x : E)) }
      norm_map' x := γ.grading.norm_map (x : E) }
  involutive x := Subtype.ext (γ.involutive (x : E))
  inner_grading x y := γ.inner_grading (x : E) (y : E)

omit [StarOrderedRing B] [CompleteSpace E] in
@[simp] theorem restrict_coe (x : ProjectionModule P) :
    ((γ.restrict P hγ).grading x : E) = γ.grading (x : E) := rfl

end GradedHilbertModule

namespace EquivariantHilbertModule

variable (U : EquivariantHilbertModule β E) (P : AdjointableMap B E E) (hP : IsStarProjection P)
  (hU : ∀ g x, P (U.action g x) = U.action g (P x))

omit [StarOrderedRing B] [CompleteSpace E] in
/-- Conjugating a compression by the restricted action compresses the conjugate. -/
theorem conjugateOperator_restrict_projectionCompress (g : Γ) {T : AdjointableMap B E E}
    (hT : Commute P T) :
    (U.restrict P hU).conjugateOperator g (projectionCompress P hP T) =
      projectionCompress P hP (U.conjugateOperator g T) := by
  ext x
  have h1 := congrArg (fun S : AdjointableMap B E E => S (U.action g⁻¹ (x : E))) hT.eq
  change P (T _) = T (P _) at h1
  rw [conjugateMap_apply, restrict_coe, projectionCompress_coe_of_commute P hP hT, restrict_coe,
    projectionCompress_coe, conjugateMap_apply, hU, h1, hU, x.property]

end EquivariantHilbertModule

/-! ## Even cycles -/

/-- A star projection on the module of a cycle that commutes exactly with all of its data. -/
structure KasparovCycle.ReducingProjection (c : KasparovCycle α β E) (P : AdjointableMap B E E) :
    Prop where
  isStarProjection : IsStarProjection P
  commute_operator : Commute P c.operator
  commute_representation : ∀ a, Commute P (c.representation a)
  grading : ∀ x, P (c.grading.grading x) = c.grading.grading (P x)
  action : ∀ g x, P (c.groupAction.action g x) = c.groupAction.action g (P x)

namespace KasparovCycle

variable (c : KasparovCycle α β E) {P : AdjointableMap B E E} (hP : c.ReducingProjection P)
include hP

/-- The complementary projection is reducing as well. -/
theorem ReducingProjection.one_sub : c.ReducingProjection (1 - P) where
  isStarProjection := hP.isStarProjection.one_sub
  commute_operator := (Commute.one_left _).sub_left hP.commute_operator
  commute_representation a := (Commute.one_left _).sub_left (hP.commute_representation a)
  grading x := by
    simp only [AdjointableMap.coe_sub_apply, AdjointableMap.one_apply, map_sub, hP.grading]
  action g x := by
    simp only [AdjointableMap.coe_sub_apply, AdjointableMap.one_apply, map_sub, hP.action]

/-- The representation compressed to the range of a reducing projection. -/
def compressRepresentation :
    A →⋆ₙₐ[ℂ] AdjointableMap B (ProjectionModule P) (ProjectionModule P) where
  toFun a := projectionCompress P hP.isStarProjection (c.representation a)
  map_smul' z a := by
    simp only [map_smul, MonoidHom.id_apply, projectionCompress_smul]
  map_zero' := by simp only [map_zero, projectionCompress_zero]
  map_add' a b := by simp only [map_add, projectionCompress_add]
  map_mul' a b := by
    simp only [map_mul, projectionCompress_mul _ _ _ (hP.commute_representation b)]
  map_star' a := by simp only [map_star, star_projectionCompress]

theorem compressRepresentation_apply (a : A) :
    c.compressRepresentation hP a = projectionCompress P hP.isStarProjection (c.representation a) :=
  rfl

/-- The cycle compressed to the range of a reducing projection. Every cycle condition is the
compression of the corresponding condition of the original cycle. -/
def compress : KasparovCycle α β (ProjectionModule P) where
  countablyGenerated :=
    projectionModule_isCountablyGenerated P hP.isStarProjection c.countablyGenerated
  grading := c.grading.restrict P hP.grading
  groupAction := c.groupAction.restrict P hP.action
  grading_preserved g x := Subtype.ext (c.grading_preserved g (x : E))
  representation := c.compressRepresentation hP
  representation_even a x := by
    apply Subtype.ext
    rw [GradedHilbertModule.restrict_coe, compressRepresentation_apply,
      projectionCompress_coe_of_commute _ _ (hP.commute_representation a),
      projectionCompress_coe_of_commute _ _ (hP.commute_representation a),
      GradedHilbertModule.restrict_coe]
    exact c.representation_even a (x : E)
  representation_equivariant g a := by
    rw [compressRepresentation_apply, compressRepresentation_apply,
      EquivariantHilbertModule.conjugateOperator_restrict_projectionCompress _ _ _ _ g
        (hP.commute_representation a), c.representation_equivariant]
  operator := projectionCompress P hP.isStarProjection c.operator
  operator_odd x := by
    apply Subtype.ext
    rw [GradedHilbertModule.restrict_coe, projectionCompress_coe_of_commute _ _ hP.commute_operator,
      Submodule.coe_neg, projectionCompress_coe_of_commute _ _ hP.commute_operator,
      GradedHilbertModule.restrict_coe]
    exact c.operator_odd (x : E)
  selfadjoint_mod_compact a := by
    have h := (c.selfadjoint_mod_compact a).projectionCompress P hP.isStarProjection
    rwa [projectionCompress_mul _ _ _ (hP.commute_representation a), projectionCompress_sub,
      ← star_projectionCompress] at h
  square_mod_compact a := by
    have h := (c.square_mod_compact a).projectionCompress P hP.isStarProjection
    rwa [projectionCompress_mul _ _ _ (hP.commute_representation a), projectionCompress_sub,
      projectionCompress_one, projectionCompress_mul _ _ _ hP.commute_operator] at h
  commutator_compact a := by
    have h := (c.commutator_compact a).projectionCompress P hP.isStarProjection
    rwa [projectionCompress_sub, projectionCompress_mul _ _ _ (hP.commute_representation a),
      projectionCompress_mul _ _ _ hP.commute_operator] at h
  equivariance_mod_compact g a := by
    have h := (c.equivariance_mod_compact g a).projectionCompress P hP.isStarProjection
    rwa [projectionCompress_mul _ _ _ (hP.commute_representation a), projectionCompress_sub,
      ← EquivariantHilbertModule.conjugateOperator_restrict_projectionCompress _ _ _ hP.action g
        hP.commute_operator] at h

@[simp] theorem compress_operator_coe (x : ProjectionModule P) :
    ((c.compress hP).operator x : E) = c.operator (x : E) :=
  projectionCompress_coe_of_commute _ _ hP.commute_operator x

@[simp] theorem compress_representation_coe (a : A) (x : ProjectionModule P) :
    ((c.compress hP).representation a x : E) = c.representation a (x : E) :=
  projectionCompress_coe_of_commute _ _ (hP.commute_representation a) x

/-- The cycle is the direct sum of its compressions to `P` and to `1 - P`. -/
def compressDirectSumIso :
    KasparovCycleIso ((c.compress hP).directSum (c.compress hP.one_sub)) c where
  moduleEquiv := (projectionModuleSplitEquiv P hP.isStarProjection).symm
  grading_intertwine x := by
    change ((c.compress hP).grading.grading x.fst : E) +
        ((c.compress hP.one_sub).grading.grading x.snd : E) =
      c.grading.grading ((x.fst : E) + (x.snd : E))
    rw [map_add]
    rfl
  action_intertwine g x := by
    change ((c.compress hP).groupAction.action g x.fst : E) +
        ((c.compress hP.one_sub).groupAction.action g x.snd : E) =
      c.groupAction.action g ((x.fst : E) + (x.snd : E))
    rw [map_add]
    rfl
  representation_intertwine a x := by
    change (projectionModuleSplitEquiv P hP.isStarProjection).symm
        (sumMap ((c.compress hP).representation a) ((c.compress hP.one_sub).representation a) x) =
      c.representation a ((projectionModuleSplitEquiv P hP.isStarProjection).symm x)
    rw [sumMap_apply, projectionModuleSplitEquiv_symm_apply, projectionModuleSplitEquiv_symm_apply]
    simp only [sumMk_fst, sumMk_snd]
    rw [compress_representation_coe, compress_representation_coe, map_add]
  operator_intertwine x := by
    change (projectionModuleSplitEquiv P hP.isStarProjection).symm
        (sumMap (c.compress hP).operator (c.compress hP.one_sub).operator x) =
      c.operator ((projectionModuleSplitEquiv P hP.isStarProjection).symm x)
    rw [sumMap_apply, projectionModuleSplitEquiv_symm_apply, projectionModuleSplitEquiv_symm_apply]
    simp only [sumMk_fst, sumMk_snd]
    rw [compress_operator_coe, compress_operator_coe, map_add]

/-- The class of a cycle is the sum of the classes of its two compressions. -/
theorem mk_eq_add_compress :
    KasparovHomotopyClass.mk.{uΓ,uA,uB,uE} (BundledKasparovCycle.of c) =
      KasparovHomotopyClass.mk (BundledKasparovCycle.of (c.compress hP)) +
        KasparovHomotopyClass.mk (BundledKasparovCycle.of (c.compress hP.one_sub)) := by
  rw [← KasparovHomotopyClass.mk_directSum]
  exact (KasparovHomotopyClass.mk_eq_of_iso (c.compressDirectSumIso hP).symm)

end KasparovCycle

/-! ## Odd cycles -/

/-- A star projection on the module of an odd cycle that commutes exactly with all of its data. -/
structure OddKasparovCycle.ReducingProjection (c : OddKasparovCycle α β E)
    (P : AdjointableMap B E E) : Prop where
  isStarProjection : IsStarProjection P
  commute_operator : Commute P c.operator
  commute_representation : ∀ a, Commute P (c.representation a)
  action : ∀ g x, P (c.groupAction.action g x) = c.groupAction.action g (P x)

namespace OddKasparovCycle

variable (c : OddKasparovCycle α β E) {P : AdjointableMap B E E} (hP : c.ReducingProjection P)
include hP

/-- The complementary projection is reducing as well. -/
theorem ReducingProjection.one_sub : c.ReducingProjection (1 - P) where
  isStarProjection := hP.isStarProjection.one_sub
  commute_operator := (Commute.one_left _).sub_left hP.commute_operator
  commute_representation a := (Commute.one_left _).sub_left (hP.commute_representation a)
  action g x := by
    simp only [AdjointableMap.coe_sub_apply, AdjointableMap.one_apply, map_sub, hP.action]

/-- The representation compressed to the range of a reducing projection. -/
def compressRepresentation :
    A →⋆ₙₐ[ℂ] AdjointableMap B (ProjectionModule P) (ProjectionModule P) where
  toFun a := projectionCompress P hP.isStarProjection (c.representation a)
  map_smul' z a := by
    simp only [map_smul, MonoidHom.id_apply, projectionCompress_smul]
  map_zero' := by simp only [map_zero, projectionCompress_zero]
  map_add' a b := by simp only [map_add, projectionCompress_add]
  map_mul' a b := by
    simp only [map_mul, projectionCompress_mul _ _ _ (hP.commute_representation b)]
  map_star' a := by simp only [map_star, star_projectionCompress]

theorem compressRepresentation_apply (a : A) :
    c.compressRepresentation hP a = projectionCompress P hP.isStarProjection (c.representation a) :=
  rfl

/-- The odd cycle compressed to the range of a reducing projection. -/
def compress : OddKasparovCycle α β (ProjectionModule P) where
  countablyGenerated :=
    projectionModule_isCountablyGenerated P hP.isStarProjection c.countablyGenerated
  groupAction := c.groupAction.restrict P hP.action
  representation := c.compressRepresentation hP
  representation_equivariant g a := by
    rw [compressRepresentation_apply, compressRepresentation_apply,
      EquivariantHilbertModule.conjugateOperator_restrict_projectionCompress _ _ _ _ g
        (hP.commute_representation a), c.representation_equivariant]
  operator := projectionCompress P hP.isStarProjection c.operator
  selfadjoint_mod_compact a := by
    have h := (c.selfadjoint_mod_compact a).projectionCompress P hP.isStarProjection
    rwa [projectionCompress_mul _ _ _ (hP.commute_representation a), projectionCompress_sub,
      ← star_projectionCompress] at h
  square_mod_compact a := by
    have h := (c.square_mod_compact a).projectionCompress P hP.isStarProjection
    rwa [projectionCompress_mul _ _ _ (hP.commute_representation a), projectionCompress_sub,
      projectionCompress_one, projectionCompress_mul _ _ _ hP.commute_operator] at h
  commutator_compact a := by
    have h := (c.commutator_compact a).projectionCompress P hP.isStarProjection
    rwa [projectionCompress_sub, projectionCompress_mul _ _ _ (hP.commute_representation a),
      projectionCompress_mul _ _ _ hP.commute_operator] at h
  equivariance_mod_compact g a := by
    have h := (c.equivariance_mod_compact g a).projectionCompress P hP.isStarProjection
    rwa [projectionCompress_mul _ _ _ (hP.commute_representation a), projectionCompress_sub,
      ← EquivariantHilbertModule.conjugateOperator_restrict_projectionCompress _ _ _ hP.action g
        hP.commute_operator] at h

@[simp] theorem compress_operator_coe (x : ProjectionModule P) :
    ((c.compress hP).operator x : E) = c.operator (x : E) :=
  projectionCompress_coe_of_commute _ _ hP.commute_operator x

@[simp] theorem compress_representation_coe (a : A) (x : ProjectionModule P) :
    ((c.compress hP).representation a x : E) = c.representation a (x : E) :=
  projectionCompress_coe_of_commute _ _ (hP.commute_representation a) x

/-- The odd cycle is the direct sum of its compressions to `P` and to `1 - P`. -/
def compressDirectSumIso :
    OddKasparovCycleIso ((c.compress hP).directSum (c.compress hP.one_sub)) c where
  moduleEquiv := (projectionModuleSplitEquiv P hP.isStarProjection).symm
  action_intertwine g x := by
    change ((c.compress hP).groupAction.action g x.fst : E) +
        ((c.compress hP.one_sub).groupAction.action g x.snd : E) =
      c.groupAction.action g ((x.fst : E) + (x.snd : E))
    rw [map_add]
    rfl
  representation_intertwine a x := by
    change (projectionModuleSplitEquiv P hP.isStarProjection).symm
        (sumMap ((c.compress hP).representation a) ((c.compress hP.one_sub).representation a) x) =
      c.representation a ((projectionModuleSplitEquiv P hP.isStarProjection).symm x)
    rw [sumMap_apply, projectionModuleSplitEquiv_symm_apply, projectionModuleSplitEquiv_symm_apply]
    simp only [sumMk_fst, sumMk_snd]
    rw [compress_representation_coe, compress_representation_coe, map_add]
  operator_intertwine x := by
    change (projectionModuleSplitEquiv P hP.isStarProjection).symm
        (sumMap (c.compress hP).operator (c.compress hP.one_sub).operator x) =
      c.operator ((projectionModuleSplitEquiv P hP.isStarProjection).symm x)
    rw [sumMap_apply, projectionModuleSplitEquiv_symm_apply, projectionModuleSplitEquiv_symm_apply]
    simp only [sumMk_fst, sumMk_snd]
    rw [compress_operator_coe, compress_operator_coe, map_add]

/-- The odd class of a cycle is the sum of the classes of its two compressions. -/
theorem mk_eq_add_compress [TopologicalSpace.SeparableSpace B] :
    OddKK.mk.{uΓ,uA,uB,uE} (BundledOddKasparovCycle.of c) =
      OddKK.mk (BundledOddKasparovCycle.of (c.compress hP)) +
        OddKK.mk (BundledOddKasparovCycle.of (c.compress hP.one_sub)) := by
  rw [← OddKK.mk_directSum]
  exact (OddKK.mk_eq_of_iso (c.compressDirectSumIso hP).symm)

end OddKasparovCycle

end BC4lean.KKTheory
