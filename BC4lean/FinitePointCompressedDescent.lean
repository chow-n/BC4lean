import BC4lean.FinitePointCharacterTensor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! Compressed descent for a finite group on the point.

Let `Γ` be finite and let `χ : Γ → U(1)` be a character. For an equivariant
cycle over `C₀(pt)` on which `Γ` acts through `χ` and the point algebra acts
unitally, the source pullback of its descent along the averaging projection
`e = |Γ|⁻¹ ∑_g δ_g` is the ordinary coefficient extension of the underlying
scalar cycle along `z ↦ z • P_χ`, where `P_χ = |Γ|⁻¹ ∑_g χ(g) λ_g` is the
projection of `C*_r(Γ)` with `λ_h P_χ = χ(h)⁻¹ P_χ`. Both parities.

The proof reduces the pulled-back cycle to the range of its support
projection, which acts on `E ⊗ C*_r(Γ)` as `1 ⊗ P_χ`, and identifies that range
with `E ⊗_{P_χ} C*_r(Γ)` by the completed map `x ⊗ c ↦ x ⊗ P_χ c`. -/

noncomputable section
namespace BC4lean.KKTheory.FinitePointCompressedDescent
open BC4lean.ProperActions BC4lean.OperatorKTheory BC4lean.Chapter8Examples
open KKTheory.GroupUniverseParityGroup KKTheory.GroupUniverseParityFunctoriality
open KKTheory.FinitePointCharacterTensor
open scoped ZeroAtInfty ComplexOrder KasparovDescent InnerProductSpace

section EvenCycle
variable {Γ : Type} [Group Γ] [Fintype Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul ℂᵐᵒᵖ E]
  [CStarModule ℂᵐᵒᵖ E] [CompleteSpace E]

local instance pointCZero_separable :
    TopologicalSpace.SeparableSpace C₀(FiniteGroupPoint.{0}, ℂ) :=
  TopologicalKHomology.cZero_separableSpace

/-- The underlying scalar cycle: the point algebra read as `ℂ`, the group forgotten. -/
def pointScalarCycle (c : KasparovCycle (pointAction Γ) (scalarAction Γ) E) :
    KasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ) E where
  countablyGenerated := c.countablyGenerated
  grading := c.grading
  groupAction := EquivariantHilbertModule.trivial
  grading_preserved _ _ := rfl
  representation := c.representation.comp (UnitPointCutoff.scalarToCZero FiniteGroupPoint.{0})
  representation_even z := c.representation_even _
  representation_equivariant g z := by
    have hg : g = 1 := Subsingleton.elim _ _
    subst g
    rw [EquivariantHilbertModule.conjugateOperator, EquivariantHilbertModule.conjugateMap_one]
    rfl
  operator := c.operator
  operator_odd := c.operator_odd
  selfadjoint_mod_compact z := c.selfadjoint_mod_compact _
  square_mod_compact z := c.square_mod_compact _
  commutator_compact z := c.commutator_compact _
  equivariance_mod_compact g z := by
    have hg : g = 1 := Subsingleton.elim _ _
    subst g
    rw [EquivariantHilbertModule.conjugateOperator, EquivariantHilbertModule.conjugateMap_one,
      sub_self, zero_mul]
    exact IsModuleCompact.zero

/-- Explicitly typed equivariance of the averaging homomorphism. -/
theorem averagingHom_equivariant : ∀ (g : Unit) (a : ℂ),
    FinitePointCutoff.averagingHom Γ
        ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ).automorphism g a) =
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit
        (ReducedCrossedProduct (pointAction Γ))).automorphism g
        (FinitePointCutoff.averagingHom Γ a) := fun _ _ => rfl

/-- The descended cycle pulled back along `z ↦ z • e`. -/
abbrev pulledDescent (c : KasparovCycle (pointAction Γ) (scalarAction Γ) E) :=
  NativeSourcePullback.evenCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
    (FinitePointCutoff.averagingHom Γ) averagingHom_equivariant
    (KasparovDescent.evenCycle (scalarAction Γ) (pointAction Γ) c)

/-- The ordinary coefficient extension of the underlying scalar cycle along `z ↦ z • P_χ`. -/
abbrev characterCycle (χ : Γ →* unitary ℂ)
    (c : KasparovCycle (pointAction Γ) (scalarAction Γ) E) :
    KasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (GroupCrossed Γ))
      (CharacterTensor E χ) :=
  (pointScalarCycle c).scalarCoefficientTensor (characterHom Γ χ)

variable (χ : Γ →* unitary ℂ) (c : KasparovCycle (pointAction Γ) (scalarAction Γ) E)

/-- Under the hypotheses, the support projection of the pulled-back descent is `1 ⊗ P_χ`. -/
theorem pulledDescent_support_mk
    (hU : ∀ g x, c.groupAction.action g x = (χ g : ℂ) • x)
    (h1 : c.representation (pointScalar 1) = 1)
    (x : E) (d : (GroupCrossed Γ)ᵐᵒᵖ) :
    (pulledDescent c).scalarSupportProjection (KasparovDescent.mk (scalarAction Γ) E x d) =
      KasparovDescent.mk (scalarAction Γ) E x (characterLeftMul χ d) := by
  change KasparovDescent.reducedSourceRepresentation (scalarAction Γ) E (pointAction Γ)
    c.groupAction c.representation c.representation_equivariant
    ((1 : ℂ) • FinitePointCutoff.averaging Γ) _ = _
  rw [one_smul]
  exact reducedSourceRepresentation_averaging_mk χ c.groupAction c.representation
    c.representation_equivariant hU h1 x d

theorem characterIsometry_grading (u : CharacterTensor E χ) :
    characterIsometry χ ((characterCycle χ c).grading.grading u) =
      (KasparovDescent.ordinaryModuleGrading (scalarAction Γ) c.grading).grading
        (characterIsometry χ u) := by
  let V := (characterIsometry (E := E) χ).toContinuousLinearMap
  have h : V.comp (characterCycle χ c).grading.grading.toLinearIsometry.toContinuousLinearMap =
      (KasparovDescent.ordinaryModuleGrading (scalarAction Γ)
        c.grading).grading.toLinearIsometry.toContinuousLinearMap.comp V := by
    apply characterTensor_clm_ext
    intro x d
    have hg : (characterCycle χ c).grading.grading (interiorModuleTensorMk _ x d) =
        interiorModuleTensorMk _ (c.grading.grading x) d :=
      GradedHilbertModule.interiorTensor_grading_mk _ _ _ x d
    change characterIsometry χ ((characterCycle χ c).grading.grading
        (interiorModuleTensorMk _ x d)) =
      (KasparovDescent.ordinaryModuleGrading (scalarAction Γ) c.grading).grading
        (characterIsometry χ (interiorModuleTensorMk _ x d))
    rw [hg, characterIsometry_mk, characterIsometry_mk]
    exact (KasparovDescent.ordinaryModuleGrading_mk (scalarAction Γ) c.grading x _).symm
  exact DFunLike.congr_fun h u

theorem characterIsometry_operator (u : CharacterTensor E χ) :
    characterIsometry χ ((characterCycle χ c).operator u) =
      KasparovDescent.operatorHom (scalarAction Γ) E c.operator (characterIsometry χ u) := by
  let V := (characterIsometry (E := E) χ).toContinuousLinearMap
  have h : V.comp (characterCycle χ c).operator.toCLM =
      (KasparovDescent.operatorHom (scalarAction Γ) E c.operator).toCLM.comp V := by
    apply characterTensor_clm_ext
    intro x d
    have hop : (characterCycle χ c).operator (interiorModuleTensorMk _ x d) =
        interiorModuleTensorMk _ (c.operator x) d :=
      interiorModuleTensorOperator_mk _ _ x d
    change characterIsometry χ ((characterCycle χ c).operator (interiorModuleTensorMk _ x d)) =
      KasparovDescent.operatorHom (scalarAction Γ) E c.operator
        (characterIsometry χ (interiorModuleTensorMk _ x d))
    refine (congrArg (characterIsometry χ) hop).trans ?_
    refine (characterIsometry_mk χ (c.operator x) d).trans ?_
    refine (KasparovDescent.operatorHom_mk (scalarAction Γ) E c.operator x _).symm.trans ?_
    exact congrArg (KasparovDescent.operatorHom (scalarAction Γ) E c.operator)
      (characterIsometry_mk χ x d).symm
  exact DFunLike.congr_fun h u

theorem characterCycle_representation (h1 : c.representation (pointScalar 1) = 1)
    (z : ℂ) (u : CharacterTensor E χ) :
    (characterCycle χ c).representation z u = z • u := by
  have hz : c.representation (pointScalar z) = z • 1 := by
    rw [show pointScalar z = z • pointScalar 1 by rw [← map_smul, smul_eq_mul, mul_one],
      map_smul, h1]
  change interiorModuleTensorOperatorHom _ (c.representation (pointScalar z)) u = z • u
  rw [hz, map_smul, map_one]
  rfl

section Generic
variable (D : KasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
    (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (GroupCrossed Γ))
    (DescendedModule (Γ := Γ) E))
  (hp : ∀ x d, D.scalarSupportProjection (KasparovDescent.mk (scalarAction Γ) E x d) =
    KasparovDescent.mk (scalarAction Γ) E x (characterLeftMul χ d))

include hp in
theorem supportEquiv_representation (h1 : c.representation (pointScalar 1) = 1)
    (z : ℂ) (u : CharacterTensor E χ) :
    characterRangeEquiv χ _ hp ((characterCycle χ c).representation z u) =
      D.scalarSupportRepresentation z (characterRangeEquiv χ _ hp u) := by
  refine Eq.trans ?_ (KasparovCycle.scalarSupportRepresentation_apply D z _).symm
  apply Subtype.ext
  refine (characterRangeEquiv_coe χ _ hp _).trans ?_
  refine (congrArg (characterIsometry χ) (characterCycle_representation χ c h1 z u)).trans ?_
  refine (map_smul _ z u).trans ?_
  rfl

include hp in
theorem supportEquiv_operator
    (hF : ∀ v, D.operator v = KasparovDescent.operatorHom (scalarAction Γ) E c.operator v)
    (u : CharacterTensor E χ) :
    characterRangeEquiv χ _ hp ((characterCycle χ c).operator u) =
      D.scalarSupportCompression (characterRangeEquiv χ _ hp u) := by
  apply Subtype.ext
  refine (characterRangeEquiv_coe χ _ hp _).trans ?_
  refine Eq.trans ?_ (KasparovCycle.scalarSupportCompression_coe D _).symm
  have hv : D.scalarSupportProjection (characterIsometry χ u) = characterIsometry χ u :=
    projection_characterIsometry χ _ hp u
  have h2 : D.scalarSupportBlockOperator (characterIsometry χ u) =
      D.scalarSupportProjection (D.operator (characterIsometry χ u)) := by
    unfold KasparovCycle.scalarSupportBlockOperator
    simp only [AdjointableMap.coe_add_apply, AdjointableMap.mul_apply,
      AdjointableMap.coe_sub_apply, AdjointableMap.one_apply, hv, sub_self, map_zero, add_zero]
  refine Eq.trans ?_ h2.symm
  refine Eq.trans ?_ (congrArg D.scalarSupportProjection (hF _)).symm
  refine Eq.trans ?_ (congrArg D.scalarSupportProjection (characterIsometry_operator χ c u))
  exact (projection_characterIsometry χ _ hp _).symm

include hp in
theorem supportEquiv_grading
    (hgr : ∀ v, D.grading.grading v =
      (KasparovDescent.ordinaryModuleGrading (scalarAction Γ) c.grading).grading v)
    (u : CharacterTensor E χ) :
    characterRangeEquiv χ _ hp ((characterCycle χ c).grading.grading u) =
      D.scalarSupportGrading.grading (characterRangeEquiv χ _ hp u) := by
  apply Subtype.ext
  refine (characterRangeEquiv_coe χ _ hp _).trans ?_
  refine Eq.trans ?_ (KasparovCycle.scalarSupportGrading_coe D _).symm
  refine (characterIsometry_grading χ c u).trans ?_
  exact (hgr _).symm

include hp in
theorem supportEquiv_action (hact : ∀ g v, D.groupAction.action g v = v)
    (g : Unit) (u : CharacterTensor E χ) :
    characterRangeEquiv χ _ hp ((characterCycle χ c).groupAction.action g u) =
      D.scalarSupportGroupAction.action g (characterRangeEquiv χ _ hp u) := by
  apply Subtype.ext
  refine Eq.trans ?_ (KasparovCycle.scalarSupportGroupAction_coe D g _).symm
  exact (hact g _).symm

/-- The whole-cycle isomorphism onto the support cycle of any cycle `D` whose
support projection is `1 ⊗ P_χ` and whose remaining data are those of descent. -/
def supportIso (h1 : c.representation (pointScalar 1) = 1)
    (hF : ∀ v, D.operator v = KasparovDescent.operatorHom (scalarAction Γ) E c.operator v)
    (hgr : ∀ v, D.grading.grading v =
      (KasparovDescent.ordinaryModuleGrading (scalarAction Γ) c.grading).grading v)
    (hact : ∀ g v, D.groupAction.action g v = v) :
    KasparovCycleIso (characterCycle χ c) D.scalarSupportCycle where
  moduleEquiv := characterRangeEquiv χ _ hp
  grading_intertwine := supportEquiv_grading χ c D hp hgr
  action_intertwine := supportEquiv_action χ c D hp hact
  representation_intertwine := supportEquiv_representation χ c D hp h1
  operator_intertwine := supportEquiv_operator χ c D hp hF

end Generic

/-- The whole-cycle isomorphism: the coefficient extension along `z ↦ z • P_χ`
is the support cycle of the pulled-back descent. -/
def characterCycleIso
    (hU : ∀ g x, c.groupAction.action g x = (χ g : ℂ) • x)
    (h1 : c.representation (pointScalar 1) = 1) :
    KasparovCycleIso (characterCycle χ c) (pulledDescent c).scalarSupportCycle :=
  supportIso χ c (pulledDescent c) (pulledDescent_support_mk χ c hU h1) h1
    (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)

/-- Compressed descent, even case. If `Γ` acts on `E` through `χ` and the point
acts unitally, the descent of `[c]` pulled back along `z ↦ z • e` is the
coefficient extension of the underlying scalar class along `z ↦ z • P_χ`. -/
theorem even_compressedDescent
    (hU : ∀ g x, c.groupAction.action g x = (χ g : ℂ) • x)
    (h1 : c.representation (pointScalar 1) = 1) :
    sourcePullback.{0,0,0,0,0} (Γ := Unit) (A := ℂ)
        (B := ReducedCrossedProduct (pointAction Γ)) (C := GroupCrossed Γ)
        («α» := (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ))
        («β» := CStarAlgebraAction.trivial) («γ» := CStarAlgebraAction.trivial)
        false (FinitePointCutoff.averagingHom Γ) averagingHom_equivariant
        (KasparovDescent.evenClass (scalarAction Γ) (pointAction Γ)
          (KasparovHomotopyClass.mk (BundledKasparovCycle.of c))) =
      GroupUniverseOrdinaryEven.coefficientPushforward.{0,0,0} (characterHom Γ χ)
        (KasparovHomotopyClass.mk (BundledKasparovCycle.of (pointScalarCycle c))) := by
  calc _ = KasparovHomotopyClass.mk (BundledKasparovCycle.of (pulledDescent c)) := by
        rw [KasparovDescent.evenClass_mk, NativeSourcePullback.even_mk]
        rfl
    _ = KasparovHomotopyClass.mk (BundledKasparovCycle.of (pulledDescent c).scalarSupportCycle) :=
        KasparovCycle.scalarSupport_class _
    _ = KasparovHomotopyClass.mk (BundledKasparovCycle.of (characterCycle χ c)) :=
        (KasparovHomotopyClass.mk_eq_of_iso (characterCycleIso χ c hU h1)).symm
    _ = _ := (GroupUniverseOrdinaryEven.coefficientPushforward_mk_scalarCoefficientTensor
        (pointScalarCycle c) (characterHom Γ χ)).symm

end EvenCycle

section OddCycle
variable {Γ : Type} [Group Γ] [Fintype Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul ℂᵐᵒᵖ E]
  [CStarModule ℂᵐᵒᵖ E] [CompleteSpace E]

local instance oddPointCZero_separable :
    TopologicalSpace.SeparableSpace C₀(FiniteGroupPoint.{0}, ℂ) :=
  TopologicalKHomology.cZero_separableSpace

/-- The underlying odd scalar cycle: the point algebra read as `ℂ`, the group forgotten. -/
def oddPointScalarCycle (c : OddKasparovCycle (pointAction Γ) (scalarAction Γ) E) :
    OddKasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ) E where
  countablyGenerated := c.countablyGenerated
  groupAction := EquivariantHilbertModule.trivial
  representation := c.representation.comp (UnitPointCutoff.scalarToCZero FiniteGroupPoint.{0})
  representation_equivariant g z := by
    have hg : g = 1 := Subsingleton.elim _ _
    subst g
    rw [EquivariantHilbertModule.conjugateOperator, EquivariantHilbertModule.conjugateMap_one]
    rfl
  operator := c.operator
  selfadjoint_mod_compact z := c.selfadjoint_mod_compact _
  square_mod_compact z := c.square_mod_compact _
  commutator_compact z := c.commutator_compact _
  equivariance_mod_compact g z := by
    have hg : g = 1 := Subsingleton.elim _ _
    subst g
    rw [EquivariantHilbertModule.conjugateOperator, EquivariantHilbertModule.conjugateMap_one,
      sub_self, zero_mul]
    exact IsModuleCompact.zero

/-- The odd descended cycle pulled back along `z ↦ z • e`. -/
abbrev oddPulledDescent (c : OddKasparovCycle (pointAction Γ) (scalarAction Γ) E) :=
  NativeSourcePullback.oddCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
    (FinitePointCutoff.averagingHom Γ) averagingHom_equivariant
    (KasparovDescent.oddCycle (scalarAction Γ) (pointAction Γ) c)

/-- The odd coefficient extension of the underlying scalar cycle along `z ↦ z • P_χ`. -/
abbrev oddCharacterCycle (χ : Γ →* unitary ℂ)
    (c : OddKasparovCycle (pointAction Γ) (scalarAction Γ) E) :
    OddKasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (GroupCrossed Γ))
      (CharacterTensor E χ) :=
  (oddPointScalarCycle c).coefficientTensor (characterHom Γ χ)

variable (χ : Γ →* unitary ℂ) (c : OddKasparovCycle (pointAction Γ) (scalarAction Γ) E)

theorem oddPulledDescent_support_mk
    (hU : ∀ g x, c.groupAction.action g x = (χ g : ℂ) • x)
    (h1 : c.representation (pointScalar 1) = 1)
    (x : E) (d : (GroupCrossed Γ)ᵐᵒᵖ) :
    (oddPulledDescent c).scalarSupportProjection (KasparovDescent.mk (scalarAction Γ) E x d) =
      KasparovDescent.mk (scalarAction Γ) E x (characterLeftMul χ d) := by
  change KasparovDescent.reducedSourceRepresentation (scalarAction Γ) E (pointAction Γ)
    c.groupAction c.representation c.representation_equivariant
    ((1 : ℂ) • FinitePointCutoff.averaging Γ) _ = _
  rw [one_smul]
  exact reducedSourceRepresentation_averaging_mk χ c.groupAction c.representation
    c.representation_equivariant hU h1 x d

theorem oddCharacterCycle_representation (h1 : c.representation (pointScalar 1) = 1)
    (z : ℂ) (u : CharacterTensor E χ) :
    (oddCharacterCycle χ c).representation z u = z • u := by
  have hz : c.representation (pointScalar z) = z • 1 := by
    rw [show pointScalar z = z • pointScalar 1 by rw [← map_smul, smul_eq_mul, mul_one],
      map_smul, h1]
  change interiorModuleTensorOperatorHom _ (c.representation (pointScalar z)) u = z • u
  rw [hz, map_smul, map_one]
  rfl

theorem oddCharacterIsometry_operator (u : CharacterTensor E χ) :
    characterIsometry χ ((oddCharacterCycle χ c).operator u) =
      KasparovDescent.operatorHom (scalarAction Γ) E c.operator (characterIsometry χ u) := by
  let V := (characterIsometry (E := E) χ).toContinuousLinearMap
  have h : V.comp (oddCharacterCycle χ c).operator.toCLM =
      (KasparovDescent.operatorHom (scalarAction Γ) E c.operator).toCLM.comp V := by
    apply characterTensor_clm_ext
    intro x d
    have hop : (oddCharacterCycle χ c).operator (interiorModuleTensorMk _ x d) =
        interiorModuleTensorMk _ (c.operator x) d :=
      interiorModuleTensorOperator_mk _ _ x d
    change characterIsometry χ ((oddCharacterCycle χ c).operator
        (interiorModuleTensorMk _ x d)) =
      KasparovDescent.operatorHom (scalarAction Γ) E c.operator
        (characterIsometry χ (interiorModuleTensorMk _ x d))
    refine (congrArg (characterIsometry χ) hop).trans ?_
    refine (characterIsometry_mk χ (c.operator x) d).trans ?_
    refine (KasparovDescent.operatorHom_mk (scalarAction Γ) E c.operator x _).symm.trans ?_
    exact congrArg (KasparovDescent.operatorHom (scalarAction Γ) E c.operator)
      (characterIsometry_mk χ x d).symm
  exact DFunLike.congr_fun h u

section Generic
variable (D : OddKasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
    (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (GroupCrossed Γ))
    (DescendedModule (Γ := Γ) E))
  (hp : ∀ x d, D.scalarSupportProjection (KasparovDescent.mk (scalarAction Γ) E x d) =
    KasparovDescent.mk (scalarAction Γ) E x (characterLeftMul χ d))

include hp in
theorem oddSupportEquiv_representation (h1 : c.representation (pointScalar 1) = 1)
    (z : ℂ) (u : CharacterTensor E χ) :
    characterRangeEquiv χ _ hp ((oddCharacterCycle χ c).representation z u) =
      D.scalarSupportRepresentation z (characterRangeEquiv χ _ hp u) := by
  refine Eq.trans ?_ (OddKasparovCycle.scalarSupportRepresentation_apply D z _).symm
  apply Subtype.ext
  refine (characterRangeEquiv_coe χ _ hp _).trans ?_
  refine (congrArg (characterIsometry χ) (oddCharacterCycle_representation χ c h1 z u)).trans ?_
  refine (map_smul _ z u).trans ?_
  rfl

include hp in
theorem oddSupportEquiv_operator
    (hF : ∀ v, D.operator v = KasparovDescent.operatorHom (scalarAction Γ) E c.operator v)
    (u : CharacterTensor E χ) :
    characterRangeEquiv χ _ hp ((oddCharacterCycle χ c).operator u) =
      D.scalarSupportCompression (characterRangeEquiv χ _ hp u) := by
  apply Subtype.ext
  refine (characterRangeEquiv_coe χ _ hp _).trans ?_
  refine Eq.trans ?_ (OddKasparovCycle.scalarSupportCompression_coe D _).symm
  have hv : D.scalarSupportProjection (characterIsometry χ u) = characterIsometry χ u :=
    projection_characterIsometry χ _ hp u
  have h2 : D.scalarSupportBlockOperator (characterIsometry χ u) =
      D.scalarSupportProjection (D.operator (characterIsometry χ u)) := by
    unfold OddKasparovCycle.scalarSupportBlockOperator
    simp only [AdjointableMap.coe_add_apply, AdjointableMap.mul_apply,
      AdjointableMap.coe_sub_apply, AdjointableMap.one_apply, hv, sub_self, map_zero, add_zero]
  refine Eq.trans ?_ h2.symm
  refine Eq.trans ?_ (congrArg D.scalarSupportProjection (hF _)).symm
  refine Eq.trans ?_ (congrArg D.scalarSupportProjection (oddCharacterIsometry_operator χ c u))
  exact (projection_characterIsometry χ _ hp _).symm

include hp in
theorem oddSupportEquiv_action (hact : ∀ g v, D.groupAction.action g v = v)
    (g : Unit) (u : CharacterTensor E χ) :
    characterRangeEquiv χ _ hp ((oddCharacterCycle χ c).groupAction.action g u) =
      D.scalarSupportGroupAction.action g (characterRangeEquiv χ _ hp u) := by
  apply Subtype.ext
  refine Eq.trans ?_ (OddKasparovCycle.scalarSupportGroupAction_coe D g _).symm
  exact (hact g _).symm

/-- The odd whole-cycle isomorphism onto the support cycle of `D`. -/
def oddSupportIso (h1 : c.representation (pointScalar 1) = 1)
    (hF : ∀ v, D.operator v = KasparovDescent.operatorHom (scalarAction Γ) E c.operator v)
    (hact : ∀ g v, D.groupAction.action g v = v) :
    OddKasparovCycleIso (oddCharacterCycle χ c) D.scalarSupportCycle where
  moduleEquiv := characterRangeEquiv χ _ hp
  action_intertwine := oddSupportEquiv_action χ c D hp hact
  representation_intertwine := oddSupportEquiv_representation χ c D hp h1
  operator_intertwine := oddSupportEquiv_operator χ c D hp hF

end Generic

/-- The odd whole-cycle isomorphism for the pulled-back descent. -/
def oddCharacterCycleIso
    (hU : ∀ g x, c.groupAction.action g x = (χ g : ℂ) • x)
    (h1 : c.representation (pointScalar 1) = 1) :
    OddKasparovCycleIso (oddCharacterCycle χ c) (oddPulledDescent c).scalarSupportCycle :=
  oddSupportIso χ c (oddPulledDescent c) (oddPulledDescent_support_mk χ c hU h1) h1
    (fun _ => rfl) (fun _ _ => rfl)

/-- Compressed descent, odd case. -/
theorem odd_compressedDescent
    (hU : ∀ g x, c.groupAction.action g x = (χ g : ℂ) • x)
    (h1 : c.representation (pointScalar 1) = 1) :
    sourcePullback.{0,0,0,0,0} (Γ := Unit) (A := ℂ)
        (B := ReducedCrossedProduct (pointAction Γ)) (C := GroupCrossed Γ)
        («α» := (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ))
        («β» := CStarAlgebraAction.trivial) («γ» := CStarAlgebraAction.trivial)
        true (FinitePointCutoff.averagingHom Γ) averagingHom_equivariant
        (KasparovDescent.oddClass (scalarAction Γ) (pointAction Γ)
          (OddKK.mk (BundledOddKasparovCycle.of c))) =
      GroupUniverseOrdinaryOdd.coefficientPushforward.{0,0,0} (characterHom Γ χ)
        (OddKK.mk (BundledOddKasparovCycle.of (oddPointScalarCycle c))) := by
  calc _ = OddKK.mk (BundledOddKasparovCycle.of (oddPulledDescent c)) := by
        rw [KasparovDescent.oddClass_mk, NativeSourcePullback.odd_mk]
        rfl
    _ = OddKK.mk (BundledOddKasparovCycle.of (oddPulledDescent c).scalarSupportCycle) :=
        OddKasparovCycle.scalarSupport_class _
    _ = OddKK.mk (BundledOddKasparovCycle.of (oddCharacterCycle χ c)) :=
        (OddKK.mk_eq_of_iso (oddCharacterCycleIso χ c hU h1)).symm
    _ = _ := (GroupUniverseOrdinaryOdd.coefficientPushforward_mk_coefficientTensor
        (oddPointScalarCycle c) (characterHom Γ χ)).symm

end OddCycle

end BC4lean.KKTheory.FinitePointCompressedDescent
