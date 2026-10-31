import BC4lean.GreenJulgCorrespondence
import BC4lean.CliffordOddEvenCornerCycle
import BC4lean.CliffordExternalEvenBalancedCompatibility
import BC4lean.GroupUniverseParityMapCoherence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Representatives of the product with a compact correspondence, and of Julg's inverse

Let `(F, V, φ)` be a `Γ`-equivariant correspondence from `B` to `C`, trivially graded, whose left
action `φ` is by compact operators, and let `[F] ∈ KK^Γ(B, C)` be the class of its zero-operator
cycle. This file identifies the product of a cycle with `[F]` with the tensor cycle, in both
parities:

* `rightEvenProduct_mk_even`: for an even cycle `c = (E, U, π, T)`,
  `[c] · [F] = [E ⊗_φ F, U ⊗ V, π ⊗ 1, T ⊗ 1]`. This is upstream's `tensorClass_eq_product`
  read through the even/graded bridge.
* `rightEvenProduct_mk_odd`: for an odd cycle `c = (E, U, π, T)`, the same formula in `KK^Γ_1`.
  The odd product is defined through the Clifford expansion of `c` and the external `Cl₁`
  extension of `[F]`. Upstream's `CliffordOddEvenCorner` extracts the odd cycle on `E ⊗_φ F`
  from any product operator `R`; we take `R = T̂ ⊗ 1`, which is a product operator because the
  second cycle has zero operator and compact left action
  (`isGradedKasparovProductOperator_of_zero_compact_second`). The extracted operator is the first
  corner of the transported `T̂ ⊗ 1`, which is `(T ⊗ 1)·(1 ⊗ J_F)`, and `J_F = 1` for a trivially
  graded `F`.

It also identifies the source pullback along an equivariant homomorphism `f` with
precomposition of the representation (`sourcePullback_mk_even`, `sourcePullback_mk_odd`).

Specialized to `ℓ²Γ` (`GreenJulgCorrespondence`), this gives the representative of Julg's
inverse on a cycle `d = (M, π, G)` over `ℂ ⋊_r Γ`, in both parities: inflate `d` to `Γ`, form
`M ⊗_{Cr} ℓ²Γ` with action `1 ⊗ ρ`, representation `π ∘ ev ⊗ 1` and operator `G ⊗ 1`
(`greenJulgInverse_mk_even`, `greenJulgInverse_mk_odd`). -/

noncomputable section
universe uΓ uA uB uC uE
namespace BC4lean.KKTheory.GreenJulgRepresentative
open scoped InnerProductSpace

/-! ## The product with a trivially graded compact correspondence -/

section Correspondence

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {C : Type uC} {F : Type uE} [Group Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F] [CompleteSpace F]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}
  (V : EquivariantHilbertModule γ F) (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
  (hφU : ModuleTensorRepresentationEquivariant φ β V)
  (hφcompact : ∀ b, IsModuleCompact (φ b)) (hF : IsCountablyGeneratedModule C F)

omit [StarOrderedRing C] [CompleteSpace F] in
/-- The action on `F` preserves the trivial grading. -/
theorem preservesGrading_trivial :
    V.PreservesGrading (GradedHilbertModule.trivial :
      GradedHilbertModule (CStarGrading.trivial : CStarGrading C) F) :=
  fun _ _ => rfl

omit [PartialOrder B] [StarOrderedRing B] [StarOrderedRing C] [CompleteSpace F] in
/-- The left action is even for the trivial gradings. -/
theorem representationGraded_trivial :
    ModuleTensorRepresentationGraded (δB := CStarGrading.trivial) φ
      (GradedHilbertModule.trivial : GradedHilbertModule (CStarGrading.trivial : CStarGrading C) F) :=
  fun _ _ => rfl

/-- The zero-operator cycle `(F, V, φ, 0)` of a trivially graded compact correspondence. -/
abbrev correspondenceCycle : GradedKasparovCycle β γ CStarGrading.trivial CStarGrading.trivial F :=
  GradedCompactCorrespondenceCycle.cycle β γ CStarGrading.trivial CStarGrading.trivial
    GradedHilbertModule.trivial V β.preservesGrading_trivial γ.preservesGrading_trivial
    (preservesGrading_trivial V) φ (representationGraded_trivial φ) hφU hφcompact hF

/-- Its class `[F] ∈ KK^Γ(B, C)`, through the even/graded bridge. -/
def correspondenceClass [TopologicalSpace.SeparableSpace C] :
    KasparovHomotopyClass.{uΓ, uB, uC, uE} β γ :=
  GroupUniverseEvenBridge.evenClass
    (GroupUniverseCompactCorrespondenceProduct.correspondenceClass β γ
      CStarGrading.trivial CStarGrading.trivial GradedHilbertModule.trivial V
      β.preservesGrading_trivial γ.preservesGrading_trivial (preservesGrading_trivial V) φ
      (representationGraded_trivial φ) hφU hφcompact hF)

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [CompleteSpace E]

/-! ### Even cycles -/

/-- The even tensor cycle `(E ⊗_φ F, U ⊗ V, π ⊗ 1, T ⊗ 1)`. -/
def evenTensorCycle (c : KasparovCycle α β E) :
    KasparovCycle α γ (InteriorModuleTensor (E := E) φ) :=
  (GradedMatrixMoritaCycle.tensorWithCompactLeftAction (GradedKasparovCycle.ofKasparovCycle c) γ
    CStarGrading.trivial GradedHilbertModule.trivial V γ.preservesGrading_trivial
    (preservesGrading_trivial V) φ (representationGraded_trivial φ) hφU hφcompact hF).toKasparovCycle

@[simp] theorem evenTensorCycle_operator (c : KasparovCycle α β E) :
    (evenTensorCycle V φ hφU hφcompact hF c).operator = interiorModuleTensorOperator φ c.operator :=
  rfl

@[simp] theorem evenTensorCycle_representation (c : KasparovCycle α β E) (a : A) :
    (evenTensorCycle V φ hφU hφcompact hF c).representation a =
      interiorModuleTensorOperator φ (c.representation a) :=
  rfl

@[simp] theorem evenTensorCycle_action (c : KasparovCycle α β E) (g : Γ)
    (z : InteriorModuleTensor (E := E) φ) :
    (evenTensorCycle V φ hφU hφcompact hF c).groupAction.action g z =
      (c.groupAction.interiorTensor V hφU).action g z :=
  rfl

/-- **Even product with `[F]`.** `[c] · [F]` is the class of the tensor cycle with operator
`T ⊗ 1`. -/
theorem rightEvenProduct_mk_even [Countable Γ] [TopologicalSpace.SeparableSpace A]
    [TopologicalSpace.SeparableSpace B] [TopologicalSpace.SeparableSpace C]
    (c : KasparovCycle α β E) :
    GroupUniverseParityUnits.rightEvenProduct false
        (KasparovHomotopyClass.mk (BundledKasparovCycle.of c))
        (correspondenceClass V φ hφU hφcompact hF) =
      KasparovHomotopyClass.mk (BundledKasparovCycle.of (evenTensorCycle V φ hφU hφcompact hF c)) := by
  have h := GroupUniverseCompactCorrespondenceProduct.tensorClass_eq_product β γ
    CStarGrading.trivial CStarGrading.trivial GradedHilbertModule.trivial V
    β.preservesGrading_trivial γ.preservesGrading_trivial (preservesGrading_trivial V) φ
    (representationGraded_trivial φ) hφU hφcompact hF (GradedKasparovCycle.ofKasparovCycle c)
  calc _ = GroupUniverseEvenBridge.evenClass (GroupUniverseProduct.product
        (GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of
          (GradedKasparovCycle.ofKasparovCycle c)))
        (GroupUniverseCompactCorrespondenceProduct.correspondenceClass β γ
          CStarGrading.trivial CStarGrading.trivial GradedHilbertModule.trivial V
          β.preservesGrading_trivial γ.preservesGrading_trivial (preservesGrading_trivial V) φ
          (representationGraded_trivial φ) hφU hφcompact hF)) := by
        change GroupUniverseEvenBridge.evenClass (GroupUniverseProduct.product
          (GroupUniverseEvenBridge.gradedClass (KasparovHomotopyClass.mk (BundledKasparovCycle.of c)))
          (GroupUniverseEvenBridge.gradedClass (correspondenceClass V φ hφU hφcompact hF))) = _
        rw [correspondenceClass, GroupUniverseEvenBridge.gradedClass_evenClass]
        rfl
    _ = _ := by rw [← h]; rfl

/-! ### Odd cycles -/

/-- The external `Cl₁` extension of the correspondence cycle; its operator is zero. -/
abbrev externalCycle := CliffordExternalEvenCycle.cycle (correspondenceCycle V φ hφU hφcompact hF)

omit [PartialOrder B] [StarOrderedRing B] in
theorem externalCycle_operator : (externalCycle V φ hφU hφcompact hF).operator = 0 := by
  change cliffordPairMap (0 : AdjointableMap C F F) 0 = 0
  exact cliffordPairMap_zero

omit [PartialOrder B] [StarOrderedRing B] in
theorem externalCycle_compact (b : B × B) :
    IsModuleCompact ((externalCycle V φ hφU hφcompact hF).representation b) := by
  have hhalf (b : B × B) : IsModuleCompact
      (CliffordExternalEvenCycle.half (correspondenceCycle V φ hφU hφcompact hF) b) := by
    rw [CliffordExternalEvenCycle.half, CliffordExternalEvenRepresentation.halfRepresentation_eq]
    exact ((hφcompact b.1).comp_right _).add ((hφcompact b.2).comp_right _)
  exact (hhalf b).cliffordPairMap (hhalf _)

/-- The product operator `T̂ ⊗ 1` on the tensor of the Clifford expansion of an odd cycle with
the external extension of `F`. -/
def oddProductOperator (c : OddKasparovCycle α β E) :
    AdjointableMap (C × C) (CliffordOddEvenCorner.Source (H := E) (correspondenceCycle V φ hφU hφcompact hF))
      (CliffordOddEvenCorner.Source (H := E) (correspondenceCycle V φ hφU hφcompact hF)) :=
  interiorModuleTensorOperator (externalCycle V φ hφU hφcompact hF).representation
    c.cliffordExpansion.operator

theorem oddProductOperator_isProduct (c : OddKasparovCycle α β E) :
    IsGradedKasparovProductOperator c.cliffordExpansion (externalCycle V φ hφU hφcompact hF)
      (oddProductOperator V φ hφU hφcompact hF c) :=
  isGradedKasparovProductOperator_of_zero_compact_second c.cliffordExpansion _
    (externalCycle_operator V φ hφU hφcompact hF) (externalCycle_compact V φ hφU hφcompact hF)

/-- The odd tensor cycle `(E ⊗_φ F, U ⊗ V, π ⊗ 1, T ⊗ 1)`: upstream's odd corner of the
odd-by-even product, for the product operator `T̂ ⊗ 1`. -/
def oddTensorCycle (c : OddKasparovCycle α β E) :
    OddKasparovCycle α γ (InteriorModuleTensor (E := E) φ) :=
  CliffordOddEvenCorner.cycle c (correspondenceCycle V φ hφU hφcompact hF)
    (oddProductOperator V φ hφU hφcompact hF c)
    (oddProductOperator_isProduct V φ hφU hφcompact hF c).cycleConditions

/-- For a trivially graded `F`, the tensor grading `1 ⊗ J_F` is the identity. -/
theorem tensorGrading_trivial (h : ∀ b, (GradedHilbertModule.trivial : GradedHilbertModule
      (CStarGrading.trivial : CStarGrading C) F).toAdjointable * φ b =
      φ b * (GradedHilbertModule.trivial : GradedHilbertModule
        (CStarGrading.trivial : CStarGrading C) F).toAdjointable) :
    (CliffordExternalEvenBalancedTensor.tensorGrading (H := E) φ GradedHilbertModule.trivial h).toAdjointable
      = 1 := by
  have hc : (CliffordExternalEvenBalancedTensor.tensorGrading (H := E) φ GradedHilbertModule.trivial
      h).grading.toContinuousLinearEquiv.toContinuousLinearMap = ContinuousLinearMap.id ℂ _ := by
    apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    intro x y
    exact CliffordExternalEvenBalancedTensor.tensorGrading_mk φ GradedHilbertModule.trivial h x y
  ext z
  exact DFunLike.congr_fun hc z

@[simp] theorem oddTensorCycle_operator (c : OddKasparovCycle α β E) :
    (oddTensorCycle V φ hφU hφcompact hF c).operator = interiorModuleTensorOperator φ c.operator := by
  have h := CliffordExternalEvenBalancedTensor.transport_signed_operator (H := E)
    (correspondenceCycle V φ hφU hφcompact hF).representation
    (correspondenceCycle V φ hφU hφcompact hF).grading
    (CliffordExternalEvenCycle.representation_commutes_grading _) c.operator
  rw [oddTensorCycle, CliffordOddEvenCorner.cycle_operator]
  refine (congrArg cliffordPairFirstCorner h).trans ?_
  rw [cliffordPairFirstCorner_pair]
  exact (congrArg (interiorModuleTensorOperator φ c.operator * ·) (tensorGrading_trivial φ _)).trans
    (mul_one _)

@[simp] theorem oddTensorCycle_representation (c : OddKasparovCycle α β E) (a : A) :
    (oddTensorCycle V φ hφU hφcompact hF c).representation a =
      interiorModuleTensorOperator φ (c.representation a) :=
  CliffordOddEvenCorner.cycle_representation c (correspondenceCycle V φ hφU hφcompact hF)
    (oddProductOperator V φ hφU hφcompact hF c)
    (oddProductOperator_isProduct V φ hφU hφcompact hF c).cycleConditions a

@[simp] theorem oddTensorCycle_action (c : OddKasparovCycle α β E) (g : Γ)
    (z : InteriorModuleTensor (E := E) φ) :
    (oddTensorCycle V φ hφU hφcompact hF c).groupAction.action g z =
      (c.groupAction.interiorTensor V hφU).action g z :=
  CliffordOddEvenCorner.cycle_action c (correspondenceCycle V φ hφU hφcompact hF)
    (oddProductOperator V φ hφU hφcompact hF c)
    (oddProductOperator_isProduct V φ hφU hφcompact hF c).cycleConditions g z

/-- **Odd product with `[F]`.** `[c] · [F]` is the class of the odd tensor cycle with operator
`T ⊗ 1`. -/
theorem rightEvenProduct_mk_odd [Countable Γ] [TopologicalSpace.SeparableSpace A]
    [TopologicalSpace.SeparableSpace B] [TopologicalSpace.SeparableSpace C]
    (c : OddKasparovCycle α β E) :
    GroupUniverseParityUnits.rightEvenProduct true
        (OddKK.mk (BundledOddKasparovCycle.of c))
        (correspondenceClass V φ hφU hφcompact hF) =
      OddKK.mk (BundledOddKasparovCycle.of (oddTensorCycle V φ hφU hφcompact hF c)) := by
  change GroupUniverseCliffordCoordinateBridge.oddClass (GroupUniverseProduct.product
    (GroupUniverseCliffordCoordinateBridge.gradedOddClass (OddKK.mk (BundledOddKasparovCycle.of c)))
    (GroupUniverseExternalEvenClass.externalClass (correspondenceClass V φ hφU hφcompact hF))) = _
  have hext : GroupUniverseExternalEvenClass.externalClass (correspondenceClass V φ hφU hφcompact hF) =
      GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of
        (externalCycle V φ hφU hφcompact hF)) := rfl
  rw [GroupUniverseCliffordCoordinateBridge.gradedOddClass_mk, hext,
    GroupUniverseProduct.product_mk_eq_of_isProduct (BundledOddKasparovCycle.of c).cliffordExpansion
      (BundledGradedKasparovCycle.of (externalCycle V φ hφU hφcompact hF))
      (oddProductOperator_isProduct V φ hφU hφcompact hF c)]
  change OddKK.mk (BundledOddKasparovCycle.of (cliffordExtractOddCycle true
      (CliffordOddEvenCorner.rawCycle c (correspondenceCycle V φ hφU hφcompact hF)
        (oddProductOperator V φ hφU hφcompact hF c)
        (oddProductOperator_isProduct V φ hφU hφcompact hF c).cycleConditions))) = _
  exact OddKK.mk_eq_of_iso (CliffordOddEvenCorner.extractionIso c
    (correspondenceCycle V φ hφU hφcompact hF) (oddProductOperator V φ hφU hφcompact hF c)
    (oddProductOperator_isProduct V φ hφU hφcompact hF c).cycleConditions)

end Correspondence

/-! ## Source pullback along an equivariant homomorphism

`GroupUniverseParityFunctoriality.sourcePullback p f` is defined as the left product with the class
of `f`. Upstream identifies it, through the graded bridges, with precomposition of the
representation (`sourcePullback_graded_even`, `sourcePullback_graded_odd`). We read this back on
cycles. -/

section Pullback

variable {Γ : Type uΓ} {A B C : Type} [Group Γ] [Countable Γ]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  [TopologicalSpace.SeparableSpace C]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B} {γ : CStarAlgebraAction Γ C}
  (f : A →⋆ₙₐ[ℂ] B) (hact : ∀ k a, f (α.automorphism k a) = β.automorphism k (f a))
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Cᵐᵒᵖ E] [CStarModule Cᵐᵒᵖ E]
  [CompleteSpace E]

/-- An even cycle with representation precomposed by `f`. -/
def evenSourcePullback (c : KasparovCycle β γ E) : KasparovCycle α γ E :=
  ((GradedKasparovCycle.ofKasparovCycle c).sourcePullback α CStarGrading.trivial
    α.preservesGrading_trivial f hact (fun _ => rfl)).toKasparovCycle

omit [Countable Γ] [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  [TopologicalSpace.SeparableSpace C] in
@[simp] theorem evenSourcePullback_operator (c : KasparovCycle β γ E) :
    (evenSourcePullback f hact c).operator = c.operator :=
  rfl

omit [Countable Γ] [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  [TopologicalSpace.SeparableSpace C] in
@[simp] theorem evenSourcePullback_representation (c : KasparovCycle β γ E) (a : A) :
    (evenSourcePullback f hact c).representation a = c.representation (f a) :=
  rfl

omit [PartialOrder A] [StarOrderedRing A] in
/-- **Even source pullback on cycles.** -/
theorem sourcePullback_mk_even (c : KasparovCycle β γ E) :
    GroupUniverseParityFunctoriality.sourcePullback.{uΓ, 0, 0, 0, 0} false f hact
        (KasparovHomotopyClass.mk (BundledKasparovCycle.of c)) =
      KasparovHomotopyClass.mk (BundledKasparovCycle.of (evenSourcePullback f hact c)) := by
  apply GroupUniverseEvenBridge.gradedClass_injective
  rw [GroupUniverseParityFunctoriality.sourcePullback_graded_even, GroupUniverseEvenBridge.gradedClass_mk,
    GroupUniverseEvenBridge.gradedClass_mk]
  change GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of
      ((GradedKasparovCycle.ofKasparovCycle c).sourcePullback α CStarGrading.trivial
        α.preservesGrading_trivial f hact (fun _ => rfl))) =
    GradedKasparovHomotopyClass.mk (BundledGradedKasparovCycle.of
      (GradedKasparovCycle.ofKasparovCycle (evenSourcePullback f hact c)))
  rw [evenSourcePullback, GradedKasparovCycle.ofKasparovCycle_toKasparovCycle]

/-- An odd cycle with representation precomposed by `f`. -/
def oddSourcePullback (c : OddKasparovCycle β γ E) : OddKasparovCycle α γ E where
  countablyGenerated := c.countablyGenerated
  groupAction := c.groupAction
  representation := c.representation.comp f
  representation_equivariant g a := by
    change c.groupAction.conjugateOperator g (c.representation (f a)) =
      c.representation (f (α.automorphism g a))
    rw [hact]
    exact c.representation_equivariant g (f a)
  operator := c.operator
  selfadjoint_mod_compact a := c.selfadjoint_mod_compact (f a)
  square_mod_compact a := c.square_mod_compact (f a)
  commutator_compact a := c.commutator_compact (f a)
  equivariance_mod_compact g a := c.equivariance_mod_compact g (f a)

omit [Countable Γ] [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  [TopologicalSpace.SeparableSpace C] in
@[simp] theorem oddSourcePullback_representation (c : OddKasparovCycle β γ E) (a : A) :
    (oddSourcePullback f hact c).representation a = c.representation (f a) :=
  rfl

omit [PartialOrder A] [StarOrderedRing A] in
/-- **Odd source pullback on cycles.** The Clifford expansion of the precomposed cycle is the
precomposed Clifford expansion, by the identity map. -/
theorem sourcePullback_mk_odd (c : OddKasparovCycle β γ E) :
    GroupUniverseParityFunctoriality.sourcePullback.{uΓ, 0, 0, 0, 0} true f hact
        (OddKK.mk (BundledOddKasparovCycle.of c)) =
      OddKK.mk (BundledOddKasparovCycle.of (oddSourcePullback f hact c)) := by
  apply GroupUniverseCliffordCoordinateBridge.gradedOddClass_injective
  rw [GroupUniverseParityFunctoriality.sourcePullback_graded_odd,
    GroupUniverseCliffordCoordinateBridge.gradedOddClass_mk,
    GroupUniverseCliffordCoordinateBridge.gradedOddClass_mk]
  change GradedKasparovHomotopyClass.mk ((BundledOddKasparovCycle.of c).cliffordExpansion.sourcePullback
      α CStarGrading.trivial α.preservesGrading_trivial f hact (fun _ => rfl)) = _
  exact GradedKasparovHomotopyClass.mk_eq_of_iso
    { moduleEquiv := HilbertModuleEquiv.refl
      grading_intertwine := fun _ => rfl
      action_intertwine := fun _ _ => rfl
      representation_intertwine := fun _ _ => rfl
      operator_intertwine := fun _ => rfl }

end Pullback

/-! ## The regular correspondence `ℓ²Γ` and Julg's inverse -/

section Regular

open GreenJulgCorrespondence BC4lean.Chapter8Examples
open scoped ZeroAtInfty ComplexOrder KasparovDescent

variable (Γ : Type) [Group Γ] [Countable Γ] [Finite Γ]

/-- `[ℓ²Γ]` is the class of the generic correspondence cycle. -/
theorem regularCorrespondenceClass_eq :
    regularCorrespondenceClass Γ = correspondenceClass (rightRegular Γ) (regularRep Γ)
      (regularRep_equivariant Γ) (regularRep_isModuleCompact Γ) (isCountablyGenerated Γ) :=
  rfl

variable {M : Type} [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul (Cr Γ)ᵐᵒᵖ M]
  [CStarModule (Cr Γ)ᵐᵒᵖ M] [CompleteSpace M]

/-- The inflation of an even cycle over the trivial group. -/
abbrev inflateEven (d : KasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
    (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (Cr Γ)) M) :
    KasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ (Cr Γ)) M :=
  d.comap (1 : Γ →* Unit) (fun _ _ => rfl) (fun _ _ => rfl)

/-- The inflation of an odd cycle over the trivial group. -/
abbrev inflateOdd (d : OddKasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
    (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (Cr Γ)) M) :
    OddKasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ (Cr Γ)) M :=
  d.comap (1 : Γ →* Unit) (fun _ _ => rfl) (fun _ _ => rfl)

/-- **Representative of `L_0`.** For an even cycle `d = (M, π, G)` over `ℂ ⋊_r Γ`,
`L_0 [d]` is the class of `(M ⊗_{Cr} ℓ²Γ, 1 ⊗ ρ, (π ∘ ev) ⊗ 1, G ⊗ 1)`. -/
theorem greenJulgInverse_mk_even
    (d : KasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (Cr Γ)) M) :
    greenJulgInverse Γ false (KasparovHomotopyClass.mk (BundledKasparovCycle.of d)) =
      KasparovHomotopyClass.mk (BundledKasparovCycle.of
        (evenSourcePullback pointEval (pointEval_equivariant Γ)
          (evenTensorCycle (rightRegular Γ) (regularRep Γ) (regularRep_equivariant Γ)
            (regularRep_isModuleCompact Γ) (isCountablyGenerated Γ) (inflateEven Γ d)))) := by
  change GroupUniverseParityFunctoriality.sourcePullback.{0} false pointEval (pointEval_equivariant Γ)
    (GroupUniverseParityUnits.rightEvenProduct false
      (KasparovHomotopyClass.mk (BundledKasparovCycle.of (inflateEven Γ d)))
      (regularCorrespondenceClass Γ)) = _
  rw [regularCorrespondenceClass_eq, rightEvenProduct_mk_even, sourcePullback_mk_even]

/-- **Representative of `L_1`.** For an odd cycle `d = (M, π, G)` over `ℂ ⋊_r Γ`,
`L_1 [d]` is the class of the odd cycle `(M ⊗_{Cr} ℓ²Γ, 1 ⊗ ρ, (π ∘ ev) ⊗ 1, G ⊗ 1)`. -/
theorem greenJulgInverse_mk_odd
    (d : OddKasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (Cr Γ)) M) :
    greenJulgInverse Γ true (OddKK.mk (BundledOddKasparovCycle.of d)) =
      OddKK.mk (BundledOddKasparovCycle.of
        (oddSourcePullback pointEval (pointEval_equivariant Γ)
          (oddTensorCycle (rightRegular Γ) (regularRep Γ) (regularRep_equivariant Γ)
            (regularRep_isModuleCompact Γ) (isCountablyGenerated Γ) (inflateOdd Γ d)))) := by
  change GroupUniverseParityFunctoriality.sourcePullback.{0} true pointEval (pointEval_equivariant Γ)
    (GroupUniverseParityUnits.rightEvenProduct true
      (OddKK.mk (BundledOddKasparovCycle.of (inflateOdd Γ d)))
      (regularCorrespondenceClass Γ)) = _
  rw [regularCorrespondenceClass_eq, rightEvenProduct_mk_odd, sourcePullback_mk_odd]

end Regular

end BC4lean.KKTheory.GreenJulgRepresentative
