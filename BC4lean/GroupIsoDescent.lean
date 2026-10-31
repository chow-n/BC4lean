import BC4lean.GroupIsoCrossedProduct
import BC4lean.ReducedCrossedLeftRegular
import BC4lean.InteriorModuleTensorScalarExtension
import BC4lean.StandardCoefficientImageTensor
import BC4lean.KasparovDescentReducedRepresentation
import BC4lean.KasparovDescentCycleIso
import BC4lean.GroupUniverseCoefficientPushforward
import BC4lean.GradedKasparovSourcePullback
import BC4lean.KKGroupRestriction
import BC4lean.GroupUniverseEvenBridge
import BC4lean.GroupUniverseParityMapCoherence
import BC4lean.KasparovDescentClass
import BC4lean.CliffordPairStandardTensor
import BC4lean.CliffordCycleIso
import BC4lean.GroupUniverseCliffordCoordinateBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Descent along a group isomorphism

For `e : Γ ≃* Γ'`, Kasparov descent commutes with restriction along `e` followed by the crossed-product
isomorphisms, on modules, operators, even classes and odd classes.
-/

noncomputable section

/-! ## Descended modules along a group isomorphism

Let `e : Γ ≃* Γ'`, let `β` be a `Γ'`-action on `B`, and let `Φ` be the crossed-product
isomorphism `B ⋊ᵣ (β ∘ e) Γ ≃ B ⋊ᵣ β Γ'`. For a right Hilbert
`B`-module `E`, the coefficient pushforward along `Φ` of the descended module of `β ∘ e`,
`(E ⊗_B (B ⋊ Γ)) ⊗_Φ (B ⋊ Γ')`, is unitarily isomorphic to the descended module
`E ⊗_B (B ⋊ Γ')` of `β`, by `(x ⊗ d) ⊗ y ↦ x ⊗ Φ(d) y`. This is BC4lean's
coefficient-extension unitary `InteriorModuleTensorScalarExtension.hilbertEquiv`; the only
new input is that `Φ` fixes the coefficient inclusion of `B`. The unitary intertwines
amplified operators `T ⊗ 1 ⊗ 1 ↦ T ⊗ 1` and, on pure tensors, the descended group operators
of `g` and of `e g`.
-/

namespace BC4lean.KKTheory.GroupIso
open KKTheory.GroupRestriction
open KKTheory KKTheory.KasparovDescent
open scoped InnerProductSpace KasparovDescent

section Generic
variable {B C E : Type*}
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

/-! The coefficient-extension unitary `InteriorModuleTensorScalarExtension.hilbertEquiv` for a module
`M` that equals the standard first-factor tensor, with instances equal to its instances. This is
upstream's device from `KasparovDescentTensorComparison` (private there, so restated): it lets the
module of a descended cycle be used without the elaborator unfolding its instances. -/

@[instance_reducible] private def canonicalFirstNormedAddCommGroup
    {D : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    (r : B →⋆ₙₐ[ℂ] AdjointableMap D Dᵐᵒᵖ Dᵐᵒᵖ) :
    NormedAddCommGroup (InteriorModuleTensor (E := E) r) :=
  inferInstance

@[instance_reducible] private def canonicalFirstNormedSpace
    {D : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    (r : B →⋆ₙₐ[ℂ] AdjointableMap D Dᵐᵒᵖ Dᵐᵒᵖ) :
    NormedSpace ℂ (InteriorModuleTensor (E := E) r) :=
  inferInstance

@[instance_reducible] private def canonicalFirstSMul
    {D : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    (r : B →⋆ₙₐ[ℂ] AdjointableMap D Dᵐᵒᵖ Dᵐᵒᵖ) :
    SMul Dᵐᵒᵖ (InteriorModuleTensor (E := E) r) :=
  inferInstance

@[instance_reducible] private def canonicalFirstCStarModule
    {D : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    (r : B →⋆ₙₐ[ℂ] AdjointableMap D Dᵐᵒᵖ Dᵐᵒᵖ) :
    CStarModule Dᵐᵒᵖ (InteriorModuleTensor (E := E) r) :=
  inferInstance

private theorem canonicalFirstCompleteSpace
    {D : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    (r : B →⋆ₙₐ[ℂ] AdjointableMap D Dᵐᵒᵖ Dᵐᵒᵖ) :
    CompleteSpace (InteriorModuleTensor (E := E) r) :=
  inferInstance

private def scalarExtensionEquiv
    {D H : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Cᵐᵒᵖ H]
    [CStarModule Cᵐᵒᵖ H] [CompleteSpace H]
    (i : B →⋆ₙₐ[ℂ] D)
    (r : B →⋆ₙₐ[ℂ] AdjointableMap D Dᵐᵒᵖ Dᵐᵒᵖ)
    (hr : r = InteriorModuleTensorScalarExtension.standardRepresentation i)
    (M : Type _) (hM : M = InteriorModuleTensor (E := E) r)
    (nM : NormedAddCommGroup M)
    (hnM : HEq nM (canonicalFirstNormedAddCommGroup (E := E) r))
    (vM : letI : NormedAddCommGroup M := nM; NormedSpace ℂ M)
    (hvM : HEq vM (canonicalFirstNormedSpace (E := E) r))
    (sM : SMul Dᵐᵒᵖ M)
    (hsM : HEq sM (canonicalFirstSMul (E := E) r))
    (mM : letI : NormedAddCommGroup M := nM;
      letI : NormedSpace ℂ M := vM;
      letI : SMul Dᵐᵒᵖ M := sM;
      CStarModule Dᵐᵒᵖ M)
    (hmM : HEq mM (canonicalFirstCStarModule (E := E) r))
    (qM : letI : NormedAddCommGroup M := nM; CompleteSpace M)
    (hqM : HEq qM (canonicalFirstCompleteSpace (E := E) r))
    (ρ : D →⋆ₙₐ[ℂ] AdjointableMap C H H)
    (ψ : B →⋆ₙₐ[ℂ] AdjointableMap C H H)
    (hρ : ∀ b, ρ (i b) = ψ b) :
    letI : NormedAddCommGroup M := nM;
    letI : NormedSpace ℂ M := vM;
    letI : SMul Dᵐᵒᵖ M := sM;
    letI : CStarModule Dᵐᵒᵖ M := mM;
    letI : CompleteSpace M := qM;
    HilbertModuleEquiv C
      (InteriorModuleTensor (E := M) ρ)
      (InteriorModuleTensor (E := E) ψ) := by
  subst M
  have hnM' : nM = canonicalFirstNormedAddCommGroup (E := E) r := eq_of_heq hnM
  subst nM
  have hvM' : vM = canonicalFirstNormedSpace (E := E) r := eq_of_heq hvM
  subst vM
  have hsM' : sM = canonicalFirstSMul (E := E) r := eq_of_heq hsM
  subst sM
  have hmM' : mM = canonicalFirstCStarModule (E := E) r := eq_of_heq hmM
  subst mM
  have hqM' : qM = canonicalFirstCompleteSpace (E := E) r := eq_of_heq hqM
  subst qM
  subst r
  exact InteriorModuleTensorScalarExtension.hilbertEquiv
    (B := B) (D := D) (C := C) (E := E) (H := H) i ρ ψ hρ

private theorem scalarExtensionEquiv_triple
    {D H : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Cᵐᵒᵖ H]
    [CStarModule Cᵐᵒᵖ H] [CompleteSpace H]
    (i : B →⋆ₙₐ[ℂ] D)
    (r : B →⋆ₙₐ[ℂ] AdjointableMap D Dᵐᵒᵖ Dᵐᵒᵖ)
    (hr : r = InteriorModuleTensorScalarExtension.standardRepresentation i)
    (M : Type _) (hM : M = InteriorModuleTensor (E := E) r)
    (nM : NormedAddCommGroup M)
    (hnM : HEq nM (canonicalFirstNormedAddCommGroup (E := E) r))
    (vM : letI : NormedAddCommGroup M := nM; NormedSpace ℂ M)
    (hvM : HEq vM (canonicalFirstNormedSpace (E := E) r))
    (sM : SMul Dᵐᵒᵖ M)
    (hsM : HEq sM (canonicalFirstSMul (E := E) r))
    (mM : letI : NormedAddCommGroup M := nM;
      letI : NormedSpace ℂ M := vM;
      letI : SMul Dᵐᵒᵖ M := sM;
      CStarModule Dᵐᵒᵖ M)
    (hmM : HEq mM (canonicalFirstCStarModule (E := E) r))
    (qM : letI : NormedAddCommGroup M := nM; CompleteSpace M)
    (hqM : HEq qM (canonicalFirstCompleteSpace (E := E) r))
    (ρ : D →⋆ₙₐ[ℂ] AdjointableMap C H H)
    (ψ : B →⋆ₙₐ[ℂ] AdjointableMap C H H)
    (hρ : ∀ b, ρ (i b) = ψ b)
    (x : E) (d : Dᵐᵒᵖ) (y : H) (u : M)
    (hu : HEq u (interiorModuleTensorMk (E := E) r x d)) :
    letI : NormedAddCommGroup M := nM;
    letI : NormedSpace ℂ M := vM;
    letI : SMul Dᵐᵒᵖ M := sM;
    letI : CStarModule Dᵐᵒᵖ M := mM;
    letI : CompleteSpace M := qM;
    scalarExtensionEquiv
        (B := B) (D := D) (C := C) (E := E) (H := H)
        i r hr M hM nM hnM vM hvM sM hsM mM hmM qM hqM ρ ψ hρ
        (interiorModuleTensorMk (E := M) ρ u y) =
      interiorModuleTensorMk (E := E) ψ x (ρ (MulOpposite.unop d) y) := by
  subst M
  have hnM' : nM = canonicalFirstNormedAddCommGroup (E := E) r := eq_of_heq hnM
  subst nM
  have hvM' : vM = canonicalFirstNormedSpace (E := E) r := eq_of_heq hvM
  subst vM
  have hsM' : sM = canonicalFirstSMul (E := E) r := eq_of_heq hsM
  subst sM
  have hmM' : mM = canonicalFirstCStarModule (E := E) r := eq_of_heq hmM
  subst mM
  have hqM' : qM = canonicalFirstCompleteSpace (E := E) r := eq_of_heq hqM
  subst qM
  subst r
  have hu' : u = interiorModuleTensorMk (E := E)
      (InteriorModuleTensorScalarExtension.standardRepresentation i) x d := eq_of_heq hu
  subst u
  exact InteriorModuleTensorScalarExtension.hilbertEquiv_triple
    (B := B) (D := D) (C := C) (E := E) (H := H) i ρ ψ hρ x d y

private theorem scalarExtensionEquiv_operator
    {D H : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Cᵐᵒᵖ H]
    [CStarModule Cᵐᵒᵖ H] [CompleteSpace H]
    (i : B →⋆ₙₐ[ℂ] D)
    (r : B →⋆ₙₐ[ℂ] AdjointableMap D Dᵐᵒᵖ Dᵐᵒᵖ)
    (hr : r = InteriorModuleTensorScalarExtension.standardRepresentation i)
    (M : Type _) (hM : M = InteriorModuleTensor (E := E) r)
    (nM : NormedAddCommGroup M)
    (hnM : HEq nM (canonicalFirstNormedAddCommGroup (E := E) r))
    (vM : letI : NormedAddCommGroup M := nM; NormedSpace ℂ M)
    (hvM : HEq vM (canonicalFirstNormedSpace (E := E) r))
    (sM : SMul Dᵐᵒᵖ M)
    (hsM : HEq sM (canonicalFirstSMul (E := E) r))
    (mM : letI : NormedAddCommGroup M := nM;
      letI : NormedSpace ℂ M := vM;
      letI : SMul Dᵐᵒᵖ M := sM;
      CStarModule Dᵐᵒᵖ M)
    (hmM : HEq mM (canonicalFirstCStarModule (E := E) r))
    (qM : letI : NormedAddCommGroup M := nM; CompleteSpace M)
    (hqM : HEq qM (canonicalFirstCompleteSpace (E := E) r))
    (ρ : D →⋆ₙₐ[ℂ] AdjointableMap C H H)
    (ψ : B →⋆ₙₐ[ℂ] AdjointableMap C H H)
    (hρ : ∀ b, ρ (i b) = ψ b)
    (T : AdjointableMap B E E)
    (S : letI : NormedAddCommGroup M := nM;
      letI : NormedSpace ℂ M := vM;
      letI : SMul Dᵐᵒᵖ M := sM;
      letI : CStarModule Dᵐᵒᵖ M := mM;
      letI : CompleteSpace M := qM;
      AdjointableMap D M M)
    (hS : HEq S (interiorModuleTensorOperator (E := E) r T))
    (u : letI : NormedAddCommGroup M := nM;
      letI : NormedSpace ℂ M := vM;
      letI : SMul Dᵐᵒᵖ M := sM;
      letI : CStarModule Dᵐᵒᵖ M := mM;
      letI : CompleteSpace M := qM;
      InteriorModuleTensor (E := M) ρ) :
    letI : NormedAddCommGroup M := nM;
    letI : NormedSpace ℂ M := vM;
    letI : SMul Dᵐᵒᵖ M := sM;
    letI : CStarModule Dᵐᵒᵖ M := mM;
    letI : CompleteSpace M := qM;
    scalarExtensionEquiv
        (B := B) (D := D) (C := C) (E := E) (H := H)
        i r hr M hM nM hnM vM hvM sM hsM mM hmM qM hqM ρ ψ hρ
        (interiorModuleTensorOperator (E := M) ρ S u) =
      interiorModuleTensorOperator (E := E) ψ T
        (scalarExtensionEquiv
        (B := B) (D := D) (C := C) (E := E) (H := H)
        i r hr M hM nM hnM vM hvM sM hsM mM hmM qM hqM ρ ψ hρ u) := by
  subst M
  have hnM' : nM = canonicalFirstNormedAddCommGroup (E := E) r := eq_of_heq hnM
  subst nM
  have hvM' : vM = canonicalFirstNormedSpace (E := E) r := eq_of_heq hvM
  subst vM
  have hsM' : sM = canonicalFirstSMul (E := E) r := eq_of_heq hsM
  subst sM
  have hmM' : mM = canonicalFirstCStarModule (E := E) r := eq_of_heq hmM
  subst mM
  have hqM' : qM = canonicalFirstCompleteSpace (E := E) r := eq_of_heq hqM
  subst qM
  subst r
  have hS' : S = interiorModuleTensorOperator (E := E)
      (InteriorModuleTensorScalarExtension.standardRepresentation i) T := eq_of_heq hS
  subst S
  exact InteriorModuleTensorScalarExtension.hilbertEquiv_operator
    (B := B) (D := D) (C := C) (E := E) (H := H) i ρ ψ hρ T u

end Generic

variable {Γ Γ' : Type*} [Group Γ] [Group Γ'] (e : Γ ≃* Γ')
  {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  (β : CStarAlgebraAction Γ' B)

variable [Countable Γ] [Countable Γ'] [TopologicalSpace.SeparableSpace B]

/-- The coefficient representation of the standard homomorphism cycle of `Φ`, the cycle that
`GroupUniverseCoefficientPushforward.coefficientPushforward` multiplies by. -/
abbrev homRepresentation :
    ReducedCrossedProduct (actionComap e.toMonoidHom β) →⋆ₙₐ[ℂ]
      AdjointableMap (ReducedCrossedProduct β) (ReducedCrossedProduct β)ᵐᵒᵖ
        (ReducedCrossedProduct β)ᵐᵒᵖ :=
  (gradedStandardModuleHomCycle
    (CStarAlgebraAction.trivial : CStarAlgebraAction Unit
      (ReducedCrossedProduct (actionComap e.toMonoidHom β)))
    (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct β))
    CStarGrading.trivial CStarGrading.trivial
    (CStarAlgebraAction.preservesGrading_trivial _) (CStarAlgebraAction.preservesGrading_trivial _)
    (crossedProductHom e β) (fun _ _ => rfl) (fun _ => rfl)).representation

omit [Countable Γ] in
theorem homRepresentation_coefficient (b : B) :
    homRepresentation e β (coefficientToReducedCrossed (actionComap e.toMonoidHom β) b) =
      coefficientRepresentation β b :=
  crossedProductHom_coefficient e β b

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

/-- The pushed-forward descended module of `β ∘ e`: the module of the compact-second product of
the descended cycle with the homomorphism cycle of `Φ`. -/
abbrev PushedModule :=
  InteriorModuleTensor (E := Module (actionComap e.toMonoidHom β) E) (homRepresentation e β)

omit [Countable Γ] in
/-- `homRepresentation` is left multiplication by `Φ`. -/
theorem homRepresentation_apply (c : ReducedCrossedProduct (actionComap e.toMonoidHom β))
    (y : (ReducedCrossedProduct β)ᵐᵒᵖ) :
    homRepresentation e β c y = MulOpposite.op (crossedProductEquiv e β c * MulOpposite.unop y) :=
  rfl

/-- The unitary `(x ⊗ d) ⊗ y ↦ x ⊗ Φ(d) y`. -/
def descentModuleEquiv :
    HilbertModuleEquiv (ReducedCrossedProduct β) (PushedModule e β E) (Module β E) :=
  scalarExtensionEquiv (B := B) (D := ReducedCrossedProduct (actionComap e.toMonoidHom β)) (C := ReducedCrossedProduct β)
    (E := E) (H := (ReducedCrossedProduct β)ᵐᵒᵖ)
    (coefficientToReducedCrossed (actionComap e.toMonoidHom β)) (coefficientRepresentation (actionComap e.toMonoidHom β)) rfl
    (Module (actionComap e.toMonoidHom β) E) rfl
    (inferInstance : NormedAddCommGroup (Module (actionComap e.toMonoidHom β) E)) HEq.rfl
    (inferInstance : NormedSpace ℂ (Module (actionComap e.toMonoidHom β) E)) HEq.rfl
    (inferInstance : SMul (ReducedCrossedProduct (actionComap e.toMonoidHom β))ᵐᵒᵖ (Module (actionComap e.toMonoidHom β) E)) HEq.rfl
    (inferInstance : CStarModule (ReducedCrossedProduct (actionComap e.toMonoidHom β))ᵐᵒᵖ (Module (actionComap e.toMonoidHom β) E)) HEq.rfl
    (inferInstance : CompleteSpace (Module (actionComap e.toMonoidHom β) E)) HEq.rfl
    (homRepresentation e β) (coefficientRepresentation β) (homRepresentation_coefficient e β)

omit [Countable Γ] in
theorem descentModuleEquiv_triple (x : E)
    (d : (ReducedCrossedProduct (actionComap e.toMonoidHom β))ᵐᵒᵖ)
    (y : (ReducedCrossedProduct β)ᵐᵒᵖ) :
    descentModuleEquiv e β E
        (interiorModuleTensorMk (homRepresentation e β) (mk (actionComap e.toMonoidHom β) E x d) y) =
      mk β E x (MulOpposite.op
        (crossedProductEquiv e β (MulOpposite.unop d) * MulOpposite.unop y)) := by
  have h : descentModuleEquiv e β E
        (interiorModuleTensorMk (homRepresentation e β) (mk (actionComap e.toMonoidHom β) E x d) y) =
      interiorModuleTensorMk (coefficientRepresentation β) x
        (homRepresentation e β (MulOpposite.unop d) y) :=
    scalarExtensionEquiv_triple (B := B) (D := ReducedCrossedProduct (actionComap e.toMonoidHom β)) (C := ReducedCrossedProduct β)
    (E := E) (H := (ReducedCrossedProduct β)ᵐᵒᵖ)
    (coefficientToReducedCrossed (actionComap e.toMonoidHom β)) (coefficientRepresentation (actionComap e.toMonoidHom β)) rfl
    (Module (actionComap e.toMonoidHom β) E) rfl
    (inferInstance : NormedAddCommGroup (Module (actionComap e.toMonoidHom β) E)) HEq.rfl
    (inferInstance : NormedSpace ℂ (Module (actionComap e.toMonoidHom β) E)) HEq.rfl
    (inferInstance : SMul (ReducedCrossedProduct (actionComap e.toMonoidHom β))ᵐᵒᵖ (Module (actionComap e.toMonoidHom β) E)) HEq.rfl
    (inferInstance : CStarModule (ReducedCrossedProduct (actionComap e.toMonoidHom β))ᵐᵒᵖ (Module (actionComap e.toMonoidHom β) E)) HEq.rfl
    (inferInstance : CompleteSpace (Module (actionComap e.toMonoidHom β) E)) HEq.rfl
    (homRepresentation e β) (coefficientRepresentation β) (homRepresentation_coefficient e β) x d y (mk (actionComap e.toMonoidHom β) E x d) HEq.rfl
  rw [h]
  exact congrArg (interiorModuleTensorMk (coefficientRepresentation β) x)
    (homRepresentation_apply e β (MulOpposite.unop d) y)

omit [Countable Γ] in
theorem descentModuleEquiv_operator (T : AdjointableMap B E E) (u : PushedModule e β E) :
    descentModuleEquiv e β E
        (interiorModuleTensorOperator (homRepresentation e β)
          (operatorHom (actionComap e.toMonoidHom β) E T) u) =
      operatorHom β E T (descentModuleEquiv e β E u) :=
  scalarExtensionEquiv_operator (B := B) (D := ReducedCrossedProduct (actionComap e.toMonoidHom β)) (C := ReducedCrossedProduct β)
    (E := E) (H := (ReducedCrossedProduct β)ᵐᵒᵖ)
    (coefficientToReducedCrossed (actionComap e.toMonoidHom β)) (coefficientRepresentation (actionComap e.toMonoidHom β)) rfl
    (Module (actionComap e.toMonoidHom β) E) rfl
    (inferInstance : NormedAddCommGroup (Module (actionComap e.toMonoidHom β) E)) HEq.rfl
    (inferInstance : NormedSpace ℂ (Module (actionComap e.toMonoidHom β) E)) HEq.rfl
    (inferInstance : SMul (ReducedCrossedProduct (actionComap e.toMonoidHom β))ᵐᵒᵖ (Module (actionComap e.toMonoidHom β) E)) HEq.rfl
    (inferInstance : CStarModule (ReducedCrossedProduct (actionComap e.toMonoidHom β))ᵐᵒᵖ (Module (actionComap e.toMonoidHom β) E)) HEq.rfl
    (inferInstance : CompleteSpace (Module (actionComap e.toMonoidHom β) E)) HEq.rfl
    (homRepresentation e β) (coefficientRepresentation β) (homRepresentation_coefficient e β)
    T (operatorHom (actionComap e.toMonoidHom β) E T) HEq.rfl u

omit [Countable Γ] in
/-- Continuous linear maps out of the pushed module agree once they agree on triples
`(x ⊗ d) ⊗ y`. -/
theorem pushed_clm_ext {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    {L R : PushedModule e β E →L[ℂ] P}
    (h : ∀ x d y,
      L (interiorModuleTensorMk (homRepresentation e β) (mk (actionComap e.toMonoidHom β) E x d) y) =
        R (interiorModuleTensorMk (homRepresentation e β)
          (mk (actionComap e.toMonoidHom β) E x d) y)) :
    L = R := by
  apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
  intro z y
  have hz := ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
    (f := L.comp (InteriorModuleTensorScalarExtension.pureCLM
      (E := Module (actionComap e.toMonoidHom β) E) (homRepresentation e β) y))
    (g := R.comp (InteriorModuleTensorScalarExtension.pureCLM
      (E := Module (actionComap e.toMonoidHom β) E) (homRepresentation e β) y))
    (fun x d => h x d y)
  exact DFunLike.congr_fun hz z

omit [Countable Γ] in
/-- Continuous linear maps intertwine through the unitary once they do so on triples
`(x ⊗ d) ⊗ y`. Stated for abstract `S`, `S'` so that each use only checks triples. -/
theorem descentModuleEquiv_intertwine (S : PushedModule e β E →L[ℂ] PushedModule e β E)
    (S' : Module β E →L[ℂ] Module β E)
    (h : ∀ x d y,
      descentModuleEquiv e β E
          (S (interiorModuleTensorMk (homRepresentation e β)
            (mk (actionComap e.toMonoidHom β) E x d) y)) =
        S' (descentModuleEquiv e β E (interiorModuleTensorMk (homRepresentation e β)
            (mk (actionComap e.toMonoidHom β) E x d) y)))
    (u : PushedModule e β E) :
    descentModuleEquiv e β E (S u) = S' (descentModuleEquiv e β E u) := by
  let V : PushedModule e β E →L[ℂ] Module β E :=
    (descentModuleEquiv e β E).linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have hV : V.comp S = S'.comp V := pushed_clm_ext e β E h
  exact DFunLike.congr_fun hV u

end BC4lean.KKTheory.GroupIso

/-! ## Descended operators along a group isomorphism

The unitary `descentModuleEquiv` intertwines, for `e : Γ ≃* Γ'`:
the descended group operator of `g` with that of `e g`; the descended gradings; and the descended
source representations of `A ⋊ᵣ (α ∘ e) Γ` and `A ⋊ᵣ α Γ'` across `Φ_A`. Each is checked on
triples `(x ⊗ d) ⊗ y` and extended by `descentModuleEquiv_intertwine`; the source representation
is then extended from finite generators by density. Together they give `evenDescentIso`, the
cycle isomorphism behind the even class-level statement.
-/

namespace BC4lean.KKTheory.GroupIso
open KKTheory.GroupRestriction
open KKTheory KKTheory.KasparovDescent

/- The proofs below avoid `rw` on goals containing `descentModuleEquiv e β E (…)`: each `rw` there
timed out in `whnf` (2026-10-31, check-descent-ops.log). Instead every step is an upstream lemma
applied to explicit arguments and glued with `congrArg`/`Eq.trans`; facts that only need abstract
coefficient algebras are proved generically first. -/

section Generic
variable {B C E F : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Cᵐᵒᵖ F] [CStarModule Cᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]

/-- `T ↦ T ⊗ 1` is `1`-Lipschitz. -/
theorem interiorModuleTensorOperatorHom_lipschitz (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) :
    LipschitzWith 1 (interiorModuleTensorOperatorHom (E := E) φ) := by
  refine LipschitzWith.of_dist_le_mul fun S T => ?_
  have h : ‖interiorModuleTensorOperatorHom (E := E) φ (S - T)‖ ≤ ‖S - T‖ := by
    rw [interiorModuleTensorOperatorHom_apply]
    exact interiorModuleTensorOperator_norm_le φ (S - T)
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, NNReal.coe_one, one_mul]
  exact h

/-- Applying `R w ⊗ 1` to a fixed vector is continuous in `w` when `R` is. -/
theorem continuous_interiorModuleTensorOperator_apply {X : Type*} [TopologicalSpace X]
    (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F) {R : X → AdjointableMap B E E} (hR : Continuous R)
    (u : InteriorModuleTensor (E := E) φ) :
    Continuous (fun w => interiorModuleTensorOperator φ (R w) u) :=
  (AdjointableMap.toCLM_isometry.continuous.comp
    ((interiorModuleTensorOperatorHom_lipschitz φ).continuous.comp hR)).clm_apply continuous_const

theorem interiorModuleTensorOperator_add (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (S T : AdjointableMap B E E) (u : InteriorModuleTensor (E := E) φ) :
    interiorModuleTensorOperator φ (S + T) u =
      interiorModuleTensorOperator φ S u + interiorModuleTensorOperator φ T u := by
  rw [← interiorModuleTensorOperatorHom_apply, map_add]
  rfl

theorem interiorModuleTensorOperator_zero (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (u : InteriorModuleTensor (E := E) φ) :
    interiorModuleTensorOperator φ (0 : AdjointableMap B E E) u = 0 := by
  rw [← interiorModuleTensorOperatorHom_apply, map_zero]
  rfl

theorem interiorModuleTensorOperator_neg (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (T : AdjointableMap B E E) (u : InteriorModuleTensor (E := E) φ) :
    interiorModuleTensorOperator φ (-T) u = -interiorModuleTensorOperator φ T u := by
  rw [← interiorModuleTensorOperatorHom_apply, map_neg]
  exact AdjointableMap.coe_neg_apply _ _

theorem interiorModuleTensorOperator_mul_apply (φ : B →⋆ₙₐ[ℂ] AdjointableMap C F F)
    (S T : AdjointableMap B E E) (u : InteriorModuleTensor (E := E) φ) :
    interiorModuleTensorOperator φ (S * T) u =
      interiorModuleTensorOperator φ S (interiorModuleTensorOperator φ T u) := by
  rw [interiorModuleTensorOperator_mul]
  rfl

end Generic

section GenericDescent
variable {Γ₀ A₀ B₀ : Type*} [Group Γ₀] [Countable Γ₀]
  [NonUnitalCStarAlgebra A₀] [NonUnitalCStarAlgebra B₀] [PartialOrder B₀] [StarOrderedRing B₀]
  [TopologicalSpace.SeparableSpace B₀]
  (β₀ : CStarAlgebraAction Γ₀ B₀)
  (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul B₀ᵐᵒᵖ E]
  [CStarModule B₀ᵐᵒᵖ E] [CompleteSpace E]

omit [Countable Γ₀] [TopologicalSpace.SeparableSpace B₀] in
theorem sourceGenerator_eq (U : EquivariantHilbertModule β₀ E)
    (π : A₀ →⋆ₙₐ[ℂ] AdjointableMap B₀ E E) (a : A₀) (g : Γ₀) :
    sourceGenerator β₀ E U π a g = operatorHom β₀ E (π a) * groupOperator β₀ E U g := rfl

end GenericDescent

variable {Γ Γ' : Type*} [Group Γ] [Group Γ'] (e : Γ ≃* Γ')
  {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  (β : CStarAlgebraAction Γ' B)

theorem leftRegular_mul (g : Γ') (c d : ReducedCrossedProduct β) :
    KasparovDescent.leftRegular β g c * d = KasparovDescent.leftRegular β g (c * d) := by
  apply Subtype.ext
  simp only [NonUnitalStarSubalgebra.coe_mul, leftRegular_coe,
    mul_assoc]

variable [Countable Γ] [Countable Γ'] [TopologicalSpace.SeparableSpace B]
  (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

omit [Countable Γ] in
/-- Descended group operators on triples. -/
theorem descentModuleEquiv_groupOperator_triple (U : EquivariantHilbertModule β E) (g : Γ)
    (x : E) (d : (ReducedCrossedProduct (actionComap e.toMonoidHom β))ᵐᵒᵖ)
    (y : (ReducedCrossedProduct β)ᵐᵒᵖ) :
    descentModuleEquiv e β E
        (interiorModuleTensorOperator (homRepresentation e β)
          (groupOperator (actionComap e.toMonoidHom β) E (moduleComap e.toMonoidHom U) g)
          (interiorModuleTensorMk (homRepresentation e β)
            (mk (actionComap e.toMonoidHom β) E x d) y)) =
      groupOperator β E U (e g) (descentModuleEquiv e β E
        (interiorModuleTensorMk (homRepresentation e β)
          (mk (actionComap e.toMonoidHom β) E x d) y)) := by
  have h1 := interiorModuleTensorOperator_mk (homRepresentation e β)
    (groupOperator (actionComap e.toMonoidHom β) E (moduleComap e.toMonoidHom U) g)
    (mk (actionComap e.toMonoidHom β) E x d) y
  have h2 := groupOperator_mk (actionComap e.toMonoidHom β) E (moduleComap e.toMonoidHom U) g x d
  have h3 := descentModuleEquiv_triple e β E ((moduleComap e.toMonoidHom U).action g x)
    (MulOpposite.op (KasparovDescent.leftRegular (actionComap e.toMonoidHom β) g (MulOpposite.unop d))) y
  have h4 := descentModuleEquiv_triple e β E x d y
  have h5 := groupOperator_mk β E U (e g) x
    (MulOpposite.op (crossedProductEquiv e β (MulOpposite.unop d) * MulOpposite.unop y))
  have h6 : crossedProductEquiv e β
        (KasparovDescent.leftRegular (actionComap e.toMonoidHom β) g (MulOpposite.unop d)) * MulOpposite.unop y =
      KasparovDescent.leftRegular β (e g) (crossedProductEquiv e β (MulOpposite.unop d) * MulOpposite.unop y) := by
    rw [crossedProductEquiv_leftRegular, leftRegular_mul]
  have h7 : (moduleComap e.toMonoidHom U).action g x = U.action (e g) x := rfl
  refine (congrArg (fun w => descentModuleEquiv e β E w)
    (h1.trans (congrArg (fun w => interiorModuleTensorMk (homRepresentation e β) w y) h2))).trans ?_
  refine h3.trans ?_
  refine Eq.trans ?_ ((congrArg (fun w => groupOperator β E U (e g) w) h4).trans h5).symm
  rw [h7, MulOpposite.unop_op, h6]
  rfl

omit [Countable Γ] in
/-- Descended group operators: `g` on the `Γ` side becomes `e g`, on the whole module. The
`Γ`-module structure on `E` is the restriction of the `Γ'`-module structure `U`. -/
theorem descentModuleEquiv_groupOperator (U : EquivariantHilbertModule β E) (g : Γ)
    (u : PushedModule e β E) :
    descentModuleEquiv e β E
        (interiorModuleTensorOperator (homRepresentation e β)
          (groupOperator (actionComap e.toMonoidHom β) E (moduleComap e.toMonoidHom U) g) u) =
      groupOperator β E U (e g) (descentModuleEquiv e β E u) :=
  descentModuleEquiv_intertwine e β E
    (interiorModuleTensorOperator (homRepresentation e β)
      (groupOperator (actionComap e.toMonoidHom β) E (moduleComap e.toMonoidHom U) g)).toCLM
    (groupOperator β E U (e g)).toCLM
    (descentModuleEquiv_groupOperator_triple e β E U g) u

omit [Countable Γ] in
/-- Gradings on triples. -/
theorem descentModuleEquiv_grading_triple
    (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) E)
    (hφ : ModuleTensorRepresentationGraded (δB := CStarGrading.trivial) (homRepresentation e β)
      (GradedHilbertModule.standard (CStarGrading.trivial : CStarGrading (ReducedCrossedProduct β))))
    (x : E) (d : (ReducedCrossedProduct (actionComap e.toMonoidHom β))ᵐᵒᵖ)
    (y : (ReducedCrossedProduct β)ᵐᵒᵖ) :
    descentModuleEquiv e β E
        (((ordinaryModuleGrading (actionComap e.toMonoidHom β) J).interiorTensor
          (GradedHilbertModule.standard CStarGrading.trivial) hφ).grading
          (interiorModuleTensorMk (homRepresentation e β)
            (mk (actionComap e.toMonoidHom β) E x d) y)) =
      (ordinaryModuleGrading β J).grading (descentModuleEquiv e β E
        (interiorModuleTensorMk (homRepresentation e β)
          (mk (actionComap e.toMonoidHom β) E x d) y)) := by
  have h1 := GradedHilbertModule.interiorTensor_grading_mk
    (ordinaryModuleGrading (actionComap e.toMonoidHom β) J)
    (GradedHilbertModule.standard (CStarGrading.trivial : CStarGrading (ReducedCrossedProduct β)))
    hφ (mk (actionComap e.toMonoidHom β) E x d) y
  have h2 := ordinaryModuleGrading_mk (actionComap e.toMonoidHom β) J x d
  have h2' : (GradedHilbertModule.standard
      (CStarGrading.trivial : CStarGrading (ReducedCrossedProduct β))).grading y = y := by
    rw [GradedHilbertModule.standard_grading_apply, CStarGrading.trivial_apply, MulOpposite.op_unop]
  have h3 := descentModuleEquiv_triple e β E (J.grading x) d y
  have h4 := descentModuleEquiv_triple e β E x d y
  have h5 := ordinaryModuleGrading_mk β J x
    (MulOpposite.op (crossedProductEquiv e β (MulOpposite.unop d) * MulOpposite.unop y))
  refine (congrArg (fun w => descentModuleEquiv e β E w)
    (h1.trans (congrArg₂ (fun w v => interiorModuleTensorMk (homRepresentation e β) w v)
      h2 h2'))).trans ?_
  exact h3.trans ((congrArg (fun w => (ordinaryModuleGrading β J).grading w) h4).trans h5).symm

omit [Countable Γ] in
/-- The grading of the compact-second product module is carried to the descended grading. -/
theorem descentModuleEquiv_grading
    (J : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) E)
    (hφ : ModuleTensorRepresentationGraded (δB := CStarGrading.trivial) (homRepresentation e β)
      (GradedHilbertModule.standard (CStarGrading.trivial : CStarGrading (ReducedCrossedProduct β))))
    (u : PushedModule e β E) :
    descentModuleEquiv e β E
        (((ordinaryModuleGrading (actionComap e.toMonoidHom β) J).interiorTensor
          (GradedHilbertModule.standard CStarGrading.trivial) hφ).grading u) =
      (ordinaryModuleGrading β J).grading (descentModuleEquiv e β E u) :=
  descentModuleEquiv_intertwine e β E
    (((ordinaryModuleGrading (actionComap e.toMonoidHom β) J).interiorTensor
      (GradedHilbertModule.standard CStarGrading.trivial) hφ).grading.toContinuousLinearEquiv.toContinuousLinearMap)
    ((ordinaryModuleGrading β J).grading.toContinuousLinearEquiv.toContinuousLinearMap)
    (descentModuleEquiv_grading_triple e β E J hφ) u

section Source
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (α : CStarAlgebraAction Γ' A)

omit [Countable Γ] [Countable Γ'] in
theorem continuous_crossedProductEquiv : Continuous (crossedProductEquiv e α) :=
  ((crossedConj_continuous (B := A) e).comp continuous_subtype_val).subtype_mk
    (fun w => crossedConj_mem e α w.1 w.2)

omit [PartialOrder A] [StarOrderedRing A] [Countable Γ] in
/-- The source generators `π(a) u_g` correspond: `g` on the `Γ` side becomes `e g`. -/
theorem descentModuleEquiv_sourceGenerator (U : EquivariantHilbertModule β E)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap B E E) (a : A) (g : Γ) (u : PushedModule e β E) :
    descentModuleEquiv e β E (interiorModuleTensorOperator (homRepresentation e β)
        (operatorHom (actionComap e.toMonoidHom β) E (π a) *
          groupOperator (actionComap e.toMonoidHom β) E (moduleComap e.toMonoidHom U) g) u) =
      operatorHom β E (π a) (groupOperator β E U (e g) (descentModuleEquiv e β E u)) := by
  have h1 := interiorModuleTensorOperator_mul_apply (homRepresentation e β)
    (operatorHom (actionComap e.toMonoidHom β) E (π a))
    (groupOperator (actionComap e.toMonoidHom β) E (moduleComap e.toMonoidHom U) g) u
  have h2 := descentModuleEquiv_operator e β E (π a)
    (interiorModuleTensorOperator (homRepresentation e β)
      (groupOperator (actionComap e.toMonoidHom β) E (moduleComap e.toMonoidHom U) g) u)
  have h3 := descentModuleEquiv_groupOperator e β E U g u
  exact (congrArg (fun w => descentModuleEquiv e β E w) h1).trans
    (h2.trans (congrArg (fun w => operatorHom β E (π a) w) h3))

omit [Countable Γ] in
/-- `descentModuleEquiv_reducedSourceRepresentation` at `0`. -/
theorem descentModuleEquiv_reducedSource_zero (U : EquivariantHilbertModule β E)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap B E E)
    (hπ : ∀ g a, U.conjugateOperator g (π a) = π (α.automorphism g a))
    (hπ' : ∀ g a, (moduleComap e.toMonoidHom U).conjugateOperator g (π a) =
      π ((actionComap e.toMonoidHom α).automorphism g a))
    (u : PushedModule e β E) :
    descentModuleEquiv e β E (interiorModuleTensorOperator (homRepresentation e β)
        (reducedSourceRepresentation (actionComap e.toMonoidHom β) E (actionComap e.toMonoidHom α)
          (moduleComap e.toMonoidHom U) π hπ' (algebraicToReducedCrossed (actionComap e.toMonoidHom α) 0)) u) =
      reducedSourceRepresentation β E α U π hπ (crossedProductEquiv e α (algebraicToReducedCrossed (actionComap e.toMonoidHom α) 0))
        (descentModuleEquiv e β E u) := by
  have z1 : reducedSourceRepresentation (actionComap e.toMonoidHom β) E
      (actionComap e.toMonoidHom α) (moduleComap e.toMonoidHom U) π hπ'
      (algebraicToReducedCrossed (actionComap e.toMonoidHom α) 0) = 0 :=
    (congrArg (reducedSourceRepresentation (actionComap e.toMonoidHom β) E
      (actionComap e.toMonoidHom α) (moduleComap e.toMonoidHom U) π hπ')
      (map_zero (algebraicToReducedCrossed (actionComap e.toMonoidHom α)))).trans
      (map_zero (reducedSourceRepresentation (actionComap e.toMonoidHom β) E
      (actionComap e.toMonoidHom α) (moduleComap e.toMonoidHom U) π hπ'))
  have z2 : reducedSourceRepresentation β E α U π hπ
      (crossedProductEquiv e α (algebraicToReducedCrossed (actionComap e.toMonoidHom α) 0)) =
        0 :=
    (congrArg (fun w => reducedSourceRepresentation β E α U π hπ (crossedProductEquiv e α w))
      (map_zero (algebraicToReducedCrossed (actionComap e.toMonoidHom α)))).trans
    ((congrArg (reducedSourceRepresentation β E α U π hπ) (map_zero (crossedProductEquiv e α))).trans
      (map_zero (reducedSourceRepresentation β E α U π hπ)))
  refine (congrArg (fun T => descentModuleEquiv e β E
    (interiorModuleTensorOperator (homRepresentation e β) T u)) z1).trans ?_
  refine (congrArg (fun w => descentModuleEquiv e β E w)
    (interiorModuleTensorOperator_zero (homRepresentation e β) u)).trans ?_
  refine (map_zero (descentModuleEquiv e β E).linearIsometryEquiv).trans ?_
  exact ((congrArg (fun T => T (descentModuleEquiv e β E u)) z2).trans
    (AdjointableMap.coe_zero_apply _)).symm

omit [Countable Γ] in
/-- `descentModuleEquiv_reducedSourceRepresentation` on a generator `a u_g`. -/
theorem descentModuleEquiv_reducedSource_single (U : EquivariantHilbertModule β E)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap B E E)
    (hπ : ∀ g a, U.conjugateOperator g (π a) = π (α.automorphism g a))
    (hπ' : ∀ g a, (moduleComap e.toMonoidHom U).conjugateOperator g (π a) =
      π ((actionComap e.toMonoidHom α).automorphism g a))
    (u : PushedModule e β E) (g : Γ) (a : A) :
    descentModuleEquiv e β E (interiorModuleTensorOperator (homRepresentation e β)
        (reducedSourceRepresentation (actionComap e.toMonoidHom β) E (actionComap e.toMonoidHom α)
          (moduleComap e.toMonoidHom U) π hπ' (algebraicToReducedCrossed (actionComap e.toMonoidHom α)
            (AlgebraicCrossedProduct.single _ g a))) u) =
      reducedSourceRepresentation β E α U π hπ (crossedProductEquiv e α (algebraicToReducedCrossed (actionComap e.toMonoidHom α)
            (AlgebraicCrossedProduct.single _ g a)))
        (descentModuleEquiv e β E u) := by
  have hs' : reducedSourceRepresentation (actionComap e.toMonoidHom β) E
      (actionComap e.toMonoidHom α) (moduleComap e.toMonoidHom U) π hπ'
      (algebraicToReducedCrossed (actionComap e.toMonoidHom α)
        (AlgebraicCrossedProduct.single _ g a)) =
      operatorHom (actionComap e.toMonoidHom β) E (π a) *
        groupOperator (actionComap e.toMonoidHom β) E (moduleComap e.toMonoidHom U) g :=
    (reducedSourceRepresentation_single (actionComap e.toMonoidHom β) E
      (actionComap e.toMonoidHom α) (moduleComap e.toMonoidHom U) π hπ' g a).trans
      (sourceGenerator_eq (actionComap e.toMonoidHom β) E (moduleComap e.toMonoidHom U) π a g)
  have hs : reducedSourceRepresentation β E α U π hπ
      (algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α (e g) a)) =
      operatorHom β E (π a) * groupOperator β E U (e g) :=
    (reducedSourceRepresentation_single β E α U π hπ (e g) a).trans
      (sourceGenerator_eq β E U π a (e g))
  refine (congrArg (fun T => descentModuleEquiv e β E
    (interiorModuleTensorOperator (homRepresentation e β) T u)) hs').trans ?_
  refine (descentModuleEquiv_sourceGenerator e β E U π a g u).trans ?_
  refine Eq.symm ((congrArg (fun w => reducedSourceRepresentation β E α U π hπ w
    (descentModuleEquiv e β E u)) (crossedProductEquiv_single e α g a)).trans ?_)
  exact (congrArg (fun T => T (descentModuleEquiv e β E u)) hs).trans
    (AdjointableMap.mul_apply _ _ _)

omit [Countable Γ] in
/-- `descentModuleEquiv_reducedSourceRepresentation` is additive in the algebraic element. -/
theorem descentModuleEquiv_reducedSource_add (U : EquivariantHilbertModule β E)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap B E E)
    (hπ : ∀ g a, U.conjugateOperator g (π a) = π (α.automorphism g a))
    (hπ' : ∀ g a, (moduleComap e.toMonoidHom U).conjugateOperator g (π a) =
      π ((actionComap e.toMonoidHom α).automorphism g a))
    (u : PushedModule e β E) (f h : AlgebraicCrossedProduct (actionComap e.toMonoidHom α))
    (ihf : descentModuleEquiv e β E (interiorModuleTensorOperator (homRepresentation e β)
        (reducedSourceRepresentation (actionComap e.toMonoidHom β) E (actionComap e.toMonoidHom α)
          (moduleComap e.toMonoidHom U) π hπ' (algebraicToReducedCrossed (actionComap e.toMonoidHom α) f)) u) =
      reducedSourceRepresentation β E α U π hπ (crossedProductEquiv e α (algebraicToReducedCrossed (actionComap e.toMonoidHom α) f))
        (descentModuleEquiv e β E u))
    (ihh : descentModuleEquiv e β E (interiorModuleTensorOperator (homRepresentation e β)
        (reducedSourceRepresentation (actionComap e.toMonoidHom β) E (actionComap e.toMonoidHom α)
          (moduleComap e.toMonoidHom U) π hπ' (algebraicToReducedCrossed (actionComap e.toMonoidHom α) h)) u) =
      reducedSourceRepresentation β E α U π hπ (crossedProductEquiv e α (algebraicToReducedCrossed (actionComap e.toMonoidHom α) h))
        (descentModuleEquiv e β E u)) :
    descentModuleEquiv e β E (interiorModuleTensorOperator (homRepresentation e β)
        (reducedSourceRepresentation (actionComap e.toMonoidHom β) E (actionComap e.toMonoidHom α)
          (moduleComap e.toMonoidHom U) π hπ' (algebraicToReducedCrossed (actionComap e.toMonoidHom α) (f + h))) u) =
      reducedSourceRepresentation β E α U π hπ (crossedProductEquiv e α (algebraicToReducedCrossed (actionComap e.toMonoidHom α) (f + h)))
        (descentModuleEquiv e β E u) := by
  have a1 : reducedSourceRepresentation (actionComap e.toMonoidHom β) E
      (actionComap e.toMonoidHom α) (moduleComap e.toMonoidHom U) π hπ'
      (algebraicToReducedCrossed (actionComap e.toMonoidHom α) (f + h)) =
      reducedSourceRepresentation (actionComap e.toMonoidHom β) E
        (actionComap e.toMonoidHom α) (moduleComap e.toMonoidHom U) π hπ'
        (algebraicToReducedCrossed (actionComap e.toMonoidHom α) f) +
      reducedSourceRepresentation (actionComap e.toMonoidHom β) E
        (actionComap e.toMonoidHom α) (moduleComap e.toMonoidHom U) π hπ'
        (algebraicToReducedCrossed (actionComap e.toMonoidHom α) h) :=
    (congrArg (reducedSourceRepresentation (actionComap e.toMonoidHom β) E
      (actionComap e.toMonoidHom α) (moduleComap e.toMonoidHom U) π hπ')
      (map_add (algebraicToReducedCrossed (actionComap e.toMonoidHom α)) f h)).trans
      (map_add (reducedSourceRepresentation (actionComap e.toMonoidHom β) E
      (actionComap e.toMonoidHom α) (moduleComap e.toMonoidHom U) π hπ') _ _)
  have a2 : reducedSourceRepresentation β E α U π hπ
      (crossedProductEquiv e α (algebraicToReducedCrossed (actionComap e.toMonoidHom α) (f + h))) =
      reducedSourceRepresentation β E α U π hπ
        (crossedProductEquiv e α (algebraicToReducedCrossed (actionComap e.toMonoidHom α) f)) +
      reducedSourceRepresentation β E α U π hπ
        (crossedProductEquiv e α (algebraicToReducedCrossed (actionComap e.toMonoidHom α) h)) :=
    (congrArg (fun w => reducedSourceRepresentation β E α U π hπ (crossedProductEquiv e α w))
      (map_add (algebraicToReducedCrossed (actionComap e.toMonoidHom α)) f h)).trans
    ((congrArg (reducedSourceRepresentation β E α U π hπ)
      (map_add (crossedProductEquiv e α) _ _)).trans
      (map_add (reducedSourceRepresentation β E α U π hπ) _ _))
  refine (congrArg (fun T => descentModuleEquiv e β E
    (interiorModuleTensorOperator (homRepresentation e β) T u)) a1).trans ?_
  refine (congrArg (fun w => descentModuleEquiv e β E w)
    (interiorModuleTensorOperator_add (homRepresentation e β) _ _ u)).trans ?_
  refine (HilbertModuleEquiv.map_add (descentModuleEquiv e β E) _ _).trans ?_
  refine (congrArg₂ (fun a b : Module β E => a + b) ihf ihh).trans ?_
  exact ((congrArg (fun T => T (descentModuleEquiv e β E u)) a2).trans
    (AdjointableMap.coe_add_apply _ _ _)).symm

omit [Countable Γ] in
/-- The descended source representations correspond under the unitary and `Φ_A`. -/
theorem descentModuleEquiv_reducedSourceRepresentation (U : EquivariantHilbertModule β E)
    (π : A →⋆ₙₐ[ℂ] AdjointableMap B E E)
    (hπ : ∀ g a, U.conjugateOperator g (π a) = π (α.automorphism g a))
    (hπ' : ∀ g a, (moduleComap e.toMonoidHom U).conjugateOperator g (π a) =
      π ((actionComap e.toMonoidHom α).automorphism g a))
    (z : ReducedCrossedProduct (actionComap e.toMonoidHom α)) (u : PushedModule e β E) :
    descentModuleEquiv e β E (interiorModuleTensorOperator (homRepresentation e β)
        (reducedSourceRepresentation (actionComap e.toMonoidHom β) E (actionComap e.toMonoidHom α)
          (moduleComap e.toMonoidHom U) π hπ' z) u) =
      reducedSourceRepresentation β E α U π hπ (crossedProductEquiv e α z)
        (descentModuleEquiv e β E u) := by
  have hL : Continuous (fun w : ReducedCrossedProduct (actionComap e.toMonoidHom α) =>
      interiorModuleTensorOperator (homRepresentation e β)
        (reducedSourceRepresentation (actionComap e.toMonoidHom β) E (actionComap e.toMonoidHom α)
          (moduleComap e.toMonoidHom U) π hπ' w) u) :=
    continuous_interiorModuleTensorOperator_apply (homRepresentation e β)
      (continuous_reducedSourceRepresentation (actionComap e.toMonoidHom β) E
        (actionComap e.toMonoidHom α) (moduleComap e.toMonoidHom U) π hπ') u
  have hR : Continuous (fun w : ReducedCrossedProduct (actionComap e.toMonoidHom α) =>
      reducedSourceRepresentation β E α U π hπ (crossedProductEquiv e α w)
        (descentModuleEquiv e β E u)) :=
    (AdjointableMap.toCLM_isometry.continuous.comp
      ((continuous_reducedSourceRepresentation β E α U π hπ).comp
        (continuous_crossedProductEquiv e α))).clm_apply continuous_const
  refine DenseRange.induction_on
    (p := fun w : ReducedCrossedProduct (actionComap e.toMonoidHom α) =>
      descentModuleEquiv e β E (interiorModuleTensorOperator (homRepresentation e β)
        (reducedSourceRepresentation (actionComap e.toMonoidHom β) E (actionComap e.toMonoidHom α)
          (moduleComap e.toMonoidHom U) π hπ' w) u) =
      reducedSourceRepresentation β E α U π hπ (crossedProductEquiv e α w)
        (descentModuleEquiv e β E u))
    (algebraicToReducedCrossed_denseRange (actionComap e.toMonoidHom α)) z
    (isClosed_eq ((descentModuleEquiv e β E).linearIsometryEquiv.continuous.comp hL) hR) ?_
  intro f
  induction f using AlgebraicCrossedProduct.induction_on (actionComap e.toMonoidHom α) with
  | zero => exact descentModuleEquiv_reducedSource_zero e β E α U π hπ hπ' u
  | single g a => exact descentModuleEquiv_reducedSource_single e β E α U π hπ hπ' u g a
  | add f h ihf ihh => exact descentModuleEquiv_reducedSource_add e β E α U π hπ hπ' u f h ihf ihh

/-- The standard homomorphism cycle of `Φ_B`, over the trivial `Unit` actions. -/
abbrev homCycle :=
  gradedStandardModuleHomCycle
    (CStarAlgebraAction.trivial : CStarAlgebraAction Unit
      (ReducedCrossedProduct (actionComap e.toMonoidHom β)))
    (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct β))
    CStarGrading.trivial CStarGrading.trivial
    (CStarAlgebraAction.preservesGrading_trivial _) (CStarAlgebraAction.preservesGrading_trivial _)
    (crossedProductHom e β) (fun _ _ => rfl) (fun _ => rfl)

variable {E}

/-- Descent commutes with relabelling on even cycles: for a `Γ'`-cycle `c`, the coefficient pushforward along `Φ_B` of
the descent of the restricted cycle is isomorphic to the source pullback along `Φ_A` of the
descent of `c`. -/
def evenDescentIso (c : KasparovCycle α β E) :
    GradedKasparovCycleIso
      (gradedKasparovCompactSecondProduct
        (GradedKasparovCycle.ofKasparovCycle
          (evenCycle (actionComap e.toMonoidHom β) (actionComap e.toMonoidHom α)
            (cycleComap e.toMonoidHom c)))
        (homCycle e β)
        (gradedStandardModuleHomCycle_representation_compact _ _ _ _ _ _ _ _ _))
      ((GradedKasparovCycle.ofKasparovCycle (evenCycle β α c)).sourcePullback
        (CStarAlgebraAction.trivial : CStarAlgebraAction Unit
          (ReducedCrossedProduct (actionComap e.toMonoidHom α)))
        CStarGrading.trivial (CStarAlgebraAction.preservesGrading_trivial _)
        (crossedProductEquiv e α).toNonUnitalStarAlgHom (fun _ _ => rfl) (fun _ => rfl)) where
  moduleEquiv := descentModuleEquiv e β E
  grading_intertwine z := descentModuleEquiv_grading e β E c.grading _ z
  action_intertwine g z := by
    have hg : g = 1 := Subsingleton.elim _ _
    subst hg
    simp only [EquivariantHilbertModule.one_apply]
  representation_intertwine a z :=
    descentModuleEquiv_reducedSourceRepresentation e β E α c.groupAction c.representation
      c.representation_equivariant _ a z
  operator_intertwine z := descentModuleEquiv_operator e β E c.operator z

end Source

end BC4lean.KKTheory.GroupIso

/-! ## Descent and group isomorphisms on even classes

For `e : Γ ≃* Γ'` and a `Γ'`-equivariant even class `x ∈ KK^{Γ'}(A, B)`, the descent of the
restriction of `x` to `Γ`, pushed forward along `Φ_B : B ⋊ᵣ (β ∘ e) Γ ≃ B ⋊ᵣ β Γ'`, equals the
descent of `x` pulled back along `Φ_A : A ⋊ᵣ (α ∘ e) Γ ≃ A ⋊ᵣ α Γ'`. On representatives this is
the cycle isomorphism `evenDescentIso`; the graded bridge and the upstream
coherence lemmas `coefficientPushforward_graded_even` / `sourcePullback_graded_even` move it to
the parity groups in which assembly is defined.
-/

namespace BC4lean.KKTheory.GroupIso
universe uΓ uA uB uE
open KKTheory.GroupRestriction
open KKTheory KKTheory.KasparovDescent

variable {Γ Γ' : Type uΓ} [Group Γ] [Group Γ'] [Countable Γ] [Countable Γ'] (e : Γ ≃* Γ')
  {A : Type uA} {B : Type uB}
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  (α : CStarAlgebraAction Γ' A) (β : CStarAlgebraAction Γ' B)

omit [Countable Γ] [Countable Γ'] [TopologicalSpace.SeparableSpace B] in
/-- The compatibility of `Φ_B` with the trivial `Unit` actions, stated exactly as the upstream
pushforward lemmas take it (an anonymous `fun _ _ => rfl` elaborates to a term whose type is only
definitionally this, and `rw` then rejects the motive). -/
theorem crossedProductHom_trivial :
    ∀ (k : Unit) (b : ReducedCrossedProduct (actionComap e.toMonoidHom β)),
      crossedProductHom e β
          ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit
            (ReducedCrossedProduct (actionComap e.toMonoidHom β))).automorphism k b) =
        (CStarAlgebraAction.trivial : CStarAlgebraAction Unit
          (ReducedCrossedProduct β)).automorphism k (crossedProductHom e β b) :=
  fun _ _ => rfl

omit [Countable Γ] [Countable Γ'] [TopologicalSpace.SeparableSpace A] in
/-- The same for `Φ_A`. -/
theorem crossedProductEquiv_trivial :
    ∀ (k : Unit) (a : ReducedCrossedProduct (actionComap e.toMonoidHom α)),
      (crossedProductEquiv e α).toNonUnitalStarAlgHom
          ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit
            (ReducedCrossedProduct (actionComap e.toMonoidHom α))).automorphism k a) =
        (CStarAlgebraAction.trivial : CStarAlgebraAction Unit
          (ReducedCrossedProduct α)).automorphism k
          ((crossedProductEquiv e α).toNonUnitalStarAlgHom a) :=
  fun _ _ => rfl

omit [Countable Γ] [Countable Γ'] [TopologicalSpace.SeparableSpace B] in
/-- The grading compatibility of `Φ_B` for the trivial gradings. -/
theorem crossedProductHom_grading :
    ∀ b : ReducedCrossedProduct (actionComap e.toMonoidHom β),
      crossedProductHom e β
          ((CStarGrading.trivial : CStarGrading
            (ReducedCrossedProduct (actionComap e.toMonoidHom β))).automorphism b) =
        (CStarGrading.trivial : CStarGrading (ReducedCrossedProduct β)).automorphism
          (crossedProductHom e β b) :=
  fun _ => rfl

omit [Countable Γ] [Countable Γ'] [TopologicalSpace.SeparableSpace A] in
/-- The grading compatibility of `Φ_A` for the trivial gradings. -/
theorem crossedProductEquiv_grading :
    ∀ a : ReducedCrossedProduct (actionComap e.toMonoidHom α),
      (crossedProductEquiv e α).toNonUnitalStarAlgHom
          ((CStarGrading.trivial : CStarGrading
            (ReducedCrossedProduct (actionComap e.toMonoidHom α))).automorphism a) =
        (CStarGrading.trivial : CStarGrading (ReducedCrossedProduct α)).automorphism
          ((crossedProductEquiv e α).toNonUnitalStarAlgHom a) :=
  fun _ => rfl

/-- Descent commutes with relabelling on even classes, in the graded classes. The proof is a
term-mode chain of upstream lemmas at explicit arguments: `rw [coefficientPushforward_mk_tensor]`
on this goal times out in `isDefEq`. -/
theorem evenDescent_graded (x : KasparovHomotopyClass.{uΓ, uA, uB, uE} α β) :
    GroupUniverseCoefficientPushforward.coefficientPushforward
        (CStarAlgebraAction.preservesGrading_trivial _)
        (CStarAlgebraAction.preservesGrading_trivial _)
        (crossedProductHom e β) (crossedProductHom_trivial e β) (crossedProductHom_grading e β)
        (GroupUniverseEvenBridge.gradedClass
          (evenClass (actionComap e.toMonoidHom β) (actionComap e.toMonoidHom α)
            (evenComap e.toMonoidHom x))) =
      GradedKasparovHomotopyClass.sourcePullback
        (CStarAlgebraAction.trivial : CStarAlgebraAction Unit
          (ReducedCrossedProduct (actionComap e.toMonoidHom α)))
        CStarGrading.trivial (CStarAlgebraAction.preservesGrading_trivial _)
        (crossedProductEquiv e α).toNonUnitalStarAlgHom (crossedProductEquiv_trivial e α)
        (crossedProductEquiv_grading e α)
        (GroupUniverseEvenBridge.gradedClass (evenClass β α x)) := by
  induction x using Quotient.inductionOn with
  | h c =>
    exact (GroupUniverseCoefficientPushforward.coefficientPushforward_mk_tensor
        (CStarAlgebraAction.preservesGrading_trivial _)
        (CStarAlgebraAction.preservesGrading_trivial _)
        (crossedProductHom e β) (crossedProductHom_trivial e β) (crossedProductHom_grading e β)
        (BundledGradedKasparovCycle.of (GradedKasparovCycle.ofKasparovCycle
          (evenCycle (actionComap e.toMonoidHom β) (actionComap e.toMonoidHom α)
            (cycleComap e.toMonoidHom c.cycle))))).trans
      ((GradedKasparovHomotopyClass.mk_eq_of_iso (evenDescentIso e β α c.cycle)).trans
        (GradedKasparovHomotopyClass.sourcePullback_mk _ _ _ _ _ _
          (BundledGradedKasparovCycle.of
            (GradedKasparovCycle.ofKasparovCycle (evenCycle β α c.cycle)))).symm)

/-- Descent commutes with relabelling on even classes, in the parity groups used by assembly: `(Φ_B)_* j_Γ(res_e x) = Φ_A^* j_Γ'(x)`.
The module universe of `x` contains `A`, as it does for assembly (`A = C₀(X)`, module universe
that of `X`). -/
theorem evenDescent_parity (x : KasparovHomotopyClass.{uΓ, uA, uB, max uA uE} α β) :
    GroupUniverseParityFunctoriality.coefficientPushforward.{0, max uΓ uA, max uΓ uB, max uΓ uB, uE}
        false (crossedProductHom e β) (crossedProductHom_trivial e β)
        (classHom (actionComap e.toMonoidHom β) (actionComap e.toMonoidHom α) false
          (evenComap e.toMonoidHom x :
            GroupUniverseParityGroup.KKParityGroup.{uΓ, uA, uB, max uA uE} false _ _)) =
      GroupUniverseParityFunctoriality.sourcePullback.{0, max uΓ uA, max uΓ uA, max uΓ uB, uE}
        false (crossedProductEquiv e α).toNonUnitalStarAlgHom (crossedProductEquiv_trivial e α)
        (classHom β α false
          (x : GroupUniverseParityGroup.KKParityGroup.{uΓ, uA, uB, max uA uE} false _ _)) := by
  apply GroupUniverseEvenBridge.gradedClass_injective
  exact (GroupUniverseParityFunctoriality.coefficientPushforward_graded_even.{0, max uΓ uA,
      max uΓ uB, max uΓ uB, uE} (crossedProductHom e β) (crossedProductHom_trivial e β)
      (evenClass (actionComap e.toMonoidHom β) (actionComap e.toMonoidHom α)
        (evenComap e.toMonoidHom x))).trans
    ((evenDescent_graded e α β x).trans
      (GroupUniverseParityFunctoriality.sourcePullback_graded_even.{0, max uΓ uA, max uΓ uA,
        max uΓ uB, uE} (crossedProductEquiv e α).toNonUnitalStarAlgHom
        (crossedProductEquiv_trivial e α) (evenClass β α x)).symm)

end BC4lean.KKTheory.GroupIso

/-! ## Descent and group isomorphisms on odd classes

Odd classes enter the graded picture through their Clifford expansions, on the pair module
`H × H` over `B × B`, and coefficient pushforward along `Φ_B` becomes pushforward along the
coordinate map `Φ_B × Φ_B`. BC4lean's Clifford pair tensor unitary
`CliffordPairStandardTensor.hilbertEquiv` identifies `(H × H) ⊗_{Φ_B × Φ_B} (C × C)` with
`(H ⊗_{Φ_B} C) × (H ⊗_{Φ_B} C)`; composing with the even unitary `descentModuleEquiv` on each
coordinate gives the odd cycle isomorphism, and the class-level statement follows as in the even
case.
-/

namespace BC4lean.KKTheory.GroupIso
universe uΓ uA uB uE
open KKTheory.GroupRestriction
open KKTheory KKTheory.KasparovDescent

section Cycle
variable {Γ Γ' : Type*} [Group Γ] [Group Γ'] [Countable Γ] [Countable Γ'] (e : Γ ≃* Γ')
  {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B]
  (β : CStarAlgebraAction Γ' B)

/-- The standard homomorphism cycle of the coordinate map `Φ_B × Φ_B`, over the trivial `Unit`
actions: the cycle that odd coefficient pushforward multiplies by. -/
abbrev oddHomCycle :=
  gradedStandardModuleHomCycle
    (cliffordCoefficientAction (CStarAlgebraAction.trivial : CStarAlgebraAction Unit
      (ReducedCrossedProduct (actionComap e.toMonoidHom β))))
    (cliffordCoefficientAction (CStarAlgebraAction.trivial : CStarAlgebraAction Unit
      (ReducedCrossedProduct β)))
    cliffordCoefficientGrading cliffordCoefficientGrading
    (cliffordCoefficientAction_preservesGrading _) (cliffordCoefficientAction_preservesGrading _)
    (cliffordCoordinateHom (crossedProductHom e β)) (fun _ _ => rfl) (fun _ => rfl)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

/-- The odd module unitary: Clifford pair tensor unitary, then `descentModuleEquiv` on both
coordinates. -/
def oddDescentModuleEquiv :
    HilbertModuleEquiv (ReducedCrossedProduct β × ReducedCrossedProduct β)
      (CliffordPairStandardTensor.Source (H := Module (actionComap e.toMonoidHom β) E)
        (crossedProductHom e β))
      (CliffordPairModule (ReducedCrossedProduct β) (Module β E)) :=
  (CliffordPairStandardTensor.hilbertEquiv (H := Module (actionComap e.toMonoidHom β) E)
    (crossedProductHom e β)).trans (descentModuleEquiv e β E).cliffordPair

omit [Countable Γ] in
theorem oddDescentModuleEquiv_pairMap
    (S T : AdjointableMap (ReducedCrossedProduct (actionComap e.toMonoidHom β))
      (Module (actionComap e.toMonoidHom β) E) (Module (actionComap e.toMonoidHom β) E))
    (S' T' : AdjointableMap (ReducedCrossedProduct β) (Module β E) (Module β E))
    (hS : ∀ u, descentModuleEquiv e β E (interiorModuleTensorOperator (homRepresentation e β) S u) =
      S' (descentModuleEquiv e β E u))
    (hT : ∀ u, descentModuleEquiv e β E (interiorModuleTensorOperator (homRepresentation e β) T u) =
      T' (descentModuleEquiv e β E u))
    (z : CliffordPairStandardTensor.Source (H := Module (actionComap e.toMonoidHom β) E)
        (crossedProductHom e β)) :
    oddDescentModuleEquiv e β (interiorModuleTensorOperator
        (CliffordPairStandardTensor.representation (crossedProductHom e β)) (cliffordPairMap S T) z) =
      cliffordPairMap S' T' (oddDescentModuleEquiv e β z) := by
  change (descentModuleEquiv e β E).cliffordPair (CliffordPairStandardTensor.hilbertEquiv
      (crossedProductHom e β) (interiorModuleTensorOperator
        (CliffordPairStandardTensor.representation (crossedProductHom e β)) (cliffordPairMap S T) z)) =
    cliffordPairMap S' T' ((descentModuleEquiv e β E).cliffordPair
      (CliffordPairStandardTensor.hilbertEquiv (crossedProductHom e β) z))
  refine (congrArg (fun w => (descentModuleEquiv e β E).cliffordPair w)
    (CliffordPairStandardTensor.hilbertEquiv_operator (H := Module (actionComap e.toMonoidHom β) E)
      (crossedProductHom e β) S T z)).trans ?_
  apply Prod.ext
  · exact hS _
  · exact hT _

section Source
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (α : CStarAlgebraAction Γ' A)

/-- The source of `oddDescentIso`: the descended relabelled cycle, pushed forward along `Φ_B`. -/
abbrev oddDescentSource (c : OddKasparovCycle α β E) :=
  gradedKasparovCompactSecondProduct
    (oddCycle (actionComap e.toMonoidHom β) (actionComap e.toMonoidHom α)
      (oddCycleComap e.toMonoidHom c)).cliffordExpansion
    (oddHomCycle e β)
    (gradedStandardModuleHomCycle_representation_compact _ _ _ _ _ _ _ _ _)

/-- The target of `oddDescentIso`: the descended cycle, pulled back along `Φ_A`. -/
abbrev oddDescentTarget (c : OddKasparovCycle α β E) :=
  (oddCycle β α c).cliffordExpansion.sourcePullback
    (CStarAlgebraAction.trivial : CStarAlgebraAction Unit
      (ReducedCrossedProduct (actionComap e.toMonoidHom α)))
    CStarGrading.trivial (CStarAlgebraAction.preservesGrading_trivial _)
    (crossedProductEquiv e α).toNonUnitalStarAlgHom (fun _ _ => rfl) (fun _ => rfl)

omit [Countable Γ] [Countable Γ'] [TopologicalSpace.SeparableSpace B] in
/-- The Clifford-pair standard representation of `Φ_B` is graded. -/
theorem crossedProductHom_cliffordGraded :
    ModuleTensorRepresentationGraded (δB := cliffordCoefficientGrading)
      (CliffordPairStandardTensor.representation (crossedProductHom e β))
      (GradedHilbertModule.standard cliffordCoefficientGrading) := by
  intro b y
  change MulOpposite.op (cliffordCoefficientGrading.automorphism
      (cliffordCoordinateHom (crossedProductHom e β) b * MulOpposite.unop y)) =
    MulOpposite.op (cliffordCoordinateHom (crossedProductHom e β)
      (cliffordCoefficientGrading.automorphism b) *
      cliffordCoefficientGrading.automorphism (MulOpposite.unop y))
  rw [map_mul]
  rfl

omit [Countable Γ] in
/-- `oddDescentModuleEquiv` on pure tensors. -/
theorem oddDescentModuleEquiv_mk
    (x' : CliffordPairModule (ReducedCrossedProduct (actionComap e.toMonoidHom β))
      (Module (actionComap e.toMonoidHom β) E))
    (y' : (ReducedCrossedProduct β × ReducedCrossedProduct β)ᵐᵒᵖ) :
    (oddDescentModuleEquiv (E := E) e β).toAdjointable.toCLM
        (interiorModuleTensorMk (CliffordPairStandardTensor.representation (crossedProductHom e β))
          x' y') =
      ((descentModuleEquiv e β E)
          (interiorModuleTensorMk (homRepresentation e β) x'.1
            (MulOpposite.op (MulOpposite.unop y').1)),
        (descentModuleEquiv e β E)
          (interiorModuleTensorMk (homRepresentation e β) x'.2
            (MulOpposite.op (MulOpposite.unop y').2))) :=
  congrArg (fun w => (descentModuleEquiv e β E).cliffordPair w)
        (CliffordPairStandardTensor.hilbertEquiv_mk (H := Module (actionComap e.toMonoidHom β) E)
          (crossedProductHom e β) x' y')

theorem oddDescentIso_grading (c : OddKasparovCycle α β E) (z : _) :
    oddDescentModuleEquiv e β ((oddDescentSource e β α c).grading.grading z) =
      (oddDescentTarget e β α c).grading.grading (oddDescentModuleEquiv e β z) := by
    let W := (oddDescentModuleEquiv (E := E) e β).toAdjointable.toCLM
    let J := ((oddCycle (actionComap e.toMonoidHom β) (actionComap e.toMonoidHom α)
      (oddCycleComap e.toMonoidHom c)).cliffordExpansion.grading.interiorTensor
        (GradedHilbertModule.standard cliffordCoefficientGrading)
        (crossedProductHom_cliffordGraded e β)).grading.toContinuousLinearEquiv.toContinuousLinearMap
    let K := (cliffordPairGrading (B := ReducedCrossedProduct β)
      (H := Module β E)).grading.toContinuousLinearEquiv.toContinuousLinearMap
    have h : W.comp J = K.comp W := by
      apply ModuleTensorFactorIsometry.interiorModuleTensor_clm_ext
      intro x y
      exact (congrArg W (GradedHilbertModule.interiorTensor_grading_mk
          (oddCycle (actionComap e.toMonoidHom β) (actionComap e.toMonoidHom α)
            (oddCycleComap e.toMonoidHom c)).cliffordExpansion.grading
          (GradedHilbertModule.standard cliffordCoefficientGrading)
          (crossedProductHom_cliffordGraded e β) x y)).trans
        ((oddDescentModuleEquiv_mk e β _ _).trans
          (congrArg Prod.swap (oddDescentModuleEquiv_mk e β x y)).symm)
    exact DFunLike.congr_fun h z

theorem oddDescentIso_representation (c : OddKasparovCycle α β E) (a : _) (z : _) :
    oddDescentModuleEquiv e β ((oddDescentSource e β α c).representation a z) =
      (oddDescentTarget e β α c).representation a (oddDescentModuleEquiv e β z) :=
    oddDescentModuleEquiv_pairMap e β _ _ _ _
      (descentModuleEquiv_reducedSourceRepresentation e β E α c.groupAction c.representation
        c.representation_equivariant _ a)
      (descentModuleEquiv_reducedSourceRepresentation e β E α c.groupAction c.representation
        c.representation_equivariant _ a) z

theorem oddDescentIso_operator (c : OddKasparovCycle α β E) (z : _) :
    oddDescentModuleEquiv e β ((oddDescentSource e β α c).operator z) =
      (oddDescentTarget e β α c).operator (oddDescentModuleEquiv e β z) := by
    refine oddDescentModuleEquiv_pairMap e β _ _ _ _
      (descentModuleEquiv_operator e β E c.operator) (fun u => ?_) z
    exact (congrArg (fun w => descentModuleEquiv e β E w)
      (interiorModuleTensorOperator_neg (homRepresentation e β)
        (operatorHom (actionComap e.toMonoidHom β) E c.operator) u)).trans
      ((map_neg (descentModuleEquiv e β E).linearIsometryEquiv _).trans
        ((congrArg (fun w => -w) (descentModuleEquiv_operator e β E c.operator u)).trans
          (AdjointableMap.coe_neg_apply _ _).symm))

/-- Descent commutes with relabelling on odd cycles. -/
def oddDescentIso (c : OddKasparovCycle α β E) :
    GradedKasparovCycleIso (oddDescentSource e β α c) (oddDescentTarget e β α c) where
  moduleEquiv := oddDescentModuleEquiv e β
  grading_intertwine := oddDescentIso_grading e β α c
  action_intertwine g z := by
    have hg : g = 1 := Subsingleton.elim _ _
    subst hg
    simp only [EquivariantHilbertModule.one_apply]
  representation_intertwine := oddDescentIso_representation e β α c
  operator_intertwine := oddDescentIso_operator e β α c

end Source
end Cycle

section Class
variable {Γ Γ' : Type uΓ} [Group Γ] [Group Γ'] [Countable Γ] [Countable Γ'] (e : Γ ≃* Γ')
  {A : Type uA} {B : Type uB}
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
  (α : CStarAlgebraAction Γ' A) (β : CStarAlgebraAction Γ' B)

/-- Descent commutes with relabelling on odd classes, in the graded classes. -/
theorem oddDescent_graded (x : OddKK.{uΓ, uA, uB, uE} α β) :
    GroupUniverseCoefficientPushforward.coefficientPushforward
        (cliffordCoefficientAction_preservesGrading _)
        (cliffordCoefficientAction_preservesGrading _)
        (cliffordCoordinateHom (crossedProductHom e β)) (fun _ _ => rfl) (fun _ => rfl)
        (GroupUniverseCliffordCoordinateBridge.gradedOddClass
          (oddClass (actionComap e.toMonoidHom β) (actionComap e.toMonoidHom α)
            (oddComap e.toMonoidHom x))) =
      GradedKasparovHomotopyClass.sourcePullback
        (CStarAlgebraAction.trivial : CStarAlgebraAction Unit
          (ReducedCrossedProduct (actionComap e.toMonoidHom α)))
        CStarGrading.trivial (CStarAlgebraAction.preservesGrading_trivial _)
        (crossedProductEquiv e α).toNonUnitalStarAlgHom (crossedProductEquiv_trivial e α) (fun _ => rfl)
        (GroupUniverseCliffordCoordinateBridge.gradedOddClass (oddClass β α x)) := by
  induction x using Quotient.inductionOn with
  | h c =>
    exact (GroupUniverseCoefficientPushforward.coefficientPushforward_mk_tensor
        (cliffordCoefficientAction_preservesGrading _)
        (cliffordCoefficientAction_preservesGrading _)
        (cliffordCoordinateHom (crossedProductHom e β)) (fun _ _ => rfl) (fun _ => rfl)
        (BundledGradedKasparovCycle.of
          (oddCycle (actionComap e.toMonoidHom β) (actionComap e.toMonoidHom α)
            (oddCycleComap e.toMonoidHom c.cycle)).cliffordExpansion)).trans
      ((GradedKasparovHomotopyClass.mk_eq_of_iso (oddDescentIso e β α c.cycle)).trans
        (GradedKasparovHomotopyClass.sourcePullback_mk _ _ _ _ _ _
          (BundledGradedKasparovCycle.of (oddCycle β α c.cycle).cliffordExpansion)).symm)

/-- Descent commutes with relabelling on odd classes, in the parity groups used by assembly. -/
theorem oddDescent_parity (x : OddKK.{uΓ, uA, uB, max uA uE} α β) :
    GroupUniverseParityFunctoriality.coefficientPushforward.{0, max uΓ uA, max uΓ uB, max uΓ uB, uE}
        true (crossedProductHom e β) (crossedProductHom_trivial e β)
        (classHom (actionComap e.toMonoidHom β) (actionComap e.toMonoidHom α) true
          (oddComap e.toMonoidHom x :
            GroupUniverseParityGroup.KKParityGroup.{uΓ, uA, uB, max uA uE} true _ _)) =
      GroupUniverseParityFunctoriality.sourcePullback.{0, max uΓ uA, max uΓ uA, max uΓ uB, uE}
        true (crossedProductEquiv e α).toNonUnitalStarAlgHom (crossedProductEquiv_trivial e α)
        (classHom β α true
          (x : GroupUniverseParityGroup.KKParityGroup.{uΓ, uA, uB, max uA uE} true _ _)) := by
  apply GroupUniverseCliffordCoordinateBridge.gradedOddClass_injective
  exact (GroupUniverseParityFunctoriality.coefficientPushforward_graded_odd.{0, max uΓ uA,
      max uΓ uB, max uΓ uB, uE} (crossedProductHom e β) (crossedProductHom_trivial e β)
      (oddClass (actionComap e.toMonoidHom β) (actionComap e.toMonoidHom α)
        (oddComap e.toMonoidHom x))).trans
    ((oddDescent_graded e α β x).trans
      (GroupUniverseParityFunctoriality.sourcePullback_graded_odd.{0, max uΓ uA, max uΓ uA,
        max uΓ uB, uE} (crossedProductEquiv e α).toNonUnitalStarAlgHom
        (crossedProductEquiv_trivial e α) (oddClass β α x)).symm)

end Class

end BC4lean.KKTheory.GroupIso
