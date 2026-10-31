import BC4lean.ReducedOperatorK1
import BC4lean.OperatorK0Equivalence
import BC4lean.OperatorK1Functoriality
import BC4lean.ReducedScalarKKComparison
import BC4lean.ReducedCrossedScalarProduct
import BC4lean.ScalarKKNativeNaturality
import BC4lean.OddKTheoryIndependentCoefficientNaturality

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Reduced group C⋆-algebras along a group isomorphism

For `e : Γ ≃* Γ'`: the relabelling isomorphism `C*_r Γ ≅ C*_r Γ'` and the induced bijection of the
analytic targets `analyticGroupEquiv e p`; the identification of the native odd pushforward with the
ordinary one; generic unital naturality of the K-theory comparisons.
-/

noncomputable section

/-! ## The analytic target along a group isomorphism

For `e : Γ ≃* Γ'`: the unitary `ℓ²(Γ) ≅ ℓ²(Γ')` induced by `e`, the resulting isomorphism of
reduced group C⋆-algebras `reducedGroupCStarEquiv e`, and the induced additive bijection
`analyticGroupEquiv e p` of the analytic targets `K_p(C*_r Γ) ≃ K_p(C*_r Γ')`. -/

namespace BC4lean.KKTheory.GroupIso
open OperatorKTheory
open scoped ENNReal

universe u
variable {Γ Γ' : Type u} [Group Γ] [Group Γ'] (e : Γ ≃* Γ')

/-- Relabelling square-summable functions along the underlying bijection. -/
def l2Relabel : L2Group Γ ≃ₗᵢ[ℂ] L2Group Γ' where
  toFun ξ := ⟨fun g' => ξ (e.symm g'), by
    apply memℓp_gen
    exact (e.symm.toEquiv).summable_iff.mpr ((lp.memℓp ξ).summable (by norm_num))⟩
  invFun η := ⟨fun g => η (e g), by
    apply memℓp_gen
    exact (e.toEquiv).summable_iff.mpr ((lp.memℓp η).summable (by norm_num))⟩
  left_inv ξ := by
    apply lp.ext
    funext g
    simp
  right_inv η := by
    apply lp.ext
    funext g
    simp
  map_add' ξ η := by
    apply lp.ext
    rfl
  map_smul' c ξ := by
    apply lp.ext
    rfl
  norm_map' ξ := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact (e.symm.toEquiv).tsum_eq (fun g => ‖ξ g‖ ^ (2 : ℝ≥0∞).toReal)

@[simp] theorem l2Relabel_apply (ξ : L2Group Γ) (g' : Γ') :
    l2Relabel e ξ g' = ξ (e.symm g') := rfl

@[simp] theorem l2Relabel_symm_apply (η : L2Group Γ') (g : Γ) :
    (l2Relabel e).symm η g = η (e g) := rfl

/-- Conjugation by the relabelling unitary on all bounded operators. -/
def conj : (L2Group Γ →L[ℂ] L2Group Γ) ≃⋆ₐ[ℂ] (L2Group Γ' →L[ℂ] L2Group Γ') :=
  (l2Relabel e).conjStarAlgEquiv

theorem conj_regularOperator (g : Γ) :
    conj e (regularOperator g) = regularOperator (e g) := by
  ext ξ h'
  simp [conj, map_inv]

theorem conj_continuous : Continuous (conj e) :=
  map_continuous (l2Relabel e).toContinuousLinearEquiv.conjContinuousAlgEquiv

theorem conj_mem (T : L2Group Γ →L[ℂ] L2Group Γ) (hT : T ∈ reducedAlgebra Γ) :
    conj e T ∈ reducedAlgebra Γ' := by
  have hle : reducedAlgebra Γ ≤ (reducedAlgebra Γ').comap (conj e).toStarAlgHom := by
    apply reducedAlgebra_minimal
    · exact (reducedAlgebra_isClosed (Γ := Γ')).preimage (conj_continuous e)
    · intro g
      change conj e (regularOperator g) ∈ reducedAlgebra Γ'
      rw [conj_regularOperator]
      exact regularOperator_mem_reducedAlgebra (Γ := Γ') (e g)
  exact hle hT

theorem conj_symm_mem (T : L2Group Γ' →L[ℂ] L2Group Γ') (hT : T ∈ reducedAlgebra Γ') :
    (conj e).symm T ∈ reducedAlgebra Γ := by
  have h := conj_mem e.symm T hT
  have hsymm : (conj e).symm T = conj e.symm T := by
    ext ξ g
    rfl
  rw [hsymm]
  exact h

/-- The reduced group C*-algebras of isomorphic groups are star-isomorphic. -/
def reducedGroupCStarEquiv : ReducedGroupCStar Γ ≃⋆ₐ[ℂ] ReducedGroupCStar Γ' where
  toFun x := ⟨conj e x.1, conj_mem e x.1 x.2⟩
  invFun y := ⟨(conj e).symm y.1, conj_symm_mem e y.1 y.2⟩
  left_inv x := Subtype.ext ((conj e).symm_apply_apply x.1)
  right_inv y := Subtype.ext ((conj e).apply_symm_apply y.1)
  map_mul' x y := Subtype.ext (map_mul (conj e) x.1 y.1)
  map_add' x y := Subtype.ext (map_add (conj e) x.1 y.1)
  map_star' x := Subtype.ext (map_star (conj e) x.1)
  map_smul' c x := Subtype.ext (map_smul (conj e) c x.1)

/-- Degree zero: `ReducedK0` is invariant under group isomorphism. -/
def reducedK0Equiv : ReducedK0 Γ ≃+ ReducedK0 Γ' := by
  letI := CStarAlgebra.spectralOrder (ReducedGroupCStar Γ)
  letI := CStarAlgebra.spectralOrderedRing (ReducedGroupCStar Γ)
  letI := CStarAlgebra.spectralOrder (ReducedGroupCStar Γ')
  letI := CStarAlgebra.spectralOrderedRing (ReducedGroupCStar Γ')
  exact k0Equiv (reducedGroupCStarEquiv e)

/-- Degree one: `ReducedK1` is invariant under group isomorphism. -/
def reducedK1Equiv : ReducedK1 Γ ≃+ ReducedK1 Γ' := by
  letI := CStarAlgebra.spectralOrder (ReducedGroupCStar Γ)
  letI := CStarAlgebra.spectralOrderedRing (ReducedGroupCStar Γ)
  letI := CStarAlgebra.spectralOrder (ReducedGroupCStar Γ')
  letI := CStarAlgebra.spectralOrderedRing (ReducedGroupCStar Γ')
  exact
    { toFun := k1Map (reducedGroupCStarEquiv e).toStarAlgHom
      invFun := k1Map (reducedGroupCStarEquiv e).symm.toStarAlgHom
      left_inv := fun x => by
        change ((k1Map _).comp (k1Map _)) x = x
        rw [← k1Map_comp]
        have h : (reducedGroupCStarEquiv e).symm.toStarAlgHom.comp
            (reducedGroupCStarEquiv e).toStarAlgHom = StarAlgHom.id ℂ _ := by
          exact StarAlgHom.ext fun a => (reducedGroupCStarEquiv e).symm_apply_apply a
        rw [h, k1Map_id]
        rfl
      right_inv := fun y => by
        change ((k1Map _).comp (k1Map _)) y = y
        rw [← k1Map_comp]
        have h : (reducedGroupCStarEquiv e).toStarAlgHom.comp
            (reducedGroupCStarEquiv e).symm.toStarAlgHom = StarAlgHom.id ℂ _ := by
          exact StarAlgHom.ext fun a => (reducedGroupCStarEquiv e).apply_symm_apply a
        rw [h, k1Map_id]
        rfl
      map_add' := (k1Map (reducedGroupCStarEquiv e).toStarAlgHom).map_add }

/-- The parity-indexed analytic target of assembly. -/
def analyticGroupEquiv [Countable Γ] [Countable Γ'] (p : Bool) : Assembly.analyticGroup Γ p ≃+ Assembly.analyticGroup Γ' p := by
  cases p
  · exact reducedK0Equiv e
  · exact reducedK1Equiv e

end BC4lean.KKTheory.GroupIso

/-! ## Native and ordinary odd pushforward; unital naturality -/

namespace BC4lean.KKTheory.GroupIso
open scoped ComplexOrder
open KKTheory OperatorKTheory
open scoped KasparovDescent
open KKTheory.GroupUniverseParityGroup KKTheory.GroupUniverseParityFunctoriality

section Bridge
universe u
variable {B C : Type u}
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [TopologicalSpace.SeparableSpace B] [TopologicalSpace.SeparableSpace C]

/-- The native odd coefficient pushforward (right product with the hom class) is the ordinary odd
pushforward of upstream: both have the same graded Clifford class. -/
theorem odd_native_eq_ordinary (f : B →⋆ₙₐ[ℂ] C)
    (hact : ∀ (k : Unit) (b : B),
      f ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit B).automorphism k b) =
        (CStarAlgebraAction.trivial : CStarAlgebraAction Unit C).automorphism k (f b))
    (x : OddKK.{0, 0, u, u} (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit B)) :
    (coefficientPushforward.{0, 0, u, u, u} true f hact
        (x : KKParityGroup.{0, 0, u, u} true _ _) :
      OddKK.{0, 0, u, u} (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
        (CStarAlgebraAction.trivial : CStarAlgebraAction Unit C)) =
      GroupUniverseOrdinaryOdd.coefficientPushforward.{u, u, u} f x :=
  GroupUniverseCliffordCoordinateBridge.gradedOddClass_injective
    ((coefficientPushforward_graded_odd.{0, 0, u, u, u} f hact x).trans
      (GroupUniverseOrdinaryOdd.gradedOddClass_coefficientPushforward.{u, u, u} f x).symm)

/-- Odd index naturality for the native pushforward. -/
theorem oddIndex_native_natural (f : B →⋆ₙₐ[ℂ] C)
    (hact : ∀ (k : Unit) (b : B),
      f ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit B).automorphism k b) =
        (CStarAlgebraAction.trivial : CStarAlgebraAction Unit C).automorphism k (f b))
    (x : OddKK.{0, 0, u, u} (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit B)) :
    oddKKOperatorK1AllModuleUniversesAddEquiv.{u, u}
        (coefficientPushforward.{0, 0, u, u, u} true f hact
          (x : KKParityGroup.{0, 0, u, u} true _ _)) =
      operatorK1Map f (oddKKOperatorK1AllModuleUniversesAddEquiv.{u, u} x) :=
  (oddKKOperatorK1AllModuleUniversesAddEquiv_apply.{u, u} _).trans
    ((congrArg oddKKOperatorK1Index (odd_native_eq_ordinary f hact x)).trans
      ((oddKKOperatorK1Index_independentCoefficientPushforward.{u, u, u} f x).trans
        (congrArg (operatorK1Map f) (oddKKOperatorK1AllModuleUniversesAddEquiv_apply.{u, u} x).symm)))

end Bridge

section UnitalGeneric
/-! Generic forms of the unital agreement step. They are stated over arbitrary algebras so that no
star homomorphism *out of* `ReducedGroupCStar` is ever elaborated against the instances that
`operatorK0Map` synthesizes: in this file every such elaboration times out in `whnf`,
and upstream never forms one either. -/

local instance spectralOrder' (B : Type*) [CStarAlgebra B] : PartialOrder B :=
  CStarAlgebra.spectralOrder B
local instance spectralOrderedRing' (B : Type*) [CStarAlgebra B] : StarOrderedRing B :=
  CStarAlgebra.spectralOrderedRing B

variable {A B C : Type*} [NonUnitalCStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]

theorem unital_k0_natural (s : A →⋆ₙₐ[ℂ] B) (ρ : B ≃⋆ₐ[ℂ] C) (σ : A →⋆ₙₐ[ℂ] C)
    (hσ : ∀ a, σ a = ρ (s a)) (w : OperatorK0 A) :
    operatorK0UnitalEquiv C (operatorK0Map σ w) =
      k0Map ρ.toStarAlgHom (operatorK0UnitalEquiv B (operatorK0Map s w)) := by
  have h : σ = ρ.toStarAlgHom.toNonUnitalStarAlgHom.comp s := NonUnitalStarAlgHom.ext hσ
  subst h
  exact (congrArg (operatorK0UnitalEquiv C)
      (DFunLike.congr_fun (operatorK0Map_comp ρ.toStarAlgHom.toNonUnitalStarAlgHom s) w)).trans
    (operatorK0UnitalEquiv_natural ρ.toStarAlgHom _)

theorem unital_k1_natural (s : A →⋆ₙₐ[ℂ] B) (ρ : B ≃⋆ₐ[ℂ] C) (σ : A →⋆ₙₐ[ℂ] C)
    (hσ : ∀ a, σ a = ρ (s a)) (w : OperatorK1 A) :
    operatorK1UnitalEquiv C (operatorK1Map σ w) =
      k1Map ρ.toStarAlgHom (operatorK1UnitalEquiv B (operatorK1Map s w)) := by
  have h : σ = ρ.toStarAlgHom.toNonUnitalStarAlgHom.comp s := NonUnitalStarAlgHom.ext hσ
  subst h
  exact (congrArg (operatorK1UnitalEquiv C)
      (DFunLike.congr_fun (operatorK1Map_comp ρ.toStarAlgHom.toNonUnitalStarAlgHom s) w)).trans
    (operatorK1UnitalEquiv_natural ρ.toStarAlgHom _)

end UnitalGeneric

end BC4lean.KKTheory.GroupIso
