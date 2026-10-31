import BC4lean.GroupIsoReducedCStar
import BC4lean.ReducedCrossedProduct
import BC4lean.HilbertModuleEquiv
import BC4lean.KKGroupRestriction
import BC4lean.ReducedCrossedLeftRegular
import BC4lean.InteriorModuleTensorScalarExtension
import BC4lean.StandardCoefficientImageTensor
import BC4lean.KasparovDescentReducedRepresentation
import BC4lean.KasparovDescentCycleIso
import BC4lean.GroupUniverseCoefficientPushforward
import BC4lean.GradedKasparovSourcePullback
import BC4lean.AssemblyPieceHom
import BC4lean.ScalarKKNativeNaturality
import BC4lean.CutoffRestrictionNaturality
import BC4lean.ReducedCrossedScalarProduct
import BC4lean.OddKTheoryIndependentCoefficientNaturality

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Reduced crossed products along a group isomorphism

For `e : Γ ≃* Γ'` and a `Γ'`-action `β` on `B`: the isomorphism
`crossedProductEquiv e β : B ⋊ᵣ (β ∘ e) Γ ≃ B ⋊ᵣ β Γ'`, its values on generators, coefficients and left
translations, its algebraic form `a u_g ↦ a u_{e g}`, and the scalar case: for the trivial action on
`ℂ` it is the relabelling isomorphism of reduced group C⋆-algebras.
-/

noncomputable section

/-! ## Reduced crossed products along a group isomorphism

A bijection `σ : Γ ≃ Γ'` relabels finite coefficient vectors, hence gives a unitary
isomorphism of the completed regular modules `ReducedCrossedHilbertModule B Γ` and
`ReducedCrossedHilbertModule B Γ'`. For a group isomorphism `e : Γ ≃* Γ'` and a
`Γ'`-action `α` on `B`, this unitary carries the coefficient operator of the restricted
action `α ∘ e` to that of `α` and the translation by `g` to the translation by `e g`.
Conjugation by it therefore maps generators `b u_g` to `b u_{e g}`, and restricts to a
star isomorphism `ReducedCrossedProduct (α ∘ e) ≃⋆ₐ ReducedCrossedProduct α`.
-/

namespace BC4lean.KKTheory.GroupIso
open KKTheory.GroupRestriction
open KKTheory UniformSpace
open scoped InnerProductSpace

section Relabel
variable {Γ Γ' : Type*} {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [StarOrderedRing B] (σ : Γ ≃ Γ')

/-- Relabel finite coefficient vectors along a bijection of index sets. -/
def finiteRelabel : ReducedCrossedVectors B Γ →ₗ[ℂ] ReducedCrossedVectors B Γ' :=
  Finsupp.lmapDomain Bᵐᵒᵖ ℂ σ

omit [PartialOrder B] [StarOrderedRing B] in
theorem finiteRelabel_eq (x : ReducedCrossedVectors B Γ) :
    finiteRelabel σ x = x.embDomain σ.toEmbedding :=
  (Finsupp.embDomain_eq_mapDomain σ.toEmbedding x).symm

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem finiteRelabel_apply (x : ReducedCrossedVectors B Γ) (i : Γ') :
    finiteRelabel σ x i = x (σ.symm i) := by
  rw [finiteRelabel_eq]
  simpa only [Equiv.toEmbedding_apply, Equiv.apply_symm_apply] using
    Finsupp.embDomain_apply_self σ.toEmbedding x (σ.symm i)

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem finiteRelabel_symm_relabel (x : ReducedCrossedVectors B Γ) :
    finiteRelabel σ.symm (finiteRelabel σ x) = x := by
  ext i
  simp only [finiteRelabel_apply, Equiv.symm_symm, Equiv.symm_apply_apply]

theorem finiteRelabel_inner (x : ReducedCrossedVectors B Γ) (y : ReducedCrossedVectors B Γ') :
    reducedCrossedFiniteInner (finiteRelabel σ x) y =
      reducedCrossedFiniteInner x (finiteRelabel σ.symm y) := by
  rw [finiteRelabel_eq]
  simp only [reducedCrossedFiniteInner, Finsupp.sum_embDomain, finiteRelabel_apply,
    Equiv.symm_symm, Equiv.toEmbedding_apply]

theorem finiteRelabel_inner_map (x y : ReducedCrossedVectors B Γ) :
    reducedCrossedFiniteInner (finiteRelabel σ x) (finiteRelabel σ y) =
      reducedCrossedFiniteInner x y := by
  rw [finiteRelabel_inner, finiteRelabel_symm_relabel]

theorem finiteRelabel_formNorm (x : ReducedCrossedVectors B Γ) :
    PositiveModuleForm.formNorm (B := B) (finiteRelabel σ x) =
      PositiveModuleForm.formNorm (B := B) x := by
  simp only [PositiveModuleForm.formNorm, reducedCrossedFinite_inner, finiteRelabel_inner_map]

/-- Relabelling on the normed finite-vector quotients, with the inverse relabelling as adjoint. -/
def quotientRelabel :
    AdjointableMap B (ReducedCrossedPreModule B Γ) (ReducedCrossedPreModule B Γ') where
  toCLM := positiveModuleQuotientLiftCLM (finiteRelabel σ) (K := 1)
    (fun x => by rw [finiteRelabel_formNorm]; simp only [one_mul, le_refl])
  adjointCLM := positiveModuleQuotientLiftCLM (finiteRelabel σ.symm) (K := 1)
    (fun x => by rw [finiteRelabel_formNorm]; simp only [one_mul, le_refl])
  adjoint_identity q r := by
    obtain ⟨x, rfl⟩ := positiveModuleQuotientMk_surjective q
    obtain ⟨y, rfl⟩ := positiveModuleQuotientMk_surjective r
    rw [positiveModuleQuotientLiftCLM_mk, positiveModuleQuotientLiftCLM_mk,
      PositiveModuleQuotient.inner_mk, PositiveModuleQuotient.inner_mk]
    exact finiteRelabel_inner σ x y

/-- Relabelling on the completed regular modules. -/
def moduleRelabelMap :
    AdjointableMap B (ReducedCrossedHilbertModule B Γ) (ReducedCrossedHilbertModule B Γ') :=
  (quotientRelabel σ).completion

@[simp] theorem moduleRelabelMap_mk (x : ReducedCrossedVectors B Γ) :
    moduleRelabelMap σ (reducedCrossedMk x) = reducedCrossedMk (finiteRelabel σ x) := by
  rw [reducedCrossedMk_apply, moduleRelabelMap, AdjointableMap.completion_apply_coe,
    reducedCrossedMk_apply]
  rfl

@[simp] theorem moduleRelabelMap_adjoint_mk (x : ReducedCrossedVectors B Γ') :
    (moduleRelabelMap σ).adjoint (reducedCrossedMk x) =
      reducedCrossedMk (finiteRelabel σ.symm x) := by
  rw [reducedCrossedMk_apply, moduleRelabelMap, AdjointableMap.completion_adjoint,
    AdjointableMap.completion_apply_coe, reducedCrossedMk_apply]
  rfl

theorem moduleRelabelMap_adjoint :
    (moduleRelabelMap (B := B) σ).adjoint = moduleRelabelMap σ.symm := by
  apply reducedCrossed_adjointable_ext_mk
  intro x
  rw [moduleRelabelMap_adjoint_mk, moduleRelabelMap_mk]

theorem moduleRelabelMap_symm_apply (x : ReducedCrossedHilbertModule B Γ) :
    moduleRelabelMap σ.symm (moduleRelabelMap σ x) = x := by
  have h : (moduleRelabelMap (B := B) σ.symm).comp (moduleRelabelMap σ) = AdjointableMap.id := by
    apply reducedCrossed_adjointable_ext_mk
    intro y
    simp only [AdjointableMap.comp_apply, moduleRelabelMap_mk, finiteRelabel_symm_relabel,
      AdjointableMap.id_apply]
  exact congrArg (fun T : AdjointableMap B (ReducedCrossedHilbertModule B Γ)
    (ReducedCrossedHilbertModule B Γ) => T x) h

theorem moduleRelabelMap_inner (x y : ReducedCrossedHilbertModule B Γ) :
    ⟪moduleRelabelMap σ x, moduleRelabelMap σ y⟫_(Bᵐᵒᵖ) = ⟪x, y⟫_(Bᵐᵒᵖ) := by
  rw [(moduleRelabelMap (B := B) σ).adjoint_identity]
  change ⟪x, (moduleRelabelMap σ).adjoint (moduleRelabelMap σ y)⟫_(Bᵐᵒᵖ) = _
  rw [moduleRelabelMap_adjoint, moduleRelabelMap_symm_apply]

/-- The unitary relabelling isomorphism of regular modules. -/
def moduleRelabel :
    HilbertModuleEquiv B (ReducedCrossedHilbertModule B Γ) (ReducedCrossedHilbertModule B Γ') where
  linearIsometryEquiv :=
    { toLinearEquiv :=
        { toFun := fun x => moduleRelabelMap σ x
          invFun := fun x => moduleRelabelMap σ.symm x
          left_inv := moduleRelabelMap_symm_apply σ
          right_inv := fun x => by
            simpa only [Equiv.symm_symm] using moduleRelabelMap_symm_apply σ.symm x
          map_add' := (moduleRelabelMap (B := B) σ).toCLM.map_add
          map_smul' := (moduleRelabelMap (B := B) σ).toCLM.map_smul }
      norm_map' := fun x => by
        change ‖moduleRelabelMap σ x‖ = ‖x‖
        rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ), moduleRelabelMap_inner]
        exact (CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) x).symm }
  inner_map := moduleRelabelMap_inner σ

@[simp] theorem moduleRelabel_apply (x : ReducedCrossedHilbertModule B Γ) :
    moduleRelabel σ x = moduleRelabelMap σ x := rfl

@[simp] theorem moduleRelabel_symm_apply (x : ReducedCrossedHilbertModule B Γ') :
    (moduleRelabel σ).symm x = moduleRelabelMap σ.symm x := rfl

end Relabel

section Group
variable {Γ Γ' : Type*} [Group Γ] [Group Γ'] (e : Γ ≃* Γ')
  {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  (α : CStarAlgebraAction Γ' B)

/-- The relabelling unitary intertwines the coefficient operators. -/
theorem moduleRelabelMap_coefficient (b : B) :
    (moduleRelabelMap e.toEquiv).comp (reducedCrossedCoefficient (actionComap e.toMonoidHom α) b) =
      (reducedCrossedCoefficient α b).comp (moduleRelabelMap e.toEquiv) := by
  apply reducedCrossed_adjointable_ext_mk
  intro x
  simp only [AdjointableMap.comp_apply, reducedCrossedCoefficient_mk, moduleRelabelMap_mk]
  congr 1
  ext i
  simp only [finiteRelabel_apply, reducedCrossedFiniteDiagonal_apply]
  rw [actionComap_apply]
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv_symm, MulEquiv.coe_toMonoidHom, map_inv,
    MulEquiv.apply_symm_apply]

/-- The relabelling unitary intertwines translation by `g` with translation by `e g`. -/
theorem moduleRelabelMap_regular (g : Γ) :
    (moduleRelabelMap (B := B) e.toEquiv).comp (reducedCrossedRegular g) =
      (reducedCrossedRegular (e g)).comp (moduleRelabelMap e.toEquiv) := by
  apply reducedCrossed_adjointable_ext_mk
  intro x
  simp only [AdjointableMap.comp_apply, reducedCrossedRegular_mk, moduleRelabelMap_mk]
  congr 1
  ext i
  simp only [finiteRelabel_apply, reducedCrossedRegular_finite_apply,
    MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv_symm, map_mul, map_inv,
    MulEquiv.symm_apply_apply]

/-- Transport of an operator that is intertwined by the relabelling map. -/
theorem transport_of_intertwine
    {S : AdjointableMap B (ReducedCrossedHilbertModule B Γ) (ReducedCrossedHilbertModule B Γ)}
    {T : AdjointableMap B (ReducedCrossedHilbertModule B Γ') (ReducedCrossedHilbertModule B Γ')}
    (h : (moduleRelabelMap e.toEquiv).comp S = T.comp (moduleRelabelMap e.toEquiv)) :
    (moduleRelabel (B := B) e.toEquiv).transport S = T := by
  ext x
  rw [HilbertModuleEquiv.transport_apply, moduleRelabel_apply, moduleRelabel_symm_apply]
  have h' := congrArg (fun R : AdjointableMap B (ReducedCrossedHilbertModule B Γ)
    (ReducedCrossedHilbertModule B Γ') => R (moduleRelabelMap e.toEquiv.symm x)) h
  simp only [AdjointableMap.comp_apply] at h'
  rw [h']
  congr 1
  simpa only [Equiv.symm_symm] using moduleRelabelMap_symm_apply e.toEquiv.symm x

/-- Conjugation by the relabelling unitary sends `b u_g` to `b u_{e g}`. -/
theorem transport_generator (b : B) (g : Γ) :
    (moduleRelabel (B := B) e.toEquiv).transport
        (reducedCrossedGenerator (actionComap e.toMonoidHom α) b g) =
      reducedCrossedGenerator α b (e g) := by
  rw [reducedCrossedGenerator, HilbertModuleEquiv.transport_mul,
    transport_of_intertwine e (moduleRelabelMap_coefficient e α b),
    transport_of_intertwine e (moduleRelabelMap_regular e g)]
  rfl

/-- Conjugation by the relabelling unitary, as a star isomorphism of operator algebras. -/
abbrev crossedConj :
    AdjointableMap B (ReducedCrossedHilbertModule B Γ) (ReducedCrossedHilbertModule B Γ) ≃⋆ₐ[ℂ]
      AdjointableMap B (ReducedCrossedHilbertModule B Γ') (ReducedCrossedHilbertModule B Γ') :=
  (moduleRelabel e.toEquiv).transportStarAlgEquiv

theorem crossedConj_continuous : Continuous (crossedConj (B := B) e) :=
  AddMonoidHomClass.continuous_of_bound _ 1 (fun T => by
    change ‖(moduleRelabel (B := B) e.toEquiv).transport T‖ ≤ 1 * ‖T‖
    rw [HilbertModuleEquiv.transport_norm, one_mul])

theorem crossedConj_symm_eq
    (T : AdjointableMap B (ReducedCrossedHilbertModule B Γ') (ReducedCrossedHilbertModule B Γ')) :
    (crossedConj (B := B) e).symm T = crossedConj e.symm T := by
  ext x
  rfl

theorem crossedConj_mem
    (T : AdjointableMap B (ReducedCrossedHilbertModule B Γ) (ReducedCrossedHilbertModule B Γ))
    (hT : T ∈ reducedCrossedAlgebra (actionComap e.toMonoidHom α)) :
    crossedConj e T ∈ reducedCrossedAlgebra α := by
  have hle : reducedCrossedAlgebra (actionComap e.toMonoidHom α) ≤
      (reducedCrossedAlgebra α).comap (crossedConj (B := B) e) := by
    apply reducedCrossedAlgebra_minimal
    · exact (reducedCrossedAlgebra_isClosed α).preimage (crossedConj_continuous e)
    · intro b g
      change crossedConj e (reducedCrossedGenerator (actionComap e.toMonoidHom α) b g) ∈
        reducedCrossedAlgebra α
      change (moduleRelabel (B := B) e.toEquiv).transport _ ∈ _
      rw [transport_generator]
      exact reducedCrossedGenerator_mem α b (e g)
  exact hle hT

theorem crossedConj_symm_mem
    (T : AdjointableMap B (ReducedCrossedHilbertModule B Γ') (ReducedCrossedHilbertModule B Γ'))
    (hT : T ∈ reducedCrossedAlgebra α) :
    (crossedConj (B := B) e).symm T ∈ reducedCrossedAlgebra (actionComap e.toMonoidHom α) := by
  have hα : α = actionComap e.symm.toMonoidHom (actionComap e.toMonoidHom α) := by
    cases α
    congr 1
    ext g b
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [actionComap_apply]
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  rw [crossedConj_symm_eq]
  rw [hα] at hT
  exact crossedConj_mem e.symm (actionComap e.toMonoidHom α) T hT

/-- Reduced crossed products along a group isomorphism. -/
def crossedProductEquiv :
    ReducedCrossedProduct (actionComap e.toMonoidHom α) ≃⋆ₐ[ℂ] ReducedCrossedProduct α where
  toFun x := ⟨crossedConj e x.1, crossedConj_mem e α x.1 x.2⟩
  invFun y := ⟨(crossedConj e).symm y.1, crossedConj_symm_mem e α y.1 y.2⟩
  left_inv x := Subtype.ext ((crossedConj e).symm_apply_apply x.1)
  right_inv y := Subtype.ext ((crossedConj e).apply_symm_apply y.1)
  map_mul' x y := Subtype.ext (map_mul (crossedConj e) x.1 y.1)
  map_add' x y := Subtype.ext (map_add (crossedConj e) x.1 y.1)
  map_star' x := Subtype.ext (map_star (crossedConj e) x.1)
  map_smul' c x := Subtype.ext (map_smul (crossedConj e) c x.1)

@[simp] theorem crossedProductEquiv_coe (x : ReducedCrossedProduct (actionComap e.toMonoidHom α)) :
    (crossedProductEquiv e α x : AdjointableMap B (ReducedCrossedHilbertModule B Γ')
      (ReducedCrossedHilbertModule B Γ')) = (moduleRelabel e.toEquiv).transport x.1 := rfl

theorem crossedProductEquiv_generator (b : B) (g : Γ) :
    (crossedProductEquiv e α ⟨_, reducedCrossedGenerator_mem _ b g⟩ :
      AdjointableMap B (ReducedCrossedHilbertModule B Γ') (ReducedCrossedHilbertModule B Γ')) =
      reducedCrossedGenerator α b (e g) :=
  transport_generator e α b g

end Group

end BC4lean.KKTheory.GroupIso

/-! ## Generators, coefficients and left translations -/

namespace BC4lean.KKTheory.GroupIso
open KKTheory.GroupRestriction
open KKTheory KKTheory.KasparovDescent
open scoped InnerProductSpace KasparovDescent

variable {Γ Γ' : Type*} [Group Γ] [Group Γ'] (e : Γ ≃* Γ')
  {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  (β : CStarAlgebraAction Γ' B)

/-- `Φ` carries left translation by `g` to left translation by `e g`. -/
theorem crossedProductEquiv_leftRegular (g : Γ)
    (c : ReducedCrossedProduct (actionComap e.toMonoidHom β)) :
    crossedProductEquiv e β (KasparovDescent.leftRegular (actionComap e.toMonoidHom β) g c) =
      KasparovDescent.leftRegular β (e g) (crossedProductEquiv e β c) := by
  apply Subtype.ext
  simp only [crossedProductEquiv_coe, leftRegular_coe, HilbertModuleEquiv.transport_mul,
    transport_of_intertwine e (moduleRelabelMap_regular e g)]

/-- `Φ` fixes the coefficient inclusion of `B`. -/
theorem crossedProductEquiv_coefficient (b : B) :
    crossedProductEquiv e β (coefficientToReducedCrossed (actionComap e.toMonoidHom β) b) =
      coefficientToReducedCrossed β b := by
  apply Subtype.ext
  simp only [crossedProductEquiv_coe, coefficientToReducedCrossed_coe]
  exact transport_of_intertwine e (moduleRelabelMap_coefficient e β b)

/-- `Φ` as a nonunital star homomorphism, the form taken by coefficient pushforward. -/
abbrev crossedProductHom :
    ReducedCrossedProduct (actionComap e.toMonoidHom β) →⋆ₙₐ[ℂ] ReducedCrossedProduct β :=
  (crossedProductEquiv e β).toNonUnitalStarAlgHom

theorem crossedProductHom_coefficient (b : B) :
    standardCoefficientImageRepresentation (crossedProductHom e β)
        (coefficientToReducedCrossed (actionComap e.toMonoidHom β) b) =
      coefficientRepresentation β b := by
  change standardLeftMul (crossedProductEquiv e β
      (coefficientToReducedCrossed (actionComap e.toMonoidHom β) b)) =
    standardLeftMul (coefficientToReducedCrossed β b)
  rw [crossedProductEquiv_coefficient]

section Source
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (α : CStarAlgebraAction Γ' A)

/-- `Φ_A` on finite generators: `a u_g ↦ a u_{e g}`. -/
theorem crossedProductEquiv_single (g : Γ) (a : A) :
    crossedProductEquiv e α (algebraicToReducedCrossed (actionComap e.toMonoidHom α)
        (AlgebraicCrossedProduct.single _ g a)) =
      algebraicToReducedCrossed α (AlgebraicCrossedProduct.single α (e g) a) := by
  have h : algebraicToReducedCrossed (actionComap e.toMonoidHom α)
      (AlgebraicCrossedProduct.single _ g a) =
      ⟨_, reducedCrossedGenerator_mem (actionComap e.toMonoidHom α) a g⟩ :=
    Subtype.ext (algebraicToReducedCrossed_single _ g a)
  rw [h]
  apply Subtype.ext
  exact (crossedProductEquiv_generator e α a g).trans
    (algebraicToReducedCrossed_single α (e g) a).symm

end Source

end BC4lean.KKTheory.GroupIso

/-! ## The algebraic form -/

namespace BC4lean.KKTheory.GroupIso
open scoped ZeroAtInfty ComplexOrder CompactlySupported
open KKTheory.GroupRestriction
open KKTheory OperatorKTheory ProperActions ProperActions.Cutoff
open KKTheory.GroupUniverseParityGroup KKTheory.GroupUniverseParityFunctoriality
open scoped KasparovDescent

section Algebraic
variable {Γ Γ' : Type*} [Group Γ] [Group Γ'] [Countable Γ] [Countable Γ'] (e : Γ ≃* Γ')
  {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (α : CStarAlgebraAction Γ' A)

/-- Relabel the coefficients of a finite crossed-product element along `e`. The source action
`αΓ` plays no role in the additive structure, so it is an arbitrary argument. -/
def algRelabel (αΓ : CStarAlgebraAction Γ A) : AlgebraicCrossedProduct αΓ →+
    AlgebraicCrossedProduct α where
  toFun z := AlgebraicCrossedProduct.ofCoeff α
    (Finsupp.equivMapDomain e.toEquiv (AlgebraicCrossedProduct.coeff _ z))
  map_zero' := by
    apply AlgebraicCrossedProduct.ext α
    intro g
    rfl
  map_add' z w := by
    apply AlgebraicCrossedProduct.ext α
    intro g
    simp only [AlgebraicCrossedProduct.coeff_ofCoeff, AlgebraicCrossedProduct.coeff_add,
      Finsupp.add_apply, Finsupp.equivMapDomain_apply]

omit [Countable Γ] [Countable Γ'] [PartialOrder A] [StarOrderedRing A] in
theorem coeff_algRelabel (αΓ : CStarAlgebraAction Γ A) (z : AlgebraicCrossedProduct αΓ) (g : Γ) :
    AlgebraicCrossedProduct.coeff α (algRelabel e α αΓ z) (e g) =
      AlgebraicCrossedProduct.coeff _ z g := by
  change Finsupp.equivMapDomain e.toEquiv (AlgebraicCrossedProduct.coeff _ z) (e g) = _
  rw [Finsupp.equivMapDomain_apply]
  exact congrArg (AlgebraicCrossedProduct.coeff _ z) (e.toEquiv.symm_apply_apply g)

omit [Countable Γ] [Countable Γ'] [PartialOrder A] [StarOrderedRing A] in
theorem algRelabel_single (αΓ : CStarAlgebraAction Γ A) (g : Γ) (a : A) :
    algRelabel e α αΓ (AlgebraicCrossedProduct.single _ g a) =
      AlgebraicCrossedProduct.single α (e g) a :=
  AlgebraicCrossedProduct.ext α fun g' =>
    congrArg (fun f : Γ' →₀ A => f g') (Finsupp.equivMapDomain_single e.toEquiv g a)

omit [Countable Γ] [Countable Γ'] in
/-- `Φ (∑ a_g u_g) = ∑ a_g u_{e g}` on finite elements. -/
theorem crossedProductEquiv_algebraic (z : AlgebraicCrossedProduct (actionComap e.toMonoidHom α)) :
    crossedProductEquiv e α (algebraicToReducedCrossed (actionComap e.toMonoidHom α) z) =
      algebraicToReducedCrossed α (algRelabel e α (actionComap e.toMonoidHom α) z) := by
  induction z using AlgebraicCrossedProduct.induction_on (actionComap e.toMonoidHom α) with
  | zero => simp only [map_zero]
  | single g a =>
    rw [algRelabel_single]
    exact crossedProductEquiv_single e α g a
  | add z w hz hw =>
    have h1 := map_add (algebraicToReducedCrossed (actionComap e.toMonoidHom α)) z w
    have h2 := map_add (algRelabel e α (actionComap e.toMonoidHom α)) z w
    have h3 := map_add (algebraicToReducedCrossed α) (algRelabel e α (actionComap e.toMonoidHom α) z)
      (algRelabel e α (actionComap e.toMonoidHom α) w)
    rw [h1, h2, h3, ← hz, ← hw]
    exact (crossedProductEquiv e α).map_add' _ _

/-- `Φ` with the restricted action replaced by an equal one. -/
def crossedProductEquiv' (αΓ : CStarAlgebraAction Γ A)
    (hα : actionComap e.toMonoidHom α = αΓ) :
    ReducedCrossedProduct αΓ ≃⋆ₐ[ℂ] ReducedCrossedProduct α := by
  subst hα
  exact crossedProductEquiv e α

omit [Countable Γ] [Countable Γ'] in
theorem crossedProductEquiv'_algebraic (αΓ : CStarAlgebraAction Γ A)
    (hα : actionComap e.toMonoidHom α = αΓ) (z : AlgebraicCrossedProduct αΓ) :
    crossedProductEquiv' e α αΓ hα (algebraicToReducedCrossed αΓ z) =
      algebraicToReducedCrossed α (algRelabel e α αΓ z) := by
  subst hα
  exact crossedProductEquiv_algebraic e α z

omit [Countable Γ] [Countable Γ'] in
/-- The compatibility of `crossedProductEquiv'` with the trivial `Unit` actions, stated as the
upstream pushforward lemmas take it. -/
theorem crossedProductEquiv'_trivial (αΓ : CStarAlgebraAction Γ A)
    (hα : actionComap e.toMonoidHom α = αΓ) :
    ∀ (k : Unit) (a : ReducedCrossedProduct αΓ),
      (crossedProductEquiv' e α αΓ hα).toNonUnitalStarAlgHom
          ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit
            (ReducedCrossedProduct αΓ)).automorphism k a) =
        (CStarAlgebraAction.trivial : CStarAlgebraAction Unit
          (ReducedCrossedProduct α)).automorphism k
          ((crossedProductEquiv' e α αΓ hα).toNonUnitalStarAlgHom a) :=
  fun _ _ => rfl

end Algebraic

end BC4lean.KKTheory.GroupIso

/-! ## The analytic side of the relabelling square

`Φ_ℂ : C*_r(Γ) ≅ C*_r(Γ')` below is the crossed-product isomorphism for the trivial action on `ℂ` (the restriction
of the trivial action of `Γ'` along `e` is definitionally the trivial action of `Γ`).

* `scalar_square`: under the upstream identification of the scalar crossed product with
  `ReducedGroupCStar`, `Φ_ℂ` is the relabelling isomorphism `reducedGroupCStarEquiv e`. Both are
  continuous and agree on the generators `z u_g ↦ z λ_{e g}`; the finite elements are dense.
* `analytic_natural_even`, `analytic_natural_odd`: the comparison `KK(ℂ, C*_r Γ) → K_p(C*_r Γ)` used by assembly turns
  pushforward along `Φ_ℂ` into `analyticGroupEquiv e p`. Even degree: upstream naturality of the
  scalar K₀ comparison for the native pushforward. Odd degree: upstream proves naturality of the
  odd index only for the *ordinary* odd pushforward; `odd_native_eq_ordinary` identifies the native
  one with it through the graded Clifford bridge (both have the same graded class).
-/

namespace BC4lean.KKTheory.GroupIso
open scoped ComplexOrder
open KKTheory OperatorKTheory
open scoped KasparovDescent
open KKTheory.GroupUniverseParityGroup KKTheory.GroupUniverseParityFunctoriality

section Scalar
universe u
variable {Γ Γ' : Type u} [Group Γ] [Group Γ'] [Countable Γ] [Countable Γ'] (e : Γ ≃* Γ')

/-- `Φ_ℂ`, the crossed-product isomorphism for the trivial scalar action. -/
abbrev scalarHom : ReducedCrossedProduct (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) →⋆ₙₐ[ℂ] ReducedCrossedProduct (CStarAlgebraAction.trivial : CStarAlgebraAction Γ' ℂ) :=
  crossedProductHom e (CStarAlgebraAction.trivial : CStarAlgebraAction Γ' ℂ)

omit [Countable Γ] [Countable Γ'] in
/-- The trivial-`Unit`-action compatibility of `Φ_ℂ`, as the upstream lemmas take it. -/
theorem scalarHom_trivial :
    ∀ (k : Unit) (b : ReducedCrossedProduct (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)),
      scalarHom e ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit
          (ReducedCrossedProduct (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ))).automorphism k b) =
        (CStarAlgebraAction.trivial : CStarAlgebraAction Unit
          (ReducedCrossedProduct (CStarAlgebraAction.trivial : CStarAlgebraAction Γ' ℂ))).automorphism k (scalarHom e b) :=
  fun _ _ => rfl

/-- The scalar identification of `Γ`, as a nonunital star homomorphism. -/
abbrev scalarId (G : Type u) [Group G] :
    ReducedCrossedProduct (CStarAlgebraAction.trivial : CStarAlgebraAction G ℂ) →⋆ₙₐ[ℂ]
      ReducedGroupCStar G :=
  (reducedCrossedScalarProductEquiv (Γ := G)).toNonUnitalStarAlgHom

/-- `reducedGroupCStarEquiv e`, as a nonunital star homomorphism. -/
abbrev groupHom : ReducedGroupCStar Γ →⋆ₙₐ[ℂ] ReducedGroupCStar Γ' :=
  (reducedGroupCStarEquiv e).toNonUnitalStarAlgHom

omit [Countable Γ] [Countable Γ'] in
/-- The scalar square on generators. -/
theorem scalar_square_single (g : Γ) (a : ℂ) :
    (scalarId Γ').comp (scalarHom e)
        (algebraicToReducedCrossed (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) (AlgebraicCrossedProduct.single (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) g a)) =
      (groupHom e).comp (scalarId Γ)
        (algebraicToReducedCrossed (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) (AlgebraicCrossedProduct.single (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) g a)) := by
  have h1 : scalarHom e (algebraicToReducedCrossed (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) (AlgebraicCrossedProduct.single (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) g a)) =
      algebraicToReducedCrossed (CStarAlgebraAction.trivial : CStarAlgebraAction Γ' ℂ) (AlgebraicCrossedProduct.single (CStarAlgebraAction.trivial : CStarAlgebraAction Γ' ℂ) (e g) a) :=
    crossedProductEquiv_single e (CStarAlgebraAction.trivial : CStarAlgebraAction Γ' ℂ) g a
  change scalarId Γ' (scalarHom e (algebraicToReducedCrossed (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
      (AlgebraicCrossedProduct.single (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) g a))) = _
  rw [h1]
  apply Subtype.ext
  change reducedCrossedScalarOperatorEquiv
      ((algebraicToReducedCrossed (CStarAlgebraAction.trivial : CStarAlgebraAction Γ' ℂ) (AlgebraicCrossedProduct.single (CStarAlgebraAction.trivial : CStarAlgebraAction Γ' ℂ) (e g) a) :
        AdjointableMap ℂ (ReducedCrossedHilbertModule ℂ Γ') (ReducedCrossedHilbertModule ℂ Γ'))) =
    conj e (reducedCrossedScalarOperatorEquiv
      ((algebraicToReducedCrossed (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) (AlgebraicCrossedProduct.single (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) g a) :
        AdjointableMap ℂ (ReducedCrossedHilbertModule ℂ Γ) (ReducedCrossedHilbertModule ℂ Γ))))
  rw [algebraicToReducedCrossed_single, algebraicToReducedCrossed_single,
    reducedCrossedScalarOperatorEquiv_generator, reducedCrossedScalarOperatorEquiv_generator,
    map_smul (conj e), conj_regularOperator]

omit [Countable Γ] [Countable Γ'] in
/-- The scalar square on finite elements. -/
theorem scalar_square_algebraic (w : AlgebraicCrossedProduct (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)) :
    (scalarId Γ').comp (scalarHom e) (algebraicToReducedCrossed (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) w) =
      (groupHom e).comp (scalarId Γ) (algebraicToReducedCrossed (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) w) := by
  induction w using AlgebraicCrossedProduct.induction_on (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) with
  | zero => rw [map_zero, map_zero, map_zero]
  | single g a => exact scalar_square_single e g a
  | add z w hz hw => rw [map_add, map_add, map_add, hz, hw]

omit [Countable Γ] [Countable Γ'] in
/-- The scalar square: `Φ_ℂ` is the relabelling isomorphism of reduced group C⋆-algebras. -/
theorem scalar_square :
    (scalarId Γ').comp (scalarHom e) = (groupHom e).comp (scalarId Γ) := by
  have hf : Continuous ((scalarId Γ').comp (scalarHom e)) := by
    first
    | exact map_continuous ((scalarId Γ').comp (scalarHom e))
    | exact (StarAlgEquiv.isometry (reducedCrossedScalarProductEquiv (Γ := Γ'))).continuous.comp
        (StarAlgEquiv.isometry (crossedProductEquiv e (CStarAlgebraAction.trivial : CStarAlgebraAction Γ' ℂ))).continuous
  have hg : Continuous ((groupHom e).comp (scalarId Γ)) := by
    first
    | exact map_continuous ((groupHom e).comp (scalarId Γ))
    | exact (StarAlgEquiv.isometry (reducedGroupCStarEquiv e)).continuous.comp
        (StarAlgEquiv.isometry (reducedCrossedScalarProductEquiv (Γ := Γ))).continuous
  have h := Continuous.ext_on (algebraicToReducedCrossed_denseRange (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)) hf hg (by
    rintro _ ⟨w, rfl⟩
    exact scalar_square_algebraic e w)
  exact NonUnitalStarAlgHom.ext fun x => congrFun h x

omit [Countable Γ] [Countable Γ'] in
/-- The scalar square, pointwise, with the relabelling isomorphism as a `StarAlgEquiv`. -/
theorem scalar_square_apply (a : ReducedCrossedProduct (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)) :
    (scalarId Γ').comp (scalarHom e) a = reducedGroupCStarEquiv e (scalarId Γ a) :=
  DFunLike.congr_fun (scalar_square e) a

/-- Naturality of the analytic comparison, even degree. -/
theorem analytic_natural_even
    (z : KKParityGroup.{0, 0, u, u} false (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)))) :
    Assembly.reducedScalarKKToAnalyticHom.{u, u} Γ' false
        (coefficientPushforward.{0, 0, u, u, u} false (scalarHom e) (scalarHom_trivial e) z) =
      analyticGroupEquiv e false (Assembly.reducedScalarKKToAnalyticHom.{u, u} Γ false z) := by
  let _ : PartialOrder (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrder _
  let _ : StarOrderedRing (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrderedRing _
  let _ : PartialOrder (ReducedGroupCStar Γ') := CStarAlgebra.spectralOrder _
  let _ : StarOrderedRing (ReducedGroupCStar Γ') := CStarAlgebra.spectralOrderedRing _
  have h1 : scalarKKOperatorK0AddEquiv.{u, u}
      (coefficientPushforward.{0, 0, u, u, u} false (scalarHom e) (scalarHom_trivial e) z) =
      operatorK0Map (scalarHom e) (scalarKKOperatorK0AddEquiv.{u, u} z) :=
    Assembly.scalarKKOperatorK0_native_coefficient_natural.{u, u, u}
      (B := ReducedCrossedProduct (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)) (C := ReducedCrossedProduct (CStarAlgebraAction.trivial : CStarAlgebraAction Γ' ℂ)) (scalarHom e) z
  have hcomp : ∀ w : OperatorK0 (ReducedCrossedProduct (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)),
      operatorK0Map (scalarId Γ') (operatorK0Map (scalarHom e) w) =
        operatorK0Map ((scalarId Γ').comp (scalarHom e)) w := fun w =>
    (DFunLike.congr_fun (operatorK0Map_comp (scalarId Γ') (scalarHom e)) w).symm
  have hnat := unital_k0_natural (scalarId Γ) (reducedGroupCStarEquiv e)
    ((scalarId Γ').comp (scalarHom e)) (scalar_square_apply e)
    (scalarKKOperatorK0AddEquiv.{u, u} z)
  change operatorK0UnitalEquiv (ReducedGroupCStar Γ') (operatorK0Map (scalarId Γ')
      (scalarKKOperatorK0AddEquiv.{u, u}
        (coefficientPushforward.{0, 0, u, u, u} false (scalarHom e) (scalarHom_trivial e) z))) =
    k0Map (reducedGroupCStarEquiv e).toStarAlgHom (operatorK0UnitalEquiv (ReducedGroupCStar Γ)
      (operatorK0Map (scalarId Γ) (scalarKKOperatorK0AddEquiv.{u, u} z)))
  exact (congrArg (fun w => operatorK0UnitalEquiv (ReducedGroupCStar Γ')
      (operatorK0Map (scalarId Γ') w)) h1).trans
    ((congrArg (operatorK0UnitalEquiv (ReducedGroupCStar Γ')) (hcomp _)).trans hnat)

/-- Naturality of the analytic comparison, odd degree. -/
theorem analytic_natural_odd
    (z : KKParityGroup.{0, 0, u, u} true (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)))) :
    Assembly.reducedScalarKKToAnalyticHom.{u, u} Γ' true
        (coefficientPushforward.{0, 0, u, u, u} true (scalarHom e) (scalarHom_trivial e) z) =
      analyticGroupEquiv e true (Assembly.reducedScalarKKToAnalyticHom.{u, u} Γ true z) := by
  let _ : PartialOrder (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrder _
  let _ : StarOrderedRing (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrderedRing _
  let _ : PartialOrder (ReducedGroupCStar Γ') := CStarAlgebra.spectralOrder _
  let _ : StarOrderedRing (ReducedGroupCStar Γ') := CStarAlgebra.spectralOrderedRing _
  have h1 : oddKKOperatorK1AllModuleUniversesAddEquiv.{u, u}
      (coefficientPushforward.{0, 0, u, u, u} true (scalarHom e) (scalarHom_trivial e) z) =
      operatorK1Map (scalarHom e) (oddKKOperatorK1AllModuleUniversesAddEquiv.{u, u} z) :=
    oddIndex_native_natural (scalarHom e) (scalarHom_trivial e) z
  have hcomp : ∀ w : OperatorK1 (ReducedCrossedProduct (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)),
      operatorK1Map (scalarId Γ') (operatorK1Map (scalarHom e) w) =
        operatorK1Map ((scalarId Γ').comp (scalarHom e)) w := fun w =>
    (DFunLike.congr_fun (operatorK1Map_comp (scalarId Γ') (scalarHom e)) w).symm
  have hnat := unital_k1_natural (scalarId Γ) (reducedGroupCStarEquiv e)
    ((scalarId Γ').comp (scalarHom e)) (scalar_square_apply e)
    (oddKKOperatorK1AllModuleUniversesAddEquiv.{u, u} z)
  change operatorK1UnitalEquiv (ReducedGroupCStar Γ') (operatorK1Map (scalarId Γ')
      (oddKKOperatorK1AllModuleUniversesAddEquiv.{u, u}
        (coefficientPushforward.{0, 0, u, u, u} true (scalarHom e) (scalarHom_trivial e) z))) =
    k1Map (reducedGroupCStarEquiv e).toStarAlgHom (operatorK1UnitalEquiv (ReducedGroupCStar Γ)
      (operatorK1Map (scalarId Γ) (oddKKOperatorK1AllModuleUniversesAddEquiv.{u, u} z)))
  exact (congrArg (fun w => operatorK1UnitalEquiv (ReducedGroupCStar Γ')
      (operatorK1Map (scalarId Γ') w)) h1).trans
    ((congrArg (operatorK1UnitalEquiv (ReducedGroupCStar Γ')) (hcomp _)).trans hnat)

end Scalar

end BC4lean.KKTheory.GroupIso
