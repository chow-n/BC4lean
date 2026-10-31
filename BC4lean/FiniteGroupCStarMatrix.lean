import BC4lean.FiniteReducedGroupCStar
import Mathlib.Algebra.Algebra.Subalgebra.Pi
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.SimpleModule.IsAlgClosed

/-! # The reduced group C⋆-algebra of a finite group is a product of matrix algebras

For a finite group `Γ`, the reduced group C⋆-algebra is ⋆-isomorphic to a finite product of
full matrix algebras `Π i, CStarMatrix (Fin (d i)) (Fin (d i)) ℂ`.

Mathlib's Wedderburn-Artin theorem (with Maschke's theorem) gives an isomorphism of
*algebras* `GroupAlgebra Γ ≃ₐ[ℂ] Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ`, which need not
respect the involutions. We correct it by the unitary trick: for a homomorphism
`ρ : Γ →* A` into a unital C⋆-algebra, the averaged Gram element `P = ∑ g, (ρ g)⋆ ρ g`
satisfies `1 ≤ P` and `(ρ h)⋆ P ρ h = P`. With `S = √P`, which is invertible and
self-adjoint, every `S ρ(g) S⁻¹` is unitary. Conjugating an algebra isomorphism
`GroupAlgebra Γ ≃ₐ[ℂ] A` by `S` therefore gives a ⋆-algebra isomorphism.

## Main declarations

* `BC4lean.GroupAlgebra.averagedGram`: the element `∑ g, (ρ g)⋆ ρ g`.
* `BC4lean.GroupAlgebra.unitarizedHom`: `x ↦ S x S⁻¹` composed with `ρ`, as a monoid hom
  into the unitary-valued maps, extended to a ⋆-algebra hom on the group algebra.
* `BC4lean.GroupAlgebra.starAlgEquivOfAlgEquiv`: an algebra isomorphism from the group algebra
  of a finite group onto a unital C⋆-algebra, conjugated into a ⋆-algebra isomorphism.
* `BC4lean.exists_reducedStarAlgEquiv_pi`: `ReducedGroupCStar Γ ≃⋆ₐ[ℂ] Π i, M_{d i}(ℂ)` for
  finite `Γ`.
* `BC4lean.card_blocks_eq_card_conjClasses`: in any such decomposition the number of blocks is
  the number of conjugacy classes (compare the dimensions of the centres);
  `BC4lean.sum_sq_blocks_eq_card`: `∑ i, d i ^ 2 = Nat.card Γ`.
* `BC4lean.exists_reducedStarAlgEquiv_pi_conjClasses_isometry`: the decomposition indexed by
  `Fin (Nat.card (ConjClasses Γ))`, with the ⋆-isomorphism isometric.

Orders on C⋆-algebras are spectral orders, as in `NonunitalOperatorK.lean`.
-/

noncomputable section

namespace BC4lean

/-! ### The unitary trick -/

namespace GroupAlgebra

local instance cstarSpectralOrder (B : Type*) [CStarAlgebra B] : PartialOrder B :=
  CStarAlgebra.spectralOrder B
local instance cstarSpectralOrderedRing (B : Type*) [CStarAlgebra B] : StarOrderedRing B :=
  CStarAlgebra.spectralOrderedRing B

section UnitaryTrick

variable {G : Type*} [Group G] [Fintype G] {A : Type*} [CStarAlgebra A]

/-- The averaged Gram element `∑ g, (ρ g)⋆ ρ g` of a homomorphism into a C⋆-algebra. -/
def averagedGram (ρ : G →* A) : A := ∑ g, star (ρ g) * ρ g

theorem star_mul_averagedGram_mul (ρ : G →* A) (h : G) :
    star (ρ h) * averagedGram ρ * ρ h = averagedGram ρ := by
  have hterm : ∀ g, star (ρ h) * (star (ρ g) * ρ g) * ρ h = star (ρ (g * h)) * ρ (g * h) := by
    intro g
    simp only [map_mul, star_mul, mul_assoc]
  rw [averagedGram, Finset.mul_sum, Finset.sum_mul]
  simp_rw [hterm]
  exact Fintype.sum_equiv (Equiv.mulRight h) _ _ fun _ => rfl

theorem star_mul_averagedGram (ρ : G →* A) (h : G) :
    star (ρ h) * averagedGram ρ = averagedGram ρ * ρ h⁻¹ := by
  calc star (ρ h) * averagedGram ρ = star (ρ h) * averagedGram ρ * (ρ h * ρ h⁻¹) := by
        rw [← map_mul, mul_inv_cancel, map_one, mul_one]
    _ = averagedGram ρ * ρ h⁻¹ := by
        rw [← mul_assoc, star_mul_averagedGram_mul]

theorem one_le_averagedGram (ρ : G →* A) : 1 ≤ averagedGram ρ := by
  classical
  rw [averagedGram, ← Finset.add_sum_erase _ _ (Finset.mem_univ 1)]
  simp only [map_one, star_one, mul_one]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun g _ => star_mul_self_nonneg (ρ g))

theorem averagedGram_nonneg (ρ : G →* A) : 0 ≤ averagedGram ρ :=
  zero_le_one.trans (one_le_averagedGram ρ)

theorem isUnit_averagedGram (ρ : G →* A) : IsUnit (averagedGram ρ) :=
  CStarAlgebra.isUnit_of_le 1 (one_le_averagedGram ρ)

/-- The positive square root of the averaged Gram element, as a unit. -/
def unitarizer (ρ : G →* A) : Aˣ :=
  ((CFC.isUnit_sqrt_iff _ (averagedGram_nonneg ρ)).2 (isUnit_averagedGram ρ)).unit

theorem coe_unitarizer (ρ : G →* A) : (unitarizer ρ : A) = CFC.sqrt (averagedGram ρ) := rfl

theorem star_unitarizer (ρ : G →* A) : star (unitarizer ρ : A) = unitarizer ρ := by
  rw [coe_unitarizer]
  exact (CFC.sqrt_nonneg _).isSelfAdjoint.star_eq

theorem star_unitarizer_inv (ρ : G →* A) :
    star ((unitarizer ρ)⁻¹ : Aˣ).val = ((unitarizer ρ)⁻¹ : Aˣ).val := by
  rw [← Units.mul_eq_one_iff_eq_inv]
  conv_lhs => rw [← star_unitarizer ρ, ← star_mul]
  simp

theorem unitarizer_mul_self (ρ : G →* A) :
    (unitarizer ρ : A) * unitarizer ρ = averagedGram ρ := by
  rw [coe_unitarizer]
  exact CFC.sqrt_mul_sqrt_self _ (averagedGram_nonneg ρ)

/-- `g ↦ S ρ(g) S⁻¹` with `S` the unitarizer: a homomorphism with unitary values. -/
def unitarized (ρ : G →* A) : G →* A where
  toFun g := unitarizer ρ * ρ g * ↑(unitarizer ρ)⁻¹
  map_one' := by simp
  map_mul' g h := by simp [mul_assoc]

theorem unitarized_apply (ρ : G →* A) (g : G) :
    unitarized ρ g = unitarizer ρ * ρ g * ↑(unitarizer ρ)⁻¹ := rfl

theorem star_unitarized (ρ : G →* A) (g : G) :
    star (unitarized ρ g) = unitarized ρ g⁻¹ := by
  rw [unitarized_apply, unitarized_apply, star_mul, star_mul, star_unitarizer_inv,
    star_unitarizer]
  -- `S⁻¹ ρ(g)⋆ S = S ρ(g⁻¹) S⁻¹`: multiply by `S` on both sides.
  apply (Units.mul_right_inj (unitarizer ρ)).1
  apply (Units.mul_left_inj (unitarizer ρ)).1
  have hl : (unitarizer ρ : A) * (↑(unitarizer ρ)⁻¹ * (star (ρ g) * unitarizer ρ)) *
      unitarizer ρ = star (ρ g) * (unitarizer ρ * unitarizer ρ) := by
    simp [mul_assoc]
  have hr : (unitarizer ρ : A) * (unitarizer ρ * ρ g⁻¹ * ↑(unitarizer ρ)⁻¹) * unitarizer ρ =
      (unitarizer ρ * unitarizer ρ) * ρ g⁻¹ := by
    simp [mul_assoc]
  rw [hl, hr, unitarizer_mul_self, star_mul_averagedGram]

end UnitaryTrick

section StarEquiv

variable {G : Type*} [Group G] [Fintype G] {A : Type*} [CStarAlgebra A]

/-- The ⋆-algebra hom `GroupAlgebra G →⋆ₐ[ℂ] A` extending the unitarized homomorphism. -/
def unitarizedHom (ρ : G →* A) : GroupAlgebra G →⋆ₐ[ℂ] A where
  toAlgHom := MonoidAlgebra.lift ℂ A G (unitarized ρ)
  map_star' a := by
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb =>
      simp only [AlgHom.toFun_eq_coe, star_add, map_add] at ha hb ⊢
      rw [ha, hb]
    | single g z =>
      change MonoidAlgebra.lift ℂ A G _ (involution _) = _
      rw [involution_single]
      simp [MonoidAlgebra.lift_single, star_smul, star_unitarized]

theorem unitarizedHom_single (ρ : G →* A) (g : G) (z : ℂ) :
    unitarizedHom ρ (MonoidAlgebra.single g z) = z • unitarized ρ g :=
  MonoidAlgebra.lift_single _ _ _

/-- The homomorphism `ρ` underlying an algebra hom out of the group algebra. -/
abbrev groupHom (f : GroupAlgebra G →ₐ[ℂ] A) : G →* A :=
  f.toMonoidHom.comp (MonoidAlgebra.of ℂ G)

theorem unitarizedHom_groupHom_apply (f : GroupAlgebra G →ₐ[ℂ] A) (x : GroupAlgebra G) :
    unitarizedHom (groupHom f) x =
      unitarizer (groupHom f) * f x * ↑(unitarizer (groupHom f))⁻¹ := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, mul_add, add_mul]
  | single g z =>
    have hz : MonoidAlgebra.single g z = z • MonoidAlgebra.single g (1 : ℂ) := by
      rw [MonoidAlgebra.smul_single', mul_one]
    rw [unitarizedHom_single, unitarized_apply, hz, map_smul, mul_smul_comm, smul_mul_assoc]
    rfl

/-- An algebra isomorphism from the group algebra of a finite group onto a unital C⋆-algebra,
conjugated by its unitarizer, is a ⋆-algebra isomorphism. -/
def starAlgEquivOfAlgEquiv (e : GroupAlgebra G ≃ₐ[ℂ] A) : GroupAlgebra G ≃⋆ₐ[ℂ] A :=
  StarAlgEquiv.ofBijective (unitarizedHom (groupHom e.toAlgHom)) <| by
    set S := unitarizer (groupHom e.toAlgHom)
    have h : ∀ x, unitarizedHom (groupHom e.toAlgHom) x = S * e x * ↑S⁻¹ :=
      unitarizedHom_groupHom_apply e.toAlgHom
    refine ⟨fun x y hxy => e.injective ?_, fun b => ⟨e.symm (↑S⁻¹ * b * S), ?_⟩⟩
    · rw [h, h] at hxy
      simpa using hxy
    · rw [h, e.apply_symm_apply]
      simp [mul_assoc]

theorem starAlgEquivOfAlgEquiv_apply (e : GroupAlgebra G ≃ₐ[ℂ] A) (x : GroupAlgebra G) :
    starAlgEquivOfAlgEquiv e x =
      unitarizer (groupHom e.toAlgHom) * e x * ↑(unitarizer (groupHom e.toAlgHom))⁻¹ :=
  unitarizedHom_groupHom_apply e.toAlgHom x

end StarEquiv

end GroupAlgebra

/-! ### Counting the blocks: the centre -/

section Centre

/-- An algebra isomorphism restricts to a linear isomorphism of centres. -/
def centerLinearEquiv {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A]
    [Algebra R B] (e : A ≃ₐ[R] B) :
    Subalgebra.toSubmodule (Subalgebra.center R A) ≃ₗ[R]
      Subalgebra.toSubmodule (Subalgebra.center R B) :=
  e.toLinearEquiv.ofSubmodules _ _ <| by
    ext z
    rw [Submodule.mem_map_equiv]
    simp only [Subalgebra.mem_toSubmodule, Subalgebra.mem_center_iff]
    constructor
    · intro h b
      apply e.symm.injective
      simpa using h (e.symm b)
    · intro h a
      have := congrArg e.symm (h (e a))
      simpa using this

theorem finrank_center_congr {A B : Type*} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]
    (e : A ≃ₐ[ℂ] B) :
    Module.finrank ℂ (Subalgebra.center ℂ A) = Module.finrank ℂ (Subalgebra.center ℂ B) :=
  (centerLinearEquiv e).finrank_eq

namespace GroupAlgebra

variable {G : Type*} [Group G]

/-- An element of the group algebra is central iff its coefficients are constant on
conjugacy classes. -/
theorem mem_center_iff_coeff_conj (a : GroupAlgebra G) :
    a ∈ Subalgebra.center ℂ (GroupAlgebra G) ↔ ∀ g x : G, a.coeff (g * x * g⁻¹) = a.coeff x := by
  rw [Subalgebra.mem_center_iff]
  constructor
  · intro h g x
    have := congrArg (fun b : GroupAlgebra G => b.coeff (g * x)) (h (MonoidAlgebra.single g 1))
    simp only [MonoidAlgebra.coeff_single_mul_apply, MonoidAlgebra.coeff_mul_single_apply,
      one_mul, mul_one, inv_mul_cancel_left] at this
    exact this.symm
  · intro h b
    induction b using MonoidAlgebra.induction_linear with
    | zero => simp
    | add b c hb hc => rw [add_mul, mul_add, hb, hc]
    | single g r =>
      ext y
      rw [MonoidAlgebra.coeff_single_mul_apply, MonoidAlgebra.coeff_mul_single_apply, mul_comm,
        ← h g (g⁻¹ * y)]
      simp

variable [Fintype G]

/-- The class function `c` as an element of the group algebra. -/
def ofClassFunction : (ConjClasses G → ℂ) →ₗ[ℂ] GroupAlgebra G :=
  (MonoidAlgebra.coeffLinearEquiv ℂ).symm.toLinearMap ∘ₗ
    (Finsupp.linearEquivFunOnFinite ℂ ℂ G).symm.toLinearMap ∘ₗ
    LinearMap.funLeft ℂ ℂ ConjClasses.mk

@[simp] theorem coeff_ofClassFunction (c : ConjClasses G → ℂ) (g : G) :
    (ofClassFunction c).coeff g = c (ConjClasses.mk g) := rfl

theorem ofClassFunction_mem_center (c : ConjClasses G → ℂ) :
    ofClassFunction c ∈ Subalgebra.center ℂ (GroupAlgebra G) := by
  rw [mem_center_iff_coeff_conj]
  intro g x
  simp only [coeff_ofClassFunction]
  congr 1
  exact ConjClasses.mk_eq_mk_iff_isConj.2 (isConj_iff.2 ⟨g, rfl⟩).symm

/-- The centre of the group algebra of a finite group is the space of class functions. -/
def classFunctionEquivCenter :
    (ConjClasses G → ℂ) ≃ₗ[ℂ] Subalgebra.toSubmodule (Subalgebra.center ℂ (GroupAlgebra G)) :=
  LinearEquiv.ofBijective (ofClassFunction.codRestrict _ ofClassFunction_mem_center) <| by
    refine ⟨fun c c' h => funext fun k => ?_, fun a => ?_⟩
    · obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective k
      have := congrArg (fun a : Subalgebra.toSubmodule (Subalgebra.center ℂ (GroupAlgebra G)) =>
        (a : GroupAlgebra G).coeff g) h
      simpa using this
    · have ha := (mem_center_iff_coeff_conj (a : GroupAlgebra G)).1 a.2
      refine ⟨Quotient.lift (fun g => (a : GroupAlgebra G).coeff g) ?_, ?_⟩
      · intro x y hxy
        obtain ⟨g, rfl⟩ := isConj_iff.1 hxy
        exact (ha g x).symm
      · apply Subtype.ext
        ext g
        rfl

theorem finrank_center : Module.finrank ℂ (Subalgebra.center ℂ (GroupAlgebra G)) =
    Nat.card (ConjClasses G) := by
  classical
  change Module.finrank ℂ (Subalgebra.toSubmodule (Subalgebra.center ℂ (GroupAlgebra G))) = _
  rw [← classFunctionEquivCenter.finrank_eq, Module.finrank_fintype_fun_eq_card,
    Nat.card_eq_fintype_card]

end GroupAlgebra

/-- Scalars in each block: the centre of a finite product of full matrix algebras. -/
def piScalarEquivCenter {n : ℕ} (d : Fin n → ℕ) [∀ i, NeZero (d i)] :
    (Fin n → ℂ) ≃ₗ[ℂ] Subalgebra.toSubmodule
      (Subalgebra.center ℂ (Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ)) :=
  LinearEquiv.ofBijective
    ((LinearMap.pi fun i => (Algebra.linearMap ℂ (Matrix (Fin (d i)) (Fin (d i)) ℂ)) ∘ₗ
      LinearMap.proj i).codRestrict _ fun c => by
        rw [Subalgebra.mem_toSubmodule, Subalgebra.center_pi, Subalgebra.mem_pi]
        intro i _
        exact Subalgebra.algebraMap_mem _ (c i)) <| by
    refine ⟨fun c c' h => funext fun i => ?_, fun x => ?_⟩
    · have := congrFun (congrArg Subtype.val h) i
      exact (algebraMap ℂ (Matrix (Fin (d i)) (Fin (d i)) ℂ)).injective this
    · obtain ⟨y, hx⟩ := x
      rw [Subalgebra.mem_toSubmodule, Subalgebra.center_pi, Subalgebra.mem_pi] at hx
      have hs : ∀ i, ∃ z : ℂ, Matrix.scalar (Fin (d i)) z = y i := by
        intro i
        have hi := hx i (Set.mem_univ i)
        rw [Subalgebra.mem_center_iff] at hi
        have : y i ∈ Set.center (Matrix (Fin (d i)) (Fin (d i)) ℂ) :=
          Semigroup.mem_center_iff.2 hi
        rwa [Matrix.center_eq_range] at this
      choose z hz using hs
      exact ⟨z, Subtype.ext <| funext fun i => hz i⟩

theorem finrank_center_pi_matrix {n : ℕ} (d : Fin n → ℕ) [∀ i, NeZero (d i)] :
    Module.finrank ℂ (Subalgebra.center ℂ (Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ)) = n := by
  change Module.finrank ℂ (Subalgebra.toSubmodule
    (Subalgebra.center ℂ (Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ))) = n
  rw [← (piScalarEquivCenter d).finrank_eq, Module.finrank_fin_fun]

/-- The number of matrix blocks of the group algebra of a finite group is the number of
conjugacy classes. -/
theorem card_conjClasses_eq_of_algEquiv_pi {Γ : Type*} [Group Γ] [Finite Γ] {n : ℕ}
    {d : Fin n → ℕ} [∀ i, NeZero (d i)]
    (e : GroupAlgebra Γ ≃ₐ[ℂ] Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    n = Nat.card (ConjClasses Γ) := by
  have : Fintype Γ := Fintype.ofFinite Γ
  rw [← GroupAlgebra.finrank_center, finrank_center_congr e, finrank_center_pi_matrix]

end Centre

/-! ### Finite groups -/

section FiniteProduct

open scoped ComplexOrder

variable {Γ : Type*} [Group Γ] [Finite Γ]

/-- Wedderburn-Artin for the complex group algebra of a finite group, as an algebra
isomorphism onto a product of `CStarMatrix` algebras. -/
theorem exists_groupAlgebra_algEquiv_pi :
    ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, NeZero (d i)) ∧
      Nonempty (GroupAlgebra Γ ≃ₐ[ℂ] Π i, CStarMatrix (Fin (d i)) (Fin (d i)) ℂ) := by
  have : Fintype Γ := Fintype.ofFinite Γ
  have : NeZero (Nat.card Γ : ℂ) := ⟨Nat.cast_ne_zero.2 Nat.card_pos.ne'⟩
  obtain ⟨n, d, hd, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ (GroupAlgebra Γ)
  exact ⟨n, d, hd, ⟨e.trans <| AlgEquiv.piCongrRight fun i =>
    (CStarMatrix.ofMatrixStarAlgEquiv (n := Fin (d i)) (A := ℂ)).toAlgEquiv⟩⟩

/-- The group algebra of a finite group is ⋆-isomorphic to a product of full matrix
algebras. -/
theorem exists_groupAlgebra_starAlgEquiv_pi :
    ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, NeZero (d i)) ∧
      Nonempty (GroupAlgebra Γ ≃⋆ₐ[ℂ] Π i, CStarMatrix (Fin (d i)) (Fin (d i)) ℂ) := by
  have : Fintype Γ := Fintype.ofFinite Γ
  obtain ⟨n, d, hd, ⟨e⟩⟩ := exists_groupAlgebra_algEquiv_pi (Γ := Γ)
  exact ⟨n, d, hd, ⟨GroupAlgebra.starAlgEquivOfAlgEquiv
    (A := Π i, CStarMatrix (Fin (d i)) (Fin (d i)) ℂ) e⟩⟩

/-- The reduced group C⋆-algebra of a finite group is ⋆-isomorphic to a product of full
matrix algebras. -/
theorem exists_reducedStarAlgEquiv_pi :
    ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, NeZero (d i)) ∧
      Nonempty (ReducedGroupCStar Γ ≃⋆ₐ[ℂ] Π i, CStarMatrix (Fin (d i)) (Fin (d i)) ℂ) := by
  obtain ⟨n, d, hd, ⟨e⟩⟩ := exists_groupAlgebra_starAlgEquiv_pi (Γ := Γ)
  exact ⟨n, d, hd, ⟨finiteReducedEquiv.symm.trans e⟩⟩

/-- The matrix-block form of a ⋆-isomorphism out of the reduced group C⋆-algebra, as an algebra
isomorphism of the group algebra onto ordinary matrices. -/
def groupAlgebraAlgEquivOfReduced {n : ℕ} {d : Fin n → ℕ}
    (e : ReducedGroupCStar Γ ≃⋆ₐ[ℂ] Π i, CStarMatrix (Fin (d i)) (Fin (d i)) ℂ) :
    GroupAlgebra Γ ≃ₐ[ℂ] Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ :=
  (finiteReducedEquiv.trans e).toAlgEquiv.trans <| AlgEquiv.piCongrRight fun i =>
    (CStarMatrix.ofMatrixStarAlgEquiv (n := Fin (d i)) (A := ℂ)).symm.toAlgEquiv

/-- In any decomposition of the reduced group C⋆-algebra of a finite group into full
matrix blocks, the number of blocks is the number of conjugacy classes. -/
theorem card_blocks_eq_card_conjClasses {n : ℕ} {d : Fin n → ℕ} [∀ i, NeZero (d i)]
    (e : ReducedGroupCStar Γ ≃⋆ₐ[ℂ] Π i, CStarMatrix (Fin (d i)) (Fin (d i)) ℂ) :
    n = Nat.card (ConjClasses Γ) :=
  card_conjClasses_eq_of_algEquiv_pi (groupAlgebraAlgEquivOfReduced e)

/-- In any decomposition of the reduced group C⋆-algebra of a finite group into full matrix
blocks, the squares of the block sizes add up to the order of the group. -/
theorem sum_sq_blocks_eq_card {n : ℕ} {d : Fin n → ℕ}
    (e : ReducedGroupCStar Γ ≃⋆ₐ[ℂ] Π i, CStarMatrix (Fin (d i)) (Fin (d i)) ℂ) :
    ∑ i, d i ^ 2 = Nat.card Γ := by
  have : Fintype Γ := Fintype.ofFinite Γ
  have h := (groupAlgebraAlgEquivOfReduced e).toLinearEquiv.finrank_eq
  rw [Module.finrank_pi_fintype, (MonoidAlgebra.coeffLinearEquiv ℂ).finrank_eq,
    Module.finrank_finsupp_self] at h
  simp only [Module.finrank_matrix, Module.finrank_self, Fintype.card_fin, mul_one] at h
  rw [Nat.card_eq_fintype_card, h]
  simp [sq]

/-- The reduced group C⋆-algebra of a finite group is ⋆-isomorphic to a product of full matrix
algebras, one block for each conjugacy class. -/
theorem exists_reducedStarAlgEquiv_pi_conjClasses :
    ∃ d : Fin (Nat.card (ConjClasses Γ)) → ℕ, (∀ i, NeZero (d i)) ∧
      Nonempty (ReducedGroupCStar Γ ≃⋆ₐ[ℂ] Π i, CStarMatrix (Fin (d i)) (Fin (d i)) ℂ) := by
  obtain ⟨n, d, hd, ⟨e⟩⟩ := exists_reducedStarAlgEquiv_pi (Γ := Γ)
  have hn := card_blocks_eq_card_conjClasses e
  subst hn
  exact ⟨d, hd, ⟨e⟩⟩

/-- The ⋆-isomorphism of `exists_reducedStarAlgEquiv_pi_conjClasses` is an isomorphism of
C⋆-algebras: like every ⋆-isomorphism between C⋆-algebras, it is isometric. -/
theorem exists_reducedStarAlgEquiv_pi_conjClasses_isometry :
    ∃ d : Fin (Nat.card (ConjClasses Γ)) → ℕ, (∀ i, NeZero (d i)) ∧
      ∃ e : ReducedGroupCStar Γ ≃⋆ₐ[ℂ] Π i, CStarMatrix (Fin (d i)) (Fin (d i)) ℂ,
        Isometry e := by
  obtain ⟨d, hd, ⟨e⟩⟩ := exists_reducedStarAlgEquiv_pi_conjClasses (Γ := Γ)
  exact ⟨d, hd, e, StarAlgEquiv.isometry e⟩

end FiniteProduct

end BC4lean
