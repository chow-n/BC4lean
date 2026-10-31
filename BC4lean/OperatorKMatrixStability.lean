import BC4lean.OperatorK0Functoriality
import BC4lean.OperatorK1Functoriality
import BC4lean.UnitaryStableConjugation

/-! # Matrix stability of unital operator K₀

Let `n` be a nonempty finite type. A matrix indexed by `ι × κ` with entries in
`M_n(A) = CStarMatrix n n A` is regrouped as one matrix over `A` indexed by
`(ι × n) × (κ × n)`. The regrouping is multiplicative on rectangular matrices and
commutes with conjugate transposes, so it carries projections to projections and
rectangular Murray–von Neumann witnesses to witnesses. The reverse regrouping
does the same, so the induced map of stable projection monoids is injective.
It is surjective: a projection `p` over `A` at index `κ` is equivalent, through
the witness `p * E` with `E i (j, b) = [i = j ∧ b = b₀]`, to a projection at
index `κ × n`, and every projection at that index is a regrouped one.

The star order on `M_n(A)` is an arbitrary compatible one: it enters no
construction (Mathlib gives `CStarMatrix` no order; the spectral order
`CStarAlgebra.spectralOrder` is one choice).
-/

noncomputable section
open scoped Matrix
namespace BC4lean.OperatorKTheory

universe u
variable {A : Type u} {n : Type}

section Regroup
variable {ι κ τ : Type*}

/-- Entries of a finite sum of C⋆-matrices. -/
theorem cstarMatrix_sum_apply [AddCommMonoid A] {γ : Type*} (s : Finset γ)
    (g : γ → CStarMatrix n n A)
    (a b : n) : (∑ c ∈ s, g c) a b = ∑ c ∈ s, g c a b := by
  induction s using Finset.cons_induction with
  | empty => rfl
  | cons c s hc ih =>
    rw [Finset.sum_cons, Finset.sum_cons, CStarMatrix.add_apply, ih]

/-- Read a matrix with entries in `M_n(A)` as one matrix over `A`. -/
def matrixFlatten (v : Matrix ι κ (CStarMatrix n n A)) : Matrix (ι × n) (κ × n) A :=
  fun x y => v x.1 y.1 x.2 y.2

/-- The reverse regrouping. -/
def matrixUnflatten (w : Matrix (ι × n) (κ × n) A) : Matrix ι κ (CStarMatrix n n A) :=
  fun i j => CStarMatrix.ofMatrix fun a b => w (i, a) (j, b)

@[simp] theorem matrixFlatten_unflatten (w : Matrix (ι × n) (κ × n) A) :
    matrixFlatten (matrixUnflatten w) = w := rfl

@[simp] theorem matrixUnflatten_flatten (v : Matrix ι κ (CStarMatrix n n A)) :
    matrixUnflatten (matrixFlatten v) = v := rfl

theorem matrixFlatten_injective :
    Function.Injective (matrixFlatten : Matrix ι κ (CStarMatrix n n A) → _) := by
  intro v w h
  rw [← matrixUnflatten_flatten v, h, matrixUnflatten_flatten]

variable [CStarAlgebra A]

theorem matrixFlatten_conjTranspose (v : Matrix ι κ (CStarMatrix n n A)) :
    (matrixFlatten v)ᴴ = matrixFlatten vᴴ := rfl

variable [Fintype n]

theorem matrixFlatten_mul [Fintype κ] (v : Matrix ι κ (CStarMatrix n n A))
    (w : Matrix κ τ (CStarMatrix n n A)) :
    matrixFlatten (v * w) = matrixFlatten v * matrixFlatten w := by
  ext x y
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  change (∑ j, v x.1 j * w j y.1) x.2 y.2 = _
  rw [cstarMatrix_sum_apply]
  rfl

end Regroup

variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Fintype n] [DecidableEq n]

/-- Over `A`, every projection at index `κ` is equivalent to one at index `κ × n`:
`v = p * E` with `E i (j, b) = [i = j ∧ b = b₀]` has `v vᴴ = p`. -/
theorem exists_rectEquivalent_prod (b₀ : n) {κ : Type} [Fintype κ] [DecidableEq κ]
    (p : MatrixProjection A κ) :
    ∃ q : MatrixProjection A (κ × n), RectEquivalent p q := by
  let E : Matrix κ (κ × n) A := (1 : Matrix (κ × n) (κ × n) A).submatrix (fun i => (i, b₀)) id
  have hE : E * Eᴴ = 1 := by
    rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one,
      ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.one_mul,
      Matrix.submatrix_one _ (fun i j h => (Prod.mk.inj h).1)]
  let v : Matrix κ (κ × n) A := projectionMatrix p * E
  have hv : v * vᴴ = projectionMatrix p := by
    calc v * vᴴ = projectionMatrix p * (E * Eᴴ) * (projectionMatrix p)ᴴ := by
          simp only [v, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = projectionMatrix p := by
          rw [hE, Matrix.mul_one, projectionMatrix_star, projectionMatrix_mul]
  have hsupp : projectionMatrix p * v = v := rectangular_left_support p v hv
  refine ⟨⟨CStarMatrix.ofMatrix (vᴴ * v), ⟨?_, ?_⟩⟩, v, hv, rfl⟩
  · change vᴴ * v * (vᴴ * v) = vᴴ * v
    calc vᴴ * v * (vᴴ * v) = vᴴ * (v * vᴴ * v) := by simp only [Matrix.mul_assoc]
      _ = vᴴ * v := by rw [hv, hsupp]
  · change (vᴴ * v)ᴴ = vᴴ * v
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

variable [PartialOrder (CStarMatrix n n A)] [StarOrderedRing (CStarMatrix n n A)]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A projection over `M_n(A)` read as a projection over `A`. -/
def projectionFlatten (p : MatrixProjection (CStarMatrix n n A) ι) :
    MatrixProjection A (ι × n) :=
  ⟨CStarMatrix.ofMatrix (matrixFlatten (projectionMatrix p)), ⟨by
    change matrixFlatten (projectionMatrix p) * matrixFlatten (projectionMatrix p) =
      matrixFlatten (projectionMatrix p)
    rw [← matrixFlatten_mul, projectionMatrix_mul], by
    change (matrixFlatten (projectionMatrix p))ᴴ = matrixFlatten (projectionMatrix p)
    rw [matrixFlatten_conjTranspose, projectionMatrix_star]⟩⟩

@[simp] theorem projectionMatrix_flatten (p : MatrixProjection (CStarMatrix n n A) ι) :
    projectionMatrix (projectionFlatten p) = matrixFlatten (projectionMatrix p) := rfl

/-- A projection over `A` at index `ι × n` read as a projection over `M_n(A)`. -/
def projectionUnflatten (q : MatrixProjection A (ι × n)) :
    MatrixProjection (CStarMatrix n n A) ι :=
  ⟨CStarMatrix.ofMatrix (matrixUnflatten (projectionMatrix q)), ⟨by
    change matrixUnflatten (projectionMatrix q) * matrixUnflatten (projectionMatrix q) =
      matrixUnflatten (projectionMatrix q)
    apply matrixFlatten_injective
    rw [matrixFlatten_mul, matrixFlatten_unflatten, projectionMatrix_mul], by
    change (matrixUnflatten (projectionMatrix q))ᴴ = matrixUnflatten (projectionMatrix q)
    apply matrixFlatten_injective
    rw [← matrixFlatten_conjTranspose, matrixFlatten_unflatten, projectionMatrix_star]⟩⟩

@[simp] theorem projectionFlatten_unflatten (q : MatrixProjection A (ι × n)) :
    projectionFlatten (projectionUnflatten q) = q := rfl

namespace FiniteProjection

/-- Regroup a finite matrix projection over `M_n(A)` as one over `A`. -/
def flatten (p : FiniteProjection (CStarMatrix n n A)) : FiniteProjection A :=
  ofProjection (projectionFlatten p.projection)

theorem flatten_equivalent {p q : FiniteProjection (CStarMatrix n n A)}
    (h : Equivalent p q) : Equivalent (flatten p) (flatten q) := by
  obtain ⟨v, hv, hv'⟩ := h
  have h₁ := matrixFlatten_mul v vᴴ
  have h₂ := matrixFlatten_mul vᴴ v
  rw [← matrixFlatten_conjTranspose, hv] at h₁
  rw [← matrixFlatten_conjTranspose, hv'] at h₂
  exact ⟨matrixFlatten v, h₁.symm, h₂.symm⟩

/-- Regrouping reflects equivalence: unflatten the rectangular witness. -/
theorem equivalent_of_flatten {p q : FiniteProjection (CStarMatrix n n A)}
    (h : Equivalent (flatten p) (flatten q)) : Equivalent p q := by
  obtain ⟨w, hw, hw'⟩ := h
  have h₁ := matrixFlatten_mul (matrixUnflatten w) (matrixUnflatten w)ᴴ
  have h₂ := matrixFlatten_mul (matrixUnflatten w)ᴴ (matrixUnflatten w)
  rw [← matrixFlatten_conjTranspose] at h₁ h₂
  exact ⟨matrixUnflatten w, matrixFlatten_injective (h₁.trans hw),
    matrixFlatten_injective (h₂.trans hw')⟩

theorem flatten_zero :
    Equivalent (flatten (zero : FiniteProjection (CStarMatrix n n A))) zero :=
  ⟨0, Matrix.ext fun x _ => x.1.elim, Matrix.ext fun x _ => x.elim⟩

theorem flatten_blockSum (p q : FiniteProjection (CStarMatrix n n A)) :
    Equivalent (flatten (blockSum p q)) (blockSum (flatten p) (flatten q)) := by
  apply rectEquivalent_of_reindex _ _ (Equiv.sumProdDistrib p.Index q.Index n).symm
  ext x y
  rcases x with ⟨i, a⟩ | ⟨i, a⟩ <;> rcases y with ⟨j, b⟩ | ⟨j, b⟩ <;> rfl

end FiniteProjection

namespace StableProjectionMonoid

/-- Regrouping on stable projection classes. -/
def flatten : StableProjectionMonoid (CStarMatrix n n A) →+ StableProjectionMonoid A where
  toFun := Quotient.map FiniteProjection.flatten fun _ _ h => FiniteProjection.flatten_equivalent h
  map_zero' := of_eq_of_equivalent FiniteProjection.flatten_zero
  map_add' x y := Quotient.inductionOn₂ x y fun p q =>
    of_eq_of_equivalent (FiniteProjection.flatten_blockSum p q)

@[simp] theorem flatten_of (p : FiniteProjection (CStarMatrix n n A)) :
    flatten (of p) = of (FiniteProjection.flatten p) := rfl

theorem flatten_injective : Function.Injective (flatten (A := A) (n := n)) := by
  intro x y
  refine Quotient.inductionOn₂ x y fun p q h => ?_
  have h' : of (FiniteProjection.flatten p) = of (FiniteProjection.flatten q) := h
  exact of_eq_of_equivalent
    (FiniteProjection.equivalent_of_flatten ((of_eq_iff _ _).mp h'))

theorem flatten_surjective [Nonempty n] : Function.Surjective (flatten (A := A) (n := n)) := by
  intro x
  refine Quotient.inductionOn x fun p => ?_
  obtain ⟨q, hq⟩ := exists_rectEquivalent_prod (Classical.arbitrary n) p.projection
  exact ⟨of (FiniteProjection.ofProjection (projectionUnflatten q)),
    of_eq_of_equivalent (rectEquivalent_symm hq)⟩

/-- Regrouping is an isomorphism of stable projection monoids. -/
def flattenEquiv [Nonempty n] :
    StableProjectionMonoid (CStarMatrix n n A) ≃+ StableProjectionMonoid A :=
  AddEquiv.ofBijective flatten ⟨flatten_injective, flatten_surjective⟩

end StableProjectionMonoid

section MonoidEquiv
variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- An isomorphism of stable projection monoids induces one of K₀ groups. -/
def k0EquivOfMonoidEquiv (e : StableProjectionMonoid A ≃+ StableProjectionMonoid B) :
    K0 A ≃+ K0 B where
  toFun := k0Universal (k0Class.comp e.toAddMonoidHom)
  invFun := k0Universal (k0Class.comp e.symm.toAddMonoidHom)
  left_inv x := by
    have h : (k0Universal (k0Class.comp e.symm.toAddMonoidHom)).comp
        (k0Universal (k0Class.comp e.toAddMonoidHom)) = AddMonoidHom.id (K0 A) := by
      apply k0Hom_ext
      intro p
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, k0Projection,
        k0Universal_class, AddEquiv.coe_toAddMonoidHom, AddEquiv.symm_apply_apply]
    exact DFunLike.congr_fun h x
  right_inv x := by
    have h : (k0Universal (k0Class.comp e.toAddMonoidHom)).comp
        (k0Universal (k0Class.comp e.symm.toAddMonoidHom)) = AddMonoidHom.id (K0 B) := by
      apply k0Hom_ext
      intro p
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, k0Projection,
        k0Universal_class, AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply]
    exact DFunLike.congr_fun h x
  map_add' := map_add _

@[simp] theorem k0EquivOfMonoidEquiv_class (e : StableProjectionMonoid A ≃+ StableProjectionMonoid B)
    (x : StableProjectionMonoid A) : k0EquivOfMonoidEquiv e (k0Class x) = k0Class (e x) :=
  k0Universal_class (k0Class.comp e.toAddMonoidHom) x

end MonoidEquiv

/-- **Matrix stability of K₀.** For a nonempty finite type `n`, `K₀(M_n(A)) ≅ K₀(A)`,
induced by reading a projection over `M_n(A)` as one over `A`. -/
def k0MatrixEquiv [Nonempty n] : K0 (CStarMatrix n n A) ≃+ K0 A :=
  k0EquivOfMonoidEquiv StableProjectionMonoid.flattenEquiv

@[simp] theorem k0MatrixEquiv_projection [Nonempty n] (p : FiniteProjection (CStarMatrix n n A)) :
    k0MatrixEquiv (k0Projection p) = k0Projection (FiniteProjection.flatten p) :=
  k0EquivOfMonoidEquiv_class _ _

end BC4lean.OperatorKTheory

/-! ## Matrix stability of K₁

The forward map regroups a unitary over `M_n(A)` as one over `A`
(`flattenStarAlgEquiv`, a ⋆-isomorphism, hence continuous). Its inverse puts a
unitary over `A` in the `(b₀, b₀)` corner and the identity elsewhere
(`padUnitary`). Going around over `A` gives a reindexing of the padded unitary;
going around over `M_n(A)` gives the padded unitary conjugated by a permutation
unitary, which is trivial in K₁ (`unitaryHomotopic_stable_conjugate`).
-/

open scoped CStarAlgebra
namespace BC4lean.OperatorKTheory

universe u

section Padding
variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
variable {n : Type} [DecidableEq n]

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem matrixBlockSum_inl_inl {ι κ : Type*} (p : CStarMatrix ι ι B)
    (q : CStarMatrix κ κ B) (i j : ι) : matrixBlockSum p q (.inl i) (.inl j) = p i j := rfl

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem matrixBlockSum_inl_inr {ι κ : Type*} (p : CStarMatrix ι ι B)
    (q : CStarMatrix κ κ B) (i : ι) (j : κ) : matrixBlockSum p q (.inl i) (.inr j) = 0 := rfl

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem matrixBlockSum_inr_inl {ι κ : Type*} (p : CStarMatrix ι ι B)
    (q : CStarMatrix κ κ B) (i : κ) (j : ι) : matrixBlockSum p q (.inr i) (.inl j) = 0 := rfl

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem matrixBlockSum_inr_inr {ι κ : Type*} (p : CStarMatrix ι ι B)
    (q : CStarMatrix κ κ B) (i j : κ) : matrixBlockSum p q (.inr i) (.inr j) = q i j := rfl

/-- `κ × n` as the slice `b = b₀` followed by its complement. -/
def padEquiv (b₀ : n) (κ : Type) : κ ⊕ κ × {b // b ≠ b₀} ≃ κ × n where
  toFun := Sum.elim (fun i => (i, b₀)) (fun p => (p.1, p.2.1))
  invFun x := if h : x.2 = b₀ then Sum.inl x.1 else Sum.inr (x.1, ⟨x.2, h⟩)
  left_inv := by
    rintro (i | ⟨i, b, hb⟩)
    · simp
    · simp [hb]
  right_inv := by
    rintro ⟨i, b⟩
    by_cases h : b = b₀
    · subst h
      simp
    · simp [h]

theorem continuous_unitaryReindex {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) : Continuous (unitaryReindex (A := B) e) :=
  ((map_continuous (CStarMatrix.reindexₐ ℂ B e).toStarAlgHom).comp
    continuous_subtype_val).subtype_mk _

variable [Fintype n]

/-- Pad a unitary at index `κ` to index `κ × n`: the unitary on the slice `b = b₀`,
the identity elsewhere. -/
def padUnitary (b₀ : n) {κ : Type} [Fintype κ] [DecidableEq κ] (u : MatrixUnitary B κ) :
    MatrixUnitary B (κ × n) :=
  unitaryReindex (padEquiv b₀ κ) (unitaryBlockSum u (1 : MatrixUnitary B (κ × {b // b ≠ b₀})))

theorem padUnitary_apply (b₀ : n) {κ : Type} [Fintype κ] [DecidableEq κ]
    (u : MatrixUnitary B κ) (x y : κ × n) :
    (padUnitary b₀ u : CStarMatrix (κ × n) (κ × n) B) x y =
      if x.2 = b₀ ∧ y.2 = b₀ then (u : CStarMatrix κ κ B) x.1 y.1
      else (1 : CStarMatrix (κ × n) (κ × n) B) x y := by
  rcases x with ⟨i, c⟩
  rcases y with ⟨j, d⟩
  simp only [padUnitary, unitaryReindex_apply, padEquiv, Equiv.coe_fn_symm_mk,
    unitaryBlockSum_coe]
  by_cases hc : c = b₀ <;> by_cases hd : d = b₀
  · subst hc hd
    simp
  · subst hc
    simp [hd, Ne.symm hd]
  · subst hd
    simp [hc]
  · simp [hc, hd, CStarMatrix.one_apply]

theorem continuous_padUnitary (b₀ : n) {κ : Type} [Fintype κ] [DecidableEq κ] :
    Continuous (padUnitary (B := B) b₀ (κ := κ)) :=
  (continuous_unitaryReindex _).comp
    (continuous_unitaryBlockSum.comp (continuous_id.prodMk continuous_const))

/-- Padding does not change the stable class. -/
theorem FiniteUnitary.equivalent_pad (b₀ : n) {κ : Type} [Fintype κ] [DecidableEq κ]
    (u : MatrixUnitary B κ) :
    FiniteUnitary.Equivalent (FiniteUnitary.ofUnitary u)
      (FiniteUnitary.ofUnitary (padUnitary b₀ u)) :=
  FiniteUnitary.equivalent_trans
    (FiniteUnitary.equivalent_stabilize _ (κ × {b // b ≠ b₀}))
    (FiniteUnitary.equivalent_reindex _ _ (padEquiv b₀ κ) rfl)

end Padding

section Permutation
variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
variable {κ : Type} [Fintype κ] [DecidableEq κ]

omit [PartialOrder B] [StarOrderedRing B] [Fintype κ] in
/-- The permutation matrix of `σ`; conjugation by it reindexes along `σ`. -/
def permMatrix (σ : κ ≃ κ) : Matrix κ κ B := (1 : Matrix κ κ B).submatrix σ.symm id

omit [PartialOrder B] [StarOrderedRing B] in
theorem permMatrix_mul_conjTranspose (σ : κ ≃ κ) :
    permMatrix (B := B) σ * (permMatrix σ)ᴴ = 1 := by
  rw [permMatrix, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one,
    ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.one_mul,
    Matrix.submatrix_one_equiv]

omit [PartialOrder B] [StarOrderedRing B] in
theorem conjTranspose_mul_permMatrix (σ : κ ≃ κ) :
    (permMatrix (B := B) σ)ᴴ * permMatrix σ = 1 := by
  rw [permMatrix, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one,
    ← Matrix.submatrix_mul _ _ _ _ _ σ.symm.bijective, Matrix.one_mul, Matrix.submatrix_id_id]

omit [PartialOrder B] [StarOrderedRing B] in
theorem permMatrix_conj (σ : κ ≃ κ) (Z : Matrix κ κ B) :
    permMatrix σ * Z * (permMatrix σ)ᴴ = Z.submatrix σ.symm σ.symm := by
  rw [permMatrix, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one]
  calc (1 : Matrix κ κ B).submatrix σ.symm id * Z * (1 : Matrix κ κ B).submatrix id σ.symm
      = (1 : Matrix κ κ B).submatrix σ.symm id * Z.submatrix id id *
          (1 : Matrix κ κ B).submatrix id σ.symm := by rw [Matrix.submatrix_id_id]
    _ = (1 * Z * 1).submatrix σ.symm σ.symm := by
        rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
          ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id]
    _ = Z.submatrix σ.symm σ.symm := by rw [Matrix.one_mul, Matrix.mul_one]

/-- The permutation unitary of `σ`. -/
def permUnitary (σ : κ ≃ κ) : MatrixUnitary B κ :=
  ⟨CStarMatrix.ofMatrix (permMatrix σ), Unitary.mem_iff.mpr
    ⟨conjTranspose_mul_permMatrix σ, permMatrix_mul_conjTranspose σ⟩⟩

theorem unitaryReindex_eq_conj (σ : κ ≃ κ) (Z : MatrixUnitary B κ) :
    unitaryReindex σ Z = permUnitary σ * Z * star (permUnitary σ) := by
  apply Subtype.ext
  change (CStarMatrix.ofMatrix.symm (Z : CStarMatrix κ κ B)).submatrix σ.symm σ.symm =
    permMatrix (B := B) σ * CStarMatrix.ofMatrix.symm (Z : CStarMatrix κ κ B) *
      (permMatrix (B := B) σ)ᴴ
  rw [permMatrix_conj]

/-- Conjugation by a unitary does not change the K₁ class. -/
theorem K1.of_conj (w a : MatrixUnitary B κ) :
    K1.of (FiniteUnitary.ofUnitary (w * a * star w)) = K1.of (FiniteUnitary.ofUnitary a) := by
  rw [← K1.of_stabilize (FiniteUnitary.ofUnitary (w * a * star w)) κ,
    ← K1.of_stabilize (FiniteUnitary.ofUnitary a) κ]
  exact K1.of_homotopic (unitaryHomotopic_stable_conjugate w a)

end Permutation

section K1Flatten
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {n : Type} [Fintype n] [DecidableEq n]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

variable (ι) in
/-- Regrouping as a ⋆-isomorphism `M_ι(M_n(A)) ≃ M_{ι × n}(A)`. -/
def flattenStarAlgEquiv :
    CStarMatrix ι ι (CStarMatrix n n A) ≃⋆ₐ[ℂ] CStarMatrix (ι × n) (ι × n) A where
  toFun M := CStarMatrix.ofMatrix (matrixFlatten (CStarMatrix.ofMatrix.symm M))
  invFun N := CStarMatrix.ofMatrix (matrixUnflatten (CStarMatrix.ofMatrix.symm N))
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' M N := matrixFlatten_mul (CStarMatrix.ofMatrix.symm M) (CStarMatrix.ofMatrix.symm N)
  map_add' _ _ := rfl
  map_star' M := (matrixFlatten_conjTranspose (CStarMatrix.ofMatrix.symm M)).symm
  map_smul' _ _ := rfl

omit [DecidableEq n] [DecidableEq ι] [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem flattenStarAlgEquiv_apply (M : CStarMatrix ι ι (CStarMatrix n n A))
    (x y : ι × n) : flattenStarAlgEquiv ι M x y = M x.1 y.1 x.2 y.2 := rfl

omit [PartialOrder A] [StarOrderedRing A] in
/-- Entries of the identity of `M_κ(M_n(A))`. -/
theorem one_apply_apply {κ : Type} [Fintype κ] [DecidableEq κ] (k k' : κ) (c d : n) :
    (1 : CStarMatrix κ κ (CStarMatrix n n A)) k k' c d =
      (1 : CStarMatrix (κ × n) (κ × n) A) (k, c) (k', d) :=
  congrArg (fun N : CStarMatrix (κ × n) (κ × n) A => N (k, c) (k', d))
    (map_one (flattenStarAlgEquiv (n := n) (A := A) κ))

variable [PartialOrder (CStarMatrix n n A)] [StarOrderedRing (CStarMatrix n n A)]

/-- A unitary over `M_n(A)` read as a unitary over `A`. -/
def unitaryFlatten (u : MatrixUnitary (CStarMatrix n n A) ι) : MatrixUnitary A (ι × n) :=
  ⟨flattenStarAlgEquiv ι u, Unitary.map_mem (flattenStarAlgEquiv ι) u.property⟩

/-- A unitary over `A` at index `ι × n` read as a unitary over `M_n(A)`. -/
def unitaryUnflatten (w : MatrixUnitary A (ι × n)) : MatrixUnitary (CStarMatrix n n A) ι :=
  ⟨(flattenStarAlgEquiv ι).symm w, Unitary.map_mem (flattenStarAlgEquiv ι).symm w.property⟩

@[simp] theorem unitaryFlatten_apply (u : MatrixUnitary (CStarMatrix n n A) ι) (x y : ι × n) :
    (unitaryFlatten u : CStarMatrix (ι × n) (ι × n) A) x y =
      (u : CStarMatrix ι ι (CStarMatrix n n A)) x.1 y.1 x.2 y.2 := rfl

@[simp] theorem unitaryUnflatten_apply (w : MatrixUnitary A (ι × n)) (i j : ι) (a b : n) :
    (unitaryUnflatten w : CStarMatrix ι ι (CStarMatrix n n A)) i j a b =
      (w : CStarMatrix (ι × n) (ι × n) A) (i, a) (j, b) := rfl

@[simp] theorem unitaryUnflatten_flatten (u : MatrixUnitary (CStarMatrix n n A) ι) :
    unitaryUnflatten (unitaryFlatten u) = u := rfl

theorem unitaryUnflatten_mul (v w : MatrixUnitary A (ι × n)) :
    unitaryUnflatten (v * w) = unitaryUnflatten v * unitaryUnflatten w :=
  Subtype.ext (map_mul (flattenStarAlgEquiv ι).symm _ _)

theorem unitaryUnflatten_star (w : MatrixUnitary A (ι × n)) :
    unitaryUnflatten (star w) = star (unitaryUnflatten w) :=
  Subtype.ext (map_star (flattenStarAlgEquiv ι).symm _)

theorem continuous_unitaryFlatten :
    Continuous (unitaryFlatten (A := A) (n := n) (ι := ι)) :=
  ((map_continuous (flattenStarAlgEquiv (n := n) (A := A) ι).toStarAlgHom).comp
    continuous_subtype_val).subtype_mk _

theorem continuous_unitaryUnflatten :
    Continuous (unitaryUnflatten (A := A) (n := n) (ι := ι)) :=
  ((map_continuous (flattenStarAlgEquiv (n := n) (A := A) ι).symm.toStarAlgHom).comp
    continuous_subtype_val).subtype_mk _

namespace FiniteUnitary

/-- Regroup a finite matrix unitary over `M_n(A)` as one over `A`. -/
def flatten (a : FiniteUnitary (CStarMatrix n n A)) : FiniteUnitary A :=
  ofUnitary (unitaryFlatten a.val)

theorem flatten_move {a b : FiniteUnitary (CStarMatrix n n A)} (h : Move a b) :
    Equivalent (flatten a) (flatten b) := by
  cases h with
  | homotopy b e h =>
    refine .rel _ _ (.homotopy _ _ (e.prodCongr (Equiv.refl n)) ?_)
    have hr : unitaryReindex (e.prodCongr (Equiv.refl n)) (unitaryFlatten a.val) =
        unitaryFlatten (unitaryReindex e a.val) := Subtype.ext rfl
    change UnitaryHomotopic (unitaryReindex (e.prodCongr (Equiv.refl n)) (unitaryFlatten a.val))
      (unitaryFlatten b.val)
    rw [hr]
    exact h.map continuous_unitaryFlatten
  | stabilize κ =>
    refine equivalent_trans (equivalent_stabilize (flatten a) (κ × n)) (equivalent_symm ?_)
    refine equivalent_reindex _ _ (Equiv.sumProdDistrib a.Index κ n) (Subtype.ext ?_)
    ext x y
    rcases x with ⟨i, c⟩ | ⟨k, c⟩ <;> rcases y with ⟨j, d⟩ | ⟨k', d⟩
    · rfl
    · rfl
    · rfl
    · exact one_apply_apply k k' c d

theorem flatten_equivalent {a b : FiniteUnitary (CStarMatrix n n A)} (h : Equivalent a b) :
    Equivalent (flatten a) (flatten b) := by
  induction h with
  | rel _ _ h => exact flatten_move h
  | refl _ => exact equivalent_refl _
  | symm _ _ _ ih => exact equivalent_symm ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact equivalent_trans ih₁ ih₂

theorem flatten_blockSum (a b : FiniteUnitary (CStarMatrix n n A)) :
    Equivalent (flatten (blockSum a b)) (blockSum (flatten a) (flatten b)) := by
  refine equivalent_reindex _ _ (Equiv.sumProdDistrib a.Index b.Index n) (Subtype.ext ?_)
  ext x y
  rcases x with ⟨i, c⟩ | ⟨i, c⟩ <;> rcases y with ⟨j, d⟩ | ⟨j, d⟩ <;> rfl

theorem flatten_zero : Equivalent (flatten (zero : FiniteUnitary (CStarMatrix n n A))) zero := by
  refine equivalent_reindex _ _ (Equiv.equivEmpty (Empty × n)) (Subtype.ext ?_)
  ext x
  exact x.elim

/-- Put a unitary over `A` in the `(b₀, b₀)` corner of `M_n(A)`, identity elsewhere. -/
def unflattenPad (b₀ : n) (a : FiniteUnitary A) : FiniteUnitary (CStarMatrix n n A) :=
  ofUnitary (unitaryUnflatten (padUnitary b₀ a.val))

theorem unflattenPad_reindex (b₀ : n) {κ τ : Type} [Fintype κ] [DecidableEq κ] [Fintype τ]
    [DecidableEq τ] (e : κ ≃ τ) (u : MatrixUnitary A κ) :
    unitaryReindex e (unitaryUnflatten (padUnitary b₀ u)) =
      unitaryUnflatten (padUnitary b₀ (unitaryReindex e u)) := by
  apply Subtype.ext
  ext i j c d
  simp only [unitaryReindex_apply, unitaryUnflatten_apply, padUnitary_apply]
  split_ifs <;> simp [CStarMatrix.one_apply]

theorem unflattenPad_blockSum_one (b₀ : n) {κ τ : Type} [Fintype κ] [DecidableEq κ]
    [Fintype τ] [DecidableEq τ] (u : MatrixUnitary A κ) :
    unitaryUnflatten (padUnitary b₀ (unitaryBlockSum u (1 : MatrixUnitary A τ))) =
      unitaryBlockSum (unitaryUnflatten (padUnitary b₀ u)) 1 := by
  apply Subtype.ext
  ext x y c d
  rcases x with i | k <;> rcases y with j | k'
  rotate_right
  · refine Eq.trans ?_ (one_apply_apply k k' c d).symm
    simp only [unitaryUnflatten_apply, padUnitary_apply, unitaryBlockSum_coe,
      matrixBlockSum_inr_inr, OneMemClass.coe_one]
    split_ifs <;> simp_all [CStarMatrix.one_apply]
  all_goals
    simp only [unitaryUnflatten_apply, padUnitary_apply, unitaryBlockSum_coe,
      matrixBlockSum_inl_inl, matrixBlockSum_inl_inr, matrixBlockSum_inr_inl]
    split_ifs <;> simp_all [CStarMatrix.one_apply, CStarMatrix.zero_apply]

theorem unflattenPad_move (b₀ : n) {a b : FiniteUnitary A} (h : Move a b) :
    Equivalent (unflattenPad b₀ a) (unflattenPad b₀ b) := by
  cases h with
  | homotopy b e h =>
    refine .rel _ _ (.homotopy _ _ e ?_)
    change UnitaryHomotopic (unitaryReindex e (unitaryUnflatten (padUnitary b₀ a.val)))
      (unitaryUnflatten (padUnitary b₀ b.val))
    rw [unflattenPad_reindex]
    exact h.map (continuous_unitaryUnflatten.comp (continuous_padUnitary b₀))
  | stabilize κ =>
    have h : unflattenPad b₀ (blockSum a (identity κ)) = blockSum (unflattenPad b₀ a) (identity κ) :=
      congrArg ofUnitary (unflattenPad_blockSum_one b₀ a.val)
    rw [h]
    exact equivalent_stabilize _ κ

theorem unflattenPad_equivalent (b₀ : n) {a b : FiniteUnitary A} (h : Equivalent a b) :
    Equivalent (unflattenPad (A := A) b₀ a) (unflattenPad b₀ b) := by
  induction h with
  | rel _ _ h => exact unflattenPad_move b₀ h
  | refl _ => exact equivalent_refl _
  | symm _ _ _ ih => exact equivalent_symm ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact equivalent_trans ih₁ ih₂

/-- Exchange the two `n` coordinates of `(ι × n) × n`. -/
def swapEquiv (ι n : Type) : (ι × n) × n ≃ (ι × n) × n where
  toFun x := ((x.1.1, x.2), x.1.2)
  invFun x := ((x.1.1, x.2), x.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Padding over `A` after regrouping is the regrouped padding over `M_n(A)`, up to
exchanging the two `n` coordinates. -/
theorem pad_flatten (b₀ : n) (u : MatrixUnitary (CStarMatrix n n A) ι) :
    padUnitary b₀ (unitaryFlatten u) =
      unitaryReindex (swapEquiv ι n) (unitaryFlatten (padUnitary b₀ u)) := by
  apply Subtype.ext
  ext x y
  rcases x with ⟨⟨i, a⟩, c⟩
  rcases y with ⟨⟨j, b⟩, d⟩
  simp only [padUnitary_apply, unitaryReindex_apply, swapEquiv, Equiv.coe_fn_symm_mk,
    unitaryFlatten_apply]
  split_ifs with h
  · rfl
  · rw [one_apply_apply]
    by_cases hij : i = j <;> by_cases hab : a = b <;> by_cases hcd : c = d <;>
      simp [CStarMatrix.one_apply, hij, hab, hcd]

theorem unflattenPad_flatten (b₀ : n) (a : FiniteUnitary (CStarMatrix n n A)) :
    Equivalent (unflattenPad b₀ (flatten a)) a := by
  let S : MatrixUnitary (CStarMatrix n n A) (a.Index × n) :=
    unitaryUnflatten (permUnitary (swapEquiv a.Index n))
  let V := padUnitary b₀ a.val
  have key : unitaryUnflatten (padUnitary b₀ (unitaryFlatten a.val)) = S * V * star S := by
    rw [pad_flatten, unitaryReindex_eq_conj, unitaryUnflatten_mul, unitaryUnflatten_mul,
      unitaryUnflatten_star, unitaryUnflatten_flatten]
  have h : K1.of (unflattenPad b₀ (flatten a)) = K1.of a := by
    calc K1.of (unflattenPad b₀ (flatten a)) = K1.of (ofUnitary (S * V * star S)) :=
          congrArg (fun w => K1.of (ofUnitary w)) key
      _ = K1.of (ofUnitary V) := K1.of_conj S V
      _ = K1.of a := (Quotient.sound (equivalent_pad b₀ a.val)).symm
  exact (K1.of_eq_iff _ _).mp h

theorem flatten_unflattenPad (b₀ : n) (a : FiniteUnitary A) :
    Equivalent (flatten (unflattenPad (n := n) b₀ a)) a :=
  equivalent_symm (equivalent_pad b₀ a.val)

end FiniteUnitary

namespace K1

/-- Regrouping on K₁. -/
def flatten : K1 (CStarMatrix n n A) →+ K1 A where
  toFun := Quotient.map FiniteUnitary.flatten fun _ _ h => FiniteUnitary.flatten_equivalent h
  map_zero' := Quotient.sound FiniteUnitary.flatten_zero
  map_add' x y := Quotient.inductionOn₂ x y fun a b =>
    Quotient.sound (FiniteUnitary.flatten_blockSum a b)

@[simp] theorem flatten_of (a : FiniteUnitary (CStarMatrix n n A)) :
    flatten (of a) = of (FiniteUnitary.flatten a) := rfl

/-- The inverse of `flatten`: corner placement padded by the identity. -/
def unflattenPad (b₀ : n) : K1 A → K1 (CStarMatrix n n A) :=
  Quotient.map (FiniteUnitary.unflattenPad b₀) fun _ _ h =>
    FiniteUnitary.unflattenPad_equivalent b₀ h

theorem unflattenPad_flatten (b₀ : n) (x : K1 (CStarMatrix n n A)) :
    unflattenPad b₀ (flatten x) = x :=
  Quotient.inductionOn x fun a => Quotient.sound (FiniteUnitary.unflattenPad_flatten b₀ a)

theorem flatten_unflattenPad (b₀ : n) (x : K1 A) : flatten (unflattenPad b₀ x) = x :=
  Quotient.inductionOn x fun a => Quotient.sound (FiniteUnitary.flatten_unflattenPad b₀ a)

end K1

/-- **Matrix stability of K₁.** For a nonempty finite type `n`, `K₁(M_n(A)) ≅ K₁(A)`,
induced by reading a unitary over `M_n(A)` as one over `A`. -/
def k1MatrixEquiv [Nonempty n] : K1 (CStarMatrix n n A) ≃+ K1 A where
  toFun := K1.flatten
  invFun := K1.unflattenPad (Classical.arbitrary n)
  left_inv := K1.unflattenPad_flatten _
  right_inv := K1.flatten_unflattenPad _
  map_add' := map_add K1.flatten

@[simp] theorem k1MatrixEquiv_of [Nonempty n] (a : FiniteUnitary (CStarMatrix n n A)) :
    k1MatrixEquiv (K1.of a) = K1.of (FiniteUnitary.flatten a) := rfl

end K1Flatten

end BC4lean.OperatorKTheory
