import BC4lean.CosetAssembly
import BC4lean.ScalarCreationCycleCounterexample
import BC4lean.FinitePointCharacterTensor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! The unit cycle of the coset space `Γ ⧸ F`.

For a discrete `Γ`-set `X`, the Hilbert space `ℓ²(X)` carries the translation action
`(U_g ξ)(x) = ξ(g⁻¹ x)` and the multiplication representation `(π(a) ξ)(x) = a(x) ξ(x)` of
`C₀(X)`, and `U_g π(a) U_g⁻¹ = π(g · a)`. Every `π(a)` is compact: it is the norm limit of the
finite sums `∑_{x ∈ K} a(x) θ_{δ_x, δ_x}`. Hence `(ℓ²(X), π, U, 0)`, trivially graded, is an
equivariant Kasparov cycle for `(C₀(X), ℂ)`. For `X = Γ ⧸ F`, `π` of the indicator of the base
coset is the rank-one projection onto `δ_{eF}`, and `F` fixes `δ_{eF}`. -/

noncomputable section
namespace BC4lean.Chapter8Examples.CosetUnitCycle
open ProperActions KKTheory OperatorKTheory
open scoped ZeroAtInfty ComplexOrder InnerProductSpace ScalarHilbertModule ENNReal

section Translation
variable {Γ : Type} [Group Γ] {X : Type} [MulAction Γ X]

/-- Translation preserves square summability by reindexing the sum. -/
theorem memℓp_translate (g : Γ) (ξ : L2Group X) : Memℓp (fun x => ξ (g⁻¹ • x)) 2 := by
  apply memℓp_gen
  have h : Summable fun x => ‖ξ x‖ ^ (2 : ℝ≥0∞).toReal := (lp.memℓp ξ).summable (by norm_num)
  exact (Equiv.summable_iff (MulAction.toPerm g⁻¹ : Equiv.Perm X)
    (f := fun x => ‖ξ x‖ ^ (2 : ℝ≥0∞).toReal)).mpr h

/-- Translation by `g`, before packaging it as a linear isometry. -/
def translate (g : Γ) (ξ : L2Group X) : L2Group X := ⟨fun x => ξ (g⁻¹ • x), memℓp_translate g ξ⟩

@[simp] theorem translate_apply (g : Γ) (ξ : L2Group X) (x : X) :
    translate g ξ x = ξ (g⁻¹ • x) := rfl

theorem translate_mul (g h : Γ) (ξ : L2Group X) :
    translate (g * h) ξ = translate g (translate h ξ) := by
  apply lp.ext
  funext x
  simp [mul_smul]

@[simp] theorem translate_one (ξ : L2Group X) : translate (1 : Γ) ξ = ξ := by
  apply lp.ext
  funext x
  simp

theorem norm_translate (g : Γ) (ξ : L2Group X) : ‖translate g ξ‖ = ‖ξ‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
  congr 1
  exact (MulAction.toPerm g⁻¹ : Equiv.Perm X).tsum_eq (fun x => ‖ξ x‖ ^ (2 : ℝ≥0∞).toReal)

/-- Translation by `g` as a linear isometric equivalence of `ℓ²(X)`. -/
def translateEquiv (g : Γ) : L2Group X ≃ₗᵢ[ℂ] L2Group X where
  toFun := translate g
  invFun := translate g⁻¹
  left_inv ξ := by rw [← translate_mul, inv_mul_cancel, translate_one]
  right_inv ξ := by rw [← translate_mul, mul_inv_cancel, translate_one]
  map_add' ξ η := by
    apply lp.ext
    rfl
  map_smul' c ξ := by
    apply lp.ext
    rfl
  norm_map' := norm_translate g

variable (Γ X) in
/-- The translation action of `Γ` on `ℓ²(X)`. -/
def translationHom : Γ →* (L2Group X ≃ₗᵢ[ℂ] L2Group X) where
  toFun := translateEquiv
  map_one' := by
    ext ξ : 1
    exact translate_one ξ
  map_mul' g h := by
    ext ξ : 1
    exact translate_mul g h ξ

variable (Γ X) in
/-- `ℓ²(X)` as an equivariant Hilbert module over the trivial action on `ℂ`. -/
def translationModule :
    EquivariantHilbertModule (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) (L2Group X) where
  action := translationHom Γ X
  inner_action g ξ η := by
    change MulOpposite.op ⟪translateEquiv g ξ, translateEquiv g η⟫_ℂ = MulOpposite.op ⟪ξ, η⟫_ℂ
    rw [LinearIsometryEquiv.inner_map_map]

@[simp] theorem translationModule_apply (g : Γ) (ξ : L2Group X) (x : X) :
    (translationModule Γ X).action g ξ x = ξ (g⁻¹ • x) := rfl

end Translation

section Multiplication
variable {X : Type}

/-- Multiplication by a function bounded by `C` preserves square summability. -/
theorem memℓp_mul (φ : X → ℂ) (C : ℝ) (hφ : ∀ x, ‖φ x‖ ≤ C) (ξ : L2Group X) :
    Memℓp (fun x => φ x * ξ x) 2 := by
  refine (L2Group.mem_iff _).mpr ?_
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun x => ?_)
    ((L2Group.summable_norm_sq ξ).mul_left (C ^ 2))
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hφ x) 2) (by positivity)

/-- Pointwise multiplication by a bounded function. -/
def mulVec (φ : X → ℂ) (C : ℝ) (hφ : ∀ x, ‖φ x‖ ≤ C) (ξ : L2Group X) : L2Group X :=
  ⟨fun x => φ x * ξ x, memℓp_mul φ C hφ ξ⟩

@[simp] theorem mulVec_apply (φ : X → ℂ) (C : ℝ) (hφ : ∀ x, ‖φ x‖ ≤ C) (ξ : L2Group X) (x : X) :
    mulVec φ C hφ ξ x = φ x * ξ x := rfl

theorem norm_mulVec_le (φ : X → ℂ) (C : ℝ) (hC : 0 ≤ C) (hφ : ∀ x, ‖φ x‖ ≤ C) (ξ : L2Group X) :
    ‖mulVec φ C hφ ξ‖ ≤ C * ‖ξ‖ := by
  have h : ‖mulVec φ C hφ ξ‖ ^ 2 ≤ (C * ‖ξ‖) ^ 2 := by
    rw [L2Group.norm_sq, mul_pow, L2Group.norm_sq, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun x => ?_) (L2Group.summable_norm_sq _)
      ((L2Group.summable_norm_sq ξ).mul_left (C ^ 2))
    rw [mulVec_apply, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hφ x) 2) (by positivity)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h

/-- The bounded multiplication operator of a function bounded by `C`. -/
def mulCLM (φ : X → ℂ) (C : ℝ) (hC : 0 ≤ C) (hφ : ∀ x, ‖φ x‖ ≤ C) : L2Group X →L[ℂ] L2Group X :=
  LinearMap.mkContinuous
    { toFun := mulVec φ C hφ
      map_add' ξ η := by
        apply lp.ext
        funext x
        simp [mul_add]
      map_smul' c ξ := by
        apply lp.ext
        funext x
        simp only [mulVec_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
    C (norm_mulVec_le φ C hC hφ)

@[simp] theorem mulCLM_apply (φ : X → ℂ) (C : ℝ) (hC : 0 ≤ C) (hφ : ∀ x, ‖φ x‖ ≤ C)
    (ξ : L2Group X) (x : X) : mulCLM φ C hC hφ ξ x = φ x * ξ x := rfl

theorem norm_mulCLM_le (φ : X → ℂ) (C : ℝ) (hC : 0 ≤ C) (hφ : ∀ x, ‖φ x‖ ≤ C) :
    ‖mulCLM φ C hC hφ‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

theorem norm_star_le (φ : X → ℂ) (C : ℝ) (hφ : ∀ x, ‖φ x‖ ≤ C) (x : X) :
    ‖star (φ x)‖ ≤ C := by
  rw [norm_star]
  exact hφ x

/-- The multiplication operator as an adjointable map; its adjoint multiplies by `φ̄`. -/
def mulOp (φ : X → ℂ) (C : ℝ) (hC : 0 ≤ C) (hφ : ∀ x, ‖φ x‖ ≤ C) :
    AdjointableMap ℂ (L2Group X) (L2Group X) :=
  ScalarHilbertModule.ofAdjointPair (mulCLM φ C hC hφ)
    (mulCLM (fun x => star (φ x)) C hC (norm_star_le φ C hφ)) (fun ξ η => by
      rw [L2Group.inner_eq_tsum, L2Group.inner_eq_tsum]
      refine tsum_congr fun x => ?_
      simp only [mulCLM_apply, star_mul']
      ring)

@[simp] theorem mulOp_apply (φ : X → ℂ) (C : ℝ) (hC : 0 ≤ C) (hφ : ∀ x, ‖φ x‖ ≤ C)
    (ξ : L2Group X) (x : X) : mulOp φ C hC hφ ξ x = φ x * ξ x := rfl

theorem norm_mulOp_le (φ : X → ℂ) (C : ℝ) (hC : 0 ≤ C) (hφ : ∀ x, ‖φ x‖ ≤ C) :
    ‖mulOp φ C hC hφ‖ ≤ C :=
  norm_mulCLM_le φ C hC hφ

end Multiplication

section Representation
variable {X : Type} [TopologicalSpace X]

theorem norm_apply_le_norm (a : C₀(X, ℂ)) (x : X) : ‖a x‖ ≤ ‖a‖ :=
  (a.toBCF.norm_coe_le_norm x).trans_eq ZeroAtInftyContinuousMap.norm_toBCF_eq_norm

/-- The multiplication representation of `C₀(X)` on `ℓ²(X)`. -/
def multiplication : C₀(X, ℂ) →⋆ₙₐ[ℂ] AdjointableMap ℂ (L2Group X) (L2Group X) where
  toFun a := mulOp a ‖a‖ (norm_nonneg a) (norm_apply_le_norm a)
  map_zero' := by
    ext ξ x
    simp
  map_add' a b := by
    ext ξ x
    simp [add_mul]
  map_smul' c a := by
    ext ξ x
    simp [mul_assoc]
  map_mul' a b := by
    ext ξ x
    simp [mul_assoc]
  map_star' a := by
    ext ξ x
    rfl

@[simp] theorem multiplication_apply (a : C₀(X, ℂ)) (ξ : L2Group X) (x : X) :
    multiplication a ξ x = a x * ξ x := rfl

variable [DiscreteTopology X]

omit [TopologicalSpace X] [DiscreteTopology X] in
open scoped Classical in
/-- `θ_{δ_y, δ_y} ξ = ξ(y) δ_y`. -/
theorem moduleRankOne_delta_apply (y : X) (ξ : L2Group X) (x : X) :
    moduleRankOne (B := ℂ) (L2Group.delta y) (L2Group.delta y) ξ x =
      (if x = y then ξ y else 0) := by
  classical
  change (MulOpposite.unop ⟪L2Group.delta y, ξ⟫_(ℂᵐᵒᵖ) • L2Group.delta y) x = _
  rw [ScalarHilbertModule.unop_inner, L2Group.inner_delta, lp.coeFn_smul, Pi.smul_apply,
    L2Group.delta_apply, smul_eq_mul]
  split_ifs <;> simp

omit [TopologicalSpace X] [DiscreteTopology X] in
/-- Finite sums of adjointable maps are evaluated pointwise. -/
theorem adjointable_sum_apply {ι : Type*} (s : Finset ι)
    (T : ι → AdjointableMap ℂ (L2Group X) (L2Group X)) (ξ : L2Group X) :
    (∑ i ∈ s, T i) ξ = ∑ i ∈ s, T i ξ := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb, AdjointableMap.coe_add_apply, ih]

/-- A function vanishing at infinity on a discrete space is small off a finite set. -/
theorem finite_setOf_le_norm (a : C₀(X, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    {x | ε ≤ ‖a x‖}.Finite := by
  have h : ∀ᶠ x in Filter.cofinite, ‖a x‖ < ε := by
    rw [← Filter.cocompact_eq_cofinite]
    have ht := (ZeroAtInftyContinuousMapClass.zero_at_infty a).norm
    rw [norm_zero] at ht
    exact ht (Iio_mem_nhds hε)
  simpa only [not_lt] using Filter.eventually_cofinite.mp h

/-- Every multiplication operator by a `C₀` function on a discrete space is compact. -/
theorem multiplication_isModuleCompact (a : C₀(X, ℂ)) : IsModuleCompact (multiplication a) := by
  classical
  refine (mem_moduleCompact_iff_approx _).mpr fun ε hε => ?_
  have hε2 : 0 < ε / 2 := half_pos hε
  let K := (finite_setOf_le_norm a hε2).toFinset
  let S : AdjointableMap ℂ (L2Group X) (L2Group X) :=
    ∑ y ∈ K, a y • moduleRankOne (B := ℂ) (L2Group.delta y) (L2Group.delta y)
  refine ⟨S, ?_, ?_⟩
  · exact Submodule.sum_mem _ fun y _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨(L2Group.delta y, L2Group.delta y), rfl⟩)
  · let φ : X → ℂ := fun x => if x ∈ K then 0 else a x
    have hφ : ∀ x, ‖φ x‖ ≤ ε / 2 := by
      intro x
      by_cases hx : x ∈ K
      · simp [φ, hx, hε2.le]
      · simp only [φ, hx, if_false]
        have : ¬ ε / 2 ≤ ‖a x‖ := fun h => hx ((Set.Finite.mem_toFinset _).mpr h)
        exact (not_le.mp this).le
    have hS : ∀ ξ : L2Group X, ∀ x, S ξ x = if x ∈ K then a x * ξ x else 0 := by
      intro ξ x
      have happ : S ξ = ∑ y ∈ K, a y • moduleRankOne (B := ℂ) (L2Group.delta y)
          (L2Group.delta y) ξ := by
        simp only [S, adjointable_sum_apply, AdjointableMap.coe_smul_apply]
      rw [happ, lp.coeFn_sum, Finset.sum_apply]
      simp only [lp.coeFn_smul, Pi.smul_apply, moduleRankOne_delta_apply, smul_eq_mul,
        mul_ite, mul_zero]
      simp only [Finset.sum_ite_eq]
    have heq : multiplication a - S = mulOp φ (ε / 2) hε2.le hφ := by
      ext ξ x
      rw [AdjointableMap.coe_sub_apply, lp.coeFn_sub, Pi.sub_apply, multiplication_apply, hS,
        mulOp_apply]
      by_cases hx : x ∈ K <;> simp [φ, hx]
    rw [heq]
    exact (norm_mulOp_le φ _ hε2.le hφ).trans_lt (half_lt_self hε)

end Representation

section Separable
variable {X : Type} [Countable X]

theorem separable : TopologicalSpace.SeparableSpace (L2Group X) := by
  have hs : TopologicalSpace.IsSeparable
      (Submodule.span ℂ (Set.range (L2Group.delta : X → L2Group X)) : Set (L2Group X)) :=
    (Set.countable_range (L2Group.delta : X → L2Group X)).isSeparable.span
  have hd : Dense
      (Submodule.span ℂ (Set.range (L2Group.delta : X → L2Group X)) : Set (L2Group X)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr L2Group.delta_dense_span
  exact hd.isSeparable_iff.mp hs

end Separable

section Cycle
variable (Γ : Type) [Group Γ] {X : Type} [TopologicalSpace X] [MulAction Γ X]
  [ContinuousConstSMul Γ X]

theorem multiplication_equivariant (g : Γ) (a : C₀(X, ℂ)) :
    (translationModule Γ X).conjugateOperator g (multiplication a) =
      multiplication ((CZero.action Γ (X := X)).automorphism g a) := by
  ext ξ x
  change a (g⁻¹ • x) * ξ (g⁻¹⁻¹ • g⁻¹ • x) = a (g⁻¹ • x) * ξ x
  rw [inv_inv, smul_inv_smul]

omit [TopologicalSpace X] [ContinuousConstSMul Γ X] in
theorem conjugateOperator_zero (g : Γ) :
    (translationModule Γ X).conjugateOperator g (0 : AdjointableMap ℂ (L2Group X) (L2Group X)) =
      0 := by
  ext ξ x
  simp

variable (X) in
/-- The unit cycle `(ℓ²(X), π, U, 0)`, trivially graded. -/
def unitCycleOf [DiscreteTopology X] [Countable X] :
    KasparovCycle (CZero.action Γ (X := X)) (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
      (L2Group X) where
  countablyGenerated := by
    let := separable (X := X)
    exact ScalarCreationCycleCounterexample.countablyGenerated_of_separable _
  grading := GradedHilbertModule.trivial
  groupAction := translationModule Γ X
  grading_preserved _ _ := rfl
  representation := multiplication
  representation_even _ _ := rfl
  representation_equivariant := multiplication_equivariant Γ
  operator := 0
  operator_odd _ := by simp
  selfadjoint_mod_compact _ := by
    simpa using (IsModuleCompact.zero : IsModuleCompact (0 : AdjointableMap ℂ (L2Group X) (L2Group X)))
  square_mod_compact a := by
    have h : ((0 : AdjointableMap ℂ (L2Group X) (L2Group X)) * 0 - 1) * multiplication a =
        -multiplication a := by
      rw [mul_zero, zero_sub, neg_one_mul]
    rw [h]
    exact (moduleCompact ℂ (L2Group X) (L2Group X)).neg_mem (multiplication_isModuleCompact a)
  commutator_compact _ := by
    simpa using (IsModuleCompact.zero : IsModuleCompact (0 : AdjointableMap ℂ (L2Group X) (L2Group X)))
  equivariance_mod_compact g _ := by
    rw [conjugateOperator_zero, sub_zero, zero_mul]
    exact (IsModuleCompact.zero : IsModuleCompact (0 : AdjointableMap ℂ (L2Group X) (L2Group X)))

end Cycle

section Coset
variable (Γ : Type) [Group Γ] [Countable Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
  (F : Subgroup Γ)

/-- `ℓ²(Γ ⧸ F)`. -/
abbrev Ell2 := L2Group (Γ ⧸ F)

/-- The basis vector `δ_{eF}` of the base coset. -/
def baseVector : L2Group (Γ ⧸ F) := L2Group.delta ((1 : Γ) : Γ ⧸ F)

/-- The unit cycle of `Γ ⧸ F`: `ℓ²(Γ ⧸ F)` with translations, multiplication and operator `0`. -/
def unitCycle : KasparovCycle (CZero.action Γ (X := Γ ⧸ F))
    (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) (L2Group (Γ ⧸ F)) :=
  unitCycleOf Γ (Γ ⧸ F)

theorem unitCycle_operator : (unitCycle Γ F).operator = 0 := rfl

theorem unitCycle_grading (x : L2Group (Γ ⧸ F)) : (unitCycle Γ F).grading.grading x = x := rfl

theorem unitCycle_representation_apply (a : C₀(Γ ⧸ F, ℂ)) (ξ : L2Group (Γ ⧸ F)) (x : Γ ⧸ F) :
    (unitCycle Γ F).representation a ξ x = a x * ξ x := rfl

theorem unitCycle_action_apply (g : Γ) (ξ : L2Group (Γ ⧸ F)) (x : Γ ⧸ F) :
    (unitCycle Γ F).groupAction.action g ξ x = ξ (g⁻¹ • x) := rfl

omit [Countable Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] in
theorem inner_baseVector_self : ⟪baseVector Γ F, baseVector Γ F⟫_(ℂᵐᵒᵖ) = 1 := by
  apply MulOpposite.unop_injective
  rw [ScalarHilbertModule.unop_inner, baseVector, L2Group.inner_delta, L2Group.delta_apply_self]
  rfl

/-- `π(1_{eF})` is the rank-one projection onto `δ_{eF}`. -/
theorem unitCycle_representation_cosetDelta :
    (unitCycle Γ F).representation (CosetAssembly.cosetDelta Γ F) =
      moduleRankOne (B := ℂ) (baseVector Γ F) (baseVector Γ F) := by
  classical
  ext ξ x
  rw [unitCycle_representation_apply, baseVector, moduleRankOne_delta_apply,
    CosetAssembly.cosetDelta_apply]
  split_ifs with h
  · rw [h, one_mul]
  · rw [zero_mul]

theorem unitCycle_representation_cosetDelta_apply (ξ : L2Group (Γ ⧸ F)) :
    (unitCycle Γ F).representation (CosetAssembly.cosetDelta Γ F) ξ =
      ⟪baseVector Γ F, ξ⟫_(ℂᵐᵒᵖ) • baseVector Γ F := by
  rw [unitCycle_representation_cosetDelta]
  rfl

/-- `F` fixes `δ_{eF}`. -/
theorem unitCycle_action_baseVector (f : Γ) (hf : f ∈ F) :
    (unitCycle Γ F).groupAction.action f (baseVector Γ F) = baseVector Γ F := by
  classical
  apply lp.ext
  funext x
  rw [unitCycle_action_apply, baseVector, L2Group.delta_apply, L2Group.delta_apply]
  have hfx : ∀ y : Γ ⧸ F, f⁻¹ • y = ((1 : Γ) : Γ ⧸ F) ↔ y = ((1 : Γ) : Γ ⧸ F) := by
    intro y
    have hfix : ∀ k ∈ F, k • ((1 : Γ) : Γ ⧸ F) = ((1 : Γ) : Γ ⧸ F) := by
      intro k hk
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq, mul_one]
      exact F.inv_mem hk
    constructor
    · intro h
      calc y = f • (f⁻¹ • y) := (smul_inv_smul f y).symm
        _ = f • ((1 : Γ) : Γ ⧸ F) := by rw [h]
        _ = _ := hfix f hf
    · intro h
      rw [h]
      exact hfix f⁻¹ (F.inv_mem hf)
  by_cases hx : x = ((1 : Γ) : Γ ⧸ F)
  · rw [if_pos ((hfx x).mpr hx), if_pos hx]
  · rw [if_neg (mt (hfx x).mp hx), if_neg hx]

end Coset

end BC4lean.Chapter8Examples.CosetUnitCycle
