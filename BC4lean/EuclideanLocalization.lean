import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Localization.Defs
import Mathlib.Algebra.EuclideanDomain.Defs
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Polynomials localised away from a set of points form a Euclidean domain

Let `K` be an algebraically closed field and `T ⊆ K`. Let `S` be the polynomials that are nonzero and
have no root in `T`, and `R = K[X][S⁻¹]`. Then `R` is a Euclidean domain whose size function is
`N(p / s) =` the number of roots of `p` in `T`, counted with multiplicity.

Division. Write `b = p' / s'` and split `p' = p₀ * p₁`, where `p₀` is the monic product of `X - α` over the
roots `α ∈ T` of `p'` and `p₁ ∈ S`. For `a = p / s`, divide `p = p₀ * q + r` in `K[X]` (`p₀` is monic).
Then `a = b * (q s' / (p₁ s)) + r / s` and `N(r / s) ≤ deg r < deg p₀ = N(b)`.

For `K = ℂ` and `T` the unit circle this is `CircleLoc`, the ring of rational functions without
poles on the circle; `CircleWinding` evaluates it on the circle.
-/

namespace BC4lean.EuclideanLocalization

open Polynomial

noncomputable section

variable {K : Type*} [Field K] (T : Set K)

/-- Polynomials that are nonzero and have no root in `T`. -/
def awaySubmonoid : Submonoid K[X] where
  carrier := {p | p ≠ 0 ∧ ∀ a ∈ T, ¬ p.IsRoot a}
  one_mem' := ⟨one_ne_zero, fun _ _ => by simp⟩
  mul_mem' := fun {p q} hp hq =>
    ⟨mul_ne_zero hp.1 hq.1, fun a ha h => by
      rcases (Polynomial.root_mul.mp h) with h' | h'
      exacts [hp.2 a ha h', hq.2 a ha h']⟩

theorem awaySubmonoid_le : awaySubmonoid T ≤ nonZeroDivisors K[X] :=
  fun _ hp => mem_nonZeroDivisors_of_ne_zero hp.1

/-- `K[X]` localised at the polynomials with no root in `T`. -/
abbrev AwayLoc : Type _ := Localization (awaySubmonoid T)

instance : IsDomain (AwayLoc T) := IsLocalization.isDomain_localization (awaySubmonoid_le T)

open Classical in
/-- Number of roots in `T`, with multiplicity. -/
def rootCount (p : K[X]) : ℕ := Multiset.card (p.roots.filter (· ∈ T))

variable {T}

open Classical in
theorem rootCount_mul {p q : K[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    rootCount T (p * q) = rootCount T p + rootCount T q := by
  simp [rootCount, roots_mul (mul_ne_zero hp hq), Multiset.filter_add]

open Classical in
theorem rootCount_eq_zero_of_mem {s : K[X]} (hs : s ∈ awaySubmonoid T) : rootCount T s = 0 := by
  rw [rootCount, Multiset.card_eq_zero, Multiset.filter_eq_nil]
  intro a ha haT
  exact hs.2 a haT ((mem_roots hs.1).mp ha)

open Classical in
theorem rootCount_le (p : K[X]) : rootCount T p ≤ p.natDegree :=
  (Multiset.card_le_card (Multiset.filter_le _ _)).trans (card_roots' p)

open Classical in
/-- The monic `T`-part of `p`: the product of `X - α` over the roots `α ∈ T`. -/
def tPart (T : Set K) (p : K[X]) : K[X] := ((p.roots.filter (· ∈ T)).map fun a => X - C a).prod

open Classical in
/-- The rest of `p`. -/
def offPart (T : Set K) (p : K[X]) : K[X] :=
  C p.leadingCoeff * ((p.roots.filter (· ∉ T)).map fun a => X - C a).prod

theorem tPart_monic (p : K[X]) : (tPart T p).Monic :=
  monic_multiset_prod_of_monic _ _ fun a _ => monic_X_sub_C a

theorem natDegree_tPart (p : K[X]) : (tPart T p).natDegree = rootCount T p := by
  rw [tPart, natDegree_multiset_prod_X_sub_C_eq_card, rootCount]

open Classical in
theorem tPart_mul_offPart [IsAlgClosed K] (p : K[X]) : tPart T p * offPart T p = p := by
  conv_rhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (k := K) (p := p)), ← Multiset.filter_add_not (· ∈ T) p.roots]
  rw [Multiset.map_add, Multiset.prod_add, tPart, offPart]
  ring

open Classical in
theorem offPart_mem {p : K[X]} (hp : p ≠ 0) : offPart T p ∈ awaySubmonoid T := by
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  have hprod : ((p.roots.filter (· ∉ T)).map fun a => X - C a).prod ≠ 0 :=
    (monic_multiset_prod_of_monic _ _ fun a _ => monic_X_sub_C a).ne_zero
  have hne : offPart T p ≠ 0 := mul_ne_zero (by simpa using hlc) hprod
  refine ⟨hne, fun a ha hroot => ?_⟩
  have hmem : a ∈ (offPart T p).roots := (mem_roots hne).mpr hroot
  rw [offPart, roots_C_mul _ hlc, roots_multiset_prod_X_sub_C] at hmem
  exact (Multiset.mem_filter.mp hmem).2 ha

variable (T)

/-- A chosen representative `(p, s)` of `x = p / s`. -/
def rep (x : AwayLoc T) : K[X] × awaySubmonoid T :=
  Classical.choose (IsLocalization.mk'_surjective (awaySubmonoid T) x)

theorem mk'_rep (x : AwayLoc T) :
    IsLocalization.mk' (AwayLoc T) (rep T x).1 (rep T x).2 = x :=
  Classical.choose_spec (IsLocalization.mk'_surjective (awaySubmonoid T) x)

/-- The Euclidean size: number of roots in `T` of the numerator. -/
def size (x : AwayLoc T) : ℕ := rootCount T (rep T x).1

variable {T}

theorem algebraMap_injective : Function.Injective (algebraMap K[X] (AwayLoc T)) :=
  IsLocalization.injective (AwayLoc T) (awaySubmonoid_le T)

theorem rep_fst_ne_zero {x : AwayLoc T} (hx : x ≠ 0) : (rep T x).1 ≠ 0 := by
  intro h
  apply hx
  rw [← mk'_rep T x, h, IsLocalization.mk'_zero]

theorem size_mk' {p : K[X]} (hp : p ≠ 0) (s : awaySubmonoid T) :
    size T (IsLocalization.mk' (AwayLoc T) p s) = rootCount T p := by
  set x := IsLocalization.mk' (AwayLoc T) p s
  have h := mk'_rep T x
  rw [IsLocalization.mk'_eq_iff_eq] at h
  have h' := algebraMap_injective h
  -- h' : (rep x).2 * p = s * (rep x).1   (up to the orientation `mk'_eq_iff_eq` gives)
  have hs := (rep T x).2.2
  have hs' := s.2
  have hq : (rep T x).1 ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h'
    exact mul_ne_zero hs.1 hp h'.symm
  have := congrArg (rootCount T) h'
  rw [rootCount_mul hs'.1 hq, rootCount_mul hs.1 hp, rootCount_eq_zero_of_mem hs,
    rootCount_eq_zero_of_mem hs'] at this
  simp only [size]
  omega

/-- The well-founded relation of the Euclidean structure. -/
def rel (x y : AwayLoc T) : Prop := y ≠ 0 ∧ (x = 0 ∨ size T x < size T y)

open Classical in
theorem rel_wf : WellFounded (rel (T := T)) := by
  let f : AwayLoc T → ℕ := fun x => if x = 0 then 0 else size T x + 1
  refine Subrelation.wf (r := InvImage (· < ·) f) ?_ (InvImage.wf f wellFounded_lt)
  intro x y ⟨hy, h⟩
  simp only [InvImage, f, if_neg hy]
  rcases h with h | h
  · simp [h]
  · split_ifs <;> omega

open Classical in
/-- The quotient: for `b ≠ 0`, `(p₀ p₁ / s') ∣ (p / s)` with quotient `q s' / (p₁ s)`. -/
def quot (a b : AwayLoc T) : AwayLoc T :=
  if hb : b = 0 then 0 else
    IsLocalization.mk' (AwayLoc T)
      ((rep T a).1 /ₘ tPart T (rep T b).1 * (rep T b).2)
      ⟨offPart T (rep T b).1 * (rep T a).2,
        (awaySubmonoid T).mul_mem (offPart_mem (rep_fst_ne_zero hb)) (rep T a).2.2⟩

open Classical in
/-- The remainder `r / s`. -/
def rem (a b : AwayLoc T) : AwayLoc T :=
  if b = 0 then a else
    IsLocalization.mk' (AwayLoc T) ((rep T a).1 %ₘ tPart T (rep T b).1) (rep T a).2

open Classical in
theorem quot_mul_add_rem [IsAlgClosed K] (a b : AwayLoc T) : b * quot a b + rem a b = a := by
  by_cases hb : b = 0
  · simp [quot, rem, hb]
  simp only [quot, rem, dif_neg hb, if_neg hb]
  set φ := algebraMap K[X] (AwayLoc T)
  set p := (rep T a).1
  set s := (rep T a).2
  set p' := (rep T b).1
  set s' := (rep T b).2
  set p₀ := tPart T p'
  set p₁ := offPart T p'
  set Q := IsLocalization.mk' (AwayLoc T) (p /ₘ p₀ * s') (⟨p₁ * s, _⟩ : awaySubmonoid T)
  set Rm := IsLocalization.mk' (AwayLoc T) (p %ₘ p₀) s
  have h1 : b * φ s' = φ p₀ * φ p₁ := by
    rw [← map_mul, tPart_mul_offPart, ← mk'_rep T b, IsLocalization.mk'_spec]
  have h2 : Q * (φ p₁ * φ s) = φ (p /ₘ p₀) * φ s' := by
    rw [← map_mul, ← map_mul]
    exact IsLocalization.mk'_spec (AwayLoc T) _ (⟨p₁ * s, _⟩ : awaySubmonoid T)
  have h3 : Rm * φ s = φ (p %ₘ p₀) := IsLocalization.mk'_spec _ _ _
  have h4 : a * φ s = φ p := by rw [← mk'_rep T a, IsLocalization.mk'_spec]
  have h5 : φ p = φ p₀ * φ (p /ₘ p₀) + φ (p %ₘ p₀) := by
    rw [← map_mul, ← map_add, add_comm, modByMonic_add_div]
  have hu : IsUnit (φ s * φ s' * φ p₁) := by
    refine ((IsLocalization.map_units (AwayLoc T) s).mul
      (IsLocalization.map_units (AwayLoc T) s')).mul ?_
    exact IsLocalization.map_units (AwayLoc T) (⟨p₁, offPart_mem (rep_fst_ne_zero hb)⟩ :
      awaySubmonoid T)
  apply hu.mul_right_cancel
  linear_combination (Q * φ s * φ p₁) * h1 + (φ p₀ * φ p₁) * h2 + (φ s' * φ p₁) * h3
    - (φ s' * φ p₁) * h4 - (φ s' * φ p₁) * h5

open Classical in
theorem rem_rel (a : AwayLoc T) {b : AwayLoc T} (hb : b ≠ 0) : rel (rem a b) b := by
  refine ⟨hb, ?_⟩
  simp only [rem, if_neg hb]
  by_cases hr : (rep T a).1 %ₘ tPart T (rep T b).1 = 0
  · left; rw [hr, IsLocalization.mk'_zero]
  right
  rw [size_mk' hr]
  have hlt : ((rep T a).1 %ₘ tPart T (rep T b).1).natDegree < (tPart T (rep T b).1).natDegree :=
    natDegree_lt_natDegree hr (degree_modByMonic_lt _ (tPart_monic _))
  exact (rootCount_le _).trans_lt (hlt.trans_le (natDegree_tPart _).le)

theorem size_mul {a b : AwayLoc T} (ha : a ≠ 0) (hb : b ≠ 0) :
    size T (a * b) = size T a + size T b := by
  conv_lhs => rw [← mk'_rep T a, ← mk'_rep T b, ← IsLocalization.mk'_mul]
  rw [size_mk' (mul_ne_zero (rep_fst_ne_zero ha) (rep_fst_ne_zero hb)),
    rootCount_mul (rep_fst_ne_zero ha) (rep_fst_ne_zero hb)]
  rfl

theorem not_rel_mul (a : AwayLoc T) {b : AwayLoc T} (hb : b ≠ 0) : ¬ rel (a * b) a := by
  rintro ⟨ha, h⟩
  rcases h with h | h
  · exact mul_ne_zero ha hb h
  · rw [size_mul ha hb] at h; omega

theorem size_one : size T (1 : AwayLoc T) = 0 := by
  have h1 : (1 : AwayLoc T) = IsLocalization.mk' (AwayLoc T) (1 : K[X]) (1 : awaySubmonoid T) := by
    rw [IsLocalization.mk'_one, map_one]
  rw [h1, size_mk' one_ne_zero]
  simp [rootCount]

open Classical in
theorem mem_of_rootCount_eq_zero {p : K[X]} (hp : p ≠ 0) (h : rootCount T p = 0) :
    p ∈ awaySubmonoid T := by
  refine ⟨hp, fun a ha hr => ?_⟩
  rw [rootCount, Multiset.card_eq_zero, Multiset.filter_eq_nil] at h
  exact h a ((mem_roots hp).mpr hr) ha

/-- The units of `K[X][S⁻¹]` are the nonzero elements of size `0`,
i.e. the fractions `s₁ / s₂` of polynomials with no root in `T`. -/
theorem isUnit_iff_size_eq_zero {x : AwayLoc T} (hx : x ≠ 0) : IsUnit x ↔ size T x = 0 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h := size_mul (T := T) u.ne_zero (u⁻¹).ne_zero
    rw [u.mul_inv, size_one] at h
    omega
  · intro h
    have hp := rep_fst_ne_zero hx
    have hmem := mem_of_rootCount_eq_zero hp h
    rw [← mk'_rep T x]
    exact IsUnit.of_mul_eq_one _ (IsLocalization.mk'_mul_mk'_eq_one' _ _ hmem)

theorem isUnit_iff_exists_mk' {x : AwayLoc T} :
    IsUnit x ↔ ∃ p q : awaySubmonoid T, IsLocalization.mk' (AwayLoc T) (p : K[X]) q = x := by
  constructor
  · intro hu
    have hx := hu.ne_zero
    refine ⟨⟨_, mem_of_rootCount_eq_zero (rep_fst_ne_zero hx) ((isUnit_iff_size_eq_zero hx).mp hu)⟩,
      (rep T x).2, mk'_rep T x⟩
  · rintro ⟨p, q, rfl⟩
    exact IsUnit.of_mul_eq_one _ (IsLocalization.mk'_mul_mk'_eq_one p q)

variable (T)

/-- `K[X]` localised away from `T` is a Euclidean domain. -/
instance euclideanDomain [IsAlgClosed K] : EuclideanDomain (AwayLoc T) :=
  { (inferInstance : CommRing (AwayLoc T)) with
    toNontrivial := inferInstance
    quotient := quot
    quotient_zero := fun a => by simp [quot]
    remainder := rem
    quotient_mul_add_remainder_eq := quot_mul_add_rem
    r := rel
    r_wellFounded := rel_wf
    remainder_lt := rem_rel
    mul_left_not_lt := not_rel_mul }

/-- `ℂ[X]` localised at the polynomials with no zero on the unit circle. -/
abbrev CircleLoc : Type := AwayLoc (Metric.sphere (0 : ℂ) 1)

example : EuclideanDomain CircleLoc := inferInstance

/-- The Euclidean ring structure is the localisation's ring structure (no diamond). -/
example : (EuclideanDomain.toCommRing : CommRing CircleLoc) =
    inferInstanceAs (CommRing (Localization (awaySubmonoid (Metric.sphere (0 : ℂ) 1)))) := by
  with_reducible_and_instances rfl

end

end BC4lean.EuclideanLocalization
