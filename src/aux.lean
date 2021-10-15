import linear_algebra
import field_theory.finite.basic

open_locale big_operators

lemma card_subtype_eq_iff (α : Type*) (p : α → Prop) [decidable_pred p] [fintype α] :
  fintype.card ({x // p x}) = fintype.card α ↔ ∀ x, p x :=
begin
  rw [fintype.card_subtype p, finset.card_eq_iff_eq_univ, finset.eq_univ_iff_forall],
  refine forall_congr (λ x, _),
  rw [finset.mem_filter],
  exact ⟨λ ⟨_, h⟩, h, λ h, ⟨finset.mem_univ x, h⟩⟩
end

lemma set.card_coe_sort_eq_iff (α : Type*) (S : set α) [decidable_pred (λ x, x ∈ S)] [fintype α] :
  fintype.card S = fintype.card α ↔ ∀ x, x ∈ S :=
card_subtype_eq_iff α (λ x, x ∈ S)

lemma card_eq_pow_finrank' {K V : Type*} [division_ring K] [add_comm_group V] [module K V] [fintype K] [fintype V] :
  fintype.card V = (fintype.card K) ^ (finite_dimensional.finrank K V) :=
begin
  let b := is_noetherian.finset_basis K V,
  rw [module.card_fintype b, ← finite_dimensional.finrank_eq_card_basis b],
end

lemma subsemiring.center_eq_top_iff (R : Type*) [semiring R] : 
  subsemiring.center R = ⊤ ↔ commutative ((*) : R → R → R) :=
begin
  simp_rw [subsemiring.eq_top_iff', subsemiring.mem_center_iff], 
  rw forall_swap,
  refl
end

lemma subring.center_eq_top_iff (R : Type*) [ring R] : 
  subring.center R = ⊤ ↔ commutative ((*) : R → R → R) :=
begin
  simp_rw [subring.eq_top_iff', subring.mem_center_iff], 
  rw forall_swap,
  refl
end

def submonoid.centralizer {M : Type*} [monoid M] (x : M) : submonoid M :=
{ carrier := {y | commute x y}, 
  one_mem' := commute.one_right x,
  mul_mem' := λ a b, commute.mul_right }

def subgroup.centralizer {G : Type*} [group G] (x : G) : subgroup G :=
{ inv_mem' := λ a, commute.inv_right,
  ..submonoid.centralizer x }

def subsemiring.centralizer {R : Type*} [semiring R] (x : R) : subsemiring R :=
{ zero_mem' := commute.zero_right x,
  add_mem' := λ a b, commute.add_right,
  ..submonoid.centralizer x }

def subring.centralizer {R : Type*} [ring R] (x : R) : subring R :=
{ neg_mem' := λ a, commute.neg_right,
  ..subsemiring.centralizer x }

instance subring.centralizer.division_ring {R : Type*} [division_ring R] (x : R) : 
division_ring (subring.centralizer x) :=
{ inv := λ ⟨y, hy⟩, ⟨y⁻¹, commute.inv_right' hy⟩,
  mul_inv_cancel := λ ⟨a, ha⟩ h, subtype.ext $ mul_inv_cancel $ subtype.coe_injective.ne h,
  inv_zero := subtype.ext inv_zero,
  ..(subring.centralizer x).nontrivial,
  ..(subring.centralizer x).to_ring }

def submodule.centralizer {R : Type*} [ring R] (x : R) : 
  submodule (subring.center R) R := 
{ smul_mem' := λ c y (hy : commute x y), 
    calc x * c • y 
        = x * (c * y) : by rw [subring.smul_def, smul_eq_mul]
    ... = (x * c) * y : by rw mul_assoc
    ... = (c * x) * y : by have : x * ↑c = ↑c * x := c.2 x; rw this
    ... = c * (x * y) : by rw mul_assoc
    ... = c * (y * x) : by rw hy.eq
    ... = (c * y) * x : by rw mul_assoc
    ... = c • y * x : by rw [subring.smul_def, smul_eq_mul],
  ..subring.centralizer x }

def units_submonoid_equiv {M : Type*} [monoid M] (S : submonoid M) 
  (hS : ∀ x : units M, (x : M) ∈ S → ((x⁻¹ : units M) : M) ∈ S) :
  units S ≃ {x : units M // (x : M) ∈ S} :=
{ to_fun := λ x, ⟨units.map S.subtype x, (coe x : S).2⟩,
  inv_fun := λ x, ⟨⟨x.1, x.2⟩, ⟨coe (x.1⁻¹), hS x.1 x.2⟩, 
    by ext; rw submonoid.coe_mul; exact x.1.mul_inv, 
    by ext; rw submonoid.coe_mul; exact x.1.inv_mul⟩,
  left_inv := λ x, by ext; refl,
  right_inv := λ x, by ext; refl }

lemma card_units' {A : Type*} [fintype A] [division_ring A] : 
  fintype.card (units A) = fintype.card A - 1 :=
begin
  classical,
  rw [eq_comm, nat.sub_eq_iff_eq_add (fintype.card_pos_iff.2 ⟨(0 : A)⟩)],
  haveI := set_fintype {a : A | a ≠ 0},
  haveI := set_fintype (@set.univ A),
  rw [fintype.card_congr (equiv.units_equiv_ne_zero _),
    ← @set.card_insert _ _ {a : A | a ≠ 0} _ (not_not.2 (eq.refl (0 : A)))
    (set.fintype_insert _ _), fintype.card_congr (equiv.set.univ A).symm],
  congr; simp [set.ext_iff, classical.em]
end

section class_formula

/-!
## Class formula corollary on the number of fixed points
-/

open fintype mul_action function

variables {G X : Type*} [group G] [mul_action G X] [fintype X] [Π (x : X), fintype (orbit G x)]
  [fintype (quotient $ orbit_rel G X)] [fintype (mul_action.fixed_points G X)]

local notation `Ω` := (quotient $ orbit_rel G X)

lemma card_eq_sum_card_orbits' {φ : Ω → X} (hφ : left_inverse quotient.mk' φ) : 
  card X = ∑ (ω : Ω), card (orbit G (φ ω)) :=
by rw [card_congr (self_equiv_sigma_orbits' G X hφ), card_sigma]

lemma card_eq_card_fixed_points_add_sum_card_nontrivial_orbits'
  {φ : Ω → X} (hφ : left_inverse quotient.mk' φ) 
  [decidable_pred (λ (ω : Ω), φ ω ∈ mul_action.fixed_points G X)] : 
  card X = 
    (∑ ω in finset.filter (λ (ω : Ω), φ ω ∉ mul_action.fixed_points G X) finset.univ, 
      card (orbit G (φ ω))) + 
    card (mul_action.fixed_points G X) :=
calc card X 
      = ∑ (ω : Ω), card (orbit G (φ ω)) : card_eq_sum_card_orbits' hφ
  ... = ∑ ω in finset.filter (λ (ω : Ω), φ ω ∈ mul_action.fixed_points G X) finset.univ, 
          card (orbit G (φ ω)) +
        ∑ ω in finset.filter (λ (ω : Ω), φ ω ∉ mul_action.fixed_points G X) finset.univ, 
          card (orbit G (φ ω)) : (finset.sum_filter_add_sum_filter_not _ _ _).symm
  ... = ∑ ω in finset.filter (λ (ω : Ω), φ ω ∈ mul_action.fixed_points G X) finset.univ, 
          1 +
        ∑ ω in finset.filter (λ (ω : Ω), φ ω ∉ mul_action.fixed_points G X) finset.univ, 
          card (orbit G (φ ω)) : 
        by {congr' 1, conv {congr, congr,  } }
  ... = _ : sorry

lemma dvd_card_trivial_orbit' 
  {φ : Ω → X} (hφ : left_inverse quotient.mk' φ) {n : ℕ} (hn₁ : n ∣ card X) 
  (hn₂ : ∀ (x : X), x ∉ mul_action.fixed_points G X → n ∣ card (orbit G x)) : 
  n ∣ card (mul_action.fixed_points G X) :=
begin
  
end

end class_formula
