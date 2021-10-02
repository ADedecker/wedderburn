import ring_theory.subring

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

def submonoid.commute_with {M : Type*} [monoid M] (x : M) : submonoid M :=
{ carrier := {y | commute x y}, 
  one_mem' := commute.one_right x,
  mul_mem' := λ a b, commute.mul_right }

def subgroup.commute_with {G : Type*} [group G] (x : G) : subgroup G :=
{ inv_mem' := λ a, commute.inv_right,
  ..submonoid.commute_with x }

def subsemiring.commute_with {R : Type*} [semiring R] (x : R) : subsemiring R :=
{ zero_mem' := commute.zero_right x,
  add_mem' := λ a b, commute.add_right,
  ..submonoid.commute_with x }

def subring.commute_with {R : Type*} [ring R] (x : R) : subring R :=
{ neg_mem' := λ a, commute.neg_right,
  ..subsemiring.commute_with x }

instance subring.commute_with.division_ring {R : Type*} [division_ring R] (x : R) : 
division_ring (subring.commute_with x) :=
{ inv := λ ⟨y, hy⟩, ⟨y⁻¹, commute.inv_right' hy⟩,
  mul_inv_cancel := λ ⟨a, ha⟩ h, subtype.ext $ mul_inv_cancel $ subtype.coe_injective.ne h,
  inv_zero := subtype.ext inv_zero,
  ..(subring.commute_with x).nontrivial,
  ..(subring.commute_with x).to_ring }

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