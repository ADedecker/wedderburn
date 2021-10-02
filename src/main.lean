import linear_algebra.finite_dimensional
import field_theory.finite.basic
import .aux

open ring finite_dimensional fintype mul_action

variables {A : Type*} [division_ring A] [fintype A] [fintype (subring.center A)]
-- we keep "unnecessary" fintype instances to avoid diamonds

local notation `K` := subring.center A
local notation `q` := card K
local notation `n` := finrank K A

lemma card_ring : card A = q^n := card_eq_pow_finrank

lemma commutative_mul_iff : commutative ((*) : A → A → A) ↔ n = 1 :=
begin
  rw [← subring.center_eq_top_iff, subring.eq_top_iff', finrank_eq_one_iff_of_nonzero' (1 : A) one_ne_zero],
  simp_rw [subring.smul_def, smul_eq_mul, mul_one],
  exact ⟨λ h x, ⟨⟨x, h x⟩, rfl⟩, λ h x, let ⟨c, hc⟩ := h x in hc ▸ c.2⟩
end

def submodule_commute_with (x : A) : submodule K A := 
{ smul_mem' := λ c y (hy : commute x y), 
    calc x * c • y 
        = x * (c * y) : by rw [subring.smul_def, smul_eq_mul]
    ... = (x * c) * y : by rw mul_assoc
    ... = (c * x) * y : by have : x * ↑c = ↑c * x := c.2 x; rw this
    ... = c * (x * y) : by rw mul_assoc
    ... = c * (y * x) : by rw hy.eq
    ... = (c * y) * x : by rw mul_assoc
    ... = c • y * x : by rw [subring.smul_def, smul_eq_mul],
  ..subring.commute_with x }

local notation `d` x := finrank K (submodule_commute_with (x : A)) 

lemma card_commute_with {x : units A} [fintype (subring.commute_with (x : A))] : 
  card (subring.commute_with (x : A)) = q^(d x) := 
card_eq_pow_finrank

def conj_action : mul_action (units A) (units A) := 
mul_action.comp_hom (units A) mul_aut.conj

lemma stabilizer_conj_eq_commute_with (x : units A) : 
  @stabilizer (units A) (units A) _ conj_action x = subgroup.commute_with x :=
begin
  ext y,
  change y * x * y⁻¹ = x ↔ x * y = y * x,
  split;
  intro h;
  nth_rewrite 0 ← h; 
  group
end

def units_subring_commute_with_equiv_subgroup_commute_with (x : units A) : 
  units (subring.commute_with (x : A)) ≃ subgroup.commute_with x :=
calc units (subring.commute_with (x : A)) 
    ≃ {y : units A // (y : A) ∈ subring.commute_with (x : A)} : 
      units_submonoid_equiv (subring.commute_with (x : A)).to_submonoid
      begin
        intros y,
        change _ = _  → _ = _,
        norm_cast,
        exact semiconj_by.inv_right
      end
... ≃ subgroup.commute_with x : equiv.set.of_eq
      begin
        ext y,
        rw [set_like.mem_coe, set_like.mem_coe],
        change (↑x * ↑y = ↑y * ↑x) ↔ (x * y = y * x),
        norm_cast
      end

lemma card_stabilizer_conj_eq {x : units A} 
  [fintype (@stabilizer (units A) (units A) _ conj_action x)]
  [fintype (subgroup.commute_with x)] [fintype (subring.commute_with (x : A))] : 
  card (@stabilizer (units A) (units A) _ conj_action x) = q^(d x) - 1 :=
by rw [card_congr (mul_equiv.subgroup_congr $ stabilizer_conj_eq_commute_with x).to_equiv,
       card_congr (units_subring_commute_with_equiv_subgroup_commute_with x).symm,
       card_units',
       card_commute_with]

lemma key_divides {x : units A} 
  [fintype (@stabilizer (units A) (units A) _ conj_action x)]
  [fintype (subgroup.commute_with x)] [fintype (subring.commute_with (x : A))] : 
  q^(d x) - 1 ∣ q^n - 1 :=
begin
  rw [← card_stabilizer_conj_eq, ← card_ring, ← card_units'],
  exact subgroup.card_subgroup_dvd_card _
end