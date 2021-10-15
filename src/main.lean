import linear_algebra.finite_dimensional
import field_theory.finite.basic
import ring_theory.polynomial.cyclotomic
import .aux

open ring finite_dimensional fintype mul_action polynomial

open_locale big_operators

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

local notation `d` := λ (x : A), finrank K (submodule.centralizer x)
local notation `e` := λ (x : A), finrank (subring.centralizer x) A

lemma card_centralizer (x : units A) [fintype (subring.centralizer (x : A))] : 
  card (subring.centralizer (x : A)) = q^(d x) := 
card_eq_pow_finrank

lemma card_ring' (x : units A) [fintype (subring.centralizer (x : A))] : 
  card A = (q^(d x))^(e x) := 
begin
  rw ← card_centralizer,
  exact card_eq_pow_finrank'
end

lemma finrank_centralizer_dvd_finrank_ring (x : units A) [fintype (subring.centralizer (x : A))] : 
  (d x) ∣ n := 
begin
  have := card_ring' x,
  rw [← pow_mul, card_ring, (nat.pow_right_injective one_lt_card).eq_iff] at this,
  exact ⟨_, this⟩,
  apply_instance
end

def conj_action : mul_action (units A) (units A) := 
mul_action.comp_hom (units A) mul_aut.conj

lemma stabilizer_conj_eq_centralizer (x : units A) : 
  @stabilizer (units A) (units A) _ conj_action x = subgroup.centralizer x :=
begin
  ext y,
  change y * x * y⁻¹ = x ↔ x * y = y * x,
  split;
  intro h;
  nth_rewrite 0 ← h; 
  group
end

def units_subring_centralizer_equiv_subgroup_centralizer (x : units A) : 
  units (subring.centralizer (x : A)) ≃ subgroup.centralizer x :=
calc units (subring.centralizer (x : A)) 
    ≃ {y : units A // (y : A) ∈ subring.centralizer (x : A)} : 
      units_submonoid_equiv (subring.centralizer (x : A)).to_submonoid
      begin
        intros y,
        change _ = _  → _ = _,
        norm_cast,
        exact semiconj_by.inv_right
      end
... ≃ subgroup.centralizer x : equiv.set.of_eq
      begin
        ext y,
        rw [set_like.mem_coe, set_like.mem_coe],
        change (↑x * ↑y = ↑y * ↑x) ↔ (x * y = y * x),
        norm_cast
      end

lemma card_stabilizer_conj_eq {x : units A} 
  [fintype (@stabilizer (units A) (units A) _ conj_action x)]
  [fintype (subgroup.centralizer x)] [fintype (subring.centralizer (x : A))] : 
  card (@stabilizer (units A) (units A) _ conj_action x) = q^(d x) - 1 :=
by rw [card_congr (mul_equiv.subgroup_congr $ stabilizer_conj_eq_centralizer x).to_equiv,
       card_congr (units_subring_centralizer_equiv_subgroup_centralizer x).symm,
       card_units',
       card_centralizer]

local notation `Ω` := (quotient $ @orbit_rel (units A) (units A) _ conj_action)

lemma key₀ [Π (x : units A), decidable_pred (λ u, u ∈ subring.centralizer (x : A))] (ω : Ω) : 
  (d ω.out' = n) ↔ (ω.out' : A) ∈ K :=
begin
  rw [← (nat.pow_right_injective (one_lt_card : 1 < q)).eq_iff],
  dsimp only,
  rw [← card_centralizer, ← card_ring],
  change card {x // x ∈ _} = _ ↔ _,
  rw card_subtype_eq_iff A,
  exact forall_congr (λ x, ⟨λ h, eq.symm h, λ h, eq.symm h⟩)
end

#check units_submonoid_equiv

def foo [fintype Ω] : 
  units K ≃ {ω : Ω // ¬ d ω.out' < n} :=
{ to_fun := λ k, ⟨@orbit (units A) (units A) _ conj_action (k : units A), _⟩}

lemma key₁ [fintype Ω] : 
  ∑ ω in finset.filter (λ (ω : Ω), ¬ d ω.out' < n) finset.univ, 
    (q^n - 1) / (q^(d ω.out') - 1) = q - 1 :=
begin
  sorry
end

lemma key₂ [fintype Ω] [Π (x : units A), fintype (@stabilizer _ _ _ conj_action x)]
  [Π (x : units A), fintype (subring.centralizer (x : A))]
  [Π (x : units A), fintype (subgroup.centralizer x)] : 
  q^n - 1 = (q - 1) + ∑ ω in finset.filter (λ (ω : Ω), d ω.out' < n) finset.univ, 
    (q^n - 1) / (q^(d ω.out') - 1) :=
calc q^n - 1 
      = card (units A) : by rw [← card_ring, ← card_units']
  ... = ∑ (ω : Ω), card (units A) / card (@stabilizer _ _ _ conj_action ω.out') : 
        @card_eq_sum_card_group_div_card_stabilizer _ _ _ conj_action _ _ _ _
  ... = ∑ (ω : Ω), (q^n - 1) / (q^(d ω.out') - 1) : 
        by conv in (_ / _) {rw [card_units', card_ring, card_stabilizer_conj_eq]}
  ... = (∑ ω in finset.filter (λ (ω : Ω), d ω.out' < n) finset.univ, 
          (q^n - 1) / (q^(d ω.out') - 1)) +
        (∑ ω in finset.filter (λ (ω : Ω), ¬ d ω.out' < n) finset.univ, 
          (q^n - 1) / (q^(d ω.out') - 1)) :
        by rw finset.sum_filter_add_sum_filter_not finset.univ (λ (ω : Ω), (d ω.out') < n) _
  ... = (∑ ω in finset.filter (λ (ω : Ω), d ω.out' < n) finset.univ, 
          (q^n - 1) / (q^(d ω.out') - 1)) + (q - 1) :
        by rw key₁
  ... = (q - 1) + ∑ ω in finset.filter (λ (ω : Ω), d ω.out' < n) finset.univ, 
          (q^n - 1) / (q^(d ω.out') - 1) : add_comm _ _

lemma key₃ [fintype Ω] [Π (x : units A), fintype (@stabilizer _ _ _ conj_action x)]
  [Π (x : units A), fintype (subring.centralizer (x : A))]
  [Π (x : units A), fintype (subgroup.centralizer x)] : 
  (q - 1 : ℤ) = (q^n - 1 : ℤ) + ∑ ω in finset.filter (λ (ω : Ω), d ω.out' < n) finset.univ, 
    (q^n - 1) / (q^(d ω.out') - 1) :=
begin

end

lemma key_dvd : (cyclotomic n ℤ).eval (q : ℤ) ∣ q - 1 :=
begin

end

--
--lemma key_divides {x : units A} 
--  [fintype (@stabilizer (units A) (units A) _ conj_action x)]
--  [fintype (subgroup.centralizer x)] [fintype (subring.centralizer (x : A))] : 
--  q^(d x) - 1 ∣ q^n - 1 :=
--begin
--  rw [← card_stabilizer_conj_eq, ← card_ring, ← card_units'],
--  exact subgroup.card_subgroup_dvd_card _
--end