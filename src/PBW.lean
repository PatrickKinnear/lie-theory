import algebra.free_monoid.basic
import algebra.free_algebra
import algebra.module.submodule.basic
import linear_algebra.free_algebra
import linear_algebra.basis
import init.algebra.order
import data.fin.basic
import algebra.module.linear_map
import algebra.ring_quot
import logic.relation

noncomputable theory
open_locale classical
open set

--We need to prove the Diamond Lemma!

variables (X : Type) 
variables (R: Type) [comm_ring R][ne_zero (1 : R)]

structure reduction_system :=
(set : set (free_monoid X × free_algebra R X))
(nondegeneracy: ∀ p : set, free_monoid.lift (free_algebra.ι R) p.val.1 ≠ p.val.2 )



---fix reduction_system, notion of reduction, and define irreducible.

variable (S : reduction_system X R)

--Inclusion of free monoid into free algebra
-- def inc_free_monoid_free_alg : free_monoid X →* free_algebra R X
-- := free_monoid.lift (free_algebra.ι R)

notation `bs`:= free_algebra.basis_free_monoid
variable q : free_algebra R X

--Define reduction on basis elements
def reduction_on_basis (σ : S.set) (A B : free_monoid X) : 
free_monoid X → free_algebra R X := 
λ x, if (x=A*σ.val.1*B) then 
(bs R X A)*σ.val.2*((bs R X) B) 
else ((bs R X) x)



def reduction (σ : S.set) (A B: free_monoid X) : free_algebra R X →ₗ[R] free_algebra R X 
:= basis.constr (bs R X) R (reduction_on_basis X R S σ A B)

--Set of irreducible polynomials
def irr_set : set (free_algebra R X) := 
{ a : free_algebra R X | ∀ σ : S.set, ∀ A : free_monoid X, ∀ B : 
free_monoid X, reduction X R S σ A B a = a}

def irr : submodule R (free_algebra R X) :=
⟨irr_set X R S, by sorry, by sorry, by sorry⟩

def irr_monomials : set (free_monoid X) :=
{ m : free_monoid X | ∀ σ : S.set, ∀ A B: free_monoid X, A*σ.val.1*B ≠ m } 

--Ambiguities

structure overlap_ambiguity :=
(σ τ : S.set)
(A B C : free_monoid X)
(overlap : σ.val.1 = A*B ∧ τ.val.1 = B*C)

structure inclusion_ambiguity :=
(σ τ : S.set)
(A B C : free_monoid X)
(inclusion : τ.val.1 = A*σ.val.1*B)

structure ambiguity:=
(σ τ : S.set)
(A B C: free_monoid X)
(overlap_not_inclusion : bool)
(ambiguity_condition : if overlap_not_inclusion 
  then σ.val.1 = A*B ∧ τ.val.1 = B*C 
  else σ.val.1 = B ∧ τ.val.1 = A*B*C )

--Sequence of reductions
def reductions : set (free_algebra R X →ₗ[R] free_algebra R X) := 
{ (reduction X R S triple.1 triple.2.1 triple.2.2) | triple : S.set × free_monoid X ×  free_monoid X }

variable n : ℕ 
variable r : fin n → reductions X R S

def compose (f : fin n → reductions X R S): (free_algebra R X →ₗ[R] free_algebra R X) :=
begin
induction n,
{exact linear_map.id},
{exact (f n_n).val ∘ₗ n_ih (f ∘ fin.succ_embedding n_n)}
end

--This seems unnecessarily set-dependent?
def final_on (r : fin n → reductions X R S) (a : free_algebra R X) : 
Prop := ((compose X R S n r) a) ∈ (irr X R S)

--Not the most elegant handling of infinite sequences?
def reduction_finite (a : free_algebra R X) : 
Prop := ∀ r : ℕ → reductions X R S, ∃ N : ℕ, ∀ n > N, (compose X R S n (r ∘ (fin.coe_embedding))) a = (compose X R S (n-1) (r ∘ (fin.coe_embedding))) a ∧ (compose X R S (n-1) (r ∘ (fin.coe_embedding))) a ∈ (irr X R S)

def rf_submodule : submodule R (free_algebra R X) :=
⟨{a : free_algebra R X | reduction_finite X R S a}, by sorry, by sorry, by sorry⟩

-- fact that maximal sequences acting nontrivially on rf things are final!! Notion of maximal element; extended natural numbers...

def reduction_unique (a : free_algebra R X) : Prop := reduction_finite X R S a ∧ ∃ x : irr X R S, ∀ n : ℕ, ∀ r : fin n → reductions X R S, (final_on X R S n r a) → (compose X R S n r) a = x

def ru_submodule : submodule R (free_algebra R X) :=
⟨{a : free_algebra R X | reduction_unique X R S a}, by sorry, by sorry, by sorry⟩

noncomputable def  r_s : ru_submodule X R S → irr X R S:=
begin
intro a,
cases a.property,
apply exists.classical_rec_on right,
intros x hx,
exact x,
-- try to use the choose tactic here!
end

--Partial order
class semigroup_partial_order (α : Type) [semigroup α] extends partial_order α :=
(semigroup_condition : ∀ b b': α, b≤b' → ∀ a c: α, a*b*c ≤ a*b'*c)

--Extracting basis terms in some element of free algebra
def basis_terms (a : free_algebra R X) : set (free_monoid X) := 
{ m : free_monoid X | (bs R X).repr a m ≠ 0}


-- This takes as argument a semigroup for now, so need to pass <X> as argument
class compatible_semigroup_partial_order (S : reduction_system X R) 
extends semigroup_partial_order (free_monoid X):=
(compatible : ∀ σ : S.set, ∀ u ∈ basis_terms X R (σ.val.2), u<σ.val.1)

-- This takes as argument a reduction system S (which already includes X and R)
def ambiguity_is_resolvable (amb : ambiguity X R S): Prop :=
begin
by_cases amb.overlap_not_inclusion = true,
{exact ∃ f g : reductions X R S, f((amb.σ.val.2)*((free_algebra.basis_free_monoid R X) amb.C)) = g(((free_algebra.basis_free_monoid R X) amb.A)*(amb.τ.val.2))},
{{exact ∃ f g : reductions X R S, f(((free_algebra.basis_free_monoid R X) amb.A)*(amb.σ.val.2)*((free_algebra.basis_free_monoid R X) amb.C)) = g(amb.τ.val.2)}}
end

variables amb : ambiguity X R S
#check (∃ f g : reductions X R S, f((amb.σ.val.2)*((free_algebra.basis_free_monoid R X) amb.C)) = 0)

lemma obvious (σ : S.set) (A B x: free_monoid X)(h: ¬ x=A*σ.val.1*B):
 ((free_algebra.basis_free_monoid R X) x)=(reduction_on_basis X R S σ A B) (x):=
begin
  unfold reduction_on_basis,
  split_ifs,
  refl,
end


lemma observation (S : reduction_system X R)[compatible_semigroup_partial_order X R S]
(A B : free_monoid X)(σ : S.set): ∀ a : free_monoid X, ∀ u ∈ (basis_terms X R)
( (reduction_on_basis X R S σ A B) a),  ¬ u > a:=
begin
  intros a u hu,
  by_cases a = A*σ.val.1*B,
  {
    have step₁: ∀ v∈ (basis_terms X R) σ.val.2, A*v*B≤A*σ.val.1*B,
    {
      intros v hv,
      apply _inst_3.semigroup_condition v σ.val.1,
      exact (le_not_le_of_lt(_inst_3.compatible σ v hv)).1,      
    },
    unfold reduction_on_basis at hu,
    split_ifs at hu,
    have armadillo : ∃ v ∈ (basis_terms X R) σ.val.2, A*v*B = u,
    {
      sorry,
    },
    cases armadillo with v hv,
    cases hv with hv₁ hv₂,
    rw ← hv₂,
    rw h,
    exact not_lt_of_ge(step₁ v hv₁),
  },
  {
    unfold basis_terms at hu,
    rw set.mem_set_of_eq at hu,
    unfold reduction_on_basis at hu,
    split_ifs at hu,
    simp[basis.repr_self] at hu,
    have step₂ : u ∈ (finsupp.single a (1 : R)).support,
    {
      simp[finsupp.mem_support_iff],
      exact hu,
    },
    rw finsupp.support_single_ne_zero at step₂,
    {
      have equality : u = a,
      {
        simp at step₂,
        exact step₂,
      },
      rw equality,
      exact lt_irrefl a,
    },
    {
      simp,
    },
  },
end

--- This is to  pick out when B*(W_σ)*C < A, which is used to define the relation which specifies when an ambiguity is resolvable rel a partial order.
def compatibility_pre_rel (A : free_monoid X) (_ : semigroup_partial_order (free_monoid X)) (S : reduction_system X R): (free_monoid X) → (free_monoid X) → S.set → Prop := λ B C σ, B*(σ.val.1)*C < A

def compatibility_pre_rel_doubled (A : free_monoid X) (_ : semigroup_partial_order (free_monoid X)) (S : reduction_system X R): ((free_monoid X) × (free_monoid X) × S.set) → ((free_monoid X) × (free_monoid X) × S.set) → Prop := λ Y Z, Y.1*(Y.2.2.val.1)*Y.2.1 < A ∧ Y = Z

--- The maps below are needed to push the compatibility pre-relation to the algebra.
def sandwich_monoid_element : ((free_monoid X) × (free_monoid X) × S.set) →  free_algebra R X := λ Y, ((free_algebra.basis_free_monoid R X) Y.1)*((free_algebra.basis_free_monoid R X) Y.2.2.val.1)*((free_algebra.basis_free_monoid R X) Y.2.1) 

def sandwich_algebra_element : ((free_monoid X) × (free_monoid X) × S.set) → free_algebra R X := λ Y, ((free_algebra.basis_free_monoid R X) Y.1)*(Y.2.2.val.2)*((free_algebra.basis_free_monoid R X) Y.2.1) 

-- This relation on the free algebra defines a quotient, used to speak of when an overlap is resolvable rel a partial order
def compatibility_rel (A : free_monoid X) (s : semigroup_partial_order (free_monoid X)): (free_algebra R X) → (free_algebra R X) → Prop :=  relation.map (compatibility_pre_rel_doubled X R A s S)(sandwich_monoid_element X R S) (sandwich_algebra_element X R S)

-- This quotient is used to talk of when an overlap is resolvable rel a partial order (in place of using an ideal which is not defined for noncommutative rings yet). Fix the type here to be more specific!
def rel_quotient (A : free_monoid X) (s : semigroup_partial_order (free_monoid X)): Type* := ring_quot (compatibility_rel X R S A s)

--- This predicate is the statement that an overlap ambiguity is resolvable rel a given partial order. Instead of saying something is in an ideal, we say it is zero in a quotient.
def overlap_resolvable_rel (amb : overlap_ambiguity X R S) (s : semigroup_partial_order (free_monoid X)) : Prop := (ring_quot.mk_ring_hom (compatibility_rel X R S (amb.A*amb.B*amb.C) s)) (amb.σ.val.2*((free_algebra.basis_free_monoid R X) amb.C) - ((free_algebra.basis_free_monoid R X) amb.A)*amb.τ.val.2) = 0

--- This predicate is the statement that an inclusion ambiguity is resolvable rel a given partial order. Instead of saying something is in an ideal, we say it is zero in a quotient.
def inclusion_resolvable_rel (amb : overlap_ambiguity X R S) (s : semigroup_partial_order (free_monoid X)) : Prop := (ring_quot.mk_ring_hom (compatibility_rel X R S (amb.A*amb.B*amb.C) s)) (((free_algebra.basis_free_monoid R X) amb.A)*(amb.σ.val.2)*((free_algebra.basis_free_monoid R X) amb.C) - amb.τ.val.2) = 0

def ambiguity_resolvable_rel (amb: ambiguity X R S) (s : semigroup_partial_order (free_monoid X)) : Prop := 
begin
by_cases amb.overlap_not_inclusion = true,
{exact (ring_quot.mk_ring_hom (compatibility_rel X R S (amb.A*amb.B*amb.C) s)) (amb.σ.val.2*((free_algebra.basis_free_monoid R X) amb.C) - ((free_algebra.basis_free_monoid R X) amb.A)*amb.τ.val.2) = 0},
{exact (ring_quot.mk_ring_hom (compatibility_rel X R S (amb.A*amb.B*amb.C) s)) (((free_algebra.basis_free_monoid R X) amb.A)*(amb.σ.val.2)*((free_algebra.basis_free_monoid R X) amb.C) - amb.τ.val.2) = 0}
end

lemma compatible_implies_all_resolvable_are_resolvable_rel (s : compatible_semigroup_partial_order X R S) (amb: ambiguity X R S): ambiguity_is_resolvable X R S amb → ambiguity_resolvable_rel X R S amb s.to_semigroup_partial_order := by sorry

---The below relation on S will be pushed to R to give the relations defining the ideal I we take the quotient by.
def defining_pre_rel (S : reduction_system X R) : S.set → S.set → Prop := λ σ τ, σ = τ

--- Now we give maps S → k<X> which allow us to define the relation on k<X> to quotient by
def rs_to_alg_left (S : reduction_system X R) : S.set → (free_algebra R X) := λ σ, (free_algebra.basis_free_monoid R X) σ.val.1

def rs_to_alg_right (S : reduction_system X R) : S.set → (free_algebra R X) := λ σ, σ.val.2

--- We push the relation on S along the above maps to R.
def defining_rel (S : reduction_system X R) : free_algebra R X → free_algebra R X → Prop := relation.map (defining_pre_rel X R S) (rs_to_alg_left X R S) (rs_to_alg_right X R S)

--- This is the quotient k<X>/I, for I the ideal given by S. Need to fix the type here!
def quotient_by_system (S : reduction_system X R) : Type* := ring_quot (defining_rel X R S)

def diamond_lemma_prop_1 (s: compatible_semigroup_partial_order X R S) : Prop :=   ∀ amb: ambiguity X R S, ambiguity_is_resolvable X R S amb 

def diamond_lemma_prop_2 (s: compatible_semigroup_partial_order X R S) : Prop :=  ∀ amb: ambiguity X R S, ambiguity_resolvable_rel X R S amb s.to_semigroup_partial_order   

def diamond_lemma_prop_3 (s: compatible_semigroup_partial_order X R S) : Prop := ∀ x : free_algebra R X, reduction_unique X R S x

def canonical_inclusion (S : reduction_system X R) : irr_monomials X R S → quotient_by_system X R S := by sorry

def diamond_lemma_prop_4 (s: compatible_semigroup_partial_order X R S) : Prop := (
canonical_inclusion X R S : basis (irr_monomials X R S) R quotient_by_system X R S )

