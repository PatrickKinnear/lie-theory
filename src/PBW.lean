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
variables (R: Type) [comm_ring R]

structure reduction_system :=
(set : set (free_monoid X × free_algebra R X))
(nondegeneracy: ∀ p : set, free_monoid.lift (free_algebra.ι R) p.val.1 ≠ p.val.2 )

---fix reduction_system, notion of reduction, and define irreducible.

variable (S : reduction_system X R)

--Inclusion of free monoid into free algebra
-- def inc_free_monoid_free_alg : free_monoid X →* free_algebra R X
-- := free_monoid.lift (free_algebra.ι R)


variable q : free_algebra R X

--Define reduction on basis elements
def reduction_on_basis (σ : S.set) (A B : free_monoid X) : 
free_monoid X → free_algebra R X := 
λ x, if (x=A*σ.val.1*B) then 
(free_algebra.basis_free_monoid R X A)*σ.val.2*((free_algebra.basis_free_monoid R X) B) 
else ((free_algebra.basis_free_monoid R X) x)

--This is just short for free_algebra.basis_free_monoid R X


def reduction (σ : S.set) (A B: free_monoid X) : free_algebra R X →ₗ[R] free_algebra R X 
:= basis.constr (free_algebra.basis_free_monoid R X) R (reduction_on_basis X R S σ A B)

--Set of irreducible polynomials
def irr_set : set (free_algebra R X) := 
{ a : free_algebra R X | ∀ σ : S.set, ∀ A : free_monoid X, ∀ B : 
free_monoid X, reduction X R S σ A B a = a}

def irr : submodule R (free_algebra R X) :=
⟨irr_set X R S, by sorry, by sorry, by sorry⟩

--Ambiguities

structure overlap_ambiguity :=
(σ τ : S.set)
(A B C : free_monoid X)
(overlap : σ.val.1 = A*B ∧ τ.val.1 = B*C)

structure inclusion_ambiguity :=
(σ τ : S.set)
(A B : free_monoid X)
(inclusion : τ.val.1 = A*σ.val.1*B)

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
{ m : free_monoid X | (free_algebra.basis_free_monoid R X).repr a m ≠ 0}


-- This takes as argument a semigroup for now, so need to pass <X> as argument
class compatible_semigroup_partial_order (S : reduction_system X R) 
extends semigroup_partial_order (free_monoid X):=
(compatible : ∀ σ : S.set, ∀ u ∈ basis_terms X R (σ.val.2), u<σ.val.1)

-- This takes as argument a reduction system S (which already includes X and R)
def ambiguity_is_resolvable (Amb : inclusion_ambiguity or ): Prop :=
begin
by_cases A.overlap, {
  ∃ f : reductions X R S,  (compose f) (reduction Amb.σ 1 1) Amb.C 
}, {},
end

lemma obvious (σ : S.set) (A B x: free_monoid X)(h: ¬ x=A*σ.val.1*B):
 ((free_algebra.basis_free_monoid R X) x)=(reduction_on_basis X R S σ A B) (x):=
begin
  unfold reduction_on_basis,
  split_ifs,
  refl,
end


lemma observation (S : reduction_system X R)[compatible_semigroup_partial_order X R S]
(A B : free_monoid X)(σ : S.set): ∀ a : free_monoid X, ∀ u ∈ (basis_terms X R)( (reduction_on_basis X R S σ A B) a),  ¬ u > a:=
begin
  intros a u hu,
  by_cases a = A*σ.val.1*B,
  {
    sorry,
  },
  {
    have step₂ : basis_terms X R ((reduction_on_basis X R S σ A B) a) = {a},
    {
      sorry,
    },
    have step₃ : u = a,
    {
      rw step₂ at hu,
      exact hu,
    },
    rw step₃,
    exact lt_irrefl a,
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

-- This quotient is used to talk of when an overlap is resolvable rel a partial order (in place of using an ideal which is not defined for noncommutative rings yet)
def rel_quotient (A : free_monoid X) (s : semigroup_partial_order (free_monoid X)): Type* := ring_quot (compatibility_rel X R S A s)

def overlap_resolvable_rel (amb : overlap_ambiguity X R S) ( _ : semigroup_partial_order (free_monoid X)) : Prop := ,