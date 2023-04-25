import algebra.free_monoid.basic
import algebra.free_algebra
import algebra.module.submodule.basic
import linear_algebra.free_algebra
import linear_algebra.basis
import init.algebra.order
import data.fin.basic
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
def inc_free_monoid_free_alg : free_monoid X →* free_algebra R X:= free_monoid.lift (free_algebra.ι R)

--Define reduction on basis elements
noncomputable def reduction_on_basis (σ : S.set) (A B : free_monoid X) : free_monoid X → free_algebra R X := 
begin
  intro x,
  by_cases x = A*σ.val.1*B,
  {
    exact (inc_free_monoid_free_alg X R A)*σ.val.2*(inc_free_monoid_free_alg X R B),
  },
  {
    exact (inc_free_monoid_free_alg X R x),
  },
end

noncomputable def reduction (σ : S.set) (A B: free_monoid X) : free_algebra R X →ₗ[R] free_algebra R X := basis.constr (free_algebra.basis_free_monoid R X) R (reduction_on_basis X R S σ A B)

--Set of irreducible polynomials
def irr_set : set (free_algebra R X) := { a : free_algebra R X | ∀ σ : S.set, ∀ A : free_monoid X, ∀ B : free_monoid X, reduction X R S σ A B a = a}

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
def reductions : set (free_algebra R X →ₗ[R] free_algebra R X) := { (reduction X R S triple.1 triple.2.1 triple.2.2) | triple : S.set × free_monoid X ×  free_monoid X }
variable n : ℕ 
variable r : fin n → reductions X R S

def compose (n : ℕ) (f : fin n → reductions X R S): (free_algebra R X →ₗ[R] free_algebra R X) 
| (1, f)     := f 0
| m+1 f   := (f m) ∘ (compose m (f ∘ (fin.succ_embedding m)))

--Partial order
class semigroup_partial_order (α : Type) [semigroup α] extends partial_order α :=
(semigroup_condition : ∀ b b': α, b≤b' → ∀ a c: α, a*b*c ≤ a*b'*c)

-- This takes as argument a semigroup for now, so need to pass <X> as argument

class compatible_semigroup_partial_order (S : reduction_system X R) extends semigroup_partial_order (free_monoid X):=
(compatible : ∀ σ : S.set, ∀ u : free_monoid X, (((free_algebra.basis_free_monoid R X).repr σ.val.2 )u≠0) → u<σ.val.1) 

-- This takes as argument a reduction system S (wich already includes X and R)
def ambiguity_is_resolvable (Amb : inclusion_ambiguity or ): Prop :=
begin
by_cases A.overlap, {
  ∃ f : reductions X R S,  (compose f) (reduction Amb.σ 1 1) Amb.C 
}, {},
end


