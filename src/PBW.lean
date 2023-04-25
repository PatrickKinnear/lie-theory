import algebra.free_monoid.basic
import algebra.free_algebra
import algebra.module.submodule.basic
open set


--We need to prove the Diamond Lemma!

variables (X : Type) 
variables (R: Type) [comm_ring R]

structure reduction_system :=
(set : set (free_monoid X × free_algebra R X))
(nondegeneracy: ∀ p : set, free_monoid.lift (free_algebra.ι R) p.val.1 ≠ p.val.2 )

---fix reduction_system, notion of reduction, and define irreducible.

variable (S : reduction_system X R)

def inc_free_monoid_free_alg : free_monoid X →* free_algebra R X:= free_monoid.lift (free_algebra.ι R)

def reduction (σ : S.set) (A B: free_monoid X) : free_algebra R X → free_algebra R X := sorry

noncomputable def reduction_fake (σ : S.set) (A : free_monoid X) (B : free_monoid X) : free_monoid X → free_algebra R X := 
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





noncomputable def reduction_step1 : free_monoid X → free_monoid X → free_monoid X × free_algebra R X →  free_monoid X → free_algebra R X :=
begin
  intros A B σ x,
  by_cases x= A*σ.1*B,
  {
    exact (inc_free_monoid_free_alg X R A)*σ.2*(inc_free_monoid_free_alg X R B), 
  },
  {
    exact (inc_free_monoid_free_alg X R x),
  },
end

def reduction : free_monoid X → free_monoid X → free_monoid X × free_algebra R X →  free_algebra R X →  free_algebra R X :=
begin
  intros A B σ,
  
end


def irr_set : set (free_algebra R X) := { a : free_algebra R X | ∀ σ : S.set, ∀ A : free_monoid X, ∀ B : free_monoid X, reduction X R S σ A B a ≠ a}

def irr : submodule R (free_algebra R X) :=
⟨irr_set X R S, by sorry, by sorry, by sorry⟩

#check irr X R S
