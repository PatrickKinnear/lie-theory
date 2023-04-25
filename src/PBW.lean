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

def reduction (σ : S.set) : free_algebra R X → free_algebra R X := sorry

def irr_set : set (free_algebra R X) := { a : free_algebra R X | ∀ σ : S.set, reduction X R S σ a ≠ a}

def irr : submodule R (free_algebra R X) :=
⟨irr_set X R S, by sorry, by sorry, by sorry⟩

#check irr X R S