import algebra.free_monoid.basic
import algebra.free_algebra
open set


--We need to prove the Diamond Lemma!

variables (X : Type) 
variables (R: Type) [comm_ring R]

structure reduction_system :=
(σ : set (free_monoid X × free_algebra R X))
(nondegeneracy: ∀ p : σ, free_monoid.lift (free_algebra.ι R) p.val.1 ≠ p.val.2 )



