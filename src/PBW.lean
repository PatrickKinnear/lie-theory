import algebra.free_monoid.basic
import algebra.free_algebra


--We need to prove the Diamond Lemma!

variables (X : Type) 
variables (R: Type) [comm_ring R]


def reduction_system : Type := set (free_monoid X × free_algebra R X)


