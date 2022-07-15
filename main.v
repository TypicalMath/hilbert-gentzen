From Coq Require Import Sets.Ensembles.

Inductive Formula : Type :=
    | atom : nat -> Formula
    | disj : Formula -> Formula -> Formula
    | conj : Formula -> Formula -> Formula
    | imp : Formula -> Formula -> Formula
    | bot : Formula. 

Notation "^ n" := (atom n) (at level 1).
Notation "x ^| y" := (disj x y) (at level 11, left associativity).
Notation "x ^& y" := (conj x y) (at level 11, left associativity).
Notation "x ^>  y" := (imp x y) (at level 12, right associativity).
Notation "^F" := bot (at level 0).
Definition neg (A : Formula) : Formula := A ^> ^F.
Notation "^~ x" := (neg x) (at level 10).
Definition top := ^~^F.
Notation "^T" := top (at level 0).
Definition iff x y := (x ^> y) ^& (y ^> x).
Notation "x <^> y" := (iff x y) (at level 13, right associativity).

Reserved Notation "C |-n f" (at level 20).

Inductive ND : Ensemble Formula -> Formula -> Prop :=
    | ax (C : Ensemble Formula) (f : Formula) (H : In Formula C  f) : C |-n f
    | conjE1 (C : Ensemble Formula) (f1 f2 : Formula) (H : C |-n (f1 ^& f2)) : C |-n f1
    | conjE2 (C : Ensemble Formula) (f1 f2 : Formula) (H : C |-n (f1 ^& f2)) : C |-n f2
    | conjI (C : Ensemble Formula) (f1 f2 : Formula) (H1 : C |-n f1) (H2 : C |-n f2) : C |-n (f1 ^& f2)
    | disjE (C : Ensemble Formula) (f1 f2 f : Formula) (H1 : (Union Formula C (Singleton Formula f1)) |-n f) 
        (H2 : (Union Formula C (Singleton Formula f2)) |-n f) (H3 : C |-n (f1 ^| f2) ) : C |-n f 
    | disjI1 (C : Ensemble Formula) (f1 f2 : Formula) (H : C |-n f1) : C |-n (f1 ^| f2)
    | disjI2 (C : Ensemble Formula) (f1 f2 : Formula) (H : C |-n f2) : C |-n (f1 ^| f2)
    | impE (C : Ensemble Formula) (f1 f2 : Formula) (H1 : C |-n (f1 ^> f2)) (H2 : C |-n f1) : C |-n f2
    | impI (C : Ensemble Formula) (f1 f2 : Formula) (H : (Union Formula C (Singleton Formula f1)) |-n f2) : C |-n (f1 ^> f2)
    | botE (C : Ensemble Formula) (f : Formula) (H : C |-n ^F): C |-n f
    where "x |-n y" := (ND x y).