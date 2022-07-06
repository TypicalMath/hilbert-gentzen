From Coq Require Import Sets.Ensembles.

Inductive Formula : Type :=
    | atom : nat -> Formula
    | disj : Formula -> Formula -> Formula
    | conj : Formula -> Formula -> Formula
    | imp : Formula -> Formula -> Formula
    | neg : Formula -> Formula
    | bot : Formula. 


Inductive ND : Ensemble Formula -> Formula -> Prop :=
    | ax (C:Ensemble Formula) (f: Formula) (H:In Formula C  f) : ND C f
    | conjE1 (C:Ensemble Formula) (f1 f2: Formula) (H:ND C (conj f1 f2)) : ND C f1
    | conjE2 (C:Ensemble Formula) (f1 f2: Formula) (H:ND C (conj f1 f2)) : ND C f2
    | conjI (C:Ensemble Formula) (f1 f2: Formula) (H1:ND C f1) (H2:ND C f2) : ND C (conj f1 f2)
    | disjE (C:Ensemble Formula) (f1 f2 f:Formula) (H1:ND (Union Formula C (Singleton Formula f1)) f) 
        (H2:ND (Union Formula C (Singleton Formula f2)) f) (H3:ND C (disj f1 f2) ): ND C f 
    | disjI1 (C:Ensemble Formula) (f1 f2:Formula) (H:ND C f1):ND C (disj f1 f2)
    | disjI2 (C:Ensemble Formula) (f1 f2:Formula) (H:ND C f2):ND C (disj f1 f2)
    | impE (C:Ensemble Formula) (f1 f2:Formula) (H1:ND C (imp f1 f2)) (H2:ND C (f1)): ND C f2
    | impI (C:Ensemble Formula) (f1 f2:Formula) (H:ND (Union Formula C (Singleton Formula f1)) f2): ND C (imp f1 f2)
    | botE (C:Ensemble Formula) (f:Formula) (H:ND C bot):ND C f.




