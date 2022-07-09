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

    Example A1ND: forall(A B : Formula), ND (Empty_set Formula) ((imp A (imp B A))).
    Proof. intros A B. apply impI. apply impI. apply ax. apply  Union_introl.
        apply  Union_intror. apply  In_singleton. Qed.    

Inductive Hilb : Ensemble Formula -> Formula -> Prop :=
    | Hax (C:Ensemble Formula) (f: Formula) (H:In Formula C  f) : Hilb C f
    | A1 (C:Ensemble Formula) (f1 f2: Formula)  : Hilb C (imp f1 (imp f2 f1))
    | A2 (C:Ensemble Formula) (f1 f2 f3: Formula)  : Hilb C (imp (imp f1 (imp f2 f3)) (imp (imp f1 f2) (imp f1 f3)))
    | A3 (C:Ensemble Formula) (f1 f2: Formula)  : Hilb C (imp (conj f1 f2) f1)
    | A4 (C:Ensemble Formula) (f1 f2: Formula)  : Hilb C (imp (conj f1 f2) f2)
    | A5 (C:Ensemble Formula) (f1 f2: Formula)  : Hilb C (imp f1 (imp f2 (conj f1 f2)))
    | A6 (C:Ensemble Formula) (f1 f2: Formula)  : Hilb C (imp f1 (disj f1 f2) )
    | A7 (C:Ensemble Formula) (f1 f2: Formula)  : Hilb C (imp f2 (disj f1 f2) )
    | A8 (C:Ensemble Formula) (f1 f2 f3: Formula)  : Hilb C (imp (imp f1 f3) (imp (imp f2 f3) (imp (disj f1 f2) f3)) )
    | A9 (C:Ensemble Formula) (f1: Formula)  : Hilb C (imp bot f1 )
    | MP (C:Ensemble Formula) (f1 f2:Formula) (H1:Hilb C (imp f1 f2)) (H2:Hilb C (f1)): Hilb C f2
    | Con (C: Ensemble Formula) (f: Formula) (H:In Formula C f) : Hilb C f. 
    
Theorem Hilbert_Natural_Deduction_Equivalence: forall (C:Ensemble Formula) (f : Formula), 
    (Hilb C f) <-> (ND C f).
    Proof. intros C. split.
    +intros H. induction H.
        -apply ax. apply H.
        -apply impI. apply impI. apply ax. apply Union_introl. apply  Union_intror. apply  In_singleton.
        -apply impI. apply impI. apply impI. apply impE with (f1:=f2) (f2:=f3). 
            ++apply impE with (f1:= f1).
             --apply ax. apply Union_introl. apply Union_introl. apply Union_intror. apply  In_singleton.
             --apply ax. apply Union_intror. apply In_singleton.
            ++apply impE with (f1:=f1).
             --apply ax. apply Union_introl. apply Union_intror. apply In_singleton.
             --apply ax. apply Union_intror. apply In_singleton.
        -apply impI. apply conjE1 with (f2:=f2) . apply ax. apply Union_intror. apply In_singleton.
        -apply impI. apply conjE2 with (f1:=f1) . apply ax. apply Union_intror. apply In_singleton.
        -apply impI. apply impI. apply conjI.
            ++apply ax. apply Union_introl. apply Union_intror. apply In_singleton.
            ++apply ax. apply Union_intror. apply In_singleton.
        -apply impI. apply disjI1 with (f1:=f1). apply ax. apply Union_intror. apply In_singleton.
        -apply impI. apply disjI2 with (f2:=f2). apply ax. apply Union_intror. apply In_singleton.
        -apply impI. apply impI. apply impI. apply disjE with (f1:=f1) (f2:=f2).
            ++apply impE with (f1:=f1).
                --apply ax. apply Union_introl. apply Union_introl. apply Union_introl. apply Union_intror. apply In_singleton.
                --apply ax. apply Union_intror. apply In_singleton.
            ++apply impE with (f1:=f2).
                --apply ax. apply Union_introl. apply Union_introl. apply Union_intror. apply In_singleton.
                --apply ax. apply Union_intror. apply In_singleton.
            ++apply ax. apply Union_intror. apply In_singleton.
        -apply impI. apply botE. apply ax. apply Union_intror. apply In_singleton.
        (*Whhhaaaaaatttt???!!!!*)
        -apply impE with (f1:=f1).
            ++apply IHHilb1.
            ++apply IHHilb2.
        -apply ax. apply H.
    +intros H. induction H.
        -apply Hax. apply H.
        -apply Hax in IHND.



