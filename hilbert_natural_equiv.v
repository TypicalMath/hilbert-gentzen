From Coq Require Import Sets.Ensembles.


Declare Scope prop_logic.
Open Scope prop_logic.

Definition Vars := nat.

Inductive Form : Set :=
    | Var     : Vars -> Form
    | Conj    : Form -> Form -> Form
    | Disj    : Form -> Form -> Form
    | Implies : Form -> Form -> Form
    | Bot     : Form.

Definition Forms := Ensemble Form.

Notation "_|" := Bot (at level 0) : prop_logic.
Notation "^ p" := (Var p) (at level 1) : prop_logic.
Notation "A ^& B" := (Conj A B) (at level 3, left associativity) : prop_logic.
Notation "A ^| B" := (Disj A B) (at level 3, left associativity) : prop_logic.
Notation "A --> B" := (Implies A B) (at level 4, right associativity) : prop_logic.
Definition neg (A : Form) : Form := A --> _|.
Notation "^~ A" := (neg A) (at level 2) : prop_logic.
Definition top : Form := ^~ _|.
Notation "^T" := (top) (at level 0) : prop_logic.
Definition iff (A B : Form) : Form := (A --> B) ^& (B --> A).
Notation "A <--> B" := (iff A B) (at level 5, right associativity) : prop_logic.

Reserved Notation "C |-N- A" (at level 10).

Inductive ND : Forms -> Form -> Prop :=
  | IConj (C : Forms) (A B : Form) (H1: C |-N- A) (H2: C |-N- B)
      : C |-N- (A ^& B)
  | IDisjl (C : Forms) (A B : Form) (H: C |-N- A)
      : C |-N- (A ^| B)
  | IDisjr (C : Forms) (A B : Form) (H: C |-N- B)
      : C |-N- (A ^| B)
  | IImpl (C : Forms) (A B : Form) (H: (Union Form C (Singleton Form A)) |-N- B)
      : C |-N- (A --> B)
  | EConjl (C : Forms) (A B : Form) (H: C |-N- A ^& B)
      : C |-N- A
  | EConjr (C : Forms) (A B : Form) (H: C |-N- A ^& B)
      : C |-N- B
  | EDisj (C : Forms) (A B X : Form) (H: C |-N- A ^| B)
          (H1: (Union Form C (Singleton Form A)) |-N- X)
          (H2: (Union Form C (Singleton Form B)) |-N- X)
      : C |-N- X
  | EImpl (C : Forms) (A B : Form) (H1: C |-N- (A --> B)) (H2: C |-N- A)
      : C |-N- B
  | Ax (C : Forms) (A : Form) (H: In Form C A)
      : C |-N- A
  | EBot (C : Forms) (A : Form) (H: C |-N- _|)
      : C |-N- A
  where "C |-N- A" := (ND C A).

Definition A1_form (A B : Form) : Form :=
  A --> B --> A.
Definition A2_form (A B C : Form) : Form :=
  (A --> B --> C) --> ((A --> B) --> (A --> C)).
Definition A3_form (A B : Form) : Form :=
  A ^& B --> A.
Definition A4_form (A B : Form) : Form :=
  A ^& B --> B.
Definition A5_form (A B : Form) : Form :=
  A --> B --> (A ^& B).
Definition A6_form (A B : Form) : Form :=
  A --> A ^| B.
Definition A7_form (A B : Form) : Form :=
  B --> A ^| B.
Definition A8_form (A B C : Form) : Form :=
  (A --> C) --> (B --> C) --> (A ^| B --> C).
Definition A9_form (A : Form) : Form :=
  _| --> A.

Reserved Notation "C |-H- A" (at level 10).

Inductive HD : Forms -> Form -> Prop :=
  | A1 (C : Forms) (A B : Form)
      : C |-H- (A1_form A B)
  | A2 (C : Forms) (A B X : Form)
      : C |-H- (A2_form A B X)
  | A3 (C : Forms) (A B : Form)
      : C |-H- (A3_form A B)
  | A4 (C : Forms) (A B : Form)
      : C |-H- (A4_form A B)
  | A5 (C : Forms) (A B : Form)
      : C |-H- (A5_form A B)
  | A6 (C : Forms) (A B : Form)
      : C |-H- (A6_form A B)
  | A7 (C : Forms) (A B : Form)
      : C |-H- (A7_form A B)
  | A8 (C : Forms) (A B X : Form)
      : C |-H- (A8_form A B X)
  | A9 (C : Forms) (A : Form)
      : C |-H- (A9_form A)
  | HAx (C : Forms) (A : Form) (H: In Form C A)
      : C |-H- A
  | MP (C : Forms) (A B : Form) (H1: C |-H- A --> B) (H2: C |-H- A)
      : C |-H- B
  where "C |-H- A" := (HD C A).

Notation "|-N- A" := (Empty_set Form |-N- A) (at level 10).
Notation "|-H- A" := (Empty_set Form |-H- A) (at level 10).

Lemma A1_in_ND : forall A B C',
  C' |-N- (A1_form A B).
Proof.
  intros. unfold A1_form. repeat apply IImpl. apply Ax.
  apply Union_introl. apply Union_intror. constructor.
Qed.

Lemma A2_in_ND : forall A B C C',
  C' |-N- (A2_form A B C).
Proof.
  intros. unfold A2_form. repeat apply IImpl.
  apply EImpl with B.
  - apply EImpl with A; apply Ax.
    + apply Union_introl. apply Union_introl.
      apply Union_intror. constructor.
    + apply Union_intror. constructor.
  - apply EImpl with A; apply Ax.
    + apply Union_introl. apply Union_intror. constructor.
    + apply Union_intror. constructor.
Qed.

Lemma A3_in_ND : forall A B C',
  C' |-N- (A3_form A B).
Proof.
  intros. unfold A3_form. apply IImpl.
  assert (H: (Union Form C' (Singleton Form A ^& B))
            |-N- A ^& B).
  { apply Ax. apply Union_intror. constructor. }
  apply EConjl in H. assumption.
Qed.

Lemma A4_in_ND : forall A B C',
  C' |-N- (A4_form A B).
Proof.
  intros. unfold A4_form. apply IImpl.
  assert (H: (Union Form C' (Singleton Form A ^& B))
            |-N- A ^& B).
  { apply Ax. apply Union_intror. constructor. }
  apply EConjr in H. assumption.
Qed.

Lemma A5_in_ND : forall A B C',
  C' |-N- (A5_form A B).
Proof.
  intros. unfold A5_form. repeat apply IImpl.
  apply IConj; constructor.
  - apply Union_introl. apply Union_intror. constructor.
  - apply Union_intror. constructor.
Qed.

Lemma A6_in_ND : forall A B C',
  C' |-N- (A6_form A B).
Proof.
  intros. unfold A6_form. apply IImpl. apply IDisjl.
  constructor. apply Union_intror. constructor.
Qed.

Lemma A7_in_ND : forall A B C',
  C' |-N- (A7_form A B).
Proof.
  intros. unfold A6_form. apply IImpl. apply IDisjr.
  constructor. apply Union_intror. constructor.
Qed.

Lemma A8_in_ND : forall A B C C',
  C' |-N- (A8_form A B C).
Proof.
  intros. unfold A8_form. repeat apply IImpl.
  apply EDisj with A B.
  - apply Ax. apply Union_intror. constructor.
  - apply EImpl with A; apply Ax.
    + repeat (try (apply Union_intror; constructor); apply Union_introl).
    + apply Union_intror. constructor.
  - apply EImpl with B; apply Ax.
    + repeat (try (apply Union_intror; constructor); apply Union_introl).
    + apply Union_intror. constructor.
Qed.

Lemma A9_in_ND : forall A C',
  C' |-N- (A9_form A).
Proof.
  intros. unfold A9_form. apply IImpl. apply EBot.
  constructor. apply Union_intror. constructor.
Qed.

Theorem HD_implies_ND : forall A C,
  C |-H- A -> C |-N- A.
Proof.
  intros. induction H;
    try (constructor; assumption);
    try (apply EImpl with A; assumption).
  - apply A1_in_ND.
  - apply A2_in_ND.
  - apply A3_in_ND.
  - apply A4_in_ND.
  - apply A5_in_ND.
  - apply A6_in_ND.
  - apply A7_in_ND.
  - apply A8_in_ND.
  - apply A9_in_ND.
Qed.

Lemma A_implies_A_HD : forall A C,
  C |-H- A --> A.
Proof.
  intros. assert (H1: C |-H- A --> (A --> A) --> A).
  { constructor. }
  assert (H2: C |-H- (A --> ((A --> A) --> A)) --> 
                      ((A --> (A --> A)) --> (A --> A))).
  { constructor. }
  assert (H3: C |-H- A --> A --> A).
  { constructor. }
  assert (H4: C |-H- (A --> (A --> A)) --> A --> A).
  { apply MP with (A --> ((A --> A) --> A)). assumption. assumption. }
  apply MP with (A --> A --> A). assumption. assumption.
Qed.

Lemma union_in_context : forall A C C',
  In Form (Union Form C C') A <-> (In Form C A) \/ (In Form C' A).
Proof.
  split; intros.
  - inversion H.
    + left; assumption.
    + right; assumption.
  - destruct H as [H | H].
    + apply Union_introl; assumption.
    + apply Union_intror; assumption.
Qed.

Lemma weakening : forall A B C,
  C |-H- B -> C |-H- A --> B.
Proof.
  intros. apply MP with B; try assumption; try constructor.
Qed.

Lemma deduction_remove_context : forall A B C,
  Union Form C (Singleton Form A) |-H- B -> C |-H- A --> B.
Proof.
  intros. remember (Union Form C (Singleton Form A)) as C'. induction H.
  - apply weakening; constructor.
  - apply weakening; constructor.
  - apply weakening; constructor.
  - apply weakening; constructor.
  - apply weakening; constructor.
  - apply weakening; constructor.
  - apply weakening; constructor.
  - apply weakening; constructor.
  - apply weakening; constructor.
  - subst. apply union_in_context in H. destruct H.
     + apply weakening. constructor; assumption.
     + inversion H; subst. apply A_implies_A_HD.
  - apply MP with A --> A0.
    + apply MP with A --> A0 --> B; try apply A2.
      apply IHHD1. assumption.
    + apply IHHD2. assumption.
Qed.

Lemma reasoning : forall A B C,
  C |-H- A --> B -> Union Form C (Singleton Form A) |-H- A --> B.
Proof. Admitted.

Lemma deduction_add_context : forall A B C,
  C |-H- A --> B -> Union Form C (Singleton Form A) |-H- B.
Proof.
  intros. apply MP with A.
  - apply reasoning. assumption.
  - constructor. apply Union_intror. constructor.
Qed.

Theorem deduction : forall A B C,
  C |-H- A --> B <-> Union Form C (Singleton Form A) |-H- B.
Proof.
  split; intros.
  - apply deduction_add_context. assumption.
  - apply deduction_remove_context. assumption.
Qed.

Theorem ND_implies_HD : forall A C,
  C |-N- A -> C |-H- A.
Proof.
  intros. induction H.
  - apply MP with B. apply MP with A. constructor.
    assumption. assumption.
  - apply MP with A. constructor. assumption.
  - apply MP with B. constructor. assumption.
  - apply deduction. assumption.
  - apply MP with A ^& B. constructor. assumption.
  - apply MP with A ^& B. constructor. assumption.
  - apply MP with A ^| B. apply MP with B --> X.
    apply MP with A --> X. constructor.
    apply deduction. assumption.
    apply deduction. assumption. assumption.
  - apply MP with A. assumption. assumption.
  - apply HAx. assumption.
  - apply MP with _|. constructor. assumption.
Qed.

Theorem ND_equiv_HD : forall A,
  |-N- A <-> |-H- A.
Proof.
  intros A. split. apply ND_implies_HD. apply HD_implies_ND.
Qed.












