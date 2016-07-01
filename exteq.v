Require Import InfSeqExt.infseq.

(* ------------------------------------------------------------------------- *)
(* Extensional equality on infinite sequences *)
Section sec_exteq.

Variable T: Type. 

CoInductive exteq : infseq T -> infseq T -> Prop :=
  exteq_intro :
    forall x s1 s2, exteq s1 s2 -> exteq (Cons x s1) (Cons x s2).

Lemma exteq_inversion :
  forall (x1:T) s1 x2 s2, 
  exteq (Cons x1 s1) (Cons x2 s2) -> x1 = x2 /\ exteq s1 s2.
Proof.
intros x1 s1 x2 s2 e. 
change (hd (Cons x1 s1) = hd (Cons x2 s2) /\
        exteq (tl (Cons x1 s1)) (tl (Cons x2 s2))).
case e; clear e x1 s1 x2 s2. simpl. intros; split; trivial. 
Qed.

Lemma exteq_refl : forall s, exteq s s. 
Proof.
cofix cf. intros (x, s). constructor. apply cf. 
Qed.

Lemma exteq_sym : forall s1 s2, exteq s1 s2 -> exteq s2 s1.
Proof.
cofix cf. destruct 1. constructor. apply cf. assumption. 
Qed.

Lemma exteq_trans :
   forall s1 s2 s3, exteq s1 s2 -> exteq s2 s3 -> exteq s1 s3.
Proof.
cofix cf.
intros (x1, s1) (x2, s2) (x3, s3) e12 e23. 
case (exteq_inversion _ _ _ _ e12); clear e12; intros e12 ex12. 
case (exteq_inversion _ _ _ _ e23); clear e23; intros e23 ex23. 
rewrite e12; rewrite e23. constructor. apply cf with s2; assumption. 
Qed.

End sec_exteq.

Implicit Arguments exteq [T]. 
Implicit Arguments exteq_inversion [T x1 s1 x2 s2]. 
Implicit Arguments exteq_refl [T]. 
Implicit Arguments exteq_sym [T]. 
Implicit Arguments exteq_trans [T]. 

(* --------------------------------------------------------------------------- *)
(* Extensional equality and temporal logic *)

Section sec_exteq_congruence.

Variable T: Type. 

(* All useful predicates are extensional in the following sense *)
Definition extensional (P: infseq T -> Prop) :=
  forall s1 s2, exteq s1 s2 -> P s1 -> P s2.

Lemma extensional_and_tl :
  forall (P Q: infseq T -> Prop), 
  extensional P -> extensional Q -> extensional (P /\_ Q).
Proof. 
intros P Q eP eQ s1 s2 e. destruct e; simpl. unfold and_tl. intuition.
  apply eP with (Cons x s1); [constructor; assumption | assumption]. 
  apply eQ with (Cons x s1); [constructor; assumption | assumption]. 
Qed.

Lemma extensional_or_tl :
  forall (P Q: infseq T -> Prop),
  extensional P -> extensional Q -> extensional (P \/_ Q).
Proof. 
intros P Q eP eQ s1 s2 e. destruct e; simpl. unfold or_tl. intuition.
  left; apply eP with (Cons x s1); [constructor; assumption | assumption]. 
  right; apply eQ with (Cons x s1); [constructor; assumption | assumption]. 
Qed.

Lemma extensional_impl_tl :
  forall (P Q: infseq T -> Prop),
  extensional P -> extensional Q -> extensional (P ->_ Q).
Proof. 
intros P Q eP eQ s1 s2 e. destruct e; simpl. unfold impl_tl. 
intros PQ1 P2. 
  apply eQ with (Cons x s1); [constructor; assumption | idtac]. 
  apply PQ1. apply eP with (Cons x s2). 
    constructor. apply exteq_sym. assumption. 
    assumption. 
Qed.

Lemma extensional_not_tl :
  forall (P: infseq T -> Prop),
  extensional P -> extensional (~_ P).
Proof.
intros P eP s1 s2 e; destruct e; simpl. unfold not_tl.
intros P1 nP2.
contradict P1.
apply eP with (Cons x s2); trivial.
apply exteq_sym.
apply exteq_intro.
assumption.
Qed.

(* *)

Lemma extensional_now:
  forall (P: T -> Prop), extensional (now P).
Proof. 
intros P s1 s2 e. destruct e; simpl. trivial.
Qed.

Lemma extensional_consecutive:
  forall (P: T -> T -> Prop), extensional (consecutive P).
Proof. 
intros P s1 s2 e. do 2 destruct e; simpl. trivial.
Qed.

Lemma extensional_eventually:
  forall (P: infseq T -> Prop), 
  extensional P -> extensional (eventually P). 
Proof.
intros P eP s1 s2 e ev1. genclear e; genclear s2. 
induction ev1 as [s1 ev1 | x1 s1 ev1 induc_hyp].
  intros s2 e. constructor 1. apply eP with s1; assumption. 
  intros (x2, s2) e. constructor 2. apply induc_hyp. 
    case (exteq_inversion e). trivial.  
Qed.

Lemma extensional_always:
  forall (P: infseq T -> Prop),
  extensional P -> extensional (always P). 
Proof.
intros P eP. cofix cf. 
intros (x1, s1) (x2, s2) e al1. case (always_Cons al1); intros Px1s1 als1. constructor. 
  eapply eP; eassumption. 
  simpl. apply cf with s1; try assumption. case (exteq_inversion e); trivial.
Qed.


Lemma extensional_until:
  forall (P Q: infseq T -> Prop),
  extensional P -> extensional Q -> extensional (until P Q). 
Proof.
intros P Q eP eQ. cofix cf. 
intros (x1, s1) (x2, s2) e un1. case (until_Cons un1). 
  intro Q1. constructor 1. eapply eQ; eassumption.
  intros (Px1s1, uns1). constructor 2.
    eapply eP; eassumption. 
    simpl. apply cf with s1; try assumption. case (exteq_inversion e); trivial.
Qed.

End sec_exteq_congruence.

Implicit Arguments extensional [T].
