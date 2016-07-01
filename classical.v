Require Import InfSeqExt.infseq.
Require Import Classical.

Section sec_classical.

Variable T : Type.

Lemma not_eventually_not_always : 
  forall (P : infseq T -> Prop) (s : infseq T),
  ~ eventually (~_ P) s -> always P s.
Proof.
intros P.
cofix c.
intro s.
destruct s as [e s].
intros evnP.
apply Always.
  case (classic (P (Cons e s))); trivial.
  intros orP.
  apply (E0 _ (~_ P)) in orP.
  contradict evnP.
  assumption.
apply c.
simpl.
intros evP.
contradict evnP.
apply E_next.
assumption.
Qed.

Lemma not_always_eventually_not : 
  forall (P : infseq T -> Prop) (s : infseq T),
  ~ always P s -> eventually (~_ P) s.
Proof.
intros P s alP.
case (classic ((eventually (~_ P)) s)); trivial.
intros evP.
apply not_eventually_not_always in evP.
contradict alP.
assumption.
Qed.

Lemma not_inf_often_continuously_not : 
  forall (P : infseq T -> Prop) (s : infseq T),
  ~ inf_often P s -> continuously (~_ P) s.
Proof.
intros P s ioP.
apply not_always_eventually_not in ioP.
induction ioP.
  apply not_eventually_always_not in H.
  apply E0.
  assumption.
apply E_next.
assumption.
Qed.

Lemma not_tl_and_tl_or_tl :
  forall (P Q : infseq T -> Prop) (s : infseq T),
  (~_ (P /\_ Q)) s -> ((~_ P) \/_ (~_ Q)) s.
Proof.
intros P Q s; unfold not_tl, and_tl, or_tl.
apply not_and_or.
Qed.

End sec_classical.

Implicit Arguments not_eventually_not_always [T P s].
Implicit Arguments not_always_eventually_not [T P s].
Implicit Arguments not_inf_often_continuously_not [T P s].
Implicit Arguments not_tl_and_tl_or_tl [T P Q s].
