Require Import InfSeqExt.infseq.
Require Import Classical.

Section sec_classical.

Variable T : Type.

Lemma weak_until_until_or_always :
  forall (J P : infseq T -> Prop) (s : infseq T),
    weak_until J P s -> until J P s \/ always J s.
Proof.
intros J P s.
case (classic (eventually P s)).
  intros evP wu.
  left.
  induction evP.
    apply U0. assumption.
  apply weak_until_Cons in wu.
  case wu.
    intros PC.
    apply U0. assumption.
  intros [Js wu'].
  apply U_next; trivial.
  apply IHevP.
  assumption.
intros evP wu.
right.
apply not_eventually_always_not in evP.
apply weak_until_always_not_always in wu; trivial.
Qed.

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

Lemma not_continously_inf_often_not :
  forall (P : infseq T -> Prop) (s : infseq T),
  ~ continuously P s -> inf_often (~_ P) s.
Proof.
intros P.
cofix c.
intros [x s] cnyP.
apply Always.
  unfold continuously in cnyP.
  apply not_eventually_always_not in cnyP.
  apply always_now in cnyP.
  unfold not_tl in cnyP.
  apply not_always_eventually_not in cnyP.
  assumption.
apply c.
intros cnynP.
contradict cnyP.
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

Arguments weak_until_until_or_always [T J P s] _.
Arguments not_eventually_not_always [T P s] _.
Arguments not_always_eventually_not [T P s] _.
Arguments not_inf_often_continuously_not [T P s] _.
Arguments not_continously_inf_often_not [T P s] _.
Arguments not_tl_and_tl_or_tl [T P Q s] _.
