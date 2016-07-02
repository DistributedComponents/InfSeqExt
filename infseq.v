(* ------------------------------------------------------------------------- *)
(* General tactics *)

Ltac genclear H := generalize H; clear H.

Ltac clearall :=
   repeat
        match goal with [H : _ |- _ ] => clear H end
     || match goal with [H : _ |- _ ] => genclear H end. 

(* ------------------------------------------------------------------------- *)
(* Infinite traces *)

Section sec_infseq.

Variable T: Type. 

CoInductive infseq : Type := Cons : T -> infseq -> infseq.

Definition hd (s:infseq) : T := match s with Cons x _ => x end.

Definition tl (s:infseq) : infseq := match s with Cons _ s => s end.

Lemma recons : forall s, Cons (hd s) (tl s) = s.
intros s. 
(* Trick : simpl doesn't progress, you have to eat s first *)
case s.  simpl. reflexivity.
Qed.

End sec_infseq.

Implicit Arguments Cons [T].
Implicit Arguments hd [T].
Implicit Arguments tl [T].
Implicit Arguments recons [T].

(* --------------------------------------------------------------------------- *)
(* Temporal logic operations *)

Section sec_modal_op_defn.

Variable T : Type.

Definition now (P: T->Prop) (s: infseq T) : Prop :=
  match s with Cons x s => P x end.

Definition next (P: infseq T -> Prop) (s: infseq T) : Prop :=
  match s with Cons x s => P s end.

Definition consecutive  (R: T -> T -> Prop) (s: infseq T) : Prop :=
  match s with Cons x1 (Cons x2 s) => R x1 x2 end. 

CoInductive always1 (P: T->Prop) : infseq T -> Prop :=
  | Always1 : forall x s, P x -> always1 P s -> always1 P (Cons x s).

CoInductive always (P: infseq T->Prop) : infseq T -> Prop :=
  | Always : forall s, P s -> always P (tl s) -> always P s.

CoInductive until (J P: infseq T->Prop) : infseq T -> Prop :=
  | Until0 : forall s, P s -> until J P s
  | Until_tl : forall s, J s -> until J P (tl s) -> until J P s.

Inductive eventually (P: infseq T->Prop) : infseq T -> Prop :=
  | E0 : forall s, P s -> eventually P s
  | E_next : forall x s, eventually P s -> eventually P (Cons x s). 

Definition inf_often (P: infseq T->Prop) (s: infseq T) : Prop :=
  always (eventually P) s.

Definition continuously (P: infseq T->Prop) (s: infseq T) : Prop :=  
  eventually (always P) s.

(* temporal logic connectors *)
Definition impl_tl (P Q: infseq T -> Prop) : infseq T -> Prop :=
  fun s => P s -> Q s. 
Definition and_tl (P Q: infseq T -> Prop) : infseq T -> Prop :=
  fun s => P s /\ Q s. 
Definition or_tl (P Q: infseq T -> Prop) : infseq T -> Prop :=
  fun s => P s \/ Q s. 
Definition not_tl (P : infseq T -> Prop) : infseq T -> Prop := 
  fun s => ~ P s.

End sec_modal_op_defn.

Implicit Arguments now [T].
Implicit Arguments next [T].
Implicit Arguments consecutive [T].
Implicit Arguments always [T].
Implicit Arguments always1 [T].
Implicit Arguments eventually [T].
Implicit Arguments until [T].
Implicit Arguments inf_often [T].
Implicit Arguments continuously [T].

Implicit Arguments impl_tl [T].
Implicit Arguments and_tl [T].
Implicit Arguments or_tl [T].
Implicit Arguments not_tl [T].

Notation "A ->_ B" := (impl_tl A B) (right associativity, at level 90).
Notation "A /\_ B" := (and_tl A B) (right associativity, at level 80).
Notation "A \/_ B" := (or_tl A B) (right associativity, at level 85).
Notation "~_ A" := (not_tl A) (right associativity, at level 90).

Section sec_modal_op_lemmas.

Variable T : Type.

(* always facts *)

Lemma always_Cons :
  forall (x: T) (s: infseq T) P,
  always P (Cons x s) -> P (Cons x s) /\ always P s.
Proof.
intros x s P al. change (P (Cons x s) /\ always P (tl (Cons x s))). 
destruct al. split; assumption.
Qed.

Lemma always_now :
  forall (x: T) (s: infseq T) P, always P (Cons x s) -> P (Cons x s).
Proof.
intros x s P al. case (always_Cons x s P al); trivial.
Qed.

Lemma always_invar :
  forall (x: T) (s: infseq T) P, always P (Cons x s) -> always P s.
Proof.
intros x s P al. case (always_Cons x s P al); trivial.
Qed.

Lemma always_tl :
  forall (s: infseq T) P, always P s -> always P (tl s).
Proof.
intros (x, s). simpl. apply always_invar. 
Qed.

Lemma always_and_tl :
  forall (P Q : infseq T -> Prop),
    forall s, always P s -> always Q s -> always (P /\_ Q) s.
Proof.
intros P Q.
cofix c.
intros s alP alQ.
destruct alP.
destruct alQ.
apply Always.
  split; assumption.
apply c; assumption.
Qed.

Lemma always_always1 :
   forall P (s: infseq T), always (now P) s <-> always1 P s.
Proof.
intros P s. split; genclear s.
  cofix alwn.
  intros s a; case a; clear a s. intros (x, s); simpl. constructor.
    assumption.
    apply alwn; assumption.

  cofix alwn. destruct 1. constructor; simpl.
    assumption.
    apply alwn; assumption.
Qed.

Lemma always_inf_often :
   forall (P: infseq T -> Prop) (s : infseq T), always P s -> inf_often P s.
Proof.
intros P. cofix f. intros s a. destruct a. constructor.
   constructor 1. assumption.
   apply f. assumption.
Qed.

Lemma always_continuously :
   forall (P: infseq T -> Prop) (s : infseq T), always P s -> continuously P s.
Proof.
intros P s alP.
apply E0.
assumption.
Qed.

(* until and eventually facts *)

Lemma until_Cons :
  forall (x: T) (s: infseq T) J P,
  until J P (Cons x s) -> P (Cons x s) \/ (J (Cons x s) /\ until J P s).
Proof.
intros x s J P un. 
change (P (Cons x s) \/ (J (Cons x s) /\ until J P (tl (Cons x s)))).
destruct un; intuition.
Qed.

Lemma eventually_Cons :
  forall (x: T) (s: infseq T) P,
  eventually P (Cons x s) -> P (Cons x s) \/ eventually P s.
Proof.
intros x s P al. change (P (Cons x s) \/ eventually P (tl (Cons x s))). case al; auto.
Qed.

Lemma eventually_next : 
  forall (s: infseq T) P, eventually (next P) s -> eventually P s. 
Proof.
intros e P ev. induction ev as [(x, s) Ps | x s ev induc_hyp]. 
  constructor 2; constructor 1; exact Ps. 
  constructor 2. apply induc_hyp.
Qed.

Lemma eventually_always_cumul :
  forall (s: infseq T) P Q,
  eventually P s -> always Q s -> eventually (P /\_ always Q) s.
Proof.
induction 1 as [s Ps | x s evPs induc_hyp]. 
  intro al. constructor 1. split; assumption.
  intro al. constructor 2. apply induc_hyp. apply (always_invar _ _ _ al). 
Qed.

Lemma eventually_until_cumul :
  forall (s: infseq T) P J,
  eventually P s -> until J P s -> eventually (P /\_ until J P) s.
intros s P J ev. induction ev as [s Ps | x s evPs induc_hyp].
  intro un. constructor 1. split; assumption.
  intro unxs. case (until_Cons _ _ _ _ unxs). 
    intro Pxs. constructor 1; split; assumption. 
    intros (_, uns). constructor 2. apply induc_hyp. exact uns. 
Qed.

Lemma until_eventually :
  forall (P Q J: infseq T -> Prop),
  (forall s, J s -> P s -> Q s) ->
  forall s, J s -> until J Q s -> eventually P s -> eventually Q s.
Proof.
intros P Q J impl s Js J_until_Q ev.
genclear J_until_Q; genclear Js.
induction ev as [s Ps | x s ev induc_hyp].
  intros Js J_until_Q. constructor 1. apply impl; assumption.
  intros _ J_until_Q. cut (s = tl (Cons x s)); [idtac | reflexivity].
  case J_until_Q; clear J_until_Q x.
    constructor 1; assumption.
    intros (x, s1) _ J_until_Q e; simpl in *.
    constructor 2. generalize e J_until_Q; clear e x. (* trick: keep J_until_Q!! *)
    case J_until_Q; clear J_until_Q s1.
       clearall. constructor 1; assumption.
       intros s2 Js2 _ e J_until_Q2. rewrite e in induc_hyp; clear e.
       apply induc_hyp; assumption.
Qed.

Lemma eventually_trans :
  forall (P Q inv: infseq T -> Prop),
  (forall x s, inv (Cons x s) -> inv s) ->
  (forall s, inv s -> P s -> eventually Q s) ->
  forall s, inv s -> eventually P s -> eventually Q s.
Proof.
intros P Q inv is_inv PeQ s invs ev. induction ev as [s Ps | x s ev IHev].
  apply PeQ; assumption.
  constructor 2. apply IHev. apply is_inv with x; assumption.
Qed.

(* inf_often and continuously facts *)

Lemma inf_often_invar :
  forall (x: T) (s: infseq T) P, inf_often P (Cons x s) -> inf_often P s.
Proof.
intros x s P; apply always_invar.
Qed.

Lemma continuously_invar :
  forall (x: T) (s: infseq T) P, continuously P (Cons x s) -> continuously P s.
Proof.
intros x s P cny.
apply eventually_Cons in cny.
case cny; trivial.
intro alP.
apply E0.
apply always_invar in alP; assumption.
Qed.

Lemma continuously_and_tl :
  forall (P Q : infseq T -> Prop) (s : infseq T),
  continuously P s -> continuously Q s -> continuously (P /\_ Q) s.
Proof.
intros P Q s cnyP.
induction cnyP as [s alP|].
  intro cnyQ.
  induction cnyQ.
  apply E0.
  apply always_and_tl; trivial.
  apply E_next.
  apply IHcnyQ.
  apply always_invar in alP; assumption.
intro cnyQ.
apply E_next.
apply IHcnyP.
apply continuously_invar in cnyQ; assumption.
Qed.

(* monotony *)

Lemma now_monotonic :
  forall (P Q: T -> Prop), 
  (forall x, P x -> Q x) -> forall s, now P s -> now Q s.
Proof.
intros P Q PQ (x, s) nP; simpl. apply PQ. assumption.
Qed.

Lemma next_monotonic :
  forall (P Q: infseq T -> Prop),
  (forall s, P s -> Q s) -> forall s, next P s -> next Q s.
Proof.
intros P Q PQ [x s]; apply PQ.
Qed.

Lemma consecutive_monotonic :
  forall (P Q: T -> T -> Prop), 
  (forall x y, P x y -> Q x y) -> forall s, consecutive P s -> consecutive Q s.
Proof.
intros P Q PQ (x, (y, s)) nP; simpl. apply PQ. assumption.
Qed.

Lemma always_monotonic :
  forall (P Q: infseq T -> Prop),
  (forall s, P s -> Q s) -> forall s, always P s -> always Q s.
Proof.
intros P Q PQ.  cofix cf. intros(x, s) a. 
generalize (always_Cons x s P a); simpl; intros (a1, a2). constructor; simpl.
  apply PQ. assumption. 
  apply cf. assumption. 
Qed.

Lemma until_monotonic :
  forall (P Q J K: infseq T -> Prop),
  (forall s, P s -> Q s) -> (forall s, J s -> K s) -> 
  forall s, until J P s -> until K Q s.
Proof.
intros P Q J K PQ JK.  cofix cf. intros(x, s) un. 
generalize (until_Cons x s J P un); simpl. intros [Pxs | (Jxs, uns)]. 
  constructor 1; simpl; auto. 
  constructor 2; simpl; auto. 
Qed.

Lemma eventually_monotonic :
  forall (P Q J: infseq T -> Prop), 
  (forall x s, J (Cons x s) -> J s) ->
  (forall s, J s -> P s -> Q s) -> 
  forall s, J s -> eventually P s -> eventually Q s.
Proof.
intros P Q J is_inv JPQ s Js ev. 
apply (eventually_trans P Q J is_inv); try assumption. 
  intros; constructor 1. apply JPQ; assumption. 
Qed.

(* corollary which turns out to be too weak in practice *)
Lemma eventually_monotonic_simple :
  forall (P Q: infseq T -> Prop), 
  (forall s, P s -> Q s) -> 
  forall s, eventually P s -> eventually Q s.
Proof.
intros P Q PQ s. 
apply (eventually_monotonic P Q (fun s:infseq T => True)); auto.
Qed.

Lemma inf_often_monotonic :
  forall (P Q : infseq T -> Prop),
  (forall s, P s -> Q s) ->
  forall s, inf_often P s -> inf_often Q s.
Proof.
intros P Q impl.
apply always_monotonic.
apply eventually_monotonic_simple.
assumption.
Qed.

Lemma continuously_monotonic :
  forall (P Q : infseq T -> Prop),
  (forall s, P s -> Q s) ->
  forall s, continuously P s -> continuously Q s.
Proof.
intros P Q impl.
apply eventually_monotonic_simple.
apply always_monotonic.
assumption.
Qed.

(* not_tl inside operators *)

Lemma not_eventually_always_not :
  forall (P : infseq T -> Prop) (s : infseq T),
  ~ eventually P s <-> always (~_ P) s.
Proof.
intros P.
split; genclear s.
  cofix c.
  intros s evP.
  destruct s as [e s].
  apply Always.
    unfold not_tl.
    intro Pn.
    case evP.
    apply E0.
    assumption.
  apply c.
  intro evPn.
  contradict evP.
  apply E_next.
  assumption.
intros s alP evP.
induction evP.
  destruct s as [e s].
  apply always_Cons in alP.
  destruct alP as [nP alP].
  unfold not_tl in nP.
  contradict nP; assumption.
apply always_invar in alP.
contradict IHevP; assumption.
Qed.

Lemma eventually_not_always :
  forall (P : infseq T -> Prop) (s : infseq T),
    eventually (~_ P) s -> ~ always P s.
Proof.
intros P s eP alP.
induction eP.
 destruct s as [x s].
 unfold not_tl in H.
 contradict H.
 apply always_Cons in alP.
 destruct alP as [PC alP].
 assumption.
apply always_invar in alP.
contradict IHeP.
assumption.
Qed.

Lemma until_always_not_always :
  forall (J P : infseq T -> Prop) (s : infseq T),
  until J P s -> always (~_ P) s -> always J s.
Proof.
intros J P.
cofix c.
intros s unJP alP.
destruct s as [e s].
apply until_Cons in unJP.
case unJP.
  intro PC.
  apply always_Cons in alP.
  destruct alP as [nP alP].
  unfold not_tl in nP.
  contradict nP.
  assumption.
intros Jun.
destruct Jun as [JC unJPs].
apply Always; trivial.
apply c; trivial.
apply always_invar in alP.
assumption.
Qed.

Lemma always_not_eventually_not :
  forall (P : infseq T -> Prop) (s : infseq T),
    always P s -> ~ eventually (~_ P) s.
Proof.
intros P s alP evP.
induction evP.
  unfold not_tl in H.
  contradict H.
  destruct s as [x s].
  apply always_now in alP.
  assumption.
contradict IHevP.
apply always_invar in alP.
assumption.
Qed.

Lemma continuously_not_inf_often :
  forall (P : infseq T -> Prop) (s : infseq T),
  continuously (~_ P) s -> ~ inf_often P s.
Proof.
intros P s cnyP.
induction cnyP.
  destruct s as [e s].
  intros ifP.
  apply always_now in ifP.
  induction ifP.
    destruct s0 as [e0 s0].
    apply always_now in H.
    unfold not_tl in H.
    contradict H.
    trivial.
  apply always_invar in H.
  contradict IHifP.
  trivial.
intro ioP.
apply always_invar in ioP.
contradict IHcnyP.
trivial.
Qed.

Lemma inf_often_not_continuously :
  forall (P : infseq T -> Prop) (s : infseq T),
  inf_often (~_ P) s -> ~ continuously P s.
Proof.
intros P s ioP cnyP.
induction cnyP.
  destruct s as [x s].
  apply always_now in ioP.
  induction ioP.
    destruct s0 as [x' s0].
    apply always_now in H.
    unfold not_tl in H0.
    contradict H0.
    assumption.
  apply always_invar in H.
  contradict IHioP.
  assumption.
apply inf_often_invar in ioP.
contradict IHcnyP.
assumption.
Qed.

(* connector facts *)

Lemma and_tl_comm : 
  forall (P Q : infseq T -> Prop) (s : infseq T),
  (P /\_ Q) s <-> (Q /\_ P) s.
Proof.
intros; split; unfold and_tl; apply and_comm.
Qed.

Lemma and_tl_assoc : 
  forall (P Q R : infseq T -> Prop) (s : infseq T),
  ((P /\_ Q) /\_ R) s <-> (P /\_ Q /\_ R) s.
Proof.
intros; split; unfold and_tl; apply and_assoc.
Qed.

Lemma or_tl_comm :
  forall (P Q : infseq T -> Prop) (s : infseq T),
  (P \/_ Q) s <-> (Q \/_ P) s.
Proof.
intros; split; unfold or_tl; apply or_comm.
Qed.

Lemma or_tl_assoc : 
  forall (P Q R : infseq T -> Prop) (s : infseq T),
  ((P \/_ Q) \/_ R) s <-> (P \/_ Q \/_ R) s.
Proof.
intros; split; unfold or_tl; apply or_assoc.
Qed.

Lemma not_tl_or_tl : 
  forall (P Q : infseq T -> Prop) (s : infseq T),
  (~_ (P \/_ Q)) s <-> ((~_ P) /\_ (~_ Q)) s.
Proof.
intros P Q s; unfold not_tl, and_tl, or_tl; split; [ intros PQs | intros [Ps Qs] PQs].
  split; intro Ps; contradict PQs; [left|right]; assumption.
case PQs; assumption.
Qed.

Lemma not_tl_or_tl_and_tl : 
  forall (P Q : infseq T -> Prop) (s : infseq T),
    ((~_ P) \/_ (~_ Q)) s -> (~_ (P /\_ Q)) s.
Proof.
intros P Q s; unfold not_tl, and_tl, or_tl; intros PQs [Ps Qs]; case PQs; intros nPQs; contradict nPQs; assumption.
Qed.

End sec_modal_op_lemmas.

Implicit Arguments always_Cons [T x s P]. 
Implicit Arguments always_now [T x s P]. 
Implicit Arguments always_invar [T x s P]. 
Implicit Arguments always_tl [T s P].
Implicit Arguments always_and_tl [T s P Q].
Implicit Arguments always_always1 [T s P].
Implicit Arguments always_inf_often [T s P].
Implicit Arguments always_continuously [T s P].

Implicit Arguments until_Cons [T x s J P].
Implicit Arguments eventually_Cons [T x s P]. 
Implicit Arguments eventually_next [T P s].
Implicit Arguments eventually_always_cumul [T s P Q].
Implicit Arguments eventually_until_cumul [T s P J].
Implicit Arguments until_eventually [T P Q s J].
Implicit Arguments eventually_trans [T P Q inv s].

Implicit Arguments inf_often_invar [T x s P].
Implicit Arguments continuously_invar [T x s P].
Implicit Arguments continuously_and_tl [T P Q s].

Implicit Arguments now_monotonic [T P Q s].
Implicit Arguments next_monotonic [T P Q s].
Implicit Arguments consecutive_monotonic [T P Q s].
Implicit Arguments always_monotonic [T P Q s].
Implicit Arguments until_monotonic [T P Q J K s].
Implicit Arguments eventually_monotonic [T P Q s].
Implicit Arguments eventually_monotonic_simple [T P Q s].
Implicit Arguments inf_often_monotonic [T P Q s].
Implicit Arguments continuously_monotonic [T P Q s].

Implicit Arguments not_eventually_always_not [T P s].
Implicit Arguments eventually_not_always [T P s].
Implicit Arguments until_always_not_always [T J P s].
Implicit Arguments always_not_eventually_not [T P s].
Implicit Arguments continuously_not_inf_often [T P s].
Implicit Arguments inf_often_not_continuously [T P s].

Implicit Arguments and_tl_comm [T P Q s].
Implicit Arguments and_tl_assoc [T P Q R s].
Implicit Arguments or_tl_comm [T P Q s].
Implicit Arguments or_tl_assoc [T P Q R s].
Implicit Arguments not_tl_or_tl [T P Q s].
Implicit Arguments not_tl_or_tl_and_tl [T P Q s].

Ltac monotony := 
  match goal with 
     | [ |- now ?P ?s -> now ?Q ?s ] => apply now_monotonic
     | [ |- next ?P ?s -> next ?Q ?s ] => apply next_monotonic
     | [ |- consecutive ?P ?s -> consecutive ?Q ?s ] =>
       apply consecutive_monotonic
     | [ |- always ?P ?s -> always ?Q ?s ] => apply always_monotonic
     | [ |- ?J ?s -> eventually ?P ?s -> eventually ?Q ?s ] =>
       apply eventually_monotonic
     | [ |- until ?J ?P ?s -> until ?K ?Q ?s ] => apply until_monotonic
     | [ |- continuously ?P ?s -> continuously ?Q ?s ] =>
       apply continuously_monotonic
     | [ |- inf_often ?P ?s -> inf_often ?Q ?s ] =>
       apply inf_often_monotonic
  end.
