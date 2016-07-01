Require Import InfSeqExt.infseq.
Require Import InfSeqExt.exteq.

(* map *)
Section sec_map.

Variable A B: Type.

CoFixpoint map (f: A->B) (s: infseq A): infseq B :=
  match s with
   Cons x s => Cons (f x) (map f s)
  end.

Lemma map_Cons: forall (f:A->B) x s, map f (Cons x s) = Cons (f x) (map f s).
intros. pattern (map f (Cons x s)). rewrite <- recons. simpl. reflexivity.
Qed.

End sec_map. 
Implicit Arguments map [A B].
Implicit Arguments map_Cons [A B].

(* --------------------------------------------------------------------------- *)
(* Zipping two infseqs: useful for map theory *)
Section sec_zip.

Variable A B: Type.

CoFixpoint zip (sA: infseq A) (sB: infseq B) : infseq (A*B) := 
  match sA, sB with
    | Cons a sA0, Cons b sB0 => Cons (a, b) (zip sA0 sB0)
  end.

Lemma zip_Cons: forall (a:A) (b:B) sA sB, zip (Cons a sA) (Cons b sB) = Cons (a, b) (zip sA sB). 
Proof.
intros. pattern (zip (Cons a sA) (Cons b sB)); rewrite <- recons. simpl. reflexivity. 
Qed.

End sec_zip.

Implicit Arguments zip [A B].
Implicit Arguments zip_Cons [A B].

(* --------------------------------------------------------------------------- *)
(* map and_tl  temporal logic *)

Section sec_map_modalop.

Variable A B: Type.

Lemma and_tl_map :
   forall (f: A->B) (P P': infseq A->Prop) (Q Q': infseq B->Prop),
   (forall s, P s -> Q (map f s)) ->
   (forall s, P' s -> Q' (map f s)) ->
   forall (s: infseq A),
   (P /\_ P') s -> (Q /\_ Q') (map f s).
Proof.
unfold and_tl; intuition. 
Qed.

Lemma and_tl_map_conv :
   forall (f: A->B) (P P': infseq A->Prop) (Q Q': infseq B->Prop),
   (forall s, Q (map f s) -> P s) ->
   (forall s, Q' (map f s) -> P' s) ->
   forall (s: infseq A),
   (Q /\_ Q') (map f s) -> (P /\_ P') s.
Proof.
unfold and_tl; intuition. 
Qed.

Lemma or_tl_map :
   forall (f: A->B) (P P': infseq A->Prop) (Q Q': infseq B->Prop),
   (forall s, P s -> Q (map f s)) ->
   (forall s, P' s -> Q' (map f s)) ->
   forall (s: infseq A),
   (P \/_ P') s -> (Q \/_ Q') (map f s).
Proof.
unfold or_tl; intuition. 
Qed.

Lemma or_tl_map_conv :
   forall (f: A->B) (P P': infseq A->Prop) (Q Q': infseq B->Prop),
   (forall s, Q (map f s) -> P s) ->
   (forall s, Q' (map f s) -> P' s) ->
   forall (s: infseq A),
   (Q \/_ Q') (map f s) -> (P \/_ P') s.
Proof.
unfold or_tl; intuition. 
Qed.

Lemma impl_tl_map :
   forall (f: A->B) (P P': infseq A->Prop) (Q Q': infseq B->Prop),
   (forall s, Q (map f s) -> P s) ->
   (forall s, P' s -> Q' (map f s)) ->
   forall (s: infseq A),
   (P ->_ P') s -> (Q ->_ Q') (map f s).
Proof.
unfold impl_tl; intuition. 
Qed.

Lemma impl_tl_map_conv :
   forall (f: A->B) (P P': infseq A->Prop) (Q Q': infseq B->Prop),
   (forall s, P s -> Q (map f s)) ->
   (forall s, Q' (map f s) -> P' s) ->
   forall (s: infseq A),
   (Q ->_ Q') (map f s) -> (P ->_ P') s.
Proof.
unfold impl_tl; intuition. 
Qed.

Lemma not_tl_map :
   forall (f: A->B) (P : infseq A->Prop) (Q: infseq B->Prop),
   (forall s, Q (map f s) -> P s) ->
   forall (s: infseq A), (~_ P) s -> (~_ Q) (map f s).
Proof.
unfold not_tl; intuition. 
Qed.

Lemma not_tl_map_conv :
   forall (f: A->B) (P: infseq A->Prop) (Q: infseq B->Prop),
   (forall s, P s -> Q (map f s)) ->
   forall (s: infseq A), (~_ Q) (map f s) -> (~_ P) s.
Proof.
unfold not_tl; intuition. 
Qed.

Lemma now_map :
   forall (f: A->B) (P: B->Prop) (s: infseq A),
   now (fun x => P (f x)) s -> now P (map f s).
Proof.
intros f P (x, s) nP; assumption. 
Qed.

Lemma now_map_conv :
   forall (f: A->B) (P: B->Prop) (s: infseq A),
   now P (map f s) -> now (fun x => P (f x)) s.
Proof.
intros f P (x, s) nP; assumption. 
Qed.

Lemma next_map :
   forall (f: A->B) (P: infseq A->Prop) (Q: infseq B->Prop),
   (forall s, P s -> Q (map f s)) ->
   forall (s: infseq A), next P s -> next Q (map f s).
Proof.
intros f P Q PQ [x s]; apply PQ.
Qed.

Lemma next_map_conv :
   forall (f: A->B) (P: infseq A->Prop) (Q: infseq B->Prop),
   (forall s, Q (map f s) -> P s) ->
   forall (s: infseq A), next Q (map f s) -> next P s.
Proof.
intros f P Q QP [x s]; apply QP.
Qed.

Lemma consecutive_map :
   forall (f: A->B) (P: B->B->Prop) (s: infseq A),
   consecutive (fun x y => P (f x) (f y)) s -> consecutive P (map f s).
Proof.
intros f P (x, (y, s)) nP; assumption. 
Qed.

Lemma consecutive_map_conv :
   forall (f: A->B) (P: B->B->Prop) (s: infseq A),
   consecutive P (map f s) -> consecutive (fun x y => P (f x) (f y)) s.
Proof.
intros f P (x, (y, s)) nP; assumption. 
Qed.

Lemma always_map :
   forall (f: A->B) (P: infseq A->Prop) (Q: infseq B->Prop),
   (forall s, P s -> Q (map f s)) ->
   forall (s: infseq A), always P s -> always Q (map f s).
Proof.
intros f P Q PQ. cofix cf.
intros (x, s) a. case (always_Cons a); intros a1 a2. constructor.
  apply PQ. assumption.
  rewrite map_Cons; simpl. apply cf; assumption.
Qed.

Lemma always_map_conv :
   forall (f: A->B) (P: infseq A->Prop) (Q: infseq B->Prop),
   (forall s, Q (map f s) -> P s) ->
   forall (s: infseq A), always Q (map f s) -> always P s.
Proof.
intros f P Q QP. cofix cf.
intros (x, s) a. rewrite map_Cons in a. case (always_Cons a); intros a1 a2. constructor.
  apply QP. rewrite map_Cons; assumption.
  simpl. apply cf; assumption. 
Qed.

Lemma until_map :
   forall (f: A->B) (J P: infseq A->Prop) (K Q: infseq B->Prop),
   (forall s, J s -> K (map f s)) ->
   (forall s, P s -> Q (map f s)) ->
   forall (s: infseq A),
   (until J P) s -> (until K Q) (map f s).
Proof.
intros f J P K Q JK PQ. cofix cf. 
intros (x, s) un. case (until_Cons un); clear un.
  intro Pxs; constructor 1. apply PQ. assumption. 
  intros (Jxs, un). rewrite map_Cons. constructor 2.
    rewrite <- map_Cons. auto.
    simpl. auto. 
Qed.

Lemma until_map_conv :
   forall (f: A->B) (J P: infseq A->Prop) (K Q: infseq B->Prop),
   (forall s, K (map f s) -> J s) ->
   (forall s, Q (map f s) -> P s) ->
   forall (s: infseq A),
   (until K Q) (map f s) -> (until J P) s.
Proof.
intros f J P K Q KJ QP. cofix cf.
intros (x, s) un.
rewrite map_Cons in un; case (until_Cons un); clear un; rewrite <- map_Cons.
  intro Qxs; constructor 1. apply QP. assumption.
  intros (Kxs, un). constructor 2; simpl; auto.
Qed.

Lemma eventually_map :
   forall (f: A->B) (P: infseq A->Prop) (Q: infseq B->Prop),
   (forall s, P s -> Q (map f s)) ->
   forall s, eventually P s -> eventually Q (map f s).
Proof.
intros f P Q PQ s e. induction e as [s ok | x s e induc_hyp].
  destruct s as (x, s); simpl in *. rewrite map_Cons. constructor 1.
    rewrite <- map_Cons. apply PQ. exact ok.
  rewrite map_Cons. constructor 2. exact induc_hyp.
Qed.

(* The converse seems to require much more work *)

Definition fstAB := fst (A:=A) (B:=B).

Lemma exteq_fst_zip:
  forall sA sB, exteq (map fstAB (zip sA sB)) sA.
Proof.
cofix cf. intros (a, sA) (b, sB). 
rewrite zip_Cons. rewrite map_Cons. constructor. apply cf.
Qed.

Lemma exteq_zip_map :
   forall (f: A->B) (sA: infseq A) (sB: infseq B),
   always (now (fun c: A*B => let (x, y) := c in y = f x)) (zip sA sB) ->
   exteq sB (map f (map fstAB (zip sA (map f sA)))).
Proof. 
intros f. cofix cf. 
intros (a, sA) (b, sB).
repeat rewrite map_Cons; repeat rewrite zip_Cons; repeat rewrite map_Cons; simpl. 
intro al; case (always_Cons al); clear al; simpl. intros e al. case e. constructor. 
apply cf. exact al. 
Qed.

Lemma eventually_map_conv_aux :
   forall (f: A->B) (Q: infseq B->Prop), extensional Q ->
   forall (s: infseq A) (sB: infseq B),
   always (now (fun c: A*B => let (x, y) := c in y = f x)) (zip s sB) ->
   eventually Q sB ->
   eventually (fun sc => Q (map f (map fstAB sc))) (zip s (map f s)).
Proof.
intros f Q extQ s sB al ev. genclear al; genclear s. 
induction ev as [(b, sB) QbsB | b sB ev induc_hyp].
  intros (a, sA) al.
  constructor 1. apply extQ with (Cons b sB); try assumption.
     apply exteq_zip_map. apply al.
  intros (a, sA). repeat rewrite map_Cons. repeat rewrite zip_Cons.
  intro al. case (always_Cons al); simpl. clear al; intros e al. 
  constructor 2. apply induc_hyp. exact al. 
Qed.

Lemma eventually_map_conv :
   forall (f: A->B) (P: infseq A->Prop) (Q: infseq B->Prop),
   extensional P -> extensional Q -> 
   (forall s, Q (map f s) -> P s) ->
   forall s, eventually Q (map f s) -> eventually P s.
Proof.
intros f P Q extP extQ QP s ev.
assert (efst: eventually P (map fstAB (zip s (map f s)))).
   assert (evzip : eventually (fun sc => Q (map f (map fstAB sc))) (zip s (map f s))).
     clear extP QP P. 
     assert (alzip : (always (now (fun c : A * B => let (x, y) := c in y = f x)) (zip s (map f s)))).
        clear ev extQ. generalize s; clear s. cofix cf. intros (x, s). constructor. 
          simpl. reflexivity. 
          simpl. apply cf. 

     apply (eventually_map_conv_aux f Q extQ s (map f s) alzip ev). 
   clear ev. induction evzip as [((a, b), sAB) QabsAB | c sAB _ induc_hyp].
      constructor 1; simpl. apply QP. assumption. 
      rewrite map_Cons. constructor 2. apply induc_hyp. 
genclear efst. apply extensional_eventually.
  exact extP. 
  apply exteq_fst_zip.
Qed.

Lemma continuously_map :
   forall (f: A->B) (P: infseq A->Prop) (Q: infseq B->Prop),
   (forall s, P s -> Q (map f s)) ->
   forall (s: infseq A), continuously P s -> continuously Q (map f s).
Proof.
intros f P Q PQ.
apply eventually_map; apply always_map; assumption.
Qed.

Lemma continuously_map_conv :
   forall (f: A->B) (P: infseq A->Prop) (Q: infseq B->Prop),
   extensional P -> extensional Q -> 
   (forall s, Q (map f s) -> P s) ->
   forall (s: infseq A), continuously Q (map f s) -> continuously P s.
Proof.
intros f P Q eP eQ QP.
apply eventually_map_conv.
- apply extensional_always; assumption.
- apply extensional_always; assumption.
- apply always_map_conv; assumption.
Qed.

Lemma inf_often_map :
   forall (f: A->B) (P: infseq A->Prop) (Q: infseq B->Prop),
   (forall s, P s -> Q (map f s)) ->
   forall (s: infseq A), inf_often P s -> inf_often Q (map f s).
Proof.
intros f P Q PQ.
apply always_map; apply eventually_map; assumption.
Qed.

Lemma inf_often_map_conv :
   forall (f: A->B) (P: infseq A->Prop) (Q: infseq B->Prop),
   extensional P -> extensional Q -> 
   (forall s, Q (map f s) -> P s) ->
   forall (s: infseq A), inf_often Q (map f s) -> inf_often P s.
Proof.
intros f P Q eP eQ QP.
apply always_map_conv; apply eventually_map_conv; trivial.
Qed.

(* Some corollaries *)

Lemma eventually_now_map :
   forall (f: A->B) (P: B->Prop) (s: infseq A),
   eventually (now (fun x => P (f x))) s -> eventually (now P) (map f s).
Proof.
intros f P. apply eventually_map. apply now_map.
Qed.

Lemma eventually_now_map_conv :
   forall (f: A->B) (P: B->Prop) (s: infseq A),
   eventually (now P) (map f s) -> eventually (now (fun x => P (f x))) s.
Proof.
intros f P s. apply eventually_map_conv.
  apply extensional_now. 
  apply extensional_now. 
  clear s. intros (x, s). repeat rewrite map_Cons. simpl. trivial.
Qed.

Lemma ev_map_now_eq :
  forall (f: A -> B) a s, eventually (now (eq a)) s -> 
  eventually (now (eq (f a))) (map f s).
Proof.
intros f a. apply eventually_map.
intros s noa. apply now_map.
genclear noa. monotony. apply f_equal.
Qed.

End sec_map_modalop. 

(* TODO: implicit arguments for others *)
Implicit Arguments eventually_map_conv [A B f P s].
Implicit Arguments eventually_now_map_conv [A B f P s].
