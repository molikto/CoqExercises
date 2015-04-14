Require Export MoreCoq.


Theorem proj2 : forall P Q : Prop, 
  P /\ Q ->  Q.
Proof. intros. inversion H. trivial. Qed.

Theorem and_assoc : forall P Q R : Prop, 
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  destruct H as [HP [HQ HR]]. apply conj. apply conj. trivial. trivial. trivial. Qed.
  

Theorem iff_refl : forall P : Prop, 
  P <-> P.
Proof. intros P. unfold iff. apply conj. intros H. apply H. intros H. apply H. Qed.

Theorem iff_trans1 : forall P Q R : Prop, 
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof. intros P Q R. intros H K. rewrite H. rewrite K. tauto. Qed.

Theorem iff_trans2 : forall P Q R : Prop, 
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof. intros P Q R. intros H K. inversion H. inversion K. apply conj. intro P0. apply H0 in P0. apply H2 in P0. trivial. intro. apply H3 in H4. apply H1 in H4. trivial. Qed.

Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q H.
  destruct H as [HP | HQ].
    Case "left". apply or_intror. apply HP.
    Case "right". apply or_introl. apply HQ.  Qed.

(** From here on, we'll use the shorthand tactics [left] and [right]
    in place of [apply or_introl] and [apply or_intror]. *)

Theorem or_commut' : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q H.
  destruct H as [HP | HQ].
    Case "left". right. apply HP.
    Case "right". left. apply HQ.  Qed.


Theorem or_distributes_over_and_2 : forall P Q R : Prop,
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof. intros. inversion H. destruct H0. left. trivial. destruct H1. left. trivial. right. apply conj. trivial. trivial. Qed.

 
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof. intros. split. intros. tauto. tauto. Qed.

Theorem andb_false : forall b c,
  andb b c = false -> b = false \/ c = false.
Proof. intros. destruct b; destruct c. inversion H. right. reflexivity.  left. reflexivity. left. reflexivity. Qed.

Theorem andb_false2 : forall b c,
  andb b c = false -> b = false \/ c = false.
  intros.
  destruct b.
  simpl in *.
  subst.
  auto.
  simpl in *.
  auto.
Qed.

Theorem orb_prop : forall b c,
  orb b c = true -> b = true \/ c = true.
Proof. destruct b. simpl. intros. left. apply H. simpl. intros. right. apply H. Qed.

Theorem orb_false_elim : forall b c,
  orb b c = false -> b = false /\ c = false. 
Proof. intros. destruct b; destruct c. inversion H.  inversion H. inversion H. split. trivial. trivial. Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof. intros. unfold not. intros. apply H0 in H. trivial. Qed.

Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof. unfold not. intros. apply H in H1. apply H0 in H1. trivial. Qed.


Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof. unfold not. intros. inversion H. apply H1 in H0. trivial. Qed.
 


Definition peirce := forall P Q: Prop, 
  ((P->Q)->P)->P.
Definition classic := forall P:Prop, 
  ~~P -> P.
Definition excluded_middle := forall P:Prop, 
  P \/ ~P.
Definition de_morgan_not_and_not := forall P Q:Prop, 
  ~(~P /\ ~Q) -> P\/Q.
Definition implies_to_or := forall P Q:Prop, 
  (P->Q) -> (~P\/Q).
  
Goal peirce -> classic.
Proof.   unfold peirce.  unfold classic.  intros.  apply (H _ (~ P)).
  intros.
  set (fun (a: P) => (H0 (H1 a))).
  apply H0 in f.
  inversion f.Qed.

Goal classic -> excluded_middle. unfold classic. unfold excluded_middle. intros H. intros. apply H. unfold not. intros. apply H0. right. intro. apply H0. left. apply H1. Qed.

Goal excluded_middle -> de_morgan_not_and_not.
Proof. unfold excluded_middle. unfold de_morgan_not_and_not. intros. assert (~ P -> Q). intros. set (H Q). destruct o. trivial. set (H0 (conj H1 H2)). inversion f. set (H P). destruct o. left. trivial. right. apply H1 in H2. trivial. Qed.

Goal de_morgan_not_and_not -> implies_to_or.
Proof. unfold de_morgan_not_and_not. unfold implies_to_or. intros. apply H. unfold not. intros. destruct H1. set (fun (a: P) => (H2 (H0 a))). apply H1 in f. inversion f. Qed.

Goal implies_to_or -> peirce.
Proof. unfold implies_to_or. unfold peirce. intros. assert (~P \/ P). apply H. intros. trivial. destruct H1. assert (False -> Q). intros. inversion H2. set (H0 (fun (a: P) => (H2 (H1 a)))). trivial. trivial. Qed.

Theorem excluded_middle_irrefutable:  forall (P:Prop), ~ ~ (P \/ ~ P).  
Proof. unfold not. intros. apply H. right. intro. set (H (or_introl H0)). inversion f. Qed.
(** this is purely fantastic shit. **)

Theorem false_beq_nat : forall n m : nat,
     n <> m ->
     beq_nat n m = false.
Proof. induction n. destruct m. intros. set (H eq_refl). inversion f. intros. simpl. trivial. intros. destruct m. simpl. trivial. simpl. assert (n <> m). unfold not. intros. subst. set (H eq_refl). trivial.  apply IHn in H0. trivial. Qed.
 