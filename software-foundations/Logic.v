Require Export MoreCoq.


Theorem proj2 : forall P Q : Prop, 
  P /\ Q ->  Q.
Proof.
