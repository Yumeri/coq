Theorem tmp : forall x y z, (x+y)+z=x+(y+z).
Proof.
  induction x. auto. intros. repeat rewrite plus_Sn_m. auto. Qed.



