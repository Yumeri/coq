Check (fun x : nat => x).
Check (fun x : True => x).
Check I.
Check (fun _ : False => I).
Check (fun x : False => x).
Inductive unit : Set := | tt.
Check unit.
Check tt.
Theorem unit_singleton : forall x : unit, x = tt.
Proof. induction x. auto. Qed.
Check unit_ind.
Inductive test : Set := t1 | t2.
Check test_ind.
Inductive Empty_set : Set := .
Theorem the_sky_is_falling : forall x : Empty_set, 2+2=5.
Proof. intros. inversion x. Qed.
Theorem false_ : forall P Q : Prop, P -> ~P -> Q.
Proof. intros. destruct H0. apply H. Qed.
Inductive nat_list : Set :=
| NNil : nat_list
| NCons : nat -> nat_list -> nat_list.

Fixpoint nlength (ls:nat_list) : nat :=
  match ls with
  | NNil => O
  | NCons _ ls' => S (nlength ls')
  end.

Fixpoint napp (ls1 ls2 : nat_list) : nat_list :=
  match ls1 with
  | NNil => ls2
  | NCons n ls1' => NCons n (napp ls1' ls2)
  end.

Theorem nlength_app : forall ls1 ls2:nat_list, nlength (napp ls1 ls2) = plus (nlength ls1) (nlength ls2).
Proof. induction ls1; auto. intros.
  simpl. f_equal. auto. Qed.

Check nat_list_ind.

Inductive nat_btree:Set:=
|NLeaf : nat_btree
|NNode:nat_btree->nat->nat_btree->nat_btree.

Fixpoint nsize (tr:nat_btree):nat:=
  match tr with
  | NLeaf => S O
  | NNode tr1 _ tr2 => plus (nsize tr1) (nsize tr2)
  end.

Fixpoint nsplice (tr1 tr2:nat_btree):nat_btree:=
  match tr1 with
  | NLeaf => NNode tr2 O NLeaf
  | NNode tr1' n tr2' => NNode (nsplice tr1' tr2) n tr2'
  end.

Theorem plus_assoc : forall a b c, a+b+c=a+(b+c).
Proof. induction a; auto. intros. repeat rewrite plus_Sn_m. auto. Qed.

Theorem nsize_nsplice : forall tr1 tr2:nat_btree, nsize (nsplice tr1 tr2) = plus (nsize tr2) (nsize tr1).
Proof. induction tr1; auto. intros. simpl. erewrite IHtr1_1. rewrite plus_assoc. reflexivity. Qed.
Check nat_btree_ind.
Print nsize_nsplice.

Inductive list (T:Set) : Set :=
| Nil:list T
| Cons:T->list T->list T.

Implicit Arguments Nil [T].

Fixpoint length (T:Set) (ls:list T) :nat:=
  match ls with
  | Nil => O
  | Cons _ _ ls' => S (length T ls')
  end.

Inductive even_list : Set :=
|ENil : even_list
| ECons : nat->odd_list->even_list
with odd_list : Set :=
     |OCons : nat->even_list->odd_list.

Fixpoint elength (el:even_list):nat :=
  match el with
  | ENil => O
  | ECons _ ol => S (olength ol)
  end
with olength (ol:odd_list) : nat :=
       match ol with
       | OCons _ el => S (elength el)
       end.

Fixpoint eapp (el1 el2 : even_list) : even_list:=
  match el1 with
  | ENil => el2
  | ECons n ol => ECons n (oapp ol el2)
  end
with oapp ( ol :odd_list) (el : even_list) : odd_list:=
       match ol with
       | OCons n el' => OCons n (eapp el' el)
       end.


Theorem elength_eapp : forall el1 el2:even_list,
    elength (eapp el1 el2) = plus (elength el1) (elength el2).