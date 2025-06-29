Inductive nat : Type :=
    | O
    | S (n : nat).

Lemma plus_r_O : forall a, a + 0 = a.
Proof.
    intros.
    induction a.
    - simpl. reflexivity.
    - simpl in *. rewrite IHa. reflexivity.
Qed. 

Lemma plus_assoc : forall a b c, a + b + c = a + (b + c).
Proof.
    intros.
    induction a.
    - simpl. reflexivity.
    - simpl. rewrite IHa. reflexivity.
Qed.

Lemma plus_S_n : forall a b, Datatypes.S (a + b) = a + Datatypes.S b.
Proof.
    intros. induction a.
    - simpl. reflexivity.
    - simpl. rewrite IHa. reflexivity.
Qed.

Theorem plus_comm : forall a b, a + b = b + a.
Proof.
    intros. induction a.
    - simpl. rewrite plus_r_O. reflexivity.
    - simpl. rewrite IHa. rewrite plus_S_n. reflexivity.
Qed.   