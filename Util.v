Require Export Wellfounded.Transitive_Closure.
Require Export Relations. 
Require Export Relation_Operators.
Require Import Program.
Require Import Eqdep.



(* Transitive closures *)

Section tcl.

  Variable A : Type.
  Variable R : relation A.

  Notation trans_clos := (clos_trans A R).
  Notation trans_clos_l := (clos_trans_1n A R).
  Notation trans_clos_r := (clos_trans_n1 A R).

  Lemma exl : forall x y, trans_clos x y -> R x y \/ exists z, R x z /\ trans_clos z y.
  Proof with auto.
    induction 1.
    left...
    right; clear IHclos_trans2; destruct IHclos_trans1 as [H1 | [u [H1 H2]]].
    exists y...
    exists u; split; [ assumption | econstructor 2; eauto].
  Qed.

  Lemma exr : forall x y, trans_clos x y -> R x y \/ exists z, R z y /\ trans_clos x z.
  Proof with auto.
    induction 1.
    left...
    right; clear IHclos_trans1; destruct IHclos_trans2 as [H1 | [u [H1 H2]]].
    exists y...
    exists u; split; [ assumption | econstructor 2; eauto].
  Qed.

  Lemma tcl_l_h : forall x y z, trans_clos x y -> trans_clos_l y z -> trans_clos_l x z.
  Proof with eauto.
    induction 1; intros...
    econstructor 2...
  Qed.

  Lemma tcl_l : forall x y, trans_clos x y <-> trans_clos_l x y.
  Proof with eauto.
    split; induction 1; intros...
    constructor...
    eapply tcl_l_h...
    constructor...
    econstructor 2...
    constructor...
  Qed.

  Lemma tcl_r_h : forall x y z, trans_clos y z -> trans_clos_r x y -> trans_clos_r x z.
  Proof with eauto.
    induction 1; intros...
    econstructor 2...
  Qed.

  Lemma tcl_r : forall x y, trans_clos x y <-> trans_clos_r x y.
  Proof with eauto.
    split; induction 1; intros.
    constructor...
    eapply tcl_r_h...
    constructor...
    econstructor 2...
    constructor...
  Qed.

  Lemma Acc_tcl_l : forall x, Acc trans_clos x -> Acc trans_clos_l x.
  Proof with auto.
    induction 1.
    constructor; intros.
    apply H0; rewrite tcl_l...
  Qed.

  Theorem wf_clos_trans_l : well_founded R -> well_founded trans_clos_l.
  Proof with auto.
    intros H a; apply Acc_tcl_l; apply wf_clos_trans...
  Qed.

  Lemma Acc_tcl_r : forall x, Acc trans_clos x -> Acc trans_clos_r x.
  Proof with auto.
    induction 1.
    constructor; intros.
    apply H0; rewrite tcl_r...
  Qed.

  Theorem wf_clos_trans_r : well_founded R -> well_founded trans_clos_r.
  Proof with auto.
    intros H a; apply Acc_tcl_r; apply wf_clos_trans...
  Qed.

End tcl.




(* Some tactics *)

Ltac clean_eqs := repeat 
                  match goal with [H : ?x = ?x |- _] => clear H end.


Ltac join H L R := first [ assert (H := conj L R); clear L R
                         | assert (H := L); clear L
                         | assert (H := R); clear R
                         | idtac ].


Ltac dependent_destruction2 H := let i := fresh in 
                                 remember H as i in *;
                                 dependent destruction i;
                                 try subst H;
                                 clean_eqs.




(* Dependent equality *)

(* Copy of JMeq_eq_dep in Type universes *)
Definition JMeq_eq_depT := 
    fun (U : Type) (P : U -> Type) (p q : U) (x : P p) (y : P q) (H : p = q)
        (H0 : x ~= y) =>
    match
    H in (_ = y0) return (forall y1 : P y0, x ~= y1 -> eq_dep U P p x y0 y1)
    with
    | eq_refl =>
        fun (y0 : P p) (H1 : x ~= y0) =>
        (fun H2 : x = y0 =>
            eq_ind_r (fun x0 : P p => eq_dep U P p x0 p y0) (eq_dep_intro U P p y0)
        H2) (JMeq_eq H1)
    end y H0.


Ltac rec_subst H := 
    (* H - proccesed hypothesis
       R - helper variable that stores information if there was 
           any substitution performed in the last aux run *)
    let rec aux H R :=
        match type of H with
        | _ /\ _   => let G1 := fresh in let G2 := fresh in
                      destruct H as (G1, G2); aux G1 R; aux G2 R; join H G1 G2
        | ?x  =  _ => subst x; clear R; set (R := true)
        | _   = ?y => subst y; clear R; set (R := true)
        | ?x ~= ?y => try (dependent_destruction2 H;
                           match goal with
                           | _ : x ~= y |- _ => fail 2 
                           | _               => clear R; set (R := true) 
                           end)
        | _        => idtac
        end
    in
    let R := fresh in 
    repeat
    (
        set (R := false);
        aux H R; 
        match R with false => clear R; fail | _ => clear R end
    ).


Ltac dep_subst :=
    repeat
    (
        subst;
        match goal with 
        | G : existT _ _ _ = existT _ _ _ |- _ => dependent_destruction2 G
        | G : ?x ~= ?y |- _                    => let tx := type of x in 
                                                  let ty := type of y in 
                                                  constr_eq tx ty;
                                                  dependent_destruction2 G
        | _ => idtac
        end
    ).


Ltac discriminateJM H := 
    match type of H with ?x ~= ?y => 
    let H := fresh in 
    assert (H : eq_dep _ _ _ x _ y); 
    [ apply JMeq_eq_depT; auto | discriminate (eq_dep_eq_sigT _ _ _ _ _ _ H) ]
    end.

