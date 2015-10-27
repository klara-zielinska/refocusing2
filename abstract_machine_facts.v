Require Import abstract_machine.


Module DetAbstractMachine_Sim (AM : DET_ABSTRACT_MACHINE).

  Import AM.


  Fixpoint n_steps c n : option configuration :=
      match n with
      | 0   => Some c
      | S n => match next_conf c with
               | None    => None
               | Some c' => n_steps c' n
               end
      end.


  Lemma n_steps_correct : forall c1 n c2, n_steps c1 (S n) = Some c2 -> c1 →+ c2.

  Proof.
    intros c1 n c2; revert c1.

    induction n; 
        intros c1 H;
        remember (next_conf c1) as c1'; destruct c1';
        simpl in H;
        rewrite <- Heqc1' in *;
        try discriminate.

    - constructor 1.
      apply next_correct. 
      congruence.
    - econstructor 2.
      + apply next_correct. 
        symmetry; exact Heqc1'.
      + apply IHn.
        simpl; auto.
  Qed.


  Lemma n_steps_complete : 
      forall c1 c2,  c1 →+ c2  -> exists n, n_steps c1 n = Some c2.

  Proof.
    induction 1.
    - exists 1; simpl. 
      apply next_correct in H.
      rewrite H; auto.
    - destruct IHtrans_close as (n, H1).
      apply next_correct in H.
      eexists (S n).
      simpl.
      rewrite H; auto.
  Qed.


(* BEGINE Hell

  Axiom conf_eq_dec : forall c1 c2 : configuration, {c1 = c2} + {c1 <> c2}.

  Definition steps_count c1 c2 (H : c1 →+ c2) : nat.
    refine (
     (fix aux c1 c2 (H : c1 →+ c2) {struct H} :=
      match next_conf c1 as c' return next_conf c1 = c' -> nat with
      | None    => fun _ => _
      | Some c' => fun G => if conf_eq_dec c' c2 then 1
                            else S (aux c' c2 _)
      end eq_refl)
      c1 c2 H).
  - destruct H0 as [? ? H0 | ? ? ? H0 ?];
        apply next_correct in H0;
        rewrite H0 in G; inversion G; subst;
    solve [tauto].
  - contradict _H.
    destruct H0 as [? ? H0 | ? ? ? H0 ?];
        apply next_correct in H0;
        rewrite H0;
    solve [discriminate].
  Defined.


  Require Import Program.
(*
  Lemma L : forall c1 c2 (H : c1 →+ c2),
                steps_count c1 c2 H <> 0.
  Proof.
    intros c1 c2 H.
    destruct H.
    simpl.
    remember (next_conf c1).
    dependent destruction (next_conf c1).
*)
  Lemma steps_count_correct : 
      forall c1 c2 (H : c1 →+ c2), n_steps c1 (steps_count c1 c2 H) = Some c2.

  Proof.
    intros c1 c2 H.
    remember (steps_count c1 c2 H) as n.
    induction n.
    destruct H as [? ? H | ? ? ? H H'];
        assert (HH := H);
        apply next_correct in HH.
    + simpl in Heqn.
      rewrite HH in Heqn.
    
    remember (next_conf c1) as c'.
    destruct c

END Hell *)

End DetAbstractMachine_Sim.

  