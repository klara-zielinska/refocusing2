Require Import Util.
Require Import Program.
Require Import refocusing_semantics.
Require Import refocusing_machine.
Require Import reduction_languages_facts reduction_semantics_facts 
                   refocusing_semantics_facts.




Module RefEvalApplyMachine_Facts (R : RED_REF_SEM) (EAM : REF_EVAL_APPLY_MACHINE R).

  Module RF := RED_LANG_Facts R.
  Import R.R R RF.

  Notation "c1 >> c2" := (init_ckind |~ c1 → c2) (no associativity, at level 70).
  Notation "k |~ c1 >> c2" := (k |~ c1 → c2)     
                                         (no associativity, at level 70, c1 at level 69).


  Import ST.
  Import EAM.


  Local Hint Constructors EAM.trans clos_trans_1n.

  Theorem am_correct :                                                      forall c1 c2,
      c1 → c2 -> decompile c1 = decompile c2 \/ decompile c1 >> decompile c2.

  Proof with eauto.
    intros c1 c2 H.
    inversion H; subst;
        try match goal with 
        | H : dec_term ?t ?k = _ |- _ =>
              assert (G := dec_term_correct t k);
              rewrite H in G
        | H : dec_context ?ec ?k ?v = _ |- _ =>
              assert (G := dec_context_correct ec k v);
              rewrite H in G
        end;
    try solve [left; simpl; congruence].
    - right. 
      unfold reduce, dec. 
      exists k c r t0.
      intuition.
      + eapply proper_death_trans...
      + simpl.
        congruence.
    - right.
      unfold reduce, dec.
      exists k c r t.
      intuition.
      + eapply proper_death_trans...
      + simpl.
        congruence.
  Qed.

Require Import Vector.


Fixpoint fin_lift {n} (m : Fin.t n) := match m with
| Fin.F1 n => @Fin.F1 (S n)
| Fin.FS _ m => Fin.FS (fin_lift m)
end.
Fixpoint fin_to_nat {n} (m : Fin.t n) := match m with
| Fin.F1 _   => 0
| Fin.FS _ m => S (fin_to_nat m)
end.

Coercion fin_lift : Fin.t >-> Fin.t.
Coercion fin_to_nat : Fin.t >-> nat.

Arguments cons {A} _ {n} _.

Import VectorNotations.
Infix "++" := append.


  Lemma dec_proc_sim :               forall t {k1 k2} (d : decomp k1) (c : context k1 k2) 
                                                                   (c0 : context ick k1),
      dec_proc t c d ->
          exists n (sts : Vector.t conf n),
          (**)Forall (fun st => decompile st = (c~+c0)[t]) sts /\
          (**)match d with 
              | d_val v      => last (c_eval t (c ~+ c0) :: sts) = c_apply c0 v 
              | d_red k r c' => last (c_eval t (c ~+ c0) :: sts) = c_eval r (c'~+c0) /\
                                dec_term r k = in_red r                              \/
                                exists ec v, dec_context ec k v = in_red r           /\
                                last (c_eval t (c ~+ c0) :: sts) = c_apply (ec=:c'~+c0) v
              end /\
          (**)forall m : Fin.t n, (c_eval t (c~+c0) :: sts)[@m] → sts[@m].
  Proof with eauto.
    intros t k1 k2 d c c0 H.
    induction H using dec_proc_Ind with
    (P := fun k2 t (c : context k1 k2) d (_ : dec_proc t c d) =>
exists (n : nat) (sts : Vector.t configuration n),
  Forall (fun st : configuration => decompile st = (c ~+ c0) [t]) sts /\
match d with 
              | d_val v      => last (c_eval t (c ~+ c0) :: sts) = c_apply c0 v 
              | d_red k r c' => last (c_eval t (c ~+ c0) :: sts) = c_eval r (c'~+c0) /\
                                dec_term r k = in_red r                              \/
                                exists ec v, dec_context ec k v = in_red r           /\
                                last (c_eval t (c ~+ c0) :: sts) = c_apply (ec=:c'~+c0) v
              end /\
  (forall m : Fin.t n, (c_eval t (c ~+ c0) :: sts)[@m] → sts[@m]))

    (P0 := fun k2 (v' : R.value k2) (c : context k1 k2) d _ =>
exists (n : nat) (sts : Vector.t configuration n),
  Forall (fun st : configuration => decompile st = (c ~+ c0) [v']) sts /\
match d with 
              | d_val v      => last (c_apply (c ~+ c0) v' :: sts) = c_apply c0 v 
              | d_red k r c' => last (c_apply (c ~+ c0) v' :: sts) = c_eval r (c'~+c0) /\
                                dec_term r k = in_red r                              \/
                                exists ec v, dec_context ec k v = in_red r           /\
                                last (c_apply (c ~+ c0) v' :: sts) = c_apply (ec=:c'~+c0) v
              end /\
  (forall m : Fin.t n, (c_apply (c ~+ c0) v' :: sts)[@m] → sts[@m]));

         subst;

      try destruct IHdec_proc as [n [sts [H0 [H1 H2]]]]; auto;
      repeat match goal with
      | H : dec_term ?t ?k = _ |- _ => 
            assert (G := dec_term_correct t k);
            rewrite H in G
      | H : dec_context ?ec ?k ?v = _ |- _ => 
            assert (G := dec_context_correct ec k v);
            rewrite H in G
      end;
      subst;

  [ exists 0 (nil configuration)
  | exists (S n) (c_apply (c~+c0) v :: sts)
  | exists (S n) (c_eval t0 (ec =: c~+c0) :: sts) 
  | exists 0 (nil configuration)
  | exists 0 (nil configuration)
  | exists (S n) (c_apply (c ~+ c0) v0 :: sts)
  | exists (S n) (c_eval t (ec0 =: c ~+ c0) :: sts) ];

  solve [ split;
  [ constructor; simpl; try rewrite G; auto
  | split;
  [ eauto
  | intro m;
    dependent_destruction2 m; 
    solve
    [ simpl; eauto 
    | apply H2 ]
  ] ] ].
  Qed.


  Lemma decctx_proc_sim :                         forall {k1 k2} v' d (c : context k1 k2) 
                                                                   (c0 : context ick k1),
      decctx_proc v' c d ->
          exists (n : nat) (sts : Vector.t configuration n),
              Forall (fun st => decompile st = (c ~+ c0) [v']) sts /\
              match d with 
              | d_val v      => last (c_apply (c ~+ c0) v' :: sts) = c_apply c0 v 
              | d_red k r c' => last (c_apply (c ~+ c0) v' :: sts) = c_eval r (c'~+c0) /\
                                dec_term r k = in_red r                              \/
                                exists ec v, dec_context ec k v = in_red r           /\
                                last (c_apply (c ~+ c0) v' :: sts) = c_apply (ec=:c'~+c0) v
              end /\
  (forall m : Fin.t n, (c_apply (c ~+ c0) v' :: sts)[@m] → sts[@m]).
  Proof with eauto.
    intros k1 k2 v' d c c0 H.
    induction H using decctx_proc_Ind with
    (P := fun k2 t (c : context k1 k2) d (_ : dec_proc t c d) =>
exists (n : nat) (sts : Vector.t configuration n),
  Forall (fun st : configuration => decompile st = (c ~+ c0) [t]) sts /\
match d with 
              | d_val v      => last (c_eval t (c ~+ c0) :: sts) = c_apply c0 v 
              | d_red k r c' => last (c_eval t (c ~+ c0) :: sts) = c_eval r (c'~+c0) /\
                                dec_term r k = in_red r                              \/
                                exists ec v, dec_context ec k v = in_red r           /\
                                last (c_eval t (c ~+ c0) :: sts) = c_apply (ec=:c'~+c0) v
              end /\
  (forall m : Fin.t n, (c_eval t (c ~+ c0) :: sts)[@m] → sts[@m]))

    (P0 := fun k2 (v' : R.value k2) (c : context k1 k2) d _ =>
exists (n : nat) (sts : Vector.t configuration n),
  Forall (fun st : configuration => decompile st = (c ~+ c0) [v']) sts /\
match d with 
              | d_val v      => last (c_apply (c ~+ c0) v' :: sts) = c_apply c0 v 
              | d_red k r c' => last (c_apply (c ~+ c0) v' :: sts) = c_eval r (c'~+c0) /\
                                dec_term r k = in_red r                              \/
                                exists ec v, dec_context ec k v = in_red r           /\
                                last (c_apply (c ~+ c0) v' :: sts) = c_apply (ec=:c'~+c0) v
              end /\
  (forall m : Fin.t n, (c_apply (c ~+ c0) v' :: sts)[@m] → sts[@m]));

         subst;

      try destruct IHdecctx_proc as [n [sts [H0 [H1 H2]]]]; auto;
      repeat match goal with
      | H : dec_term ?t ?k = _ |- _ => 
            assert (G := dec_term_correct t k);
            rewrite H in G
      | H : dec_context ?ec ?k ?v = _ |- _ => 
            assert (G := dec_context_correct ec k v);
            rewrite H in G
      end;
      subst;

  [ exists 0 (nil configuration)
  | exists (S n) (c_apply (c~+c0) v :: sts)
  | exists (S n) (c_eval t0 (ec =: c~+c0) :: sts) 
  | exists 0 (nil configuration)
  | exists 0 (nil configuration)
  | exists (S n) (c_apply (c ~+ c0) v0 :: sts)
  | exists (S n) (c_eval t (ec0 =: c ~+ c0) :: sts) ];

  solve [ split;
  [ constructor; simpl; try rewrite G; auto
  | split;
  [ eauto
  | intro m;
    dependent_destruction2 m; 
    solve
    [ simpl; eauto 
    | apply H2 ]
  ] ] ].
  Qed.


  Lemma mid_ccons_as_append :                      forall {k1 k2} (c1 : context k1 k2) ec
                                                         {k3} (c2 : context (k2+>ec) k3),
      c2 ~+ ec =: c1 = c2 ~+ (ec =: [.]) ~+ c1.

  Proof.
    intros k1 k2 c1 ec k3 c2.
    induction c2;
    solve [ auto ].
  Qed.


  Lemma append_assoc : forall {k4 k3} (c1 : context k3 k4) {k2} (c2 : context k2 k3)
                         {k1} (c3 : context k1 k2),
      c1 ~+ c2 ~+ c3 = (c1 ~+ c2) ~+ c3.
  Proof.
    induction c1; intros; 
    solve [simpl; f_equal; eauto].
  Qed.


  Lemma ccons_append_empty_self_JM : forall {k1 k2} (c1 : context k1 k2) {k3} (c2 : context k2 k3),
      k2 = k3 -> c1 ~= c2 ~+ c1 -> c2 ~= [.](k2).

  Proof with eauto.
    intros k1 k2 c1.
    induction c1; intros k3 c2 H H0;
      destruct c2...
    - discriminateJM H0.
    - exfalso.
      simpl in H0.
      inversion_ccons H0; clear H5 x.
      assert (H1 : c2 ~+ ec0 =: [.](k0) ~= [.](k0)). 
      {
          eapply IHc1...
          rewrite <- append_assoc. 
          rewrite <- (mid_ccons_as_append c1 ec0 c2).
          rewrite <- x0.
          reflexivity.
      }
      revert H1. clear. revert c2.
      cut (forall k (c : context (k0 +> ec0) k), k = k0 -> ~ (c ~+ ec0 =: [.](k0) ~= [.](k0))).
      intro. intros. eapply H. reflexivity. exact H1.
      intros k c G H.
      destruct c;
      discriminateJM H.
  Qed.


  Lemma ccons_append_empty_self : forall {k1 k2} (c1 : context k1 k2) (c2 : context k2 k2),
      c1 = c2 ~+ c1 -> c2 = [.](k2).

  Proof with eauto. 
    intros.
    cut (c2 ~= [.](k2)).
    { intro H0; rewrite H0... }
    eapply ccons_append_empty_self_JM with c1...
    rewrite <- H.
    solve [trivial].
  Qed.


  Lemma local1 : forall {n} (sts : Vector.t configuration n) st1 st2,
  (*1*)(forall m : Fin.t n, (st1 :: sts)[@m] → sts[@m]) ->
  (*2*)last (st1 :: sts) → st2 ->

      forall m : Fin.t (n + 1), (st1 :: sts ++ [st2])[@m] → (sts ++ [st2])[@m].

  Proof.
    intros n sts st1 st2 H H0. revert st1 H H0.
    induction sts; intros.
    - dependent destruction m.
      + auto.
      + inversion m.
    - dependent destruction m.
      + apply (H Fin.F1).
      + apply IHsts.
        * intro m0. apply (H (Fin.FS m0)).
        * auto.
  Qed.



  Theorem am_context_complete :                  forall t1 t2 {k} (c : context ick k) st,
      k |~ t1 >> t2 -> decompile st = c[t1] -> 
          exists n (sts : Vector.t configuration n) st,
          (**)Forall (fun st => decompile st = c[t1]) sts /\
          (**)decompile st = c[t2]                        /\
          (**)forall m : Fin.t (n+1), 
                  (c_eval t1 c :: sts ++ [st])[@m] → (sts ++ [st])[@m].

  Proof with eauto.
    intros t1 t2 k c st H H0.
    destruct H as [k2 [c2 [r [t [[H H1] [H2 H3]]]]]].
    assert (H4 : dec c[t1] ick (d_red r (c2~+c))).
    {
        constructor;
        solve [subst; simpl; eauto using dead_context_dead, plug_compose].
    }
    assert (~dead_ckind k2) by eauto using (proper_death2 [.]).
    apply dec_proc_eqv_dec in H4...
    destruct (dec_proc_sim _ _ _ [.] H4) as [n [sts [G [ [[G0 G1] | [ec [v [G1 G0]]]] G2] ]]];
        rewrite <- (compose_empty c) in *;
        rewrite <- (compose_empty (c2~+c)) in *;
        exists n sts (c_eval t (c2 ~+ c));
    (
        split;
        [ auto
        | split;
        [ simpl; rewrite plug_compose; congruence
        | apply local1; eauto;
          unfold configuration; (*sic*)
          rewrite G0
        ] ]
    );
    [ econstructor 1 | econstructor 4 ]...
  Qed.



  Corollary am_complete :                                                forall t1 t2 st,
      t1 >> t2 -> decompile st = t1 -> 
          exists n (sts : Vector.t configuration n) st,
          (**)Forall (fun st => decompile st = t1) sts /\
          (**)decompile st = t2                        /\
          (**)forall m : Fin.t (n+1), 
                  (c_eval t1 [.] :: sts ++ [st])[@m] → (sts ++ [st])[@m].
  Proof with eauto.
    intros.
    apply (am_context_complete t1 t2 [.] st)...
  Qed.



  Axiom init_ckind_alive : ~dead_ckind ick.


  Lemma vec_last_by_index : forall {T n} (v : Vector.t T (S n)) (H : n < S n), 
      last v = v[@ Fin.of_nat_lt H].

  Proof.
    intros.
    dependent induction v.
    destruct v.
    - auto.
    - apply (IHv n (h0 :: v)); auto.
  Qed.



  Lemma no_silent_loops_eval : forall t {k} (c : context ick k),
      ~ exists sts : nat -> configuration, 
          sts 0 = c_eval t c /\
          forall n, sts n → sts (S n) /\ ~ decompile (sts n) >> decompile (sts (S n)).

  Proof with eauto using init_ckind_alive.
    intros t k c [sts [H H0]].
    destruct (decompose c[t] ick) as [d H1]...
    assert (H2 : ~dead_ckind k).
    { intro H2; apply dec_term_from_dead with t k in H2. 
      destruct (H0 0) as [H3 _].
      rewrite H in H3.
      inversion H3; congruence. }
    apply dec_proc_eqv_dec in H1...
    destruct (dec_proc_sim _ _ _ [.] H1) as [n [sts' [H3 [H4 H5]]]].
    rewrite <- (compose_empty c) in *.
    cut (forall m, (sts 0 :: sts')[@m] = sts m).
    {
        intro H6.
        destruct d.
        - rewrite <- (compose_empty c0) in *.
          destruct H4 as [[G G0] | [ec [v [G0 G]]]];
              assert (H7 : n < S n) by eauto with arith;
              rewrite vec_last_by_index with _ H7 in G;
              rewrite <- H in G;
              rewrite H6 in G;
              destruct (H0 (Fin.of_nat_lt H7)) as [H8 H9];
              rewrite G in H8;
              dependent destruction H8; dep_subst; try congruence;
              replace r0 with r in * by congruence;
              apply H9.
          + rewrite G; rewrite <- x.
            simpl.
            exists k' c0 r t1.
            intuition unfold dec... 
          + rewrite G; rewrite <- x.
            simpl.
            assert (H10 := dec_context_correct ec k' v); rewrite H4 in H10.
            rewrite H10.
            exists k' c0 r t0.
            intuition unfold dec...
        - assert (H7 : n < S n) by eauto with arith;
          rewrite vec_last_by_index with _ H7 in H4.
          rewrite <- H in H4.
          rewrite H6 in H4.
          destruct (H0 (Fin.of_nat_lt H7)) as [H8 _].
          rewrite H4 in H8.
          inversion H8.
    }
    rewrite <- H in H5.
    clear t k c H d H1 H2 H3 H4. 
    remember (sts 0) as st. revert sts H0 st Heqst H5.
    induction sts'; intros.
    - dependent destruction m.
      + auto. 
      + inversion m.
    - dependent destruction m. 
      + auto.
      + eapply (IHsts' (fun n => sts (S n)))...
        * destruct (H0 0) as [H1 _].
          assert (H2 := H5 Fin.F1); simpl in H2.
          rewrite <- Heqst in H1.
          rewrite trans_computable in H1, H2.
          destruct H1, H2.
          unfold next_conf in H, H1; congruence.
        * intro m0. apply (H5 (Fin.FS m0)).
  Qed.


  Lemma no_silent_loops_apply : forall {k} v (c : context ick k),
      ~ exists sts : nat -> configuration, 
          sts 0 = c_apply c v /\
          forall n, sts n → sts (S n) /\ ~ decompile (sts n) >> decompile (sts (S n)).

  Proof with eauto using init_ckind_alive.
    intros k v c [sts [H H0]].
    destruct (decompose c[v] ick) as [d H1]...
    assert (H2 : ~dead_ckind k).
    { destruct (H0 0) as [H3 _].
      rewrite H in H3.
      inversion H3; dep_subst;
          intro H2; apply dec_context_from_dead with ec k0 v in H2; congruence. }
    apply dec_proc_eqv_dec in H1...
    apply dec_proc_val_eqv_decctx in H1.
    destruct (decctx_proc_sim _ _ _ [.] H1) as [n [sts' [H3 [H4 H5]]]].
    rewrite <- (compose_empty c) in *.
    cut (forall m, (sts 0 :: sts')[@m] = sts m).
    {
        intro H6.
        destruct d.
        - rewrite <- (compose_empty c0) in *.
          destruct H4 as [[G G0] | [ec [v0 [G0 G]]]];
              assert (H7 : n < S n) by eauto with arith;
              rewrite vec_last_by_index with _ H7 in G;
              rewrite <- H in G;
              rewrite H6 in G;
              destruct (H0 (Fin.of_nat_lt H7)) as [H8 H9];
              rewrite G in H8;
              dependent destruction H8; dep_subst; try congruence;
              replace r0 with r in * by congruence;
              apply H9.
          + rewrite G; rewrite <- x.
            simpl.
            exists k' c0 r t0.
            intuition unfold dec... 
          + rewrite G; rewrite <- x.
            simpl.
            assert (H10 := dec_context_correct ec k' v0); rewrite H4 in H10.
            rewrite H10.
            exists k' c0 r t.
            intuition unfold dec...
        - assert (H7 : n < S n) by eauto with arith;
          rewrite vec_last_by_index with _ H7 in H4.
          rewrite <- H in H4.
          rewrite H6 in H4.
          destruct (H0 (Fin.of_nat_lt H7)) as [H8 _].
          rewrite H4 in H8.
          inversion H8.
    }
    rewrite <- H in H5.
    clear v k c H d H1 H2 H3 H4. 
    remember (sts 0) as st. revert sts H0 st Heqst H5.
    induction sts'; intros.
    - dependent destruction m.
      + auto. 
      + inversion m.
    - dependent destruction m. 
      + auto.
      + eapply (IHsts' (fun n => sts (S n)))...
        * destruct (H0 0) as [H1 _].
          assert (H2 := H5 Fin.F1); simpl in H2.
          rewrite <- Heqst in H1.
          rewrite trans_computable in H1, H2.
          destruct H1, H2.
          unfold next_conf in H, H1; congruence.
        * intro m0. apply (H5 (Fin.FS m0)).
  Qed.
  

  Theorem no_silent_loops :
      ~ exists sts : nat -> configuration,
          forall n, sts n → sts (S n) /\ ~ decompile (sts n) >> decompile (sts (S n)).

  Proof with eauto.
    intros [sts H].
    remember (sts 0) as st.
    destruct st.
    - apply (no_silent_loops_eval t c)...
    - apply (no_silent_loops_apply v c)...
  Qed.

End RefEvalApplyMachine_Facts.




(*Module PushEnterMachine_Facts (R : RED_LANG) (PERS : PE_RED_REF_SEM R) 
                                        (PEM : REF_PUSH_ENTER_MACHINE R PERS).

  Module PENS  := PE_RefNaturalSem R PERS.
  Module PENSF := PE_RefNaturalSem_Facts R PERS PENS.
  Import R PERS.ST.
  Import PEM.



  Local Hint Constructors PEM.trans PEM.trans_close PENS.dec.


  Lemma dec_PENS_eqv_PEM : forall {t} {k1 k2} {c : context k1 k2} {v}, 
                               PENS.dec t c v <-> c_eval t c →+ c_fin v.
  Proof with eauto.
    intros t k1 k2 v; split; intro H.

  (* -> *) {
    induction H...
  }

  (* <- *) {
    dependent induction H;
        match goal with H : _ → _ |- _ => 
            dependent_destruction2 H end;
    solve 
    [ eauto
    | inversion H0 as [? ? H | ? ? ? H ]; inversion H
    | constructor; auto;
      intro H; 
      assert (H0 := dec_term_from_dead t _ H); rewrite H0 in *; 
      discriminate ].
  }
  Qed.


  Lemma eval_PENS_eqv_PEM : forall {t v}, PENS.eval t v <-> PEM.eval t v.
  Proof.
    intros t v; split; intro H;
    solve
    [ dependent destruction H; constructor; apply dec_PENS_eqv_PEM; eauto ].
  Qed.


  Theorem dec_iter_composition :
      forall {t k1 k2} {c : context k1 k2} {v},
          (exists d, PERS.dec t c d /\ PERS.iter d v) <-> c_eval t c →+ c_fin v.
  Proof.
    etransitivity; eauto using PENSF.dec_iter_composition, dec_PENS_eqv_PEM.
  Qed.


  Theorem eval_preserved : forall {t v}, PERS.eval t v <-> PEM.eval t v.

  Proof. etransitivity; eauto using PENSF.eval_preserved, eval_PENS_eqv_PEM. Qed.

End PushEnterMachine_Facts.*)
