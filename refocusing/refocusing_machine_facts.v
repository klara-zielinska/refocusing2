Require Import Program
               Fin2 
               Vector2
               Subset
               Util
               rewriting_system
               rewriting_system_following
               refocusing_semantics
               refocusing_machine
               reduction_languages_facts
               reduction_semantics_facts 
               reduction_strategy_facts
               refocusing_semantics_facts.
        Import rewriting_system.Paths.




Local Open Scope vector.

Module SloppyRefEvalApplyMachine_Facts (R   : RED_REF_SEM) 
                                       (EAM : SLOPPY_REF_EVAL_APPLY_MACHINE R).

  Module RLF := RED_LANG_Facts R.
  Module RSF := RED_STRATEGY_STEP_Facts R R.ST.
  Module RF := RED_REF_SEM_Facts R.
  Import R.R R RLF RSF RF ST EAM.


  Notation eam := EAM.rws.
  Notation rs  := R.rws.


  Local Hint Constructors EAM.trans clos_trans_1n.
  Local Hint Unfold transition.


  Theorem decompile_surj : 
      forall t, exists st, decompile st = t.

  Proof.
    intro t.
    exists (c_eval t [.]).
    auto.
  Qed.


  Theorem am_correct :                                                    forall st1 st2,
      `(eam) st1 → st2 -> decompile st1 = decompile st2 \/ 
                              `(rs) decompile st1 → decompile st2.

  Proof with eauto.
    intros st1 st2 H.
    inversion H; subst;
        try match goal with 
        | H : dec_term ?t ?k = _ |- _ =>
              assert (G := dec_term_correct t k);
              rewrite H in G
        | H : dec_context ?ec ?k ?v = _ |- _ =>
              assert (G := dec_context_correct ec k v);
              rewrite H in G
        end;

    try solve 
    [ left; 
      simpl; congruence ].

    - right.
      simpl; unfold reduce, dec.
      exists k, c, r, t0.
      intuition.
      + eapply proper_death_trans...
      + simpl.
        congruence.

    - right.
      simpl; unfold reduce, dec.
      exists k, c, r, t.
      intuition.
      + eapply proper_death_trans...
      + simpl.
        congruence.
  Qed.



  Lemma refocus_in_sim :             forall t {k1 k2} (d : decomp k1) (c : context k1 k2)
                                                                   (c0 : context ick k1),
      refocus_in t c d ->
          exists n (sts : Vector.t configuration n), (*such that: *)

          (**)Forall (fun st => decompile st = (c~+c0)[t] /\ alive_state st) sts /\

          (**)match d with 
              | d_val v => last (c_eval t (c ~+ c0) :: sts) = c_apply c0 v 

              | @d_red _ k r c' => 
                           last (c_eval t (c ~+ c0) :: sts) = c_eval r (c'~+c0) /\
                           dec_term r k = in_red r  \/

                           exists ec v, dec_context ec k v = in_red r /\
                           last (c_eval t (c ~+ c0) :: sts) = c_apply (ec=:c'~+c0) v
              end /\

          (**)path (c_eval t (c~+c0) :: sts).

  Proof with eauto.
    intros t k1 k2 d c c0 H.
    induction H using refocus_in_Ind with
    (P0 := fun k2 (v' : R.value k2) (c : context k1 k2) d _ =>

        exists n (sts : Vector.t configuration n),

        (**)Forall (fun st => decompile st = (c ~+ c0) [v'] /\ alive_state st) sts /\

        (**)match d with 
            | d_val v  => last (c_apply (c ~+ c0) v' :: sts) = c_apply c0 v 

            | @d_red _ k r c' => 
                          last (c_apply (c ~+ c0) v' :: sts) = c_eval r (c'~+c0) /\
                          dec_term r k = in_red r  \/

                          exists ec v, dec_context ec k v = in_red r /\
                          last (c_apply (c ~+ c0) v' :: sts) = c_apply (ec=:c'~+c0) v
            end /\

        (**)path (c_apply (c ~+ c0) v' :: sts)
    );

        subst;
        try destruct IHrefocus_in as [n [sts [H0 [H1 H2]]]]; auto;
        repeat match goal with
        | H : dec_term ?t ?k = _ |- _ => 
              assert (G := dec_term_correct t k);
              rewrite H in G
        | H : dec_context ?ec ?k ?v = _ |- _ => 
              assert (G := dec_context_correct ec k v);
              rewrite H in G
        end;
        subst;

    [ exists    0,  [](configuration)
    | exists (S n), (c_apply (c~+c0) v :: sts)
    | exists (S n), (c_eval t0 (ec =: c~+c0) :: sts) 
    | exists    0,  [](configuration)
    | exists    0,  [](configuration)
    | exists (S n), (c_apply (c ~+ c0) v0 :: sts)
    | exists (S n), (c_eval t (ec0 =: c ~+ c0) :: sts) ];

    solve 
    [ split; [ | split ];

    [ constructor; simpl; 
      try rewrite G; 
      eauto using dec_term_val_alive, dec_term_next_alive, 
                  dec_context_val_alive, dec_context_next_alive

    | eauto

    | intro m;
      dependent_destruction2 m; 
      solve
      [ simpl; eauto 
      | apply H2 ]
    ] ].
  Qed.



  Lemma refocus_out_sim :                         forall {k1 k2} v' d (c : context k1 k2)
                                                                   (c0 : context ick k1),
      refocus_out v' c d ->
          exists n (sts : Vector.t configuration n),

          (**)Forall (fun st => decompile st = (c ~+ c0) [v'] /\ alive_state st) sts /\

          (**)match d with 
              | d_val v => last (c_apply (c ~+ c0) v' :: sts) = c_apply c0 v 

              | @d_red _ k r c' => 
                           last (c_apply (c ~+ c0) v' :: sts) = c_eval r (c'~+c0) /\
                           dec_term r k = in_red r \/

                           exists ec v, dec_context ec k v = in_red r /\
                           last (c_apply (c ~+ c0) v' :: sts) = c_apply (ec=:c'~+c0) v
              end /\

          (**)path (c_apply (c ~+ c0) v' :: sts).

  Proof with eauto.
    intros k1 k2 v' d c c0 H.
    induction H using refocus_out_Ind with
    (P := fun k2 t (c : context k1 k2) d (_ : refocus_in t c d) =>

        exists n (sts : Vector.t configuration n),

        (**)Forall (fun st => decompile st = (c ~+ c0) [t] /\ alive_state st) sts /\

        (**)match d with 
            | d_val v => last (c_eval t (c ~+ c0) :: sts) = c_apply c0 v 

            | @d_red _ k r c' => 
                         last (c_eval t (c ~+ c0) :: sts) = c_eval r (c'~+c0) /\
                         dec_term r k = in_red r \/

                         exists ec v, dec_context ec k v = in_red r           /\
                         last (c_eval t (c ~+ c0) :: sts) = c_apply (ec=:c'~+c0) v
            end /\

        (**)path (c_eval t (c ~+ c0) :: sts)
    );

         subst;
         try destruct IHrefocus_out as [n [sts [H0 [H1 H2]]]]; auto;
         repeat match goal with
         | H : dec_term ?t ?k = _ |- _ => 
               assert (G := dec_term_correct t k);
               rewrite H in G
         | H : dec_context ?ec ?k ?v = _ |- _ => 
               assert (G := dec_context_correct ec k v);
               rewrite H in G
         end;
         subst;

    [ exists    0,  [](configuration)
    | exists (S n), (c_apply (c~+c0) v :: sts)
    | exists (S n), (c_eval t0 (ec =: c~+c0) :: sts) 
    | exists    0,  [](configuration)
    | exists    0,  [](configuration)
    | exists (S n), (c_apply (c ~+ c0) v0 :: sts)
    | exists (S n), (c_eval t (ec0 =: c ~+ c0) :: sts) ];

    solve [ split; [ | split ];
    [ constructor; simpl; 
      try rewrite G; 
      eauto using dec_term_val_alive, dec_term_next_alive, 
                  dec_context_val_alive, dec_context_next_alive

    | eauto

    | intro m;
      dependent_destruction2 m; 
      solve
      [ simpl; eauto 
      | apply H2 ]
    ] ].
  Qed.



  Lemma am_context_complete_eval :                forall t1 t2 {k} (c : context ick k) t,

      `(rs) t1 → t2  ->  ~dead_ckind k  ->  t1 = c[t] ->
          exists n (sts : Vector.t configuration n) st,

          (**)Forall (fun st => decompile st = t1 /\ alive_state st) sts /\
          (**)(decompile st = t2 /\ alive_state st)                      /\
          (**)path (c_eval t c :: sts ++ [st]).

  Proof with eauto.
    intros t1 t2 k c t H H0 H1.
    destruct H as [k2 [c2 [r [t' [[H H2] [H3 H4]]]]]].
    assert (H5 : dec c[t] ick (d_red r c2)).
    {
        constructor;
        solve [subst; simpl; eauto using dead_context_dead, plug_compose].
    }
    assert (~dead_ckind k2) by eauto using (proper_death2 [.]).
    apply refocus_in_eqv_dec in H5...
    destruct (refocus_in_sim _ _ _ [.] H5) as [n [sts [G [G1 G2] ]]];
    destruct                          G1 as [[G0 G1] | [ec [v [G1 G0]]]];
        rewrite <- (compose_empty c) in *;
        rewrite <- (compose_empty (c2)) in *;
        exists n, sts, (c_eval t' c2);
    (
        split; [ | split];
        [ rewrite H1; auto
        | auto
        | apply (path_snoc (c_eval t c :: sts)); eauto;
          rewrite G0
        ]
    );
    [ econstructor 1 | econstructor 4 ]...
  Qed.


  Lemma am_context_complete_apply : forall t1 t2 {k} (c : context ick k) (v : R.value k),

      `(rs) t1 → t2 ->  ~dead_ckind k  ->  t1 = c[v]  ->
          exists n (sts : Vector.t configuration n) st,

          (**)Forall (fun st => decompile st = t1 /\ alive_state st) sts /\
          (**)(decompile st = t2 /\ alive_state st)                      /\
          (**)path (c_apply c v :: sts ++ [st]).

  Proof with eauto.
    intros t1 t2 k c v H H0 H1.
    destruct H as [k2 [c2 [r [t' [[H H2] [H3 H4]]]]]].
    assert (H5 : dec c[v] ick (d_red r c2)).
    {
        constructor;
        solve [subst; simpl; eauto using dead_context_dead, plug_compose].
    }
    assert (~dead_ckind k2) by eauto using (proper_death2 [.]).
    apply refocus_in_eqv_dec in H5...
    apply refocus_in_val_eqv_refocus_out in H5.
    destruct (refocus_out_sim _ _ _ [.] H5) as [n [sts [G [G1 G2] ]]];
    destruct                             G1 as[[G0 G1] | [ec [v' [G1 G0]]]];
        rewrite <- (compose_empty c) in *;
        rewrite <- (compose_empty (c2)) in *;
        exists n, sts, (c_eval t' c2);
    (
        split; [ | split];
        [ rewrite H1; auto
        | auto
        | apply (path_snoc (c_apply c v :: sts)); eauto;
          rewrite G0
        ]
    );
    [ econstructor 1 | econstructor 4 ]...
  Qed.



  Corollary am_complete :                                               forall t1 t2 st1,
      `(rs) t1 → t2 -> alive_state st1 -> decompile st1 = t1 -> 
          exists n (sts : Vector.t configuration n) st2,
          (**)Forall (fun st => decompile st = t1 /\ alive_state st) sts /\
          (**)(decompile st2 = t2 /\ alive_state st2)                    /\
          (**)path (st1 :: sts ++ [st2]).

  Proof with eauto.
    intros t1 t2 st1 H H0 H1.
    destruct st1.
    - apply am_context_complete_eval...
    - eapply am_context_complete_apply...
  Qed.



  Lemma no_silent_loops_eval :                          forall t {k} (c : context ick k),

      ~exists sts : nat -> configuration, 

      (**)sts 0 = c_eval t c /\

      (**)forall n, `(eam) sts n → sts (S n) /\ 
                    ~ `(rs) decompile (sts n) → decompile (sts (S n)).

  Proof with eauto using init_ckind_alive.
    intros t k c [sts [H H0]].
    destruct (decompose c[t] ick) as [d H1]...
    assert (~dead_ckind k).
    {
        intro H2; apply dec_term_from_dead with t k in H2. 
        destruct (H0 0) as [H3 _].
        rewrite H in H3.
        inversion H3;
        congruence.
    }
    apply refocus_in_eqv_dec in H1...
    destruct (refocus_in_sim _ _ _ [.] H1) as [n [sts' [H3 [H4 H5]]]].
    rewrite <- (compose_empty c) in *.
    assert (H6 : forall m, (sts 0 :: sts')[@m] = sts m).
    {
        rewrite <- H in H5.
        clear t k c H d H1 H2 H3 H4; remember (sts 0) as st; revert sts H0 st Heqst H5;
        induction sts'; 
            intros sts H0 st Heqst H5 m;
            dependent destruction m.
        - auto.
        - inversion m.
        - auto.
        - eapply (IHsts' (fun n => sts (S n)))...
          + destruct (H0 0) as [H1 _].
            assert (H2 := H5 Fin.F1); simpl in H2.
            rewrite <- Heqst in H1.
            rewrite trans_computable in H1, H2.
            destruct H1, H2.
            unfold next_conf in H, H1.
            congruence.
          + intro m0.
            apply (H5 (Fin.FS m0)).
    }
    destruct d as [k' r c0 | v].
    - rewrite <- (compose_empty c0) in *.
      destruct H4 as [[G G0] | [ec [v [G0 G]]]];
          assert (H7 : n < S n) by eauto with arith;
          rewrite vec_last_by_index with _ H7 in G;
          rewrite <- H in G;
          rewrite H6 in G;
          destruct (H0 (Fin.of_nat_lt H7)) as [H8 H9];
          rewrite G in H8; compute in H8;
          dependent destruction H8 (*as [r0 t1/t0 x]*); dep_subst; try congruence;
          replace r0 with r in * by congruence;
          apply H9.
      + rewrite G; compute; rewrite <- x.
        exists k', c0, r, t1.
        intuition unfold dec... 
      + rewrite G; compute; rewrite <- x.
        assert (H10 := dec_context_correct ec k' v); rewrite H4 in H10.
        rewrite H10.
        exists k', c0, r, t0.
        intuition unfold dec...
    - assert (H7 : n < S n) by eauto with arith;
      rewrite vec_last_by_index with _ H7 in H4.
      rewrite <- H in H4.
      rewrite H6 in H4.
      destruct (H0 (Fin.of_nat_lt H7)) as [H8 _].
      rewrite H4 in H8.
      inversion H8.
  Qed.



  Lemma no_silent_loops_apply :                         forall {k} v (c : context ick k),

      ~exists sts : nat -> configuration, 

      (**)sts 0 = c_apply c v /\

      (**)forall n, `(eam) sts n → sts (S n) /\ 
                    ~ `(rs) decompile (sts n) → decompile (sts (S n)).

  Proof with eauto using init_ckind_alive.
    intros k v c [sts [H H0]].
    destruct (decompose c[v] ick) as [d H1]...
    assert (~dead_ckind k).
    {
        destruct (H0 0) as [H3 _].
        rewrite H in H3.
        inversion H3; dep_subst;
        match goal with H : dec_context ?ec ?k0 ?v = _ |- _ =>
        intro H2; apply dec_context_from_dead with ec k0 v in H2; 
        congruence
        end.
    }
    apply refocus_in_eqv_dec in H1...
    apply refocus_in_val_eqv_refocus_out in H1.
    destruct (refocus_out_sim _ _ _ [.] H1) as [n [sts' [H3 [H4 H5]]]].
    rewrite <- (compose_empty c) in *.
    assert (H6 : forall m, (sts 0 :: sts')[@m] = sts m).
    {
        rewrite <- H in H5.
        clear k v c H d H1 H2 H3 H4; remember (sts 0) as st; revert sts H0 st Heqst H5;
        induction sts'; 
            intros sts H0 st Heqst H5 m;
            dependent destruction m.
        - auto.
        - inversion m.
        - auto.
        - eapply (IHsts' (fun n => sts (S n)))...
          + destruct (H0 0) as [H1 _].
            assert (H2 := H5 Fin.F1); simpl in H2.
            rewrite <- Heqst in H1.
            rewrite trans_computable in H1, H2.
            destruct H1, H2.
            unfold next_conf in H, H1.
            congruence.
          + intro m0.
            apply (H5 (Fin.FS m0)).
    }
    destruct d as [k' r c0 | v0].
    - rewrite <- (compose_empty c0) in *.
      destruct H4 as [[G G0] | [ec [v0 [G0 G]]]];
          assert (H7 : n < S n) by eauto with arith;
          rewrite vec_last_by_index with _ H7 in G;
          rewrite <- H in G;
          rewrite H6 in G;
          destruct (H0 (Fin.of_nat_lt H7)) as [H8 H9];
          rewrite G in H8; compute in H8;
          dependent destruction H8 (*as [r0 t0/t x]*); dep_subst; try congruence;
          replace r0 with r in * by congruence;
          apply H9.
      + rewrite G; compute; rewrite <- x.
        exists k', c0, r, t0.
        intuition unfold dec... 
      + rewrite G; compute; rewrite <- x.
        assert (H10 := dec_context_correct ec k' v0); rewrite H4 in H10.
        rewrite H10.
        exists k', c0, r, t.
        intuition unfold dec...
    - assert (H7 : n < S n) by eauto with arith;
      rewrite vec_last_by_index with _ H7 in H4.
      rewrite <- H in H4.
      rewrite H6 in H4.
      destruct (H0 (Fin.of_nat_lt H7)) as [H8 _].
      rewrite H4 in H8.
      inversion H8.
  Qed.



  Theorem no_silent_loops :
      ~ exists sts : nat -> configuration,
          forall n, `(eam) sts n → sts (S n) /\ 
                    ~ `(rs) decompile (sts n) → decompile (sts (S n)).

  Proof with eauto.
    intros [sts H].
    remember (sts 0) as st.
    destruct st.
    - apply (no_silent_loops_eval t c)...
    - apply (no_silent_loops_apply v c)...
  Qed.



  Instance safe_region_map                                                            {P}
      `(R.SafeKRegion init_ckind P) : 
      EAM.SafeRegion (fun st => alive_state st /\ P (decompile st)).

  Proof with eautof. split.

  (* preservation: *) {
    intros st1 st2 [H1 H2] H3.
    split.
    - eapply trans_alive...
    - destruct (am_correct _ _ H3).
      + congruence.
      + eapply R.preservation...
  }

  (* progress: *) {
    intros st1 [H1 H2].
    destruct st1.
    {
        right.
        remember (dec_term t k) as DEC eqn: H3; symmetry in H3.
        assert (H4 := dec_term_correct t k); rewrite H3 in H4.
        destruct DEC; subst;
        try solve
        [ autof
        | eexists; compute; eauto]. 
        - assert (~dead_ckind k) by auto using (proper_death2 [.]). 
          destruct (R.progress _ H2) as [[v H4] | [t2 H4]].
          + apply value_trivial in H4...
            destruct H4 as [v' H4]; symmetry in H4.
            apply value_redex in H4...
          + destruct (am_complete _ _ (c_eval r c) H4) as [n [sts [st2 [G [G0 G1]]]]]...
            destruct sts as [ | st n sts];
            [ exists st2 | exists st ]; 
            apply (G1 F1).
    }

    {
        destruct c as [ | ec k c].
        - left; exists v...
        - right.
          remember (dec_context ec k v) as DEC eqn: H3; symmetry in H3.
          assert (H4 := dec_context_correct ec k v); rewrite H3 in H4.
          destruct DEC; subst;
          try solve
          [ autof
          | eexists; compute; eauto].
          + assert (~dead_ckind k) by auto using (proper_death2 [.]). 
            destruct (R.progress _ H2) as [[v0 H5] | [t2 H5]].
            * simpl in H5; rewrite H4 in H5.
              apply value_trivial in H5...
              destruct H5 as [v' H5]; symmetry in H5.
              apply value_redex in H5...
            * destruct (am_complete _ _ (c_apply (ec=:c) v) H5) 
                                                        as [n [sts [st2 [G [G0 G1]]]]]...
              destruct sts as [ | st n sts];
              [ exists st2 | exists st ]; 
              apply (G1 F1).
    }
  }
  Qed.

End SloppyRefEvalApplyMachine_Facts.





Module RefEvalApplyMachine_Facts                                (R : PRECISE_RED_REF_SEM)
                                                        (EAM : REF_EVAL_APPLY_MACHINE R).

  Module RAWF := SloppyRefEvalApplyMachine_Facts R EAM.RAW.
  Import R EAM.


  Instance following : RW_FOLLOWING EAM.rws R.rws := 
  {
      semantics := EAM.decompile;
      correct   := RAWF.am_correct
  }.

  Proof with eauto.

  (*semantics_surj:*) {
    intro t.
    exists (submember_by alive_state (c_eval t [.]) init_ckind_alive).
    auto.
  }

  (*complete:*) {
    intros t1 t2 st1 H H0.
    assert (alive_state st1).
    { destruct st1; eapply (witness_elim)... }
    destruct (RAWF.am_complete t1 t2 st1 H) as [n [sts [st2 [H2 [[H3 H4] H5]]]]]...
    set (sts' := map2forall _ (fun st H => submember_by _ st (proj2 H)) sts H2).

    exists n, sts', (submember_by _ st2 H4).
    split; [| split].
    - clear st2 H3 H4 H5.
      induction sts as [ | st1' ? sts].
      + constructor.
      + dependent destruction H2 (*as [p ?]*); dep_subst.
        destruct p as [H3 H4].
        constructor.
        * clear.
          destruct st1', st1; auto.
        * apply IHsts.
    - destruct st2; auto.
    - apply (path_snoc (st1::sts') (submember_by alive_state st2 H4)).
      + clear H0 H1; revert st1 H5.
        induction sts as [ | st1' ? sts]; 
            intros st1 H5 m;
            dependent destruction m;
            dependent destruction H2; dep_subst.
        * destruct st1';
          solve [ apply (H5 Fin.F1) ].
        * apply IHsts.
          intro m0.
          destruct st1';
          apply (H5 (Fin.FS m0)).
      + clear H0 H1; revert st1 H5.
        induction sts as [ | st1' ? sts]; 
            intros st1 H5.
        * destruct st2; 
          solve [ apply (H5 Fin.F1) ].
        * dependent destruction H2; dep_subst.
          apply IHsts.
          intro m.
          destruct st1';
          apply (H5 (Fin.FS m)).
  }

  (*no_silent_loops:*) {
    intros [crs H].
    apply RAWF.no_silent_loops.
    exists crs.
    solve [intuition].
  }
  Qed.



  Instance safe_region_map                                                            {P}
      `(R.SafeKRegion init_ckind P) : 
      EAM.SafeRegion (fun st => P (decompile st)).

  Proof. split.

  (*preservation:*) {
      intros [st1 H1] [st2 H2] H3 H4.
      assert (H5 := witness_elim _ _ H1).
      destruct (RAW.preservation st1 st2);
      solve [intuition].
  }

  (*progress:*) {
      intros [st1 H1] H2.
      assert (H3 := witness_elim _ _ H1).
      destruct (RAW.progress st1) as [[v H4] | [st2 H4]]; try solve [intuition];
          subst.
      - left. exists v. auto.
      - right.
        assert (H5 : alive_state st2) by eauto using trans_alive.
        exists (submember_by _ st2 H5).
        auto.
  }
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

