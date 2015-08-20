Require Import Program.
Require Export refocusing_signatures.
Require Import refocusing_lang_facts.
Require Import Wellfounded.Inclusion.
Require Import Wellfounded.Inverse_Image.


Module RedRefSem (R : RED_REF_LANG) <: RED_REF_SEM R.R.

  Import R.R.
  Import R.
  Module RRF := RED_LANG_Facts R.R.
  Import RRF.


  Inductive dec : term -> forall {k1 k2}, context k1 k2 -> decomp k1 -> Prop :=

  | d_dec  : forall t {k1 k2} (c : context k1 k2) {r},
               dec_term t k2 = in_red r -> 
               dec t c (d_red r c)
  | d_v    : forall t {k1 k2} {c : context k1 k2} {v d},
               dec_term t k2 = in_val v ->
               decctx v c d ->
               dec t c d
  | d_term : forall t {t0 k1 k2} {c : context k1 k2} {ec d},
               dec_term t k2 = in_term t0 ec ->
               dec t0 (ec=:c) d ->
               dec t c d

  with decctx : forall {k2}, value k2 -> 
                    forall {k1}, context k1 k2 -> decomp k1 -> Prop :=

  | dc_end  : forall {k} (v : value k), 
                ~ dead_ckind k ->
                decctx v [.] (d_val v)
  | dc_dec  : forall ec {k2} (v : value (k2+>ec)) {k1} (c : context k1 k2) {r},
                dec_context ec k2 v = in_red r ->
                decctx v (ec=:c) (d_red r c)
  | dc_val  : forall {k2} {v0 : value k2} ec (v : value (k2+>ec)) 
                     {k1} {c  : context k1 k2} {d},
                dec_context ec k2 v = in_val v0 ->
                decctx v0 c d ->
                decctx v (ec=:c) d
  | dc_term : forall ec {ec0 k2} (v : value (k2+>ec)) 
                            {k1} {c : context k1 k2} {t d},
                dec_context ec k2 v = in_term t ec0 ->
                dec t (ec0=:c) d ->
                decctx v (ec=:c) d.

  Scheme dec_Ind    := Induction for dec Sort Prop
    with decctx_Ind := Induction for decctx Sort Prop.


  Lemma sto_trans : forall t t0 t1,  t <| t0  ->  t0 <| t1  ->  t <| t1.
  Proof with eauto.
    induction 1.
    - econstructor 2...
    - econstructor 2. 
      + eauto.
      + apply IHclos_trans_1n...
  Qed.


  Lemma plug_le_eq : forall {k1 k2} (c : context k1 k2) t t0, c[t0] = t -> 
                         t0 <| t \/ (c ~= @empty k1 /\ t = t0).
  Proof with eauto.
    intros k1 k2;
    induction c; intros.
    - simpl in H...
    - left; simpl in H.
      destruct (IHc t ec:[t0]). 
      + eauto.
      + apply t1n_trans with (y := ec:[t0]).
        * econstructor... 
        * assumption. 
      + destruct H0. 
        subst; rewrite H1.
        do 2 econstructor...
  Qed.


  Lemma st_c : forall t0 t1, t0 <| t1 -> 
                   forall k1, exists k2 (c : context k1 k2), c[t0] = t1.
  Proof with eauto.
    intros t0 t1 H k1;
    induction H; intros.
    - inversion H; subst.
      exists (k1+>ec); eexists (ec=:[.]).
      simpl...
    - destruct IHclos_trans_1n as (k2, (c, H1)). 
      inversion H.
      subst.
      exists (k2+>ec); exists (ec=:c)...
  Qed.


  Lemma dec_not_dead : forall {t k1 k2} {c : context k1 k2} {d},
                           dec t c d -> ~ dead_ckind k2.
  Proof.
    intros; intro.
    assert (hh := dec_term_from_dead t k2 H0).
    destruct H;
    solve
    [ rewrite H in hh;
      discriminate hh ].
  Qed.


  Lemma decctx_not_dead : forall {k1 k2} {c : context k1 k2} {v d},
                              decctx v c d -> ~ dead_ckind k2.
  Proof with auto.
    intros; intro.
    destruct H;
    solve 
    [ intuition
    | assert (hh := dec_context_from_dead ec k2 v H0);
      rewrite H in hh;
      discriminate hh ].
  Qed.


  Lemma dec_context_not_dead : 
      forall ec1 k v ec2 t, ~ dead_ckind (k+>ec1) -> 
          dec_context ec1 k v = in_term t ec2 -> ~ dead_ckind (k+>ec2).
  Proof.
    intros.
    destruct (dec_context_term_next _ _ _ H0) as (H1, _).
    apply (ec_order_comp_fi _ _ _ _ H1).
  Qed.


  Lemma dec_val : forall {k2} (v : value k2) {k1} {c : context k1 k2} {d},
                      dec v c d -> decctx v c d.
  Proof with eauto.
    intros k2 v k1; remember (value_to_term v) as t; revert k2 v Heqt.
    induction t using (well_founded_ind wf_sto); intros; subst.

    dependent destruction H0;
        assert (hh := dec_term_correct v k2); rewrite H0 in hh.

    - contradiction (value_redex _ _ hh).

    - rewrite (value_to_term_injective _ _ hh)...

    - destruct (value_trivial v t0 _ (ec=:[.])); auto;
          try solve [eapply dec_term_next_alive; eassumption];
          destruct H2.

      + discriminateJM H3.

      + { clear H0; revert t0 H1 x hh H2.
        induction ec using (well_founded_ind (wf_eco k2 v)); intros.

        assert (decctx x (ec=:c) d).
          { apply (H t0)... do 2 econstructor... }

        dependent destruction H3;
            assert (G1 := ccons_inj _ _ _ _ x1 x);
            subst; rec_subst G1;

            assert (gg := dec_context_correct ec k2 x0); rewrite H3 in gg.

        - contradiction (value_redex v r); congruence.

        - assert (v0 = v).
            { apply (value_to_term_injective v0 v); congruence. }
          subst...

        - assert (~ dead_ckind (k2+>ec1)).
          {
              destruct ec_order_comp_fi with k2 v ec1 ec as (?, (?, (?, ?)))...
              - rewrite hh; eapply dec_context_term_next...
          }

          destruct (value_trivial v t _ (ec1=:[.])); auto;
              try solve 
              [ simpl; congruence];
              destruct H5.
          + discriminateJM H6.
          + eapply (H0 ec1); eauto.
            * rewrite hh; eapply dec_context_term_next; eauto.
            * congruence.
        }
  Qed.


  Lemma val_dec : forall {k2} {v : value k2} {k1} {c : context k1 k2} {d},
                      decctx v c d -> dec v c d.
  Proof with eauto.
    intros k2 v k1; remember (value_to_term v); revert k2 v Heqt.
    induction t using (well_founded_ind wf_sto); intros; subst.

    remember (dec_term v k2) as i;
    assert (hh := dec_term_correct v k2);
    destruct i; rewrite <- Heqi in hh; symmetry in Heqi.

    - contradict (value_redex _ _ hh).

    - apply (d_term _ Heqi).

      assert (~ dead_ckind (k2+>e)) as Hndk.
        { eapply dec_term_next_alive... }
      destruct (value_trivial v t _ (e=:[.]));
          try solve [auto];
          destruct H1.

      + discriminateJM H2.

      + { clear Heqi; revert e t hh Hndk x H1.
        induction e using (well_founded_ind (wf_eco k2 v)); intros.

        apply (H t) with (v := x)...
          { do 2 econstructor... }
        remember (dec_context e _ x) as i.
        assert (gg := dec_context_correct e _ x);
        destruct i; rewrite <- Heqi in gg; subst;
        symmetry in Heqi.

        - contradiction (value_redex v r); congruence.

        - assert (~ dead_ckind (k2+>e0)).
          {
              destruct ec_order_comp_fi with k2 v e0 e as (?, (?, (?, ?)))...
              - rewrite hh; eapply dec_context_term_next...
          }

          destruct (value_trivial v t0 _ (e0=:[.]));
              try solve [simpl; congruence];
              destruct H3.

          + discriminateJM H4.

          + apply dc_term with e0 t0...
            apply (H1 e0) with x0...
            * rewrite hh; eapply dec_context_term_next...
            * congruence.

        - eapply dc_val...
          assert (v0 = v).
          + apply (value_to_term_injective v0 v); congruence.
          + subst...

        - intuition.
      }

    - assert (H1 := value_to_term_injective _ _ hh); subst; econstructor...

    - contradiction (decctx_not_dead H0).
  Qed.



  Module RS : RED_SEM R.R with Definition dec := dec.

    Lemma decompose : 
        forall (t : term) k1, ~ dead_ckind k1 ->
            (exists (v : value k1), t = v) \/
            (exists k2 (r : redex k2) (c : context k1 k2), t = c[r]).

    Proof with eauto.
      induction t using (well_founded_ind wf_sto); intros.

      remember (dec_term t k1); assert (hh := dec_term_correct t k1);
      symmetry in Heqi;
      destruct i; rewrite Heqi in hh.

      - right; exists k1; exists r; eexists [.]...

      - destruct (H t0) with (k1 := k1+>e) as [(v, Hv) | (k2, (r, (c, Hrc)))].
            repeat econstructor...
            eapply dec_term_next_alive... 

        + { subst t0.
          assert (~ dead_ckind (k1+>e)) as Hndk.
            { eapply dec_term_next_alive... } 
          clear Heqi; generalize dependent v.
          induction e using (well_founded_ind (wf_eco k1 t)); intros.

          remember (dec_context e _ v); assert (ht := dec_context_correct e _ v); 
          destruct i; rewrite <- Heqi in ht; try rewrite <- hh in ht.

          - right; exists k1; exists r; eexists [.]...

          - destruct (H t0) with (k1 := k1+>e0) as [(v0, Hv) | (k2, (r, (c, Hrc)))].
                repeat econstructor...
                eapply dec_context_not_dead...

            + symmetry in Heqi.
              destruct (dec_context_term_next _ _ _ Heqi) as (H2, _).

              subst t0.
              assert (~ dead_ckind (k1+>e0)) as Hndk2.
                { eapply dec_context_not_dead... }
              rewrite <- hh in H2.
              destruct (H1 e0 H2 Hndk2 v0 ht) as [(v1, Hv1) | (k2, (r, (c, Hrc)))].
              * left; exists v1...
              * right; exists k2; exists r; exists c...

            + right; exists k2; exists r; exists (c~+e0=:[.]).
              subst t0; rewrite plug_compose...

          - left; exists v0...

          - intuition. 
          }

        + right; exists k2; exists r; exists (c~+(e=:[.])).
          subst t0; rewrite plug_compose...

      - left; exists v...

      - intuition.
    Qed. 


    Lemma dec_redex_self_e : forall {k} (r : redex k), dec r [.] (d_red r [.]).
    Proof with eauto.
      intros; 
      remember (dec_term r k).
      assert (~ dead_ckind k).
        { eapply proper_death2... apply [.]. }

      destruct i;
          assert (hh := dec_term_correct r k);
          rewrite <- Heqi in hh; 
          simpl in hh; try symmetry in hh.

      - apply redex_to_term_injective in hh; subst; constructor...

      - symmetry in Heqi; assert (H0 := dec_term_term_top _ _ Heqi).
        assert (~ dead_ckind (k+>e)) as Hndk.
          { eapply dec_term_next_alive... } 
        econstructor 3...
        destruct (redex_trivial r t _ (e=:[.]) hh) as [(H1, H2) | (v, H1)]...

        + discriminateJM H2. 

        + { subst t.
          clear H0 Heqi; generalize dependent v; generalize dependent e.
          induction e using (well_founded_ind (wf_eco k r)); intros.

          apply val_dec.
          remember (dec_context e _ v); assert (ht := dec_context_correct e _ v);
          rewrite <- Heqi in ht; symmetry in Heqi.

          destruct i; simpl in ht.

          - rewrite hh in ht.
            apply redex_to_term_injective in ht; subst.
            constructor...

          - econstructor 4...
            rewrite ht in hh.
            assert (~ dead_ckind (k+>e0)).
              { eapply dec_context_not_dead... }
            destruct (redex_trivial r t _ (e0=:[.]) hh) as [(H4, H5) | (v1, H4)]...
            + discriminateJM H5.
            + subst t.
              destruct (dec_context_term_next _ _ _ Heqi).
              apply H0...
              * congruence.

          - rewrite ht in hh; contradiction (value_redex _ _ hh).

          - intuition. 
          }

      - contradict hh; apply value_redex.

      - intuition.
    Qed.


    Lemma dec_redex_self : forall {k2} (r : redex k2) {k1} (c : context k1 k2), 
                               dec r c (d_red r c).
    Proof with eauto.
      intros;
      assert (H := dec_redex_self_e r);
      generalize c.

      (* induction on H *)
      apply dec_Ind with

      (P  := fun t k1' k2' c0 d (_ : dec t c0 d) => 
                 match d with
                 | d_val v        => True
                 | d_red k' r' c1 => forall (c : context k1 k1'), 
                                         dec t (c0~+c) (d_red r' (c1~+c))
                 end)
      (P0 := fun k2' v k1' c0 d (_ : decctx v c0 d) => 
                 match d with
                 | d_val v => True
                 | d_red k' r' c1 => forall (c : context k1 k1'), 
                                         decctx v (c0~+c) (d_red r' (c1~+c))
                 end)
      (d0 := H);
      
      intros;
      try destruct d;
      solve 
      [ auto
      | econstructor;   eauto
      | econstructor 3; eauto
      | econstructor 4; eauto ].
    Qed.



    Lemma dec_correct : 
        forall t {k1 k2} (c : context k1 k2) d, dec t c d -> c[t] = d.

    Proof.
      induction 1 using dec_Ind with
      (P := fun t _ _ c d (_ : dec t c d)     => c[t] = d)
      (P0:= fun _ v _ c d (_ : decctx v c d)  => c[v] = d);

      simpl; auto;
      match goal with
      | _ : dec_term ?t ?k2 = _      |- _ => assert (hh := dec_term_correct t k2)
      | _ : dec_context ?ec _ ?v = _ |- _ => assert (hh := dec_context_correct ec _ v)
      end;
      rewrite e in hh; simpl in *; 
      congruence.
    Qed.


    Lemma dec_plug : 
        forall {k1 k2} (c : context k1 k2) {k3} {c0 : context k3 k1} {t d}, 
            ~ dead_ckind k2 -> dec c[t] c0 d -> dec t (c~+c0) d.

    Proof with eauto.
      induction c; intros; simpl.
      - trivial.

      - apply IHc in H0; clear IHc;
        [ | apply (death_propagation2 _ _ H) ].
        inversion H0; subst;
            assert (hh := dec_term_correct (ec:[t]) k2); 
            rewrite H6 in hh.

        + destruct (dec_term_red_empty _ _ H6 t _ (ec=:[.]))...
          discriminateJM H3.

        + destruct (dec_term_val_empty _ _ H6 t _ (ec=:[.]))...
          discriminateJM H4.

        + dep_subst.
          destruct ec_order_comp_if with ec:[t] ec0 ec k2 as [H2 | [H2 | H2]].
              compute...
              compute...
              eapply dec_term_next_alive...
              apply H.

          * contradiction (dec_term_term_top _ _ H6 ec).
          * destruct (elem_context_det _ _ hh _ _ H2) as (v, H3)...
            subst t1.
            {
                clear H6; generalize dependent v; generalize dependent ec0.
                induction ec0 using (well_founded_ind (wf_eco k2 ec:[t])); intros.
                
                assert (H3 := dec_val _ H7).
                dependent destruction H3;
                inversion_ccons x.
                - rewrite hh in H2; 
                  contradiction (dec_context_red_bot _ _ _ H3 _ H2).
                - rewrite hh in H2; 
                  contradiction (dec_context_val_bot _ _ _ H3 _ H2).
                - assert (ht := dec_context_correct ec0 _ v).
                  rewrite H3 in ht.
                  rewrite <- hh in ht.
                  destruct (dec_context_term_next _ _ _ H3) as (H4', H5).
                  destruct ec_order_comp_if with ec:[t] ec2 ec k2 as [H6 | [H6 | H6]].
                      compute...
                      compute...
                      assert (H6 := ec_order_comp_fi _ _ _ _ H4'); intuition.
                      assert (H6 := ec_order_comp_fi _ _ _ _ H2); intuition.

                  + contradiction (H5 ec); rewrite <- hh...
                  + destruct (elem_context_det _ _ ht _ _ H6) as (v1, h4)...
                    subst t0.
                    apply H1 with ec2 v1...
                      { congruence. }
                  + subst; assert (H8 := elem_plug_injective1 _ ht).
                    subst...
            }

          * subst; assert (H8 := elem_plug_injective1 _ hh).
            subst...
    Qed.


    Lemma dec_plug_rev : 
        forall {k1 k2} (c : context k1 k2) {k3} {c0 : context k3 k1} {t d}, 
            ~ dead_ckind k2 -> dec t (c~+c0) d -> dec c[t] c0 d.

    Proof with eauto.
      induction c; intros; simpl.

      - trivial.

      - apply IHc; clear IHc.
        eapply death_propagation2...
        remember (dec_term ec:[t] k2) as i.
        destruct i;
        assert (hh := dec_term_correct ec:[t] k2);
        rewrite <- Heqi in hh;
        symmetry in Heqi.

        + destruct (dec_term_red_empty _ _ Heqi t _ (ec=:[.]))...
          discriminateJM H2.

        + destruct ec_order_comp_if with ec:[t] e ec k2 as [H1 | [H1 | H1]].
              compute...
              compute...
              eapply dec_term_next_alive...
              assumption.

          * contradict (dec_term_term_top _ _ Heqi _ H1).

          * destruct (elem_context_det _ _ hh _ _ H1) as (v, H2)...
            subst t0.
            econstructor 3; eauto.
            {
              clear H Heqi; generalize dependent v; generalize dependent e.
              induction e using (well_founded_ind (wf_eco k2 ec:[t])); intros.

              apply val_dec.
              remember (dec_context e _ v).
              destruct i;
                  symmetry in Heqi;
                  assert (ht := dec_context_correct e _ v); 
                  rewrite Heqi in ht.

              - rewrite hh in H1;
                contradiction (dec_context_red_bot _ _ _ Heqi _ H1).

              - destruct (dec_context_term_next _ _ _ Heqi) as (H3, H4).
                econstructor 4...
                rewrite <- hh in ht.
                destruct ec_order_comp_if with ec:[t] e0 ec k2 as [H5 | [H5 | H5]].
                    compute...
                    compute...
                    apply (ec_order_comp_fi _ _ _ _ H3).
                    apply (ec_order_comp_fi _ _ _ _ H1).

                + rewrite hh in H1; 
                  contradiction (H4 ec H1). 
                  congruence.
                + destruct (elem_context_det _ _ ht _ _ H5) as (v0, H6)...
                  subst t0.
                  apply H...
                    { congruence. }
                + subst.
                  assert (H5 := elem_plug_injective1 _ ht).
                  subst...

              - rewrite hh in H1;
                contradiction (dec_context_val_bot _ _ _ Heqi _ H1).

              - contradict ht.
                eapply ec_order_comp_fi...
            }

          * subst.
            assert (H5 := elem_plug_injective1 _ hh).
            subst.
            econstructor 3...

        + destruct (dec_term_val_empty _ _ Heqi t _ (ec=:[.]))...
          discriminateJM H2.

        + contradict H...
          apply death_propagation...
    Qed.


    Inductive decempty : term -> forall {k}, decomp k -> Prop :=
    | d_intro : forall {t k} {d : decomp k}, dec t [.] d -> decempty t d.

    Inductive iter : forall {k}, decomp k -> value k -> Prop :=
    | i_val : forall {k} (v : value k), iter (d_val v) v
    | i_red : forall {k2} (r : redex k2) {t k1} (c : context k1 k2) {d v},
                  contract r = Some t -> decempty c[t] d -> iter d v ->
                  iter (d_red r c) v.

    Inductive eval : term -> value init_ckind -> Prop :=
    | e_intro : forall {t} {d : decomp init_ckind} {v : value init_ckind}, 
                    decempty t d -> iter d v -> eval t v.


    Definition dec := dec.

  End RS.



  Lemma dec_val_self : forall {k2} (v : value k2) {k1} (c : context k1 k2) d, 
                           dec v c d <-> decctx v c d.
  Proof.
    split; [apply dec_val | apply val_dec].
  Qed.


  Module DEC := DEC.

  Definition dec_term    := dec_term.
  Definition dec_context := dec_context.

  Definition dec_term_correct      := dec_term_correct.
  Definition dec_context_correct   := dec_context_correct.
  Definition dec_term_next_alive   := dec_term_next_alive.
  Definition dec_term_from_dead    := dec_term_from_dead.
  Definition dec_context_from_dead := dec_context_from_dead.

End RedRefSem.



Module Red_Sem_Proper (R : RED_LANG) (RS : RED_REF_SEM R) : RED_SEM_PROPER R RS.RS.

  Import R.
  Module RLF := RED_LANG_Facts R.
  Import RLF.
  Import RS.
  Export DEC.


  Lemma dec_is_function : forall {t k} {d d0 : decomp k}, 
                              decempty t d -> decempty t d0 -> d = d0.
  Proof.
    intros t k d1 d2 DE1 DE2.
    dependent destruction DE1; dependent destruction DE2.

    induction H using dec_Ind with 
    (P  := fun t _ _ c d _ => forall d0, dec t c d0    -> d = d0)
    (P0 := fun _ v _ c d _ => forall d0, decctx v c d0 -> d = d0);

    intros;

    (* automated cases *)
    match goal with

    | [ RD : (dec ?t ?c ?d), DT1 : (dec_term ?t ?k = _) |- _ ] => 
             inversion RD; dep_subst; 
             match goal with DT2 : (dec_term ?t ?k = _) |- _ => 
                 rewrite DT2 in DT1; inversion DT1 end

    | [ RC : (decctx ?v (?ec=:?c) ?d), DC1 : (dec_context ?ec ?k ?v = _) |- _ ] => 
             dependent_destruction2 RC; inversion_ccons x2; dep_subst;
             match goal with DC2 : (dec_context ?ec' ?k' ?v' = _) |- _ => 
                 rewrite DC2 in DC1; inversion DC1 end

    | [ RC : (decctx ?v [.] ?d) |- _] => 
             dependent_destruction2 RC

    end;

    subst; eauto.
  Qed.
  Hint Resolve dec_is_function : prop.


  Lemma iter_is_function : forall {k} {d : decomp k} {v v0}, 
                               iter d v -> iter d v0 -> v = v0.
  Proof with eauto with prop.
    induction 1; intros.
    - dependent destruction H...
    - dependent destruction H2; subst. 
      rewrite H2 in H; inversion H; subst.
      apply IHiter.
      cutrewrite (d = d0)...
  Qed.
  Hint Resolve iter_is_function : prop.


  Lemma eval_is_function : forall {t} {v v0 : value init_ckind}, 
                               eval t v -> eval t v0 -> v = v0.
  Proof with eauto with prop.
    intros.
    dependent destruction H.
    dependent destruction H1.
    cutrewrite (d = d0) in H0...
  Qed.


  Lemma dec_correct : forall {t k1 k2} {c : context k1 k2} {d}, 
                          dec t c d -> decomp_to_term d = c[t].
  Proof.
    induction 1 using dec_Ind with
    (P := fun t _ _ c d (H : dec t c d)     => decomp_to_term d = c[t])
    (P0:= fun _ v _ c d (H:RS.decctx v c d) => decomp_to_term d = c[v]);
    simpl; auto;

    first
    [ assert (G := dec_term_correct t k2);       rewrite e in G
    | assert (G := dec_context_correct ec k2 v); rewrite e in G ]; 
    
    simpl in *; 
    try rewrite IHdec;
    congruence.
  Qed.


  Lemma dec_total : forall t k, ~ dead_ckind k -> exists (d : decomp k), decempty t d.
  Proof with auto.
    intros t k H.
    destruct (decompose t k H) as [(v, ?) | (?, (r, (c, ?)))]; 
    intros; subst.
    - exists (d_val v); constructor.
      rewrite dec_val_self.
      constructor...
    - exists (d_red r c); constructor.
      apply dec_plug_rev.
        { apply (proper_death2 _ _ [.] r). }
      rewrite <- compose_empty.
      apply dec_redex_self.
  Qed.


  Lemma unique_decomposition :

      forall (t : term) k1, ~ dead_ckind k1 ->
          (exists v : value k1, t = v) \/ 
          (exists k2 (r : redex k2) (c : context k1 k2),  t = c[r] /\ 
	      forall k2' (r0 : redex k2') (c0 : context k1 k2'), 
                  t = c0[r0] -> k2' = k2 /\ r ~= r0 /\ c ~= c0).

  Proof with eauto.
    intros.
    destruct (decompose t k1 H) as [(v, H0) | (k', (r, (c, H0)))].
    - left; exists v...
    - right; exists k' r; exists c; split.
      + congruence.
      + intros.
        assert (H2 : decempty t (d_red r c) /\ decempty t (d_red r0 c0)).
        {
            split;
            constructor; 
            [ rewrite H0 | rewrite H1 ]; 
            apply dec_plug_rev;
            solve
            [ apply (proper_death2 _ _ [.]); auto
            | rewrite <- compose_empty; apply dec_redex_self ]. 
        }
        destruct H2.
        assert (H4 := dec_is_function H2 H3); dependent destruction H4.
        intuition.
  Qed.

End Red_Sem_Proper.



Module PreAbstractMachine (R : RED_LANG) (RS : RED_REF_SEM R) <: PRE_ABSTRACT_MACHINE R.

  Import R.
  Module RF := RED_LANG_Facts R.
  Import RF.
  Import RS.
  Export DEC.


  (** A decomposition function specified in terms of the atomic functions above *)
  Inductive dec : term -> forall {k1 k2}, context k1 k2 -> decomp k1 -> Prop :=
  | d_dec  : forall t {k1 k2} (c : context k1 k2) {r},
               dec_term t k2 = in_red r -> 
               dec t c (d_red r c)
  | d_v    : forall t {k1 k2} {c : context k1 k2} {v d},
               dec_term t k2 = in_val v ->
               decctx v c d ->
               dec t c d
  | d_term : forall t {t0 k1 k2} {c : context k1 k2} {ec d},
               dec_term t k2 = in_term t0 ec ->
               dec t0 (ec=:c) d ->
               dec t c d

  with decctx : forall {k2}, value k2 -> forall {k1}, context k1 k2 -> decomp k1 -> Prop :=
  | dc_end  : forall {k} (v : value k), 
                ~ dead_ckind k ->
                decctx v [.] (d_val v)
  | dc_dec  : forall ec {k2} (v : value (k2+>ec)) {k1} (c : context k1 k2) {r},
                dec_context ec k2 v = in_red r ->
                decctx v (ec=:c) (d_red r c)
  | dc_val  : forall {k2} {v0 : value k2} ec (v : value (k2+>ec)) 
                     {k1} {c  : context k1 k2} {d},
                dec_context ec k2 v = in_val v0 ->
                decctx v0 c d ->
                decctx v (ec=:c) d
  | dc_term : forall ec {ec0 k2} (v : value (k2+>ec)) 
                            {k1} {c : context k1 k2} {t d},
                dec_context ec k2 v = in_term t ec0 ->
                dec t (ec0=:c) d ->
                decctx v (ec=:c) d.

  Scheme dec_Ind := Induction for dec Sort Prop
    with decctx_Ind := Induction for decctx Sort Prop.

  Inductive iter : forall {k}, decomp k -> value k -> Prop :=
  | i_val : forall {k} (v : value k), iter (d_val v) v
  | i_red : forall {k2} (r : redex k2) {t k1} {c : context k1 k2} {d v},
              contract r = Some t -> dec t c d -> iter d v ->
              iter (d_red r c) v.

  Inductive eval : term -> value init_ckind -> Prop :=
  | e_intro : forall {t} {d : decomp init_ckind} {v : value init_ckind},
                dec t [.] d -> iter d v -> eval t v.


  Lemma dec_id_l : forall {t k1 k2} {c : context k1 k2} {d}, 
                       RS.RS.dec t c d -> dec t c d.
  Proof with eauto.
    induction 1 using RS.dec_Ind with 
    (P := fun t _ _ c d (_ : RS.RS.dec t c d) => dec t c d)
    (P0:= fun _ v _ c d (_ : RS.decctx v c d) => decctx v c d);
    solve 
    [ econstructor; eauto
    | eapply d_term; eauto
    | eapply dc_term; eauto ].
  Qed.
  Hint Resolve dec_id_l.


  Lemma dec_id_r : forall {t k1 k2} {c : context k1 k2} {d}, 
                       dec t c d -> RS.RS.dec t c d.
  Proof with eauto.
    induction 1 using dec_Ind with 
    (P := fun t _ _ c d (_ : dec t c d)    => RS.RS.dec t c d)
    (P0:= fun _ v _ c d (_ : decctx v c d) => RS.decctx v c d);
    solve
    [ econstructor; eauto
    | eapply RS.d_term; eauto
    | eapply RS.dc_term; eauto ].
  Qed.
  Hint Resolve dec_id_r.


  Lemma iterRedPam : forall {k} {d : decomp k} {v}, RS.RS.iter d v -> iter d v.
  Proof with eauto.
    induction 1; econstructor...
    dependent destruction H0.
    apply dec_id_l.
    apply RS.RS.dec_plug in H0.
    - rewrite <- compose_empty in H0...
    - eapply proper_death2... exact [.].
  Qed.


  Lemma evalRedPam : forall {t} {v : value init_ckind},  RS.RS.eval t v -> eval t v.
  Proof with eauto.
    intros.
    dependent destruction H;
    econstructor;
    dependent destruction H...
    apply iterRedPam...
  Qed.
  Hint Resolve evalRedPam.


  Lemma iterPamRed : forall {k} {d : decomp k} {v}, iter d v -> RS.RS.iter d v.
  Proof with eauto.
    induction 1.
    - constructor.
    - econstructor...
      constructor.
      apply RS.RS.dec_plug_rev.
      + eapply proper_death2... exact [.].
      + rewrite <- compose_empty...
  Qed.


  Lemma evalPamRed : forall {t} {v : value init_ckind}, eval t v -> RS.RS.eval t v.
  Proof with eauto.
    intros.
    dependent destruction H.
    econstructor.
    - constructor...
    - apply iterPamRed...
  Qed.
  Hint Resolve evalPamRed.


  Theorem evalPam : forall {t} {v : value init_ckind}, RS.RS.eval t v <-> eval t v.
  Proof with auto.
    split...
  Qed.


  Module DEC := DEC.

End PreAbstractMachine.



Module StagedAbstractMachine (R : RED_LANG) (RS : RED_REF_SEM R) <: STAGED_ABSTRACT_MACHINE R.

  Import R.
  Module RF := RED_LANG_Facts R.
  Import RF.
  Import RS.
  Export DEC.

  Module PAM := PreAbstractMachine R RS.


  Inductive dec : term -> forall {k1 k2}, context k1 k2 -> value k1 -> Prop :=
  | d_dec  : forall t {k1 k2} {c : context k1 k2} {r v},
               dec_term t k2 = in_red r -> iter (d_red r c) v ->
               dec t c v
  | d_v    : forall t {k1 k2} {c : context k1 k2} {v v0},
               dec_term t k2 = in_val v -> decctx v c v0 ->
               dec t c v0
  | d_many : forall t {t0 ec k1 k2} {c : context k1 k2} {v},
               dec_term t k2 = in_term t0 ec -> dec t0 (ec=:c) v ->
               dec t c v

  with decctx : forall {k2}, value k2 -> forall {k1}, context k1 k2 -> value k1 -> Prop :=
  | dc_end  : forall {k} {v v0 : value k},
               ~ dead_ckind k ->
               iter (d_val v) v0 ->
               decctx v [.] v0
  | dc_dec  : forall ec {k2} (v : value (k2+>ec)) {k1} {c : context k1 k2} {r v0},
               dec_context ec k2 v = in_red r -> iter (d_red r c) v0 ->
               decctx v (ec=:c) v0
  | dc_val  : forall ec {k2} (v : value (k2+>ec)) {v0 k1} {c : context k1 k2} {v1},
               dec_context ec k2 v = in_val v0 -> decctx v0 c v1 ->
               decctx v (ec=:c) v1
  | dc_term : forall ec {k2} (v : value (k2+>ec)) {t ec0 k1} {c : context k1 k2} {v0},
               dec_context ec k2 v = in_term t ec0 -> dec t (ec0=:c) v0 ->
               decctx v (ec=:c) v0

  with iter : forall {k}, decomp k -> value k -> Prop :=
  | i_val : forall {k} (v : value k), 
               iter (d_val v) v
  | i_red : forall {k2} (r : redex k2) {k1} {c : context k1 k2} {t v},
               contract r = Some t -> dec t c v -> 
               iter (d_red r c) v.

  Scheme dec_Ind    := Induction for dec Sort Prop
    with decctx_Ind := Induction for decctx Sort Prop
    with iter_Ind   := Induction for iter Sort Prop.


  Inductive eval : term -> value init_ckind -> Prop :=
  | e_intro : forall {t} {v : value init_ckind}, dec t [.] v -> eval t v.


  Lemma decPamSam : forall {t k1 k2} {c : context k1 k2} {d},
                        PAM.dec t c d -> forall {v}, iter d v -> dec t c v.
  Proof with eauto.
    induction 1 using PAM.dec_Ind with
    (P  := fun t _ _ c d (_ : PAM.dec t c d)    => forall v,  iter d v -> dec t c v)
    (P0 := fun _ v _ c d (_ : PAM.decctx v c d) => forall v', iter d v' -> decctx v c v');
    intros; simpl; solve 
    [ econstructor; eauto
    | eapply d_v; eauto
    | eapply d_many; eauto 
    | eapply dc_val; eauto
    | eapply dc_term; eauto ].
  Qed.
  Hint Resolve decPamSam.


  Lemma iterPamSam : forall {k} {d : decomp k} {v}, PAM.iter d v -> iter d v.
  Proof with eauto.
    induction 1; [constructor | econstructor 2]...
  Qed.
  Hint Resolve iterPamSam.


  Lemma evalPamSam : forall {t} {v : value init_ckind}, PAM.eval t v -> eval t v.
  Proof with eauto.
    intros; dependent destruction H; constructor...
  Qed.
  Hint Resolve evalPamSam.


  Module RSP := Red_Sem_Proper R RS.
  Import RSP.


  Lemma decSamPam : forall {t k1 k2} {c : context k1 k2} {v}, dec t c v -> 
                        forall {d}, PAM.dec t c d -> PAM.iter d v.
  Proof with eauto.
    induction 1 using dec_Ind with
    (P  := fun t _ _ c v  (_ : dec t c v)     => forall d, PAM.dec t c d -> PAM.iter d v)
    (P0 := fun _ v _ c v' (_ : decctx v c v') => forall d, PAM.decctx v c d -> PAM.iter d v')
    (P1 := fun _ d v      (_ : iter d v)      => PAM.iter d v); 
    try (intros d0 G; dependent destruction G; try inversion_ccons x);
    try solve 
    [ rewrite H in e; inversion e; subst; eauto
    | rewrite H0 in e; inversion e; subst; eauto 
    | eauto
    | constructor ].

    - destruct (dec_total c[t] k1) as [d H0].
        { eapply proper_death2... }
      dependent destruction H0.
      apply RS.RS.dec_plug in H0;
          try solve [eapply proper_death2; eauto; exact [.] ].
      rewrite <- compose_empty in H0.
      econstructor...
  Qed.
  Hint Resolve decSamPam.


  Lemma evalSamPam : forall {t} {v : value init_ckind}, eval t v -> PAM.eval t v.
  Proof with eauto.
    intros.
    dependent destruction H.
    destruct (dec_total t init_ckind) as [d H0].
      { dependent destruction H. eapply proper_death2... exact [.].
        dependent destruction H0; try discriminateJM x...
        eapply death_propagation2; eapply dec_term_next_alive... }
    dependent destruction H0;
    econstructor...
  Qed.
  Hint Resolve evalSamPam.


  Theorem evalSam : forall {t} {v : value init_ckind}, RS.RS.eval t v <-> eval t v.
  Proof with auto.
    intros; rewrite PAM.evalPam; split; intros...
  Qed.


  Module DEC := DEC.

End StagedAbstractMachine.



Module EvalApplyMachine (R : RED_LANG) (RS : RED_REF_SEM R) <: EVAL_APPLY_MACHINE R.

  Import R.
  Import RS.
  Export DEC.

  Module SAM := StagedAbstractMachine R RS.


  Inductive dec : term -> forall {k1 k2}, context k1 k2 -> value k1 -> Prop :=
  | d_d_r  : forall t {t0 k1 k2} {c : context k1 k2} {r v},
               dec_term t k2 = in_red r -> contract r = Some t0 -> dec t0 c v ->
               dec t c v
  | d_v    : forall t {k1 k2} {c : context k1 k2} {v v0},
               dec_term t k2 = in_val v -> decctx v c v0 ->
               dec t c v0
  | d_term : forall t {t0 ec k1 k2} {c : context k1 k2} {v},
               dec_term t k2 = in_term t0 ec -> dec t0 (ec=:c) v ->
               dec t c v

  with decctx : forall {k2}, value k2 -> forall {k1}, context k1 k2 -> value k1 -> Prop :=
  | dc_end : forall {k} (v : value k), 
               ~ dead_ckind k ->
               decctx v [.] v
  | dc_red : forall ec {k2} (v : value (k2+>ec)) {k1} {c : context k1 k2} {r t v0},
               dec_context ec k2 v = in_red r -> contract r = Some t -> dec t c v0 ->
               decctx v (ec=:c) v0
  | dc_rec : forall ec {k2} (v : value (k2+>ec)) {k1} {c : context k1 k2} {v0 v1},
               dec_context ec k2 v = in_val v0 -> decctx v0 c v1 ->
               decctx v (ec=:c) v1
  | dc_trm : forall ec {k2} (v : value (k2+>ec)) {k1} {c : context k1 k2} {t ec0 v0},
               dec_context ec k2 v = in_term t ec0 -> dec t (ec0=:c) v0 ->
               decctx v (ec=:c) v0.

  Scheme dec_Ind := Induction for dec Sort Prop
    with decctx_Ind := Induction for decctx Sort Prop.


  Inductive eval : term -> value init_ckind -> Prop :=
  | e_intro : forall {t} {v : value init_ckind}, dec t [.] v -> eval t v.


  Lemma decSamEam : forall {t k1 k2} {c : context k1 k2} {v}, SAM.dec t c v -> dec t c v.
  Proof with eauto.
    induction 1 using SAM.dec_Ind with
    (P := fun t _ _ c v  (_ : SAM.dec t c v)     => dec t c v)
    (P0:= fun _ v _ c v' (_ : SAM.decctx v c v') => decctx v c v')
    (P1:= fun k d v      (_ : SAM.iter d v)      => 
              match d with
              | d_val v'    => ~ dead_ckind k -> decctx v [.] v'
              | d_red _ r c => forall t, contract r = Some t -> dec t c v
              end);
    simpl; intros.

    (* Case 1 *)
    dependent destruction i; subst; econstructor 1...
    (* Case 2 *)
    econstructor 2...
    (* Case 3 *)
    econstructor 3...
    (* Case 4 *)
    assert (IHdec' := IHdec n).
    dependent destruction IHdec'; subst; constructor...
    (* Case 5 *)
    dependent destruction i; econstructor 2...
    (* Case 6 *)
    econstructor 3...
    (* Case 7 *)
    econstructor 4...
    (* Case 8 *)
    constructor...
    (* Case 9 *)
    rewrite e in H0; inversion H0; subst...
  Qed.


  Lemma evalSamEam : forall {t} {v : value init_ckind}, SAM.eval t v -> eval t v.
  Proof.
    intros; dependent destruction H; constructor; apply decSamEam; auto.
  Qed.
  Hint Resolve evalSamEam.


  Lemma decEamSam : forall {t k1 k2} {c : context k1 k2} {v}, dec t c v -> SAM.dec t c v.
  Proof with eauto.
    induction 1 using dec_Ind with
    (P := fun t _ _ c v  (_ : dec t c v)     => SAM.dec t c v)
    (P0:= fun _ v _ c v' (_ : decctx v c v') => SAM.decctx v c v'); 
    intros; simpl.

    econstructor 1; try econstructor...
    econstructor 2...
    econstructor 3...
    repeat constructor...
    econstructor 2; try econstructor 2...
    econstructor 3...
    econstructor 4...
  Qed.


  Lemma evalEamSam : forall {t} {v : value init_ckind}, eval t v -> SAM.eval t v.
  Proof.
    intros; dependent destruction H; constructor; apply decEamSam; auto.
  Qed.
  Hint Resolve evalEamSam.


  Theorem evalEam : forall {t} {v : value init_ckind}, RS.RS.eval t v <-> eval t v.
  Proof with auto.
    intros; rewrite SAM.evalSam; split...
  Qed.


  Module DEC := DEC.

End EvalApplyMachine.



Module ProperEAMachine (R : RED_LANG) (RS : RED_REF_SEM R) <: PROPER_EA_MACHINE R.

  Import R.
  Import RS.
  Export DEC.

  Module EAM := EvalApplyMachine R RS.


  Inductive configuration : Set :=
  | c_eval  : term -> forall {k1 k2}, context k1 k2 -> configuration
  | c_apply : forall {k1 k2}, context k1 k2 -> value k2 -> configuration.


  Definition c_init t := c_eval t [.](init_ckind).
  Definition c_final (v : value init_ckind) := c_apply [.] v.


  Reserved Notation " a → b " (at level 40, no associativity).


  Inductive transition : configuration -> configuration -> Prop :=

  | t_red  : forall t {k1 k2} (c : context k1 k2) {r t0},
               dec_term t k2 = in_red r -> contract r = Some t0 ->
               c_eval t c → c_eval t0 c
  | t_val  : forall t {k1 k2} (c : context k1 k2) {v},
      	       dec_term t k2 = in_val v ->
               c_eval t c → c_apply c v
  | t_term : forall t {k1 k2} (c : context k1 k2) {t0 ec},
               dec_term t k2 = in_term t0 ec ->
               c_eval t c → c_eval t0 (ec=:c)
  | t_cred : forall ec {k2} (v : value (k2+>ec)) {k1} (c : context k1 k2) {r t},
               dec_context ec k2 v = in_red r -> contract r = Some t ->
               c_apply (ec=:c) v → c_eval t c
  | t_cval : forall ec {k2} (v : value (k2+>ec)) {k1} (c : context k1 k2) {v0},
               dec_context ec k2 v = in_val v0 ->
               c_apply (ec=:c) v → c_apply c v0
  | t_cterm: forall ec {k2} (v : value (k2+>ec)) {k1} (c : context k1 k2) {t ec0},
               dec_context ec k2 v = in_term t ec0 ->
               c_apply (ec=:c) v → c_eval t (ec0=:c)

  where " a → b " := (transition a b).


  Module AM : ABSTRACT_MACHINE
    with Definition term          := term
    with Definition value         := value init_ckind
    with Definition configuration := configuration
    with Definition transition    := transition
    with Definition c_init        := c_init
    with Definition c_final       := c_final.

    Definition term          := term.
    Definition value         := value init_ckind.
    Definition configuration := configuration.
    Definition transition    := transition.
    Definition c_init        := c_init.
    Definition c_final       := c_final.

    Inductive trans_close : configuration -> configuration -> Prop :=
    | one_step   : forall (c0 c1 : configuration), 
                       transition c0 c1 -> trans_close c0 c1
    | multi_step : forall (c0 c1 c2 : configuration), 
                       transition c0 c1 -> trans_close c1 c2 -> trans_close c0 c2.

    Inductive eval : term -> value -> Prop :=
    | e_intro : forall t v, trans_close (c_init t) (c_final v) -> eval t v.

  End AM.

  Notation " a →+ b " := (AM.trans_close a b) (at level 40, no associativity).


  Lemma decEamTrans : forall {t k1 k2} (c : context k1 k2) {v}, 
                          EAM.dec t c v -> c_eval t c →+ c_apply [.] v.
  Proof with eauto.
    induction 1 using EAM.dec_Ind with
    (P := fun t _ _ c v  (_ : EAM.dec t c v)     => 
              c_eval t c  →+ c_apply [.] v)
    (P0:= fun k2 v k1 c v' (_ : EAM.decctx v c v') => 
              c_apply c v →+ c_apply [.] v' \/ k1 = k2 /\ @empty k1 ~= c /\ v ~=v');
    intuition;
    try solve
    [ (try apply or_introl); econstructor 2; eauto; econstructor; eauto 
    | dep_subst; constructor 1; constructor; auto].

    - dep_subst; left; constructor 1; econstructor...
  Qed.
  Hint Resolve decEamTrans.


  Lemma evalEamMachine : forall {t v}, 
                             EAM.eval t v -> AM.eval t v.
  Proof with eauto.
    intros.
    dependent destruction H.
    constructor.
    apply decEamTrans...
  Qed.
  Hint Resolve evalEamMachine.


  Lemma transDecEam : forall {t k1 k2} {c : context k1 k2} {v : value k1}, 
                          c_eval t c →+ c_apply [.] v -> EAM.dec t c v.
  Proof with eauto.
    intros t k1 k2 c v; revert t k2 c.
    cut (forall co, co →+ c_apply [.] v -> 
         match co with 
         | c_eval t k1' _ c   => k1 = k1' -> forall v', v ~= v' -> EAM.dec t c v'
         | c_apply k1' _ c v0 => k1 = k1' -> forall v', v ~= v' -> EAM.decctx v0 c v'
         end); intros.
    apply (H _ H0)...

    dependent induction H;

    let rec rc := first 
        [ econstructor 1; eauto; rc 
        | econstructor 2; eauto; rc 
        | econstructor 3; eauto; rc 
        | econstructor 4; eauto; rc
        | intro; assert (dec_term t k1 = in_dead); 
          [ eapply dec_term_from_dead; eauto | congruence] 
        | intro; assert (dec_context ec k1 v0 = in_dead); 
          [ eapply dec_context_from_dead; eauto; apply death_propagation; auto 
          | congruence ] ]
    in 
    dependent destruction H; intros; dep_subst; try solve [rc].
  Qed.
  Hint Resolve transDecEam.


  Lemma evalMachineEam : forall {t v}, AM.eval t v -> EAM.eval t v.
  Proof with eauto.
    intros.
    dependent destruction H.
    constructor.
    apply transDecEam...
  Qed.
  Hint Resolve evalMachineEam.


  Theorem eval_apply_correct : forall {t} {v : value init_ckind}, 
                                   RS.RS.eval t v <-> AM.eval t v.
  Proof with auto.
    intros t v; rewrite EAM.evalEam; split...
  Qed.


  Module DEC := DEC.

End ProperEAMachine.



Module PushEnterMachine (R : RED_LANG) (PRS : PE_REF_SEM R) <: PUSH_ENTER_MACHINE R.

  Import R.
  Import PRS.
  Export DEC.

  Module EAM := EvalApplyMachine R RefSem.
  Module PR  := Red_Sem_Proper R PRS.RefSem.


  Inductive dec : term -> forall {k1 k2}, context k1 k2 -> value k1 -> Prop :=

  | dec_r    : forall t {t0 k1 k2} {c : context k1 k2} {r v},
                 dec_term t k2 = in_red r -> contract r = Some t0 -> dec t0 c v ->
                 dec t c v
  | dec_val  : forall t {k} {v : value k},
                 dec_term t k = in_val v ->
                 dec t [.] v
  | dec_v_t  : forall t ec {t0 ec0} {k1 k2} {c : context k1 k2} {v v0},
                 dec_term t (k2+>ec) = in_val v -> 
                 dec_context ec k2 v = in_term t0 ec0 -> 
                 dec t0 (ec0=:c) v0 ->
                 dec t (ec=:c) v0
  | dec_red  : forall t ec {t0} {k1 k2} {c : context k1 k2} {v v0 r},
                 dec_term t (k2+>ec) = in_val v ->
                 dec_context ec k2 v = in_red r -> 
                 contract r = Some t0 -> 
                 dec t0 c v0 ->
                 dec t (ec=:c) v0
  | dec_rec  : forall t {t0 ec} {k1 k2} {c : context k1 k2} {v},
                 dec_term t k2 = in_term t0 ec ->
                 dec t0 (ec=:c) v ->
                 dec t c v.


  Inductive eval : term -> value init_ckind -> Prop :=
  | e_intro : forall {t} {v : value init_ckind}, dec t [.] v -> eval t v.


  Lemma decEamPem : forall {t k1 k2} {c : context k1 k2} {v}, EAM.dec t c v -> dec t c v.
  Proof with eauto.
    induction 1 using EAM.dec_Ind with
    (P := fun t _ _ c v  (_ : EAM.dec t c v) => dec t c v)
    (P0:= fun _ v _ c v0 (_ : EAM.decctx v c v0) =>
      match c in context _ k2' return value k2' -> Prop with
      | [.] => fun v => dec v [.] v0
      | ccons ec _ c => fun v => forall d, dec_context ec _ v = d ->
        match d with
        | in_red r => forall t, contract r = Some t -> dec t c v0
        | in_term t ec0 => dec t (ec0=:c) v0
        | in_val v => False
        | in_dead => False
        end
      end v); intros; simpl.
    (* Case 1 *)
    econstructor...
    (* Case 2 *)
    dependent destruction d; subst.
    (* Case 2.1 *)
    constructor...
    (* Case 2.2 *)
    econstructor 4...
    apply (IHdec (in_red r))...
    (* Case 2.3 *)
    contradict (dec_context_not_val _ _ _ H).
    (* Case 2.4 *)
    econstructor 3...
    apply (IHdec (in_term t0 ec0))...
    (* Case 3 *)
    econstructor 5...
    (* Case 4 *)
    constructor; apply dec_term_value...
    (* Case 5 *)
    rewrite e in H0; inversion H0; subst; intros.
    rewrite e0 in H0; inversion H0; subst...
    (* Case 7 *)
    contradict (dec_context_not_val _ _ _ e).
    (* Case 8 *)
    rewrite e in H0; subst...
  Qed.


  Lemma evalEamPem : forall {t v}, EAM.eval t v -> eval t v.
  Proof.
    intros t v H; dependent destruction H; constructor; apply decEamPem; auto.
  Qed.
  Hint Resolve evalEamPem.


  Lemma decPemEam : forall {t k1 k2} {c : context k1 k2} {v}, dec t c v -> EAM.dec t c v.
  Proof with eauto.
    induction 1; intros; simpl; auto.
    econstructor 1...
    econstructor 2... econstructor... 
        intro H0; rewrite (dec_term_from_dead t _ H0) in H; discriminate.
    econstructor 2... econstructor 4...
    econstructor 2... econstructor 2...
    econstructor 3...
  Qed.


  Lemma evalPemEam : forall {t v}, eval t v -> EAM.eval t v.
  Proof.
    intros t v H; dependent destruction H; constructor; apply decPemEam; auto.
  Qed.
  Hint Resolve evalPemEam.


  Theorem evalPem : forall {t v}, PRS.RefSem.RS.eval t v <-> eval t v.
  Proof.
    intros t v; rewrite EAM.evalEam; split; auto.
  Qed.


  Module DEC := DEC.

  Definition dec_context_not_val := dec_context_not_val.
  Definition dec_term_value      := @dec_term_value.

End PushEnterMachine.



Module ProperPEMachine (R : RED_LANG) (PRS : PE_REF_SEM R) <: PROPER_PE_MACHINE R.

  Import R.
  Import PRS.
  Export DEC.

  Module PEM := PushEnterMachine R PRS.


  Inductive configuration : Set :=
  | c_eval  : term -> forall {k1 k2}, context k1 k2 -> configuration
  | c_final : forall {k}, value k                   -> configuration.

  Definition c_init t := c_eval t (@empty init_ckind).

  Reserved Notation " a → b " (at level 40, no associativity).


  Inductive transition : configuration -> configuration -> Prop :=
  | t_red  : forall t {k1 k2} (c : context k1 k2) {t0 r},
               dec_term t k2 = in_red r -> contract r = Some t0 ->
               c_eval t c → c_eval t0 c
  | t_cval : forall t {k} {v : value k},
               dec_term t k = in_val v ->
               c_eval t [.](k) → c_final v
  | t_cred : forall t ec {t0} {k1 k2} (c : context k1 k2) {v r},
               dec_term t (k2+>ec) = in_val v ->
               dec_context ec k2 v = in_red r ->
               contract r = Some t0 ->
               c_eval t (ec=:c) → c_eval t0 c
  | t_crec : forall t ec {t0 ec0 k1 k2} (c : context k1 k2) {v},
               dec_term t (k2+>ec) = in_val v ->
               dec_context ec k2 v = in_term t0 ec0 ->
               c_eval t (ec=:c) → c_eval t0 (ec0=:c)
  | t_rec  : forall t {t0 ec k1 k2} (c : context k1 k2),
               dec_term t k2 = in_term t0 ec ->
               c_eval t c → c_eval t0 (ec=:c)
  where " a →  b " := (transition a b).


  Module AM : ABSTRACT_MACHINE
    with Definition term          := term
    with Definition value         := value init_ckind
    with Definition configuration := configuration
    with Definition transition    := transition
    with Definition c_init        := c_init
    with Definition c_final       := @c_final init_ckind.

    Definition term          := term.
    Definition value         := value init_ckind.
    Definition configuration := configuration.
    Definition transition    := transition.
    Definition c_init        := c_init.
    Definition c_final       := @c_final init_ckind .


    Inductive trans_close : configuration -> configuration -> Prop :=
    | one_step   : forall {c0 c1},    transition c0 c1 -> trans_close c0 c1
    | multi_step : forall {c0 c1 c2}, transition c0 c1 -> 
                                          trans_close c1 c2 -> trans_close c0 c2.

    Inductive eval : term -> value -> Prop :=
    | e_intro : forall {t v}, trans_close (c_init t) (c_final v) -> eval t v.

  End AM.

  Notation " a →+ b " := (AM.trans_close a b) (at level 40, no associativity).


  Lemma decPemTrans : forall {t} {k1 k2} {c : context k1 k2} {v}, 
                          PEM.dec t c v -> c_eval t c →+ c_final v.
  Proof with eauto.
    induction 1; intros;
    solve 
    [ do 2 constructor; auto
    | econstructor 2; eauto; econstructor; eauto ].
  Qed.
  Hint Resolve decPemTrans.


  Lemma evalPemMachine : forall {t v}, PEM.eval t v -> AM.eval t v.
  Proof with eauto.
    intros.
    dependent destruction H.
    constructor.
    apply decPemTrans...
  Qed.
  Hint Resolve evalPemMachine.


  Lemma transDecPem : forall {t k1 k2} {c : context k1 k2} {v}, 
                          c_eval t c →+ c_final v -> PEM.dec t c v.
  Proof with eauto.
    intros.
    dependent induction H;

    dependent destruction H.

    apply PEM.dec_val...
    eapply PEM.dec_r...
    do 2 dependent destruction H0.
    eapply PEM.dec_red...
    eapply PEM.dec_v_t...
    eapply PEM.dec_rec...
  Qed.
  Hint Resolve transDecPem.


  Lemma evalMachinePem : forall {t v}, AM.eval t v -> PEM.eval t v.
  Proof with auto.
    intros.
    constructor.
    destruct H.
    apply transDecPem...
  Qed.
  Hint Resolve evalMachinePem.


  Theorem push_enter_correct : forall {t v}, PRS.RefSem.RS.eval t v <-> AM.eval t v.
  Proof.
    intros t v; rewrite (PEM.evalPem); split; auto.
  Qed.


  Module DEC := DEC.

  Definition dec_context_not_val := dec_context_not_val.
  Definition dec_term_value      := @dec_term_value.

End ProperPEMachine.