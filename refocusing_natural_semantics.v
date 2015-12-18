
(*** Signatures ***)


Require Import reduction_semantics.
Require Import refocusing_semantics.



Module Type REF_EVALUATOR (R : RED_REF_SEM).

  Import R.
  Export ST.


  (*
  Inductive dec' : term -> forall {k1 k2}, context k1 k2 -> decomp k1 -> Prop :=

  | d_dec  : forall t {k1 k2} (c : context k1 k2) {r},
               dec_term t k2 = in_red r -> 
               dec' t c (d_red r c)
  | d_v    : forall t {k1 k2} {c : context k1 k2} {v d},
               dec_term t k2 = in_val v ->
               decctx v c d ->
               dec' t c d
  | d_term : forall t {t0 k1 k2} {c : context k1 k2} {ec d},
               dec_term t k2 = in_term t0 ec ->
               dec' t0 (ec=:c) d ->
               dec' t c d

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
                dec' t (ec0=:c) d ->
                decctx v (ec=:c) d.
  *)



  (* The evaluation function that is going to be realized :
     Fixpoint eval k t := 
         match dec_fun t [.](k) with
         | d_val v   => v
         | d_red r c => match contract r with
                        | None    => undefined
                        | Some t' => eval k c[t]
                        end
         end. *)
  Inductive eval k t : value k -> Prop :=
  | e_val : forall {v}, 
                dec_proc t [.](k) (d_val v) -> eval k t v
  | e_red : forall {k'} {c : context k k'} {r t' v}, 
                dec_proc t [.](k) (d_red r c) -> 
                contract r = Some t'     ->
                eval k c[t'] v           ->
                eval k t v.


  Axiom evalRS_imp_eval :                                    forall  {k t} {v : value k},
      ~dead_ckind k  ->  (k |~ t →* v)  ->  eval k t v.
  Axiom eval_eqv_RS :                                                     forall {k t v},
      eval k t v  <->  ~dead_ckind k /\ (k |~ t →* v).

End REF_EVALUATOR.




Module Type REF_NATURAL_SEM (R : RED_REF_SEM).

  Import R.
  Export ST.


  Inductive dec_eval : 
      term -> forall {k1 k2}, context k1 k2 -> value k1 -> Prop :=

  | de_dec  : forall t {t0 k1 k2} {c : context k1 k2} {r : redex k2} {v},
                  dec_term t k2 = in_red r -> 
                  contract r = Some t0 -> 
                  dec_eval t0 c v ->
                  dec_eval t c v
  | de_v    : forall t {k1 k2} {c : context k1 k2} {v v0},
                  dec_term t k2 = in_val v -> 
                  decctx_eval v c v0 ->
                  dec_eval t c v0
  | de_term : forall t {t0 ec k1 k2} {c : context k1 k2} {v},
                  dec_term t k2 = in_term t0 ec -> 
                  dec_eval t0 (ec=:c) v ->
                  dec_eval t c v

  with decctx_eval : forall {k2}, value k2 -> 
                         forall {k1}, context k1 k2 -> value k1 -> Prop :=

  | dce_end  : forall {k} (v : value k), 
                   ~ dead_ckind k ->
                   decctx_eval v [.] v
  | dce_dec  : forall ec {k2} (v0 : value (k2+>ec)) {k1} (c : context k1 k2) {r t v1},
                   dec_context ec k2 v0 = in_red r ->
                   contract r = Some t             ->
                   dec_eval t c v1                 ->
                   decctx_eval v0 (ec=:c) v1
  | dce_val  : forall {k2} {v1 : value k2} ec (v0 : value (k2+>ec)) 
                     {k1} {c  : context k1 k2} {v2},
                   dec_context ec k2 v0 = in_val v1 ->
                   decctx_eval v1 c v2 ->
                   decctx_eval v0 (ec=:c) v2
  | dce_term : forall ec {ec0 k2} (v0 : value (k2+>ec)) 
                            {k1} {c : context k1 k2} {t v1},
                   dec_context ec k2 v0 = in_term t ec0 ->
                   dec_eval t (ec0=:c) v1 ->
                   decctx_eval v0 (ec=:c) v1.

  Scheme dec_eval_Ind    := Induction for dec_eval    Sort Prop
    with decctx_eval_Ind := Induction for decctx_eval Sort Prop.


  Definition eval k t v := dec_eval t [.](k) v.



  Axioms
  (dec_evalRS_imp_dec_eval :         forall t {k1 k2} (v : value k1) (c : context k1 k2),
       ~dead_ckind k2  ->  (k1 |~ c[t] →* v)  ->  dec_eval t c v)
  (dec_eval_eqv_RS :                 forall t {k1 k2} (v : value k1) (c : context k1 k2),
          dec_eval t c v  <->  ~dead_ckind k1 /\ (k1 |~ c[t] →* v))

  (evalRS_imp_eval :                                         forall  {k t} {v : value k},
      ~dead_ckind k  ->  (k |~ t →* v)  ->  eval k t v)
  (eval_eqv_RS :                                                          forall {k t v},
      eval k t v  <->  ~dead_ckind k /\ (k |~ t →* v)).

End REF_NATURAL_SEM.




(*
Module Type PE_REF_NATURAL_SEM (R : RED_LANG) (PERS : PE_RED_REF_SEM R).

  Module ST := PERS.ST.
  Export ST.
  Import R.


  Axiom dec_context_not_val : 
      forall ec {k} v1 v0, dec_context ec k v0 <> in_val v1.

  Axiom dec_term_value : 
      forall {k} (v : value k), dec_term v k = in_val v.


  Inductive dec : term -> forall {k1 k2}, context k1 k2 -> value k1 -> Prop :=

  | dec_r    : forall t {t0 k1 k2} {c : context k1 k2} {r  v},
                 dec_term t k2 = in_red r -> 
                 contract r = Some t0 -> 
                 dec t0 c v ->
                 dec t c v
  | dec_val  : forall t {k} {v : value k},
               ~ dead_ckind k ->
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
  | e_intro : forall {t v}, dec t [.] v -> eval t v.

End PE_REF_NATURAL_SEM.*)





(*** Functors ***)


Require Export reduction_strategy.
Require Import 
    Program 
    Util
    reduction_languages_facts 
    reduction_semantics_facts 
    refocusing_semantics_facts.



Module RefEvaluator (R : RED_REF_SEM) <: REF_EVALUATOR R.

  Module RLF := RED_LANG_Facts R.
  Module RF  := RED_REF_SEM_Facts R.
  Module RD  := RedRefSemDet R.
  Import R RLF RF RD.
  Export ST.


  Inductive eval k t : value k -> Prop :=
  | e_val : forall {v}, 
                dec_proc t [.](k) (d_val v) -> eval k t v
  | e_red : forall {k'} {c : context k k'} {r t' v}, 
                dec_proc t [.](k) (d_red r c) -> 
                contract r = Some t'     ->
                eval k c[t'] v           ->
                eval k t v.



  Local Hint Constructors dec_proc decctx_proc eval.

  Lemma eval_imp_RS :                                                     forall {k} t v,
      eval k t v  ->  (k |~ t →* v).

  Proof with eauto using dec_proc_starts_alive.
    intros k t v E.
    dependent induction E.
    - apply dec_proc_eqv_dec in H...
      destruct H.
      simpl in H0; subst.
      constructor 1.
    - constructor 2 with (y:=c[t'])...
      exists k' c r t'.
      intuition.
      rewrite <- plug_empty with t k.
      apply dec_proc_eqv_dec...
  Qed.


  Lemma evalRS_imp_eval :                                     forall {k} t (v : value k),
      ~dead_ckind k  ->  (k |~ t →* v)  ->  eval k t v.

  Proof with eauto.
    intros k t v H H0.
    dependent induction H0. 
    - constructor 1.
      apply dec_proc_eqv_dec...
      constructor...
    - destruct H1 as [k' [c [r [t' [? [? ?]]]]]].
      subst.
      constructor 2 with k' c r t'...
      apply dec_proc_eqv_dec...
  Qed.


  Theorem eval_eqv_RS :                                                   forall {k} t v,
      eval k t v  <->  ~dead_ckind k /\ (k |~ t →* v).

  Proof.
    intuition eauto using evalRS_imp_eval, eval_imp_RS.
    destruct H;
    (
        assert (H' := dec_term_from_dead t k H0);
        dependent destruction H; 
        congruence
    ).
  Qed.

End RefEvaluator.




Module RefNaturalSem (R : RED_REF_SEM) <: REF_NATURAL_SEM R.

  Module RF := RED_LANG_Facts R.
  Import R RF.
  Export ST.


  Inductive dec_eval : 
      term -> forall {k1 k2}, context k1 k2 -> value k1 -> Prop :=

  | de_dec  : forall t {t0 k1 k2} {c : context k1 k2} {r : redex k2} {v},
                  dec_term t k2 = in_red r -> 
                  contract r = Some t0 -> 
                  dec_eval t0 c v ->
                  dec_eval t c v
  | de_v    : forall t {k1 k2} {c : context k1 k2} {v v0},
                  dec_term t k2 = in_val v -> 
                  decctx_eval v c v0 ->
                  dec_eval t c v0
  | de_term : forall t {t0 ec k1 k2} {c : context k1 k2} {v},
                  dec_term t k2 = in_term t0 ec -> 
                  dec_eval t0 (ec=:c) v ->
                  dec_eval t c v

  with decctx_eval : forall {k2}, value k2 -> 
                         forall {k1}, context k1 k2 -> value k1 -> Prop :=

  | dce_end  : forall {k} (v : value k), 
                   ~ dead_ckind k ->
                   decctx_eval v [.] v
  | dce_dec  : forall ec {k2} (v0 : value (k2+>ec)) {k1} (c : context k1 k2) {r t v1},
                   dec_context ec k2 v0 = in_red r ->
                   contract r = Some t             ->
                   dec_eval t c v1                 ->
                   decctx_eval v0 (ec=:c) v1
  | dce_val  : forall {k2} {v1 : value k2} ec (v0 : value (k2+>ec)) 
                     {k1} {c  : context k1 k2} {v2},
                   dec_context ec k2 v0 = in_val v1 ->
                   decctx_eval v1 c v2 ->
                   decctx_eval v0 (ec=:c) v2
  | dce_term : forall ec {ec0 k2} (v0 : value (k2+>ec)) 
                            {k1} {c : context k1 k2} {t v1},
                   dec_context ec k2 v0 = in_term t ec0 ->
                   dec_eval t (ec0=:c) v1 ->
                   decctx_eval v0 (ec=:c) v1.

  Scheme dec_eval_Ind    := Induction for dec_eval    Sort Prop
    with decctx_eval_Ind := Induction for decctx_eval Sort Prop.


  Definition eval k t v := dec_eval t [.](k) v.



  Module RE := RefEvaluator R.

  Local Hint Constructors dec_proc decctx_proc RE.eval dec_eval decctx_eval.


  Lemma dec_eval_imp_evalRE :                     forall t {k1 k2} v (c : context k1 k2),
     dec_eval t c v -> RE.eval k1 c[t] v.

  Proof with eauto using (proper_death2 [.]), dead_context_dead.
    intros t k1 k2 v c H.
    induction H using dec_eval_Ind with
    (P  := fun t k1 _ c v _                 => RE.eval k1 c[t] v)
    (P0 := fun k2 (v0 : value k2) k1 c v1 _ => RE.eval k1 c[v0] v1);
        try match goal with 
        | H : dec_term ?t ?k = _ |- _ =>
              assert (G := dec_term_correct t k); rewrite H in G 
        | H : dec_context ?ec ?k ?v = _ |- _ => 
              assert (G := dec_context_correct ec k v); rewrite H in G
        end;
        subst;
    try solve [simpl in *; congruence].

    - constructor 2 with k2 c r t0...
      assert (~dead_ckind k1) by (intro; eapply proper_death_trans; eauto).
      apply dec_proc_eqv_dec...
      constructor...
    - constructor 1.
      apply dec_proc_eqv_dec...
      constructor...
    - constructor 2 with k2 c r t...
      assert (~dead_ckind k1) by (intro; eapply proper_death_trans; eauto).
      apply dec_proc_eqv_dec... simpl.
      rewrite G.
      constructor...
  Qed.


  Lemma evalRE_imp_dec_eval :                                         forall t {k1 k2} v,
      forall c : context k1 k2, 
          ~dead_ckind k2 -> RE.eval k1 c[t] v -> dec_eval t c v.

  Proof with eauto using (proper_death2 [.]), death_propagation2, 
                             dec_term_next_alive, dec_context_next_alive.
    intros t k1 k2 v c G H.
    dependent induction H.
        apply dec_plug in H; eauto; 
        rewrite <- compose_empty in H.

    - remember (d_val v) as d eqn: H0; revert v H0; clear G.
      induction H using dec_Ind with
      (P  := fun t _ _ c d _  => forall v, d = d_val v -> dec_eval t c v)
      (P0 := fun _ v0 _ c d _ => forall v, d = d_val v -> decctx_eval v0 c v);
      solve 
      [ intuition eautof
      | intros v0 H; inversion H; eauto ].

    - remember (d_red r c0) as d eqn: H2; 
      revert G k' c0 r t' v H0 H1 H2 IHeval.
      induction H using dec_Ind with
      (P  := fun t k1 k2 c d _ =>
                 ~ dead_ckind k2 ->
                 forall (k' : ckind) (c0 : context k1 k') (r : redex k') 
                             (t' : term) (v : value k1),
                     contract r = Some t' ->
                     RE.eval k1 (c0) [t'] v ->
                     d = d_red r c0 ->
                     (forall (k3 : ckind) (c1 : context k1 k3), ~ dead_ckind k3 ->
                      forall t0 : term, (c0) [t'] = (c1) [t0] -> dec_eval t0 c1 v) ->
                     dec_eval t c v)

      (P0 := fun k2 v0 k1 c d _ =>
                 ~ dead_ckind k2 ->
                 forall (k' : ckind) (c0 : context k1 k') (r : redex k') (t' : term)
                            (v : value k1),
                     contract r = Some t' ->
                     RE.eval k1 (c0) [t'] v ->
                     d = d_red r c0 ->
                     (forall (k3 : ckind) (c1 : context k1 k3), ~ dead_ckind k3 ->
                      forall t0 : term, (c0) [t'] = (c1) [t0] -> dec_eval t0 c1 v) ->
                     decctx_eval v0 c v);

    intros G k' c0 r' t' v' H0 H1 H2 IH;
    inversion H2; clear H2; dep_subst...
  Qed.


  Axiom dec_evalRS_imp_dec_eval :              forall {t k1 k2} {v : value k1},
      forall c : context k1 k2,
          ~dead_ckind k2  ->  (k1 |~ c[t] →* v)  ->  dec_eval t c v.
  Axiom dec_eval_eqv_RS :                                   forall {t k1 k2 v},
      forall c : context k1 k2, 
          dec_eval t c v  <->  ~dead_ckind k1 /\ (k1 |~ c[t] →* v).


  Axiom evalRS_imp_eval :                          forall  {k t} {v : value k},
      ~dead_ckind k  ->  (k |~ t →* v)  ->  eval k t v.
  Axiom eval_eqv_RS :                                           forall {k t v},
      eval k t v  <->  ~dead_ckind k /\ (k |~ t →* v).

  Scheme dec_Ind    := Induction for dec    Sort Prop
    with decctx_Ind := Induction for decctx Sort Prop.


  Inductive eval : term -> value init_ckind -> Prop :=
  | e_intro : forall {t v}, dec t [.] v -> eval t v.

End RefNaturalSem.




Module PE_RefNaturalSem (R : RED_LANG) (PERS : PE_RED_REF_SEM R)
                                                  <: PE_REF_NATURAL_SEM R PERS.

  Module ST := PERS.ST.
  Export ST.
  Import R.


  Axiom dec_context_not_val : 
      forall ec {k} v1 v0, dec_context ec k v0 <> in_val v1.

  Axiom dec_term_value : 
      forall {k} (v : value k), dec_term v k = in_val v.


  Inductive dec : term -> forall {k1 k2}, context k1 k2 -> value k1 -> Prop :=

  | dec_r    : forall t {t0 k1 k2} {c : context k1 k2} {r  v},
                 dec_term t k2 = in_red r -> 
                 contract r = Some t0 -> 
                 dec t0 c v ->
                 dec t c v
  | dec_val  : forall t {k} {v : value k},
               ~ dead_ckind k ->
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
  | e_intro : forall {t v}, dec t [.] v -> eval t v.

End PE_RefNaturalSem.


