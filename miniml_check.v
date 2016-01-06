Require Import Program
               Entropy
               Util
               Subset
               rewriting_system
               miniml
               abstract_machine
               reduction_semantics
               reduction_languages_facts.




Module MiniML_HandDecProc.

  Module RF := RED_LANG_Facts MiniML_PreRefSem.
  Import MiniML_PreRefSem RF.

  Inductive dec_proc' : term -> context' -> decomp' -> Prop :=

  | d_z   : forall c d, decctx_proc' vZ c d             -> dec_proc' Z c d

  | d_s   : forall t c d, dec_proc' t (s_c =: c) d      -> dec_proc' (S t) c d

  | d_case: forall t ez x es c d, 
              dec_proc' t (case_c ez x es =: c) d       -> dec_proc' (Case t ez x es) c d

  | d_var : forall x c d, decctx_proc' (vVar x) c d     -> dec_proc' (Var x) c d

  | d_lam : forall x t c d, decctx_proc' (vLam x t) c d -> dec_proc' (Lam x t) c d

  | d_app : forall t1 t2 c d, 
              dec_proc' t1 (ap_r t2 =: c) d             -> dec_proc' (App t1 t2) c d

  | d_let : forall x t e c d, 
              dec_proc' t (let_c x e =: c) d            -> dec_proc' (Letv x t e) c d

  | d_fix : forall x t c, 
              dec_proc' (Fix x t) c (d_red (rFix x t) c)

  | d_pair: forall t1 t2 c d, 
              dec_proc' t1 (pair_r t2 =: c) d           -> dec_proc' (Pair t1 t2) c d

  | d_fst : forall t c d, dec_proc' t (fst_c =: c) d    -> dec_proc' (Fst t) c d

  | d_snd : forall t c d, dec_proc' t (snd_c =: c) d    -> dec_proc' (Snd t) c d


  with decctx_proc' : value' -> context' -> decomp' -> Prop :=

  | dc_em : forall v,
              decctx_proc' v [.] (d_val v)

  | dc_s  : forall v c d, decctx_proc' (vS v) c d -> decctx_proc' v (s_c =: c) d

  | dc_cs : forall v x ez es (c : context'),
              decctx_proc' v (case_c ez x es =: c) (d_red (rCase v ez x es) c)

  | dc_apr: forall v t (c : context') d, 
              dec_proc' t (ap_l v =: c) d         -> decctx_proc' v (ap_r t =: c) d

  | dc_apl: forall v v0 (c : context'),
              decctx_proc' v (ap_l v0 =: c) (d_red (rApp v0 v) c)

  | dc_let: forall v x e (c : context'),
              decctx_proc' v (let_c x e =: c) (d_red (rLet x v e) c)

  | dc_p_r: forall t v (c : context') d, 
              dec_proc' t (pair_l v =: c) d       -> decctx_proc' v (pair_r t =: c) d

  | dc_p_l: forall v v0 c d, 
              decctx_proc' (vPair v0 v) c d       -> decctx_proc' v (pair_l v0 =: c) d

  | dc_fst: forall v (c : context'), 
              decctx_proc' v (fst_c =: c) (d_red (rFst v) c)

  | dc_snd: forall v (c : context'), 
              decctx_proc' v (snd_c =: c) (d_red (rSnd v) c).


  Definition dec_proc : 
      term -> forall {k1 k2 : ckind}, context k1 k2 -> decomp k1 -> Prop 

      := fun t => ů ů(dec_proc' t).

  Definition decctx_proc : 
      forall {k2}, value k2 -> forall {k1}, context k1 k2 -> decomp k1 -> Prop 

      := ů(fun v => ů(decctx_proc' v)).

  Scheme dec_proc_Ind    := Induction for dec_proc'    Sort Prop
    with decctx_proc_Ind := Induction for decctx_proc' Sort Prop.


  Lemma dec_val_self : forall (v : value') c d, dec_proc' v c d <-> decctx_proc' v c d.
  Proof.
    induction v;
        intros c d; split; intro H;
        inversion H; dep_subst; 

    solve
    [ auto

    | constructor; auto

    | match goal with H : _ |- _ => 
      apply IHv in H;
      inversion H1; dep_subst;
      solve [ auto ]
      end

    | match goal with H : _ |- _ => 
      apply IHv1 in H;
      inversion H; dep_subst;
      match goal with H : _ |- _ => 
      apply IHv2 in H;
      inversion H; dep_subst;
      solve [ auto ]
      end end

    | constructor; fold (@value_to_term ()); 
      apply IHv; 
      constructor;
      auto

    | constructor; fold (@value_to_term ());
      apply IHv1; constructor;
      apply IHv2; constructor;
      auto ].
  Qed.


  Module RS := MiniML_RefSem.


  Hint Constructors RS.dec_proc RS.decctx_proc dec_proc' decctx_proc'.
  Hint Transparent MiniML_Strategy.dec_term MiniML_Strategy.dec_context.

  Theorem dec_proc_eqv_RS :                       forall {k1 k2} (c : context k1 k2) t d,
      dec_proc t c d <-> RS.dec_proc t c d.

  Proof.
    intros k1 k2 c t d; split; intro H.

  (* -> *) {
    destruct k1, k2.
    induction H using dec_proc_Ind with
    (P0 := fun v c d _ => RS.decctx_proc v c d); eauto;
    match goal with c : RS.context _ ?k |- RS.decctx_proc _ (?ec =: c) _ => 
    solve
    [ eapply (RS.dc_dec ec c); eauto
    | eapply (RS.dc_val ec c); eauto
    | eapply (RS.dc_term ec c); eauto ]
    end.
  }

 (* <- *) {
    induction H using RS.dec_proc_Ind with
    (P0 := fun _ v c d _ => decctx_proc v c d);
    try match goal with
    | H : RS.ST.dec_term ?t ?k = _        |- _ => destruct t, k2; 
                                                  inversion H; subst
    | H : RS.ST.dec_context ?ec ?k ?v = _ |- _ => destruct ec, k2; 
                                                  dependent_destruction2 v; 
                                                  inversion H; subst
    end;
    destruct_all ckind; simpl; eauto.
 }
 Qed.


  Theorem decctx_proc_eqv_RS :                    forall {k1 k2} (c : context k1 k2) v d,
      decctx_proc v c d <-> RS.decctx_proc v c d.

  Proof.
    intros k1 k2 c v d; split; intro H.

  (* -> *) {
    destruct k1, k2.
    induction H using decctx_proc_Ind with
    (P := fun t c d _ => RS.dec_proc t c d); eauto;
    match goal with c : RS.context _ ?k |- RS.decctx_proc _ (?ec =: c) _ => 
    solve
    [ eapply (RS.dc_dec ec c); eauto
    | eapply (RS.dc_val ec c); eauto
    | eapply (RS.dc_term ec c); eauto ]
    end.
  }

 (* <- *) {
    induction H using RS.decctx_proc_Ind with
    (P := fun _ t c d _ => dec_proc t c d);
    try match goal with
    | H : RS.ST.dec_term ?t ?k = _        |- _ => destruct t, k2; 
                                                  inversion H; subst
    | H : RS.ST.dec_context ?ec ?k ?v = _ |- _ => destruct ec, k2; 
                                                  dependent_destruction2 v; 
                                                  inversion H; subst
    end; 
    destruct_all ckind; simpl; eauto.
 }
 Qed.

End MiniML_HandDecProc.




Module MiniML_HandMachine.

  Import MiniML_EAM MiniML_PreRefSem.

  Notation "[$ t $]"         := (load t)                                 (t at level 99).
  Notation "[: v :]"         := (value_to_conf v)                        (v at level 99).
  Notation "[$ t , c , H $]" := (exist _ (RAW.c_eval t c) H)                     (t, k, c at level 99).
  Notation "[: c , v , H :]" := (exist _ (RAW.c_apply c v) H)                       (c, v at level 99).


  (*Lemma ick_aw : init_ckind ? alive_ckind.
  Proof. apply (init_ckind_alive `as witness of alive_ckind). Qed.*)

  Notation "[$ t , c $]" := (submember_by _ (RAW.c_eval t c) init_ckind_alive)                     (t, k, c at level 99).
  Notation "[: c , v :]" := (submember_by _ (RAW.c_apply c v) init_ckind_alive)                       (c, v at level 99).

  Definition next_conf0 (st : configuration) : option configuration :=
      match st with
      | [$ Z, c, _ $]               => Some [: c, vZ :]
      | [$ S t, c, _ $]             => Some [$ t, s_c =: c $]
      | [$ Var x, c, _ $]           => Some [: c, vVar x :]
      | [$ Lam x t, c, _ $]         => Some [: c, vLam x t :]
      | [$ App t1 t2, c, _ $]       => Some [$ t1, ap_r t2 =: c $]
      | [$ Case t ez x es, c, _ $]  => Some [$ t, case_c ez x es =: c $]
      | [$ Fix x t, c, _ $]         => Some [$ subst x (Fix x t) t, c $]
      | [$ Letv x t1 t2, c, _ $]    => Some [$ t1, let_c x t2 =: c $]
      | [$ Pair t1 t2, c, _ $]      => Some [$ t1, pair_r t2 =: c $]
      | [$ Fst t, c, _ $]           => Some [$ t, fst_c =: c $]
      | [$ Snd t, c, _ $]           => Some [$ t, snd_c =: c $]

      | [: (s_c =: c), v, _ :]               => Some [: c, vS v :]
      | [: (ap_r t =: c), v, _ :]            => Some [$ t, ap_l v =: c $]
      | [: (ap_l (vLam x t) =: c), v2, _ :]  => Some [$ subst x (v2 : term) t, c $]
      | [: (case_c ez x es =: c), vZ, _ :]   => Some [$ ez, c $]
      | [: (case_c ez x es =: c), vS v, _ :] => Some [$ subst x (v : term) es, c $]
      | [: (let_c x e =: c), v, _ :]         => Some [$ subst x (v : term) e, c $]
      | [: (pair_r t =: c), v, _ :]          => Some [$ t, pair_l v =: c $]
      | [: (pair_l v1 =: c), v2, _ :]        => Some [: c, vPair v1 v2 :]
      | [: (fst_c =: c), vPair v1 _, _ :]    => Some [$ v1 : term, c $]
      | [: (snd_c =: c), vPair _ v2, _ :]    => Some [$ v2 : term, c $]

      | _ => None
      end.
  Definition next_conf (_ : entropy) := next_conf0.

  Definition transition st1 st2 := next_conf0 st1 = Some st2.


  Instance rws : REWRITING_SYSTEM configuration :=
  { transition := transition }.


  Fact trans_computable0 :                              forall (st1 st2 : configuration),
       `(rws) st1 → st2 <-> next_conf0 st1 = Some st2.

  Proof. intuition. Qed.


  Fact trans_computable :                                                 forall st1 st2,
       `(rws) st1 → st2 <-> exists e, next_conf e st1 = Some st2.

  Proof. 
    intuition. 
    - destruct (draw_fin_correct 1 Fin.F1) as [e _]; exists e; auto.
    - destruct H; eauto.
  Qed.




  Theorem next_conf0_eq_EAM :                                                  forall st,
      next_conf0 st = MiniML_EAM.next_conf0 st.

  Proof.
    destruct st as [[t k ? | k c v] ?].
    - destruct t, k; compute; auto.
    - destruct c as [| ec k c]; auto.
      destruct ec, k; destruct v; 
      solve
      [ compute; auto
      | match goal with v : value' |- _ => 
        destruct v; compute; auto 
        end ].
  Qed.


  Corollary next_conf_eq_EAM :                                               forall e st,
      next_conf e st = MiniML_EAM.next_conf e st.

  Proof. eauto using next_conf0_eq_EAM. Qed.


  Corollary transition_eqv_EAM :                                          forall st1 st2,
      `(MiniML_EAM.rws) st1 → st2  <->  `(rws) st1 → st2.

  Proof.
    intros.
    rewrite trans_computable, MiniML_EAM.trans_computable.
    unfold MiniML_EAM.next_conf, next_conf.
    rewrite next_conf0_eq_EAM.
    intuition.
  Qed.


  Proposition final_correct :                                                  forall st,
       final st <> None -> ~exists st', `(rws) st → st'.

  Proof.
    destruct st as [[? | ? c v] ?]; auto.
    destruct c; auto.
    intros _ [st' H].
    inversion H.
  Qed.


  Fact finals_are_vals :                                                     forall st v,
       final st = Some v <-> st = v. 

  Proof. exact MiniML_EAM.finals_are_vals. Qed.


  Definition term          := term.
  Definition value         := value init_ckind.
  Definition configuration := configuration.
  Definition load          := load.
  Definition value_to_conf := value_to_conf.
  Definition final         := final.

End MiniML_HandMachine.
