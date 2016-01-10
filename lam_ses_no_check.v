Require Import Util
               Entropy
               Program
               Subset
               rewriting_system
               refocusing_semantics
               abstract_machine
               refocusing_machine
               reduction_languages_facts
               lam_ses_no.




Module Lam_SES_NO_HandDecProc.

  Module RF := RED_LANG_Facts Lam_SES_NO_PreRefSem.
  Import Lam_SES_NO_PreRefSem RF.


  Inductive dec_proc {k1} :  forall {k2}, term -> context k1 k2 -> decomp k1 -> Prop :=

  | d_Var    : forall n {k2} (c : context k1 k2) d, CECaD k2 ->
                 decctx_proc (vVar n k2) c d ->
                 dec_proc (Var n) c d

  | d_LamC   : forall t (c : context k1 C) d,
                 dec_proc t (lam_c =: c) d -> (*!*)
                 dec_proc (Lam t) c d
  | d_LamECa : forall t (c : context k1 ECa) d,
                 decctx_proc (vECaLam t) c d -> (*!*)
                 dec_proc (Lam t) c d
  | d_LamD  : forall t (c : context k1 D) d,
                 decctx_proc (vDLam t) c d -> (*!*)
                 dec_proc (Lam t) c d

  | d_App    : forall t1 t2 {k2} (c : context k1 k2) d, CECa k2 ->
                 dec_proc t1 (ap_r t2 =: c) d ->
                 dec_proc (App t1 t2) c d

  | d_AppD   : forall t1 t2 (c : context k1 D) d,
                 decctx_proc (vDApp t1 t2) c d ->
                 dec_proc (App t1 t2) c d

  | d_Sub    : forall t1 n t2 {k2} (c : context k1 k2) d, CECaD k2 ->
                 dec_proc t1 (stag_c (n, st_sub t2) =: c) d ->
                 dec_proc (Sub t1 n t2) c d

  | d_Shift  : forall t1 n m {k2} (c : context k1 k2) d, CECaD k2 ->
                 dec_proc t1 (stag_c (n, st_shift m) =: c) d ->
                 dec_proc (Shift t1 n m) c d


  with decctx_proc {k1} : forall {k2}, value k2 -> 
                              context k1 k2 -> decomp k1 -> Prop :=

  | dc_end        : forall (v : value k1),
                      ~ dead_ckind k1 ->
                      decctx_proc v [.] (d_val v)

  | dc_ap_rLamC   : forall t0 t (c : context k1 C),
                      decctx_proc (vECaLam t0) (ap_r t =: c) (d_red (rCApp t0 t) c)
  | dc_ap_rLamECa : forall t0 t (c : context k1 ECa),
                      decctx_proc (vECaLam t0) (ap_r t =: c) (d_red (rECaApp t0 t) c)

  | dc_ap_rVarC   : forall n t (c : context k1 C) d,
                      dec_proc t (ap_l (vCaVar n) =: c) d ->
                      decctx_proc (vECaVar n) (ap_r t =: c) d
  | dc_ap_rVarECa : forall n t (c : context k1 ECa) d,
                      dec_proc t (ap_l (vCaVar n) =: c) d ->
                      decctx_proc (vECaVar n) (ap_r t =: c) d

  | dc_ap_rAppC   : forall v1 v2 t (c : context k1 C) d,
                      dec_proc t (ap_l (vCaApp v1 v2) =: c) d ->
                      decctx_proc (vECaApp v1 v2) (ap_r t =: c) d
  | dc_ap_rAppECa : forall v1 v2 t (c : context k1 ECa) d,
                      dec_proc t (ap_l (vCaApp v1 v2) =: c) d ->
                      decctx_proc (vECaApp v1 v2) (ap_r t =: c) d

  | dc_ap_lC      : forall v1 v2 (c : context k1 C) d,
                      decctx_proc (vCApp v1 v2) c d ->
                      decctx_proc v2 (ap_l v1 =: c) d
  | dc_ap_lECa    : forall v1 v2 (c : context k1 ECa) d,
                      decctx_proc (vECaApp v1 v2) c d ->
                      decctx_proc v2 (ap_l v1 =: c) d

  | dc_lam_cC     : forall v (c : context k1 C) d,
                      decctx_proc (vCLam v) c d ->
                      decctx_proc v (lam_c =: c) d

  | dc_sub_cLamC   : forall t d (c : context k1 C),
                      decctx_proc (vDLam t) (stag_c d =: c) 
                                  (d_red (rSubLam C I t d) c)
  | dc_sub_cLamECa : forall t d (c : context k1 ECa),
                      decctx_proc (vDLam t) (stag_c d =: c) 
                                  (d_red (rSubLam ECa I t d) c)
  | dc_sub_cLamD   : forall t d (c : context k1 D),
                      decctx_proc (vDLam t) (stag_c d =: c)
                                  (d_red (rSubLam D I t d) c)

  | dc_sub_cVarC   : forall n d (c : context k1 C),
                      decctx_proc (vDVar n) (stag_c d =: c) 
                                  (d_red (rSubVar C I n d) c)
  | dc_sub_cVarECa : forall n d (c : context k1 ECa),
                      decctx_proc (vDVar n) (stag_c d =: c) 
                                  (d_red (rSubVar ECa I n d) c)
  | dc_sub_cVarD   : forall n d (c : context k1 D),
                      decctx_proc (vDVar n) (stag_c d =: c) 
                                  (d_red (rSubVar D I n d) c)

  | dc_sub_cAppC   : forall t1 t2 d (c : context k1 C),
                      decctx_proc (vDApp t1 t2) (stag_c d =: c)
                                  (d_red (rSubApp C I t1 t2 d) c)
  | dc_sub_cAppECa : forall t1 t2 d (c : context k1 ECa),
                      decctx_proc (vDApp t1 t2) (stag_c d =: c) 
                                  (d_red (rSubApp ECa I t1 t2 d) c)
  | dc_sub_cAppD   : forall t1 t2 d (c : context k1 D),
                      decctx_proc (vDApp t1 t2) (stag_c d =: c) 
                                  (d_red (rSubApp D I t1 t2 d) c).

  Scheme dec_proc_Ind    := Induction for dec_proc Sort Prop
    with decctx_proc_Ind := Induction for decctx_proc Sort Prop.


  Module RS := Lam_SES_NO_RefSem.


  Hint Constructors RS.dec_proc RS.decctx_proc dec_proc decctx_proc.
  Hint Transparent Lam_SES_NO_Strategy.dec_term Lam_SES_NO_Strategy.dec_context.

  Theorem dec_proc_eqv_RS :                       forall {k1 k2} (c : context k1 k2) t d,
      dec_proc t c d <-> RS.dec_proc t c d.

  Proof.
    intros k1 k2 c t d; split; intro H.

  (* -> *) { 
    induction H using dec_proc_Ind with
    (P0 := fun _ v c d _ => RS.decctx_proc v c d); 
    solve 
    [ try destruct k2; eautof
    | match goal with c : RS.context _ ?k |- RS.decctx_proc _ (?ec =: c) _ => 
      solve
      [ eapply (RS.dc_dec ec c); eauto
      | eapply (RS.dc_val ec c); eauto
      | eapply (RS.dc_term ec c); eauto ]
      end ].
  }

  (* <- *) {
    induction H using RS.dec_proc_Ind with
    (P0 := fun _ v c d _ => decctx_proc v c d);
    try match goal with
    | H : RS.ST.dec_term ?t ?k = _        |- _ => destruct t, k; 
                                                  inversion H; subst
    | H : RS.ST.dec_context ?ec ?k ?v = _ |- _ => destruct ec, k; 
                                                  dependent_destruction2 v; 
                                                  inversion H; subst
    end; eautof.
  }
  Qed.


  Theorem decctx_proc_eqv_RS :                    forall {k1 k2} (c : context k1 k2) v d,
      decctx_proc v c d <-> RS.decctx_proc v c d.

  Proof.
    intros k1 k2 c v d; split; intro H.

  (* -> *) {
    induction H using decctx_proc_Ind with
    (P := fun _ t c d _ => RS.dec_proc t c d); 
    solve 
    [ try destruct k2; eautof
    | match goal with c : RS.context _ ?k |- RS.decctx_proc _ (?ec =: c) _ => 
      solve
      [ eapply (RS.dc_dec ec c); eauto
      | eapply (RS.dc_val ec c); eauto
      | eapply (RS.dc_term ec c); eauto ]
      end ].
  }

  (* <- *) {
    induction H using RS.decctx_proc_Ind with
    (P := fun _ t c d _ => dec_proc t c d);
    try match goal with
    | H : RS.ST.dec_term ?t ?k = _        |- _ => destruct t, k; 
                                                  inversion H; subst
    | H : RS.ST.dec_context ?ec ?k ?v = _ |- _ => destruct ec, k; 
                                                  dependent_destruction2 v; 
                                                  inversion H; subst
    end; 
    solve [eauto].
  }
  Qed.

End Lam_SES_NO_HandDecProc.





Module Lam_SES_NO_HandMachine <: ABSTRACT_MACHINE.

  Import Lam_SES_NO_EAM Lam_SES_NO_PreRefSem.


  Definition term          := term.
  Definition value         := value init_ckind.
  Definition configuration := configuration.
  Definition load          := load.
  Definition value_to_conf := value_to_conf : value -> configuration.
  Coercion   value_to_conf : value >-> configuration.
  Definition final         := final.


  Definition contextD := (context C C + context C ECa + context C D) %type.
  Definition contextC := (context C C + context C ECa) %type.
  Definition contextA := context C C.

  Notation "[$ t $]"       := (submember_by _ (c_eval t [.]) init_ckind_alive
                                   : configuration)                      (t at level 99).
  Notation "[: v :]"       := (submember_by _ (c_apply [.] v) init_ckind_alive
                                   : configuration)                      (v at level 99).
  Notation "[$ t , k , c , H $]" := (@c_eval t k c ?& H)              (t, c at level 99).
  Notation "[: c , v , H :]"     := (c_apply c v ?& H)                (c, v at level 99).
  Notation "[: ( ec , k ) =: c , v , H :]" := 
      (c_apply (@ccons _ ec k c) v ?& H)                       (ec, k, c, v at level 99).


  Lemma pre_sub_CECaD_is_CECaD : forall k d, CECaD (k+>stag_c d) -> CECaD k.
  Proof. destruct k, d; simpl; auto. Qed.

  Lemma pre_ap_r_CECa_is_CECa : forall k t, CECa (k+>ap_r t) -> CECa k.
  Proof. destruct k; simpl; auto. Qed.

  Definition bs {A} (devil : False) : A := match devil with end.

  Definition rCECaApp t1 t2 k : CECa k -> redex k :=
      match k as k return CECa k -> redex k with
      | C    => fun _ => rCApp t1 t2 
      | ECa  => fun _ => rECaApp t1 t2
      | D    => bs
      | CBot => bs
      end.


  Definition next_conf0 (st : configuration) : option configuration :=
      match st with

      | [$ _, CBot, _, _ $]    => None

      | [$ Var n, k, c, _ $]   => Some [: c, vVar n k, I :]

      | [$ Lam t, D,   c, _ $] => Some [: c, vDLam t, I :]
      | [$ Lam t, ECa, c, _ $] => Some [: c, vECaLam t, I :]
      | [$ Lam t, C,   c, _ $] => Some [$ t, C, lam_c =: c, I $]

      | [$ App t1 t2, D,   c, _ $]  => Some [: c, vDApp t1 t2, I :]
      | [$ App t1 t2, ECa, c, _ $]  => Some [$ t1, ECa, ap_r t2 =: c, I  $]
      | [$ App t1 t2, C,   c, _ $]  => Some [$ t1, ECa, ap_r t2 =: c, I  $]

      | [$ Sub t1 j t2,  k, c, _ $] => Some [$ t1, _, stag_c (j, st_sub t2) =: c, I  $]
      | [$ Shift t1 j g, k, c, _ $] => Some [$ t1, _, stag_c (j, st_shift g) =: c, I  $]


      | [: (_, CBot) =: _, _, _ :] => None

       (* aux_D *)

       | [: stag_c d =: c, vDApp t1 t2, _ :] => 
                                      Some [$ contract0 (rSubApp D I t1 t2 d), _, c, I $]

       | [: stag_c d =: c, vDLam t, _ :] => 
                                      Some [$ contract0 (rSubLam D I t d) , _ , c , I $]

       | [: stag_c d =: c, vDVar i, _ :] => 
                                      Some [$ contract0 (rSubVar D I i d), _, c, I $]

       (* aux_C *)

       | [: (ap_r t2, ECa) =: c, vECaVar i, _ :] => 
                                      Some [$ t2, C, ap_l (vCaVar i) =: c, I $]
       | [: (ap_r t2, C)   =: c, vECaVar i, _ :] => 
                                      Some [$ t2, C, ap_l (vCaVar i) =: c, I $]

       | [: (ap_r t2, ECa) =: c, vECaApp v1 v2, _ :] => 
                                      Some [$ t2, C, ap_l (vCaApp v1 v2) =: c, I $]
       | [: (ap_r t2, C)   =: c, vECaApp v1 v2, _ :] => 
                                      Some [$ t2, C, ap_l (vCaApp v1 v2) =: c, I $]

       | [: (ap_r t2, ECa) =: c, vECaLam t1, _ :] => 
                                      Some [$ contract0 (rECaApp t1 t2), ECa, c, I $]
       | [: (ap_r t2, C)   =: c, vECaLam t1, _ :] => 
                                      Some [$ contract0 (rECaApp t1 t2), C, c, I $]

       (* aux_A *)

       | [: (ap_l v1, ECa) =: c, v2, _ :] => Some [: c, vECaApp v1 v2, I :]
       | [: (ap_l v1, C)   =: c, v2, _ :] => Some [: c, vCApp v1 v2, I :]

       | [: (lam_c, C)     =: c, v, _ :]  => Some [: c, vCLam v, I :]

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
      next_conf0 st = Lam_SES_NO_EAM.next_conf0 st.

  Proof.
    destruct st as [[t k ? | k c v] ?].
    - destruct t, k; eauto.
    - destruct c as [| ec k c]; eauto.
      destruct ec, k; dependent destruction v; eauto.
  Qed.


  Corollary next_conf_eq_EAM :                                               forall e st,
      next_conf e st = Lam_SES_NO_EAM.next_conf e st.

  Proof. eauto using next_conf0_eq_EAM. Qed.


  Corollary transition_eqv_EAM :                                          forall st1 st2,
      `(Lam_SES_NO_EAM.rws) st1 → st2  <->  `(rws) st1 → st2.

  Proof.
    intros.
    rewrite trans_computable, Lam_SES_NO_EAM.trans_computable.
    unfold Lam_SES_NO_EAM.next_conf, next_conf.
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

  Proof. exact Lam_SES_NO_EAM.finals_are_vals. Qed.


  Class SafeRegion (P : configuration -> Prop) :=
  { 
      preservation :                                                        forall t1 t2,
          P t1  ->  t1 → t2  ->  P t2;
      progress :                                                               forall t1,
          P t1  ->  (exists (v : value), t1 = v) \/ (exists t2, t1 → t2)
  }.

End Lam_SES_NO_HandMachine.
